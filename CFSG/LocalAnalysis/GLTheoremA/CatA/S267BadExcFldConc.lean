module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldNF
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcToralRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem five_le_card_of_dvd_sq_sub_one {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) : 5 ≤ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hdvdK : ringChar K ∣ Nat.card K := by rw [hK]; exact dvd_pow_self _ n.ne_zero
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  by_contra hlt
  push Not at hlt
  interval_cases h : Nat.card K
  · exact hK2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvdK)
  · have h8 : p ∣ 2 ^ 3 := by norm_num at hpK ⊢; exact hpK
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h8))
  · have h4 : ringChar K ∣ 2 ^ 2 := by norm_num; exact hdvdK
    exact hK2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h4))

theorem natCast_ne_zero_of_dvd_sq_sub_one {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K ^ 2 - 1) : (p : K) ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  intro h
  have hd : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).1 h
  have hpc : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 hd
  have hpQ : p ∣ Nat.card K ^ 2 := by
    rw [hK, ← hpc]
    exact dvd_pow (dvd_pow_self _ n.ne_zero) two_ne_zero
  have h1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have : p ∣ 1 := by
    have := Nat.dvd_sub hpQ hpK
    rwa [Nat.sub_sub_self h1] at this
  exact hp.not_dvd_one this

theorem orderOf_eq_two_of_dvd_sq_sub_one {p Q : ℕ} (hp : p.Prime) (hQ : 1 ≤ Q)
    (hpQ : p ∣ Q ^ 2 - 1) (hpQ1 : ¬ p ∣ Q - 1) : orderOf ((Q : ℕ) : ZMod p) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine orderOf_eq_prime ?_ ?_
  · have h := (ZMod.natCast_eq_zero_iff (Q ^ 2 - 1) p).2 hpQ
    rw [Nat.cast_sub hQ2, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h
    exact h
  · intro h
    apply hpQ1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hQ, h, Nat.cast_one, sub_self]


theorem card_le_pow_rank_F4_of_dvd_sq {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K ^ 2 - 1) {F : Subgroup (adjointGroup .F4 K)}
    (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ Tag.F4.rank := by
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.ringChar_ne_zero_of_finite K)⟩
  set L := FiniteField.Extension K (ringChar K) 2
  have hL : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K (ringChar K) 2
  have hL1 : p ∣ Nat.card L - 1 := by rw [hL]; exact hpq
  have hT : CFSG.StandardType.GGF4ToralRankInput L p := by
    rcases eq_or_ne p 3 with rfl | h3
    · exact CFSG.StandardType.TableBF4.ggF4ToralRankInput_three hL1
    · have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by decide)
      have := hp.two_le
      exact CFSG.StandardType.TableBF4.ggF4ToralRankInput_of_five_le hp (by omega) hL1
  have h := CFSG.StandardType.GGF4ToralRankInput.card_le hp hL1 hT
    (CFSG.StandardType.TableB.isElemAbelian_map hF
      (CFSG.StandardType.TableBExcTwo.adjointMap .F4 (algebraMap K L)))
  rwa [Subgroup.card_map_of_injective (CFSG.StandardType.TableBExcTwo.adjointMap_injective _)]
    at h

theorem card_le_pow_four_E6_of_dvd_sq {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 - 1) (hpq1 : ¬ p ∣ Nat.card K - 1)
    {F : Subgroup (adjointGroup .E6 K)} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ frameSize .E6 :=
  (CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_two K hp (by omega)
    (orderOf_eq_two_of_dvd_sq_sub_one hp Nat.card_pos hpq hpq1)).rank_le hp hF

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_adjointGroup_of_outer_of_nf {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hNF : ∀ β : MulAut (adjointGroup τ K), β ^ p = 1 →
      β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
      ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup τ K)), orderOf σ = p ∧
        δ * β * δ⁻¹ = entrywiseAdjointAut τ σ)
    (hpQ : p ∣ Nat.card K ^ 2 - 1) (hS : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hBc : Nat.card B = p ^ (frameSize τ + 2)) (eX : ↥(adjointGroup τ K) ≃* PSimple p S)
    (hX : ∀ F : Subgroup ↥(adjointGroup τ K), IsElemAbelian p F →
      Nat.card F ≤ p ^ frameSize τ) :
    S267ConcA p S B := by
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  set eS : PSimple p S ≃* ↥S := (psimpleEquivCenterQuotOfCore hcore).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with heS
  set φ : ↥(adjointGroup τ K) →* Ω := S.subtype.comp (eX.trans eS).toMonoidHom with hφdef
  have hφ : Function.Injective φ := S.subtype_injective.comp (eX.trans eS).injective
  have hφS : φ.range = S := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (eX.trans eS).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨b, hb, β, hβ, hβφ⟩ := exists_outer_mem_of_card hp hS hcore hB hBc hBC φ hφ hφS
    center_adjointGroup_eq_bot hX
  have hn : 2 ≤ frameSize τ := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  exact concA_of_outer_of_nf hp hNF hn hS hcore hZ hB hBC hBc.le hφ hφS hb hβ hβφ
    fun σ hσ hout => modelBGen_frame hτ hK2 hp hp2 (natCast_ne_zero_of_dvd_sq_sub_one hp hpQ)
      hpQ hσ hout

theorem concA_of_adjointGroup_of_outer {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : τ = .E6 → p ≠ 3) (hpQ : p ∣ Nat.card K ^ 2 - 1) (hS : S.Normal)
    (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hBc : Nat.card B = p ^ (frameSize τ + 2)) (eX : ↥(adjointGroup τ K) ≃* PSimple p S)
    (hX : ∀ F : Subgroup ↥(adjointGroup τ K), IsElemAbelian p F →
      Nat.card F ≤ p ^ frameSize τ) :
    S267ConcA p S B :=
  concA_of_adjointGroup_of_outer_of_nf hτ hK2 hp hp2
    (fun _ h1 h2 => exists_conj_entrywise_exc hτ hK2 hp hp2 hp3 h1 h2) hpQ hS hcore hZ hB hBC hBc
    eX hX

theorem concA_badExcCore_F4_of_outer {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.F4 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.F4 Q, hv⟩).Group) (hp2 : p ≠ 2)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hBc : Nat.card B = p ^ (frameSize .F4 + 2)) :
    S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_F4] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp hp2 hpK
  set eX : ↥(adjointGroup .F4 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    haveI := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_hopfMultiplier hK5).2
    rw [Nat.card_of_subsingleton
      (1 : CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .F4 K))]
    exact hp.not_dvd_one)
  exact concA_of_adjointGroup_of_outer (Or.inl rfl) hK2 hp hp2 (fun h => absurd h (by decide))
    hpK hS hcore hZ hB hBC hBc eX fun F hF => card_le_pow_rank_F4_of_dvd_sq hp hp2 hpK hF

theorem concA_badExcCore_E6_of_outer {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hp5 : 5 ≤ p)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hdvd1 : ¬ p ∣ Q.card - 1)
    (hBc : Nat.card B = p ^ (frameSize .E6 + 2)) : S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E6] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hpK1 : ¬ p ∣ Nat.card K - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp (by omega) hpK
  set eX : ↥(adjointGroup .E6 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact not_dvd_of_dvd_three hp hp5 (Nat.gcd_dvd_left 3 _))
  exact concA_of_adjointGroup_of_outer (Or.inr (Or.inl rfl)) hK2 hp (by omega)
    (fun _ => by omega) hpK hS hcore hZ hB hBC hBc eX fun F hF =>
      card_le_pow_four_E6_of_dvd_sq hp hp5 hpK hpK1 hF

theorem concA_badExcCore_E7_of_outer {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E7 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E7 Q, hv⟩).Group) (hp2 : p ≠ 2)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hBc : Nat.card B = p ^ (frameSize .E7 + 2)) :
    S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E7] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp hp2 hpK
  set eX : ↥(adjointGroup .E7 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e7_hopfMultiplier hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro h
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (h.trans (Nat.gcd_dvd_left 2 _))
    exact hp2 h2)
  exact concA_of_adjointGroup_of_outer (Or.inr (Or.inr (Or.inl rfl))) hK2 hp hp2
    (fun h => absurd h (by decide)) hpK hS hcore hZ hB hBC hBc eX fun F hF =>
      card_le_pow_rank_of_E7_or_E8_of_dvd_sq (Or.inl rfl) hp hp2 hpK hF

theorem concA_badExcCore_E8_of_outer {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E8 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E8 Q, hv⟩).Group) (hp2 : p ≠ 2)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hBc : Nat.card B = p ^ (frameSize .E8 + 2)) :
    S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E8] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sq_sub_one hK2 hp hp2 hpK
  set eX : ↥(adjointGroup .E8 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    haveI := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.e8_hopfMultiplier hK5).2
    rw [Nat.card_of_subsingleton
      (1 : CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .E8 K))]
    exact hp.not_dvd_one)
  exact concA_of_adjointGroup_of_outer (Or.inr (Or.inr (Or.inr rfl))) hK2 hp hp2
    (fun h => absurd h (by decide)) hpK hS hcore hZ hB hBC hBc eX fun F hF =>
      card_le_pow_rank_of_E7_or_E8_of_dvd_sq (Or.inr rfl) hp hp2 hpK hF

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
