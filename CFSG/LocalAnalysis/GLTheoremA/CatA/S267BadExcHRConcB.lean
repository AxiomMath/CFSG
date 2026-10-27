module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRModelB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldNF
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcToralRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelAGen)

theorem exists_orderOf_eq_fixSubfield {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {σ : K ≃+* K} (hσ : orderOf σ = p) (hpK : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p ∧ σ (ζ : K) = ζ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow σ
  rw [hσ] at hc
  have hn1 : 1 ≤ Nat.card (fixSubfield σ) := Nat.card_pos
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  have h1 : p ∣ Nat.card (fixSubfield σ) - 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hpK ⊢
    rw [Nat.cast_sub hK1, ← hc] at hpK
    rw [Nat.cast_sub hn1]
    push_cast at hpK ⊢
    rwa [ZMod.pow_card] at hpK
  haveI : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨ζ', hζ'⟩ := CFSG.StandardType.TableBSymp.exists_orderOf_eq_of_dvd
    (K := fixSubfield σ) h1
  refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom ζ', ?_, ?_⟩
  · rw [orderOf_injective _ (Units.map_injective fun a b h => Subtype.ext h) ζ', hζ']
  · exact (mem_fixSubfield σ).1 (ζ' : fixSubfield σ).2

theorem dvd_sq_sub_one_of_dvd_sub_one {p Q : ℕ} (h : p ∣ Q - 1) : p ∣ Q ^ 2 - 1 :=
  h.trans (Nat.sub_one_dvd_pow_sub_one Q 2)

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem exists_embedding_of_equiv {p : ℕ} {X : Type} [Group X] (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (eX : X ≃* PSimple p S) :
    ∃ φ : X →* Ω, Function.Injective φ ∧ φ.range = S := by
  set eS : PSimple p S ≃* ↥S := (psimpleEquivCenterQuotOfCore hcore).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with heS
  refine ⟨S.subtype.comp (eX.trans eS).toMonoidHom,
    S.subtype_injective.comp (eX.trans eS).injective, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (eX.trans eS).surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Outer


theorem exists_hom_ringAut_E_of_not_dvd {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type)
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ τ.cartan.det) :
    ∃ Θ : MulAut (adjointGroup τ K) →* RingAut K, ∀ x ∈ Θ.ker, x ^ p = 1 →
      x ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨Φ, -, -, hΦ⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  refine ⟨(MonoidHom.fst _ _).comp (Φ.comp (QuotientGroup.mk' (inner (adjointGroup τ K)))), ?_⟩
  intro x hx hxp
  set y := QuotientGroup.mk' (inner (adjointGroup τ K)) x with hy
  have hyp : y ^ p = 1 := by rw [hy, ← map_pow, hxp, map_one]
  have h1 : (Φ y).1 = 1 := hx
  have hne : exactE τ ≠ 0 := by rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  have hE2 : exactE τ ∣ 2 := by rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  have h2 : (Φ y).2 = 1 := by
    have : NeZero (exactE τ) := ⟨hne⟩
    have hcard : Nat.card (Multiplicative (ZMod (exactE τ))) = exactE τ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hz2 : (Φ y).2 ^ 2 = 1 := by
      have h0 : (Φ y).2 ^ Nat.card (Multiplicative (ZMod (exactE τ))) = 1 := pow_card_eq_one'
      rw [hcard] at h0
      obtain ⟨c, hc⟩ := hE2
      rw [hc, pow_mul, h0, one_pow]
    have hzp : (Φ y).2 ^ p = 1 := by
      have := congrArg Prod.snd (show Φ y ^ p = 1 by rw [← map_pow, hyp, map_one])
      simpa using this
    have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.2 (hp.odd_of_ne_two hp2)
    exact (pow_eq_one_iff_of_coprime hcop).1 ⟨hz2, hzp⟩
  have hyk : y ∈ Φ.ker := Prod.ext h1 h2
  have hcop : Nat.Coprime (Nat.card Φ.ker) p := by
    refine Nat.Coprime.coprime_dvd_left hΦ ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact fun h => hdet (Int.natCast_dvd.2 h)
  have hw : (⟨y, hyk⟩ : Φ.ker) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).1 ⟨pow_card_eq_one', Subtype.ext (by simpa using hyp)⟩
  exact (QuotientGroup.eq_one_iff (N := inner (adjointGroup τ K)) x).1 (congrArg Subtype.val hw)

theorem card_le_pow_rank_add_two_E78 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {K : Type} [Field K] [Finite K]
    (hpK : p ∣ Nat.card K ^ 2 - 1) (eX : ↥(adjointGroup τ K) ≃* PSimple p S) :
    Nat.card B ≤ p ^ (τ.rank + 2) := by
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hdet : ¬ (p : ℤ) ∣ τ.cartan.det := by
    rcases hτ with rfl | rfl
    · rw [det_cartan_E7]
      intro h
      have h2 : p ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · rw [det_cartan_E8]
      intro h
      have h1 : p ∣ 1 := by exact_mod_cast h
      exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E_of_not_dvd (hτ.elim (fun h => Or.inr (Or.inl h))
    (fun h => Or.inr (Or.inr h))) K hp hp2 hdet
  exact card_le_pow_add_two_of_hom hp hS hperf hB hBC eX center_adjointGroup_eq_bot Θ hΘ
    fun F hF => card_le_pow_rank_of_E7_or_E8_of_dvd_sq hτ hp hp2 hpK hF

end Outer

section HeadE6


theorem concA_badExcCore_E6_of_dvd_sub_one_of_card_eq {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hp5 : 5 ≤ p)
    (hdvd : p ∣ Q.card - 1) (hBc : Nat.card B = p ^ (Tag.E6.rank + 2)) : S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_E6] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have hpK : p ∣ Nat.card K - 1 := by rwa [hK]
  have hK5 := five_le_card_of_dvd_sub_one hp5 hpK
  set eX : ↥(adjointGroup .E6 K) ≃* PSimple p S := eC.symm.trans e.symm with heX
  have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup hp hperf hcore eX (by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact not_dvd_of_dvd_three hp hp5 (Nat.gcd_dvd_left 3 _))
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_equiv hcore hZ eX
  obtain ⟨b, hb, β, hβ, hβφ⟩ := exists_outer_mem_of_card hp hS hcore hB hBc hBC φ hφ hφS
    center_adjointGroup_eq_bot (card_le_pow_rank_E6_of_dvd_sub_one hp hp5 hpK)
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  have hdet : ¬ (p : ℤ) ∣ Tag.E6.cartan.det := by
    rw [det_cartan_E6]
    intro h
    have h3 : p ∣ 3 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  refine concA_of_outer_exc (Or.inr (Or.inl rfl)) hK2 hp (by omega) (fun _ => by omega)
    (by decide : 2 ≤ Tag.E6.rank) hS hcore hZ hB hBC hBc.le hφ hφS hb hβ hβφ ?_
  intro σ hσ hout
  obtain ⟨ζ, hζ, hσζ⟩ := exists_orderOf_eq_fixSubfield hp hσ hpK
  exact modelBGen_hr (Or.inr (Or.inl rfl)) hK2 hp (by omega) hdet hσ hout
    (dvd_card_fixSubfield_sq_sub_one hp hσ (dvd_sq_sub_one_of_dvd_sub_one hpK)) hζ hσζ
    (fun γ hγ => abs_coeff_highNode_le_two hτ hγ) (sum_highRoot_mul_cartan hτ)
    (isQuasisimple_perpLevi_E6 hK2) (i₁ := (3 : Fin Tag.E6.rank)) (by decide)

end HeadE6

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
