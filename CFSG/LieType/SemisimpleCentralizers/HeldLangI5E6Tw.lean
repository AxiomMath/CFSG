module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6Perfect
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5CoverExcTwo
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwRank
public import CFSG.LieType.SeitzGeneration.TwE6SubfieldInndiag
public import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc CFSG.LieType.SeitzGeneration.TwE6Subfield

theorem three_dvd_add_one_of_three_dvd_cube_add_one {c : ℕ} (h : 3 ∣ c ^ 3 + 1) : 3 ∣ c + 1 := by
  have hx : c ^ 3 % 3 = c % 3 := by
    have := Nat.mod_lt c (by norm_num : 3 > 0)
    interval_cases hm3 : c % 3 <;> simp [Nat.pow_mod, hm3]
  omega

section Certificates

theorem kd264I5Universal_twE6 (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (h3q : 3 ∣ q.card + 1) (L : Type) [Group L]
    [Finite L] (hL : IsI5UniversalCover ⟨.twistedE6 q, hd⟩ L) (β : MulAut L) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L)) :
    ∃ E : Subgroup L, E ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β ∧ IsElemAbelian 3 E ∧
      5 + CFSG.Open.pRank 3 (Subgroup.center L) ≤ CFSG.Open.pRank 3 E := by
  classical
  haveI hcyc : IsCyclic ↥(Subgroup.center L) := hL.2.2.1
  obtain ⟨eX⟩ := hL.2.1
  have hγ3 : onCenterQuotient β ^ 3 = 1 := by
    have := congrArg (centerQuotientHom L) hβ3
    rwa [map_pow, map_one] at this
  by_cases hq2 : q.card = 2
  · exact (false_of_outer_three_twistedE6_two q hd hq2 eX (onCenterQuotient β) hγ3 hout).elim
  have hZ3 : Nat.card (Subgroup.center L) = 3 := by
    rw [hL.2.2.2]
    exact Nat.gcd_eq_left h3q
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p (2 * q.exponent) with hF
  have hF2 : Nat.card F = q.card ^ 2 := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
  have hFt : Nat.card F = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := hF2
  let σF : F →+* F := iterateFrobenius F q.p q.exponent
  have hσF : ∀ x, σF x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact iterateFrobenius_def q.p q.exponent x
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hd F hFt σF hσF
  have hTw : TwistedChevalleyModel (L ⧸ Subgroup.center L) .E6 (q.p ^ q.exponent) :=
    ⟨F, inferInstance, inferInstance, by rw [hF2, TauCeti.PrimePower.card_def]; rfl, σF,
      fun x => by rw [hσF x, TauCeti.PrimePower.card_def], ⟨eX.trans b.symm⟩⟩
  have hE : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, hTw⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv q.prime_p q.exponent_pos hTw
  have hC := commutator_twistedE6RootGroup hE σ e
  have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  let α : MulAut (twistedE6RootGroup K σ) := MulAut.congr e.symm (onCenterQuotient β)
  have hα3 : α ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, -, -⟩, -, hΓ, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  have hαo : α ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := fun hmem =>
    hout ((mem_innAutDerived_congr e.symm).1
      (commutator_le_innAutDerived _ (twistedE6Inndiag_le_commutator σ hK hσ hC hmem)))
  obtain ⟨hηo, ⟨f₀, hf₀⟩, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag q.prime_p
    q.exponent_pos K hK2 σ hσ Θ hΘ Nat.prime_three (by norm_num) hα3 hαo
  set η : K ≃+* K := Θ α with hη
  have hKq : Nat.card K = q.card ^ 2 := by rw [hK, TauCeti.PrimePower.card_def]
  have hσq : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ x, TauCeti.PrimePower.card_def]
  obtain ⟨q₀, hq₀p, hqq, hFix⟩ := exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hKq η
    Nat.prime_three (by norm_num) hηo
  have hσ₀q : ∀ x : ↥(fixSubfield η), fixSubfieldRestrict σ η x = x ^ q₀.card :=
    fixSubfieldRestrict_eq_pow_twE6 hqq (by decide) σ hσq η hFix
  have hσ₀ : ∀ x : ↥(fixSubfield η), fixSubfieldRestrict σ η x = x ^ (q₀.p ^ q₀.exponent) := fun x => by
    rw [hσ₀q x, TauCeti.PrimePower.card_def]
  have hK₀ : Nat.card ↥(fixSubfield η) = (q₀.p ^ q₀.exponent) ^ 2 := by
    rw [hFix, TauCeti.PrimePower.card_def]
  have h3q₀ : 3 ∣ q₀.p ^ q₀.exponent + 1 := by
    rw [← TauCeti.PrimePower.card_def]
    rw [hqq] at h3q
    exact three_dvd_add_one_of_three_dvd_cube_add_one h3q
  have hJfix : ∀ x ∈ twFJ σ η, fieldActor σ η x = x := fun x hx => twFJ_le_twR σ η hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hΓ₀, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q₀.prime_p q₀.exponent_pos
      ↥(fixSubfield η) hK₀ (fixSubfieldRestrict σ η) hσ₀
  have hperf₀ : commutator ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)) = ⊤ :=
    commutator_twistedE6RootGroup_eq_top q₀.prime_p q₀.exponent_pos hK₀ (fixSubfieldRestrict σ η) hσ₀
  let JC : Subgroup ↥(twistedE6RootGroup K σ) := (twFJ σ η).map ψ⁻¹.toMonoidHom
  let JX : Subgroup (L ⧸ Subgroup.center L) := JC.map e.toMonoidHom
  let Ψ₁ : ↥JX ≃* ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)) :=
    (Subgroup.equivMapOfInjective JC e.toMonoidHom e.injective).symm.trans
      ((Subgroup.equivMapOfInjective (twFJ σ η) ψ⁻¹.toMonoidHom ψ⁻¹.injective).symm.trans
        (twFJModelEquiv σ η).symm)
  let σ₀ : ↥(fixSubfield η) →+* ↥(fixSubfield η) := (fixSubfieldRestrict σ η).toRingHom
  let Ψ : ↥JX ≃* ↥(twDerived σ₀) := Ψ₁.trans (MulEquiv.subgroupCongr hΓ₀.symm)
  haveI : Finite ↥(twDerived σ₀) := Finite.of_equiv ↥JX Ψ.toEquiv
  haveI : Group.IsPerfect ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)) :=
    Group.isPerfect_def.2 hperf₀
  haveI : Group.IsPerfect ↥JX :=
    Group.IsPerfect.ofSurjective (f := Ψ₁.symm.toMonoidHom) Ψ₁.symm.surjective
  have hJ : ⁅JX, JX⁆ = JX := commutator_eq_self_of_isPerfect JX
  have hfix : ∀ j ∈ JX, onCenterQuotient β j = j := by
    rintro _ ⟨c, ⟨j₀, hj₀, rfl⟩, rfl⟩
    have h1 : α (ψ⁻¹ j₀) = ψ⁻¹ j₀ := by
      have h3 : ψ (α (ψ⁻¹ j₀)) = j₀ := by
        have := congrArg (fun a : MulAut ↥(twistedE6RootGroup K σ) => a j₀) hψ
        exact this.trans (hJfix j₀ hj₀)
      calc α (ψ⁻¹ j₀) = ψ⁻¹ (ψ (α (ψ⁻¹ j₀))) := (ψ.symm_apply_apply _).symm
        _ = ψ⁻¹ j₀ := by rw [h3]
    have h2 : onCenterQuotient β (e (ψ⁻¹ j₀)) = e (α (ψ⁻¹ j₀)) := by
      simp [α, MulAut.congr_apply]
    exact h2.trans (congrArg e h1)
  have hH : Subgroup.center ↥(twDerived σ₀) = ⊥ :=
    center_twDerived_eq_bot σ₀ q₀.prime_p q₀.exponent_pos hK₀ hσ₀
  have hrank : ∀ (M : Type) [Group M] [Finite M] (π : M →* ↥(twDerived σ₀)), Function.Surjective π →
      (∀ x, π x = 1 ↔ x ∈ Subgroup.center M) → 3 ∣ Nat.card (Subgroup.center M) →
        6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup M) := by
    intro M _ _ π hπ hker hZ
    haveI : Fact q₀.p.Prime := ⟨q₀.prime_p⟩
    haveI : Fintype ↥(fixSubfield η) := Fintype.ofFinite _
    haveI : CharP ↥(fixSubfield η) q₀.p := charP_of_card_eq_prime_pow (f := 2 * q₀.exponent)
      (by rw [← Nat.card_eq_fintype_card, hK₀, ← pow_mul, mul_comm])
    exact six_le_pRank_of_cover_twE6 σ₀ q₀.exponent_pos h3q₀ hK₀ hσ₀ π hπ hker hZ
  obtain ⟨E, hEfix, hEab, m, hEcard, hm⟩ :=
    exists_elemAbelian_of_perfect_fixed_subgroup β hβ3 hZ3 hJ hfix Ψ hH hrank
  refine ⟨E, hEfix, hEab, ?_⟩
  have h1 : m ≤ CFSG.Open.pRank 3 E := le_pRank_of_card E hEab hEcard
  have h2 : CFSG.Open.pRank 3 (Subgroup.center L) ≤ 1 := pRank_le_one_of_isCyclic _
  omega

end Certificates

end CFSG.LieType.SemisimpleCentralizers.HeldLang
