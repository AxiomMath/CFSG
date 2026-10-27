module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz8
public import CFSG.GF2Type.Smith1979W3.CaseD.Stab
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM7Omega

open CFSG.LocalAnalysis.GLTheoremB.MovingAround

abbrev V8 : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ZMod 2

noncomputable abbrev Q8 : QuadraticForm (ZMod 2) V8 :=
  CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1

theorem nonempty_mulEquiv_elementaryGroup_of_catalog {S : Type} [Group S]
    (h : CFSG.Yardstones.Md0ec50421ce4.catalogIs S
      (CFSG.Yardstones.Md0ec50421ce4.onLie fun d => d = TauCeti.LieTypeIndex.twistedD 4 gfTwoPP)) :
    Nonempty (S ≃* ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q8)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p k => exact hi.elim
  | alternating n k => exact hi.elim
  | sporadic s => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    have hd : d = TauCeti.LieTypeIndex.twistedD 4 gfTwoPP := hi
    subst hd
    haveI : Fact (Nat.Prime gfTwoPP.p) := ⟨Nat.prime_two⟩
    exact InputsSeitz8.nonempty_equiv_elementaryGroup_minus_orthF2
      (n := 4) (q := gfTwoPP) (by norm_num) hv rfl rfl e

theorem card_V8 : Nat.card V8 = 256 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_sum]
  norm_num

theorem card_zeros_Q8 : Nat.card {v : V8 // Q8 v = 0} = 120 := by
  have h := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.card_zeros_quadMinus
    (m := 4) (by norm_num)
  norm_num at h
  rw [Nat.card_eq_fintype_card]
  exact h

theorem exists_ne_zero_fixed_of_alternatingGroup {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : alternatingGroup (Fin 7) →* (V ≃ₗ[ZMod 2] V)) (U : Submodule (ZMod 2) V)
    (hU : ∀ a : alternatingGroup (Fin 7), ∀ x ∈ U, ρ a x ∈ U)
    (h1 : 1 ≤ Module.finrank (ZMod 2) U) (h4 : Module.finrank (ZMod 2) U ≤ 4)
    {σ : alternatingGroup (Fin 7)} (hσ : orderOf σ = 7) :
    ∃ u ∈ U, u ≠ 0 ∧ ρ σ u = u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let d := Module.finrank (ZMod 2) U
  let ρU : alternatingGroup (Fin 7) →* (U ≃ₗ[ZMod 2] U) :=
    MonoidHom.mk' (fun a =>
      LinearEquiv.ofLinearMap
        (((ρ a).toLinearMap.comp U.subtype).codRestrict U fun x => hU a x.1 x.2)
        (((ρ a⁻¹).toLinearMap.comp U.subtype).codRestrict U fun x => hU a⁻¹ x.1 x.2)
        (LinearMap.ext fun x => by
          apply Subtype.ext
          change (ρ a) ((ρ a⁻¹) (x : V)) = (x : V)
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl)
        (LinearMap.ext fun x => by
          apply Subtype.ext
          change (ρ a⁻¹) ((ρ a) (x : V)) = (x : V)
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl))
      (fun a b => LinearEquiv.ext fun x => by
        apply Subtype.ext
        change (ρ (a * b)) (x : V) = (ρ a) ((ρ b) (x : V))
        rw [map_mul, LinearEquiv.mul_apply])
  have hρU_apply : ∀ (a : alternatingGroup (Fin 7)) (u : U),
      (((ρU a) u : U) : V) = ρ a u.1 := by
    intro a u
    rfl
  have hpow : (ρU σ).toEquiv ^ 7 = 1 := by
    have hσ7 : σ ^ 7 = 1 := by simpa [hσ] using pow_orderOf_eq_one σ
    have h7 : (ρU σ) ^ 7 = 1 := by
      rw [← map_pow, hσ7, map_one]
    have hperm : (ρU σ).toEquiv = MulAction.toPermHom (U ≃ₗ[ZMod 2] U) U (ρU σ) := by
      ext x
      simp [MulAction.toPermHom_apply, LinearEquiv.smul_def]
    rw [hperm, ← map_pow, h7, map_one]
  by_cases hd3 : d = 3
  · have hU3 : Module.finrank (ZMod 2) U = 3 := by simpa [d] using hd3
    have hcardU3 : Nat.card (U ≃ₗ[ZMod 2] U) = 168 :=
      CFSG.GF2Type.Smith1979W3.CaseD.card_linearEquiv_of_finrank_three (W := U) hU3
    haveI : Finite (U ≃ₗ[ZMod 2] U) :=
      Finite.of_injective (fun e : U ≃ₗ[ZMod 2] U => (e : U → U))
        (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
    have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    haveI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hnotinj : ¬ Function.Injective ρU := by
      intro hinj
      have hle := Nat.card_le_card_of_injective ρU hinj
      rw [hA7, hcardU3] at hle
      omega
    have hker : ρU.ker = ⊤ := by
      haveI : ρU.ker.Normal := MonoidHom.normal_ker ρU
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρU.ker with hbot | htop
      · exact absurd ((MonoidHom.ker_eq_bot_iff ρU).mp hbot) hnotinj
      · exact htop
    have hσker : σ ∈ ρU.ker := by
      rw [hker]
      exact Subgroup.mem_top σ
    have hρUσ : ρU σ = 1 := MonoidHom.mem_ker.mp hσker
    obtain ⟨u, hu⟩ :=
      Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hU3]; norm_num)
    refine ⟨u.1, u.2, ?_, ?_⟩
    · intro h0
      exact hu (Subtype.ext h0)
    · have h := congrArg (fun e : U ≃ₗ[ZMod 2] U => ((e u : U) : V)) hρUσ
      simpa [hρU_apply] using h
  · have hdmem : d = 1 ∨ d = 2 ∨ d = 4 := by omega
    let F : Submodule (ZMod 2) U := LinearMap.ker ((ρU σ).toLinearMap - 1)
    have hFmem : ∀ x : U, x ∈ F ↔ (ρU σ) x = x := by
      intro x
      simp [F, sub_eq_zero]
    let eF : {x : U // (ρU σ).toEquiv x = x} ≃ F :=
      Equiv.subtypeEquiv (Equiv.refl U) (fun x => by
        simpa using (hFmem x).symm)
    have hcardU : Nat.card U = 2 ^ d := by
      rw [← FiniteField.pow_finrank_eq_natCard 2 U]
    have hFpow : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
      rw [← FiniteField.pow_finrank_eq_natCard 2 F]
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hmod := SFM7Lin.card_perm_modEq (ρU σ).toEquiv (p := 7) hpow
    rw [Nat.card_congr eF] at hmod
    have hpos : 0 < Module.finrank (ZMod 2) F := by
      by_contra hle
      have hzero : Module.finrank (ZMod 2) F = 0 := Nat.eq_zero_of_not_pos hle
      have hF1 : Nat.card F = 1 := by rw [hFpow, hzero, pow_zero]
      rw [hF1, hcardU] at hmod
      rcases hdmem with hd1 | hd2 | hd4
      · rw [hd1] at hmod; norm_num at hmod
      · rw [hd2] at hmod; norm_num at hmod
      · rw [hd4] at hmod; norm_num at hmod
    obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    refine ⟨u.1.1, u.1.2, ?_, ?_⟩
    · intro h0
      exact hu (Subtype.ext (Subtype.ext h0))
    · have hfix := (hFmem u.1).1 u.2
      have hval := congrArg Subtype.val hfix
      rwa [hρU_apply σ u.1] at hval

end CFSG.LocalAnalysis.GLTheoremA.SFM7Omega
