module

public import CFSG.ClassicalInvolution.Asc77.AscT7JSq
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen
public import CFSG.ClassicalInvolution.Q3.Q3NMInner
public import CFSG.ClassicalInvolution.Q3.Q3NMTwin
import CFSG.ClassicalInvolution.AschTight.S19GD4Aut
import CFSG.ClassicalInvolution.AschTight.S19GG2Aut
public import CFSG.ClassicalInvolution.Q3.Q3NMClass

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.FrameVertex CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.LieType.Universal

section Generic

theorem alphaOf_pair_inner_eq_bot {H : Type} [Group H] (L : Subgroup H)
    (hL : Q3NM.AutOddFreeInner ↥L) {a b : ↥(inducedAutOn L)} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (hne : a ≠ 1 ∨ b ≠ 1) (hai : ((a : ↥(inducedAutOn L)) : MulAut ↥L) ∈
      Q3NM.innSubgroup ↥L) (hbi : ((b : ↥(inducedAutOn L)) : MulAut ↥L) ∈ Q3NM.innSubgroup ↥L) :
    alphaOf (Subgroup.closure ({a, b} : Set ↥(inducedAutOn L))) = ⊥ := by
  refine Q3NM.alphaOf_eq_bot_of_on L (fun τ => τ ∈ Q3NM.innSubgroup ↥L)
    (Q3NM.AutOddFreeInner.toOn hL) _ (Q3NM.mul_self_eq_one_of_mem_closure_pair ha2 hb2 hab)
    (by
      rcases hne with h | h
      · exact ⟨a, Subgroup.subset_closure (by simp), h⟩
      · exact ⟨b, Subgroup.subset_closure (by simp), h⟩) ?_
  intro g hg _
  have hle : Subgroup.closure ({a, b} : Set ↥(inducedAutOn L)) ≤
      (Q3NM.innSubgroup ↥L).comap (inducedAutOn L).subtype := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hai
    · exact hbi
  exact hle hg

end Generic

section Model

variable {H : Type} [Group H] [Finite H]

theorem innerHom_mem_innSubgroup {S : Type} [Group S] (ψ : S →* H) (s : S) :
    ((innerHom ψ s : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) ∈
      Q3NM.innSubgroup ↥ψ.range := by
  rw [innerHom_apply]
  exact Q3NM.toInducedAutOn_mem_innSubgroup ψ.range (ψ s)
    (FrameVertex.mem_normalizer_range ψ s) ⟨s, rfl⟩

theorem exists_innerHom_of_fixes {t : StatedLieTag} (M : LieUniversal) [Group.IsPerfect M.K]
    (hZ : Subgroup.center M.K = ⊥)
    (hfix : ∀ (α : MulAut M.K) (n : ℕ), α ^ (2 ^ n) = 1 → ∀ R ∈ fundamentalSubgroups t M.D,
      (∀ r ∈ R, α r = r) → ∃ g : M.K, α = MulAut.conj g)
    (ψ : M.K →* H) (hker : ψ.ker ≤ Subgroup.center M.K) {R : Subgroup M.K}
    (hR : R ∈ fundamentalSubgroups t M.D) (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) (hv4 : v * v * (v * v) = 1) :
    ∃ b : M.K, v = innerHom ψ b := by
  let π := MonoidHom.id M.K
  have hπ : Function.Surjective π := Function.surjective_id
  have hπk : π.ker = Subgroup.center M.K := by
    rw [hZ]
    exact MonoidHom.ker_id
  have hfixr : ∀ r ∈ R, outerAction ψ hker π hπ hπk v (π r) = π r := fun r hr => by
    apply (outerEquiv ψ hker π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hvR r hr]
    group
  have hφ4 : (outerAction ψ hker π hπ hπk v) ^ (2 ^ 2) = 1 := by
    have h := congrArg (outerAction ψ hker π hπ hπk) hv4
    simp only [map_mul, map_one] at h
    calc (outerAction ψ hker π hπ hπk v) ^ (2 ^ 2) =
        outerAction ψ hker π hπ hπk v * outerAction ψ hker π hπ hπk v *
          (outerAction ψ hker π hπ hπk v * outerAction ψ hker π hπ hπk v) := by
          norm_num [pow_succ, mul_assoc]
      _ = 1 := h
  obtain ⟨b, hb⟩ := hfix _ 2 hφ4 R hR hfixr
  refine ⟨b, ?_⟩
  have h1 : outerAction ψ hker π hπ hπk ((innerHom ψ b)⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, outerAction_innerHom, hb]
    exact inv_mul_cancel _
  exact (inv_mul_eq_one.mp (eq_one_of_outerAction_eq_one ψ hker π hπ hπk h1)).symm

theorem twinSqOuter_of_fixInner {t : StatedLieTag} (M : LieUniversal) [Group.IsPerfect M.K]
    (hZ : Subgroup.center M.K = ⊥)
    (hfix : ∀ (α : MulAut M.K) (n : ℕ), α ^ (2 ^ n) = 1 → ∀ R ∈ fundamentalSubgroups t M.D,
      (∀ r ∈ R, α r = r) → ∃ g : M.K, α = MulAut.conj g)
    (hodd : ∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H), ψ.ker ≤ Subgroup.center M.K →
      Q3NM.AutOddFreeInner ↥ψ.range) :
    TwinSqAlphaOn t M ∧ TwinOuterAlphaOn t M := by
  have hcen : ∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H) (hker : ψ.ker ≤ Subgroup.center M.K)
      (g : M.K), innerHom ψ g = 1 → g = 1 := fun H _ _ ψ hker g hg => by
    have := (innerHom_spec ψ hker).1 g hg
    rwa [hZ, Subgroup.mem_bot] at this
  refine ⟨?_, ?_⟩
  · intro H _ _ ψ R R' x x' hpair k hk hkk v hvR hvR' hvv
    have hxx : innerHom ψ x * innerHom ψ x = 1 := by
      rw [← map_mul, hpair.hx2, map_one]
    have hv4 : v * v * (v * v) = 1 := by rw [hvv, hxx]
    obtain ⟨b, rfl⟩ := exists_innerHom_of_fixes M hZ hfix ψ hpair.ker hpair.mem v hvR hv4
    have hxi1 : innerHom ψ x ≠ 1 := fun h => hpair.hx1 (hcen H ψ hpair.ker x h)
    have hkk' : innerHom ψ k * innerHom ψ k = innerHom ψ x := by
      rw [innerHom_apply, innerHom_apply, ← map_mul]
      have : (⟨ψ k, FrameVertex.mem_normalizer_range ψ k⟩ *
          ⟨ψ k, FrameVertex.mem_normalizer_range ψ k⟩ :
            ↥(Subgroup.normalizer (ψ.range : Set H))) =
          ⟨ψ x, FrameVertex.mem_normalizer_range ψ x⟩ := Subtype.ext hkk
      rw [this]
    have hkb : innerHom ψ b * innerHom ψ k = innerHom ψ k * innerHom ψ b := hvR k hk
    have hxb : innerHom ψ b * innerHom ψ x = innerHom ψ x * innerHom ψ b := hvR x hpair.hx
    have hxk : innerHom ψ k * innerHom ψ x = innerHom ψ x * innerHom ψ k := by
      rw [← hkk']
      group
    have hy2 : (innerHom ψ k * innerHom ψ b) * (innerHom ψ k * innerHom ψ b) = 1 := by
      calc (innerHom ψ k * innerHom ψ b) * (innerHom ψ k * innerHom ψ b) =
          (innerHom ψ k * innerHom ψ k) * (innerHom ψ b * innerHom ψ b) := by
            rw [mul_assoc, ← mul_assoc (innerHom ψ b), hkb, mul_assoc, ← mul_assoc]
        _ = 1 := by rw [hkk', hvv, hxx]
    have hyx : (innerHom ψ k * innerHom ψ b) * innerHom ψ x =
        innerHom ψ x * (innerHom ψ k * innerHom ψ b) := by
      rw [mul_assoc, hxb, ← mul_assoc, hxk, mul_assoc]
    exact alphaOf_pair_inner_eq_bot ψ.range (hodd H ψ hpair.ker) hy2 hxx hyx (Or.inr hxi1)
      (by
        have := (Q3NM.innSubgroup ↥ψ.range).mul_mem (innerHom_mem_innSubgroup ψ k)
          (innerHom_mem_innSubgroup ψ b)
        exact this)
      (innerHom_mem_innSubgroup ψ x)
  · intro H _ _ ψ R R' x x' hpair v hvR hvR' hv4 hv2 hv2x
    obtain ⟨b, hb⟩ := exists_innerHom_of_fixes M hZ hfix ψ hpair.ker hpair.mem v hvR hv4
    have hxx : innerHom ψ x * innerHom ψ x = 1 := by
      rw [← map_mul, hpair.hx2, map_one]
    have hxi1 : innerHom ψ x ≠ 1 := fun h => hpair.hx1 (hcen H ψ hpair.ker x h)
    have hxv : innerHom ψ x * (v * v) = (v * v) * innerHom ψ x := by
      have h1 : v * innerHom ψ x = innerHom ψ x * v := hvR x hpair.hx
      rw [← mul_assoc, ← h1, mul_assoc, ← h1, mul_assoc]
    rw [Set.pair_comm]
    refine alphaOf_pair_inner_eq_bot ψ.range (hodd H ψ hpair.ker) hv4 hxx hxv.symm
      (Or.inr hxi1) ?_ (innerHom_mem_innSubgroup ψ x)
    · subst hb
      exact (Q3NM.innSubgroup ↥ψ.range).mul_mem (innerHom_mem_innSubgroup ψ b)
        (innerHom_mem_innSubgroup ψ b)

end Model

section Rows


theorem twinRows3_g2 (hadm : StatedLieAdmissible .G2 0 3 1) :
    TwinSqAlpha 3 1 .G2 0 ∧ TwinOuterAlpha 3 1 .G2 0 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hZ : Subgroup.center (modelUniv .G2 0 3 1 Fact.out).K = ⊥ :=
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0 le_rfl
  have : Group.IsPerfect (modelUniv .G2 0 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .G2 0 3 1 Fact.out trivial hadm).1.1
  refine twinSqOuter_of_fixInner (t := .G2) (modelUniv .G2 0 3 1 Fact.out) hZ ?_ ?_
  · intro α n hα R hR hfixR
    exact Disconnected.AschTight.S19G.exists_conj_of_fixes_g2 (p := 3) hp2 (e := 1) le_rfl α hR
      hfixR
  · intro H _ _ ψ hker
    exact Q3NM.autOddFreeInnerTag_of_not_D4 (t := .G2) (n := 0) (by simp) (by decide)
      Nat.prime_three trivial hadm ↥ψ.range ψ.rangeRestrict ψ.rangeRestrict_surjective
      (by rwa [MonoidHom.ker_rangeRestrict])

theorem twinRows3_trialityD4 (hadm : StatedLieAdmissible .trialityD4 0 3 1) :
    TwinSqAlpha 3 1 .trialityD4 0 ∧ TwinOuterAlpha 3 1 .trialityD4 0 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hZ : Subgroup.center (modelUniv .trialityD4 0 3 1 Fact.out).K = ⊥ :=
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 le_rfl
  have : Group.IsPerfect (modelUniv .trialityD4 0 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .trialityD4 0 3 1 Fact.out trivial
        hadm).1.1
  refine twinSqOuter_of_fixInner (t := .trialityD4) (modelUniv .trialityD4 0 3 1 Fact.out) hZ ?_ ?_
  · intro α n hα R hR hfixR
    exact Disconnected.AschTight.S19G.exists_conj_of_fixes_d4 (p := 3) hp2 (e := 1) le_rfl α hα hR
      hfixR
  · intro H _ _ ψ hker
    exact Q3NM.autOddFreeInnerTag_trialityD4 Nat.prime_three trivial hadm ↥ψ.range
      ψ.rangeRestrict ψ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])

theorem twinSqAlpha3_g2 {n : ℕ} (hadm : StatedLieAdmissible .G2 n 3 1) : TwinSqAlpha 3 1 .G2 n := by
  obtain rfl : n = 0 := hadm.2.2.1
  exact (twinRows3_g2 hadm).1

theorem twinOuterAlpha3_g2 {n : ℕ} (hadm : StatedLieAdmissible .G2 n 3 1) :
    TwinOuterAlpha 3 1 .G2 n := by
  obtain rfl : n = 0 := hadm.2.2.1
  exact (twinRows3_g2 hadm).2

theorem twinSqAlpha3_trialityD4 {n : ℕ} (hadm : StatedLieAdmissible .trialityD4 n 3 1) :
    TwinSqAlpha 3 1 .trialityD4 n := by
  obtain rfl : n = 0 := hadm.2.2
  exact (twinRows3_trialityD4 hadm).1

theorem twinOuterAlpha3_trialityD4 {n : ℕ} (hadm : StatedLieAdmissible .trialityD4 n 3 1) :
    TwinOuterAlpha 3 1 .trialityD4 n := by
  obtain rfl : n = 0 := hadm.2.2
  exact (twinRows3_trialityD4 hadm).2

end Rows

end CFSG.ClassicalInvolution.Q3.Q3OT
