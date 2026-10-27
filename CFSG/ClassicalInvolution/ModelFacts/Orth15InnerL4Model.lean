module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Red
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Split
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4NS
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Std

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem exists_layer_u0 [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    ∃ Q : Subgroup SL(4, F), SLayer (u0 F) Q ∧ t0 F ∈ Q ∧ U1 F ∈ Q := by
  by_cases hi : ∃ i : F, i * i = -1
  · obtain ⟨i, hi⟩ := hi
    exact exists_layer_u0_of_split h2 h4 hi
  · exact exists_layer_u0_of_nonsplit h4 hi

theorem x0_not_mem_R0' (h2 : (2 : F) ≠ 0) : x0 F ∉ R0' F := by
  rintro ⟨B, hB⟩
  have e := congrFun (congrFun (congrArg (fun x : SL(4, F) => (x : Matrix (Fin 4) (Fin 4) F)) hB)
    0) 0
  simp only [coe_blockSL, blockMat_four_two, coe_x0] at e
  simp at e
  apply h2
  linear_combination e

theorem twin_neg (h2 : (2 : F) ≠ 0) {g : SL(4, F)} {x x' : SL(4, F)}
    (hxg : x = g * x0 F * g⁻¹) {R' : Subgroup SL(4, F)}
    (hR'g : R' = (R0' F).map (MulAut.conj g).toMonoidHom) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx2 : x * x = 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) :
    x' = zneg F * x := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hxx : ((x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx2, Matrix.SpecialLinearGroup.coe_one]
  have hxx' : ((x' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x' : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx'2, Matrix.SpecialLinearGroup.coe_one]
  have hx'x : (x' : Matrix (Fin 4) (Fin 4) F) = r • (x : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : (x' : Matrix (Fin 4) (Fin 4) F) =
        ((x' * x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [h1, ← hr, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hr2 : r * r = 1 := by
    have h1 : ((x' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x' : Matrix (Fin 4) (Fin 4) F) =
        (r * r) • (1 : Matrix (Fin 4) (Fin 4) F) := by
      rw [hx'x, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
    rw [hxx'] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · exfalso
    have hxx'' : x' = x := by
      apply Subtype.ext
      rw [hx'x, hr1, one_smul]
    apply x0_not_mem_R0' h2
    have : x ∈ R' := hxx'' ▸ hx'R'
    rw [hR'g, mem_map_conj_iff, hxg] at this
    have e : g⁻¹ * (g * x0 F * g⁻¹) * g = x0 F := by group
    rwa [e] at this
  · apply Subtype.ext
    rw [hx'x, hr1, neg_one_smul, Matrix.SpecialLinearGroup.coe_mul, coe_zneg, neg_one_mul]

theorem alphaOf_twin_psl4 [Finite F] [Group.IsPerfect SL(4, F)] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) {H : Type} [Group H] [Finite H] (ψ : SL(4, F) →* H)
    (hker : ψ.ker ≤ Subgroup.center SL(4, F)) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R')
    {x x' : SL(4, F)} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hsame : ψ x = ψ x') {u : H}
    (hun : u ∈ Subgroup.normalizer (ψ.range : Set H)) (hu : u ∈ R.map ψ ⊔ R'.map ψ)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ ψ x) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, ← hsame, mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hRg' : R = (R0 F).map (MulAut.conj g).toMonoidHom := hRg
  have hR'g' : R' = (R0' F).map (MulAut.conj g).toMonoidHom := hR'g
  have hx'neg := twin_neg h2 hxg hR'g' hx'R' hx'2 hx2 hc
  have hzneg : ψ (zneg F) = 1 := by
    have h1 : ψ x' = ψ (zneg F) * ψ x := by rw [hx'neg, map_mul]
    rw [← hsame] at h1
    exact (mul_eq_right.mp h1.symm)
  have hu' : u ∈ (R ⊔ R').map ψ := by
    rw [Subgroup.map_sup]
    exact hu
  obtain ⟨s, hs, hsu⟩ := hu'
  have hs' : s ∈ (R0 F ⊔ R0' F).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_sup, ← hRg', ← hR'g']
    exact hs
  obtain ⟨w, hw, rfl⟩ := hs'
  have hsu' : ψ (g * w * g⁻¹) = u := hsu
  have hww : w * w ∈ Subgroup.center SL(4, F) := by
    have h1 : (g * w * g⁻¹) * (g * w * g⁻¹) ∈ Subgroup.center SL(4, F) :=
      hker (by rw [MonoidHom.mem_ker, map_mul, hsu', hu2])
    have e : (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    rw [e] at h1
    exact mem_center_of_conj_mem_center h1
  have hzc : ∀ y : SL(4, F), y * zneg F = zneg F * y := fun y =>
    Subgroup.mem_center_iff.mp zneg_mem_center y
  rcases classify_w h2 hw hww with rfl | rfl | rfl | rfl | ⟨h, hh, rfl⟩
  · exact absurd (by simpa using hsu'.symm) hu1
  · have hxg' : x = g * x0 F * g⁻¹ := hxg
    exact absurd (by rw [hxg']; exact hsu'.symm) huz
  · refine absurd ?_ huz
    have hxg' : x = g * x0 F * g⁻¹ := hxg
    have e : g * (zneg F * x0 F) * g⁻¹ = zneg F * x := by
      calc g * (zneg F * x0 F) * g⁻¹ = (g * zneg F) * x0 F * g⁻¹ := by group
        _ = (zneg F * g) * x0 F * g⁻¹ := by rw [hzc g]
        _ = zneg F * (g * x0 F * g⁻¹) := by group
        _ = zneg F * x := by rw [hxg']
    rw [e, map_mul, hzneg, one_mul] at hsu'
    exact hsu'.symm
  · refine absurd ?_ hu1
    have e : g * zneg F * g⁻¹ = zneg F := by rw [hzc g]; group
    rw [e, hzneg] at hsu'
    exact hsu'.symm
  · have hxh : h * x0 F = x0 F * h := by
      have := sup_le R0_le_centralizer R0'_le_centralizer hh
      exact (Subgroup.mem_centralizer_iff.mp this (x0 F) rfl).symm
    have key := alphaOf_klein_psl4 h2 h4 (exists_layer_u0 h2 h4) ψ hker hzneg (g * h)
    have e1 : toInducedAutOn ψ.range ⟨u, hun⟩ = innerHom ψ (g * h * u0 F * (g * h)⁻¹) := by
      rw [innerHom_apply]
      congr 1
      apply Subtype.ext
      show u = ψ (g * h * u0 F * (g * h)⁻¹)
      rw [← hsu']
      congr 1
      group
    have e2 : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ =
        innerHom ψ (g * h * x0 F * (g * h)⁻¹) := by
      rw [innerHom_apply]
      congr 1
      apply Subtype.ext
      show ψ x = ψ (g * h * x0 F * (g * h)⁻¹)
      congr 1
      have hxg' : x = g * x0 F * g⁻¹ := hxg
      rw [hxg']
      calc g * x0 F * g⁻¹ = g * (h * x0 F * h⁻¹) * g⁻¹ := by rw [hxh]; group
        _ = g * h * x0 F * (g * h)⁻¹ := by group
    rw [e1, e2]
    exact key

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem twinInnerAlpha_psl4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSL 4 p e) : TwinInnerAlpha p e .PSL 4 := by
  have hf : 1 ≤ e := hadm.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    omega
  have hperf : Group.IsPerfect SL(4, GaloisField p e) :=
    Group.isPerfect_def.2 (modelClauseZero .PSL 4 p e Fact.out trivial hadm).1.1
  intro H _ _ ψ R R' x x' hpair u hun hu hu2 hu1 huz
  exact InnerL4.alphaOf_twin_psl4 h2 h4 ψ hpair.ker
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num)
      hpair.mem)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num)
      hpair.mem')
    hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hpair.same hun hu hu2 hu1
    huz

end CFSG.ClassicalInvolution.ModelFacts.Orth15
