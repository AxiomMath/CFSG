module

import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas
import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.LinearAlgebra

open CFSG.LocalAnalysis.ComponentInitial

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]

private lemma orthExtend_comm_of_comm {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U W : Submodule K V} (hUW : IsCompl U W) (g : U ≃ₗ[K] U) (r : V →ₗ[K] V)
    (rU : U →ₗ[K] U) (rW : W →ₗ[K] W)
    {ιU : Type*} [Fintype ιU] [DecidableEq ιU] (bU : Module.Basis ιU K U)
    (hmat : LinearMap.toMatrix bU bU ((g : U →ₗ[K] U) * rU) =
      LinearMap.toMatrix bU bU (rU * (g : U →ₗ[K] U)))
    (hrU : ∀ u : U, r (u : V) = (rU u : V))
    (hrW : ∀ w : W, r (w : V) = (rW w : V))
    (hgU : ∀ u : U,
      (orthExtend hUW g : V →ₗ[K] V) (u : V) = (g u : V))
    (hgW : ∀ w : W,
      (orthExtend hUW g : V →ₗ[K] V) (w : V) = (w : V)) :
    (orthExtend hUW g : V →ₗ[K] V) * r = r * (orthExtend hUW g : V →ₗ[K] V) := by
  apply LinearMap.ext
  intro x
  obtain ⟨u, w, hx, -⟩ := Submodule.existsUnique_add_of_isCompl hUW x
  rw [Module.End.mul_apply, Module.End.mul_apply, ← hx]
  have hcomm : (g : U →ₗ[K] U) * rU = rU * (g : U →ₗ[K] U) := by
    have := congrArg (Matrix.toLin bU bU) hmat
    simpa only [Matrix.toLin_toMatrix] using this
  have hpoint : ∀ u : U, g (rU u) = rU (g u) := fun u => LinearMap.congr_fun hcomm u
  calc
    (orthExtend hUW g : V →ₗ[K] V) (r ((u : V) + (w : V))) =
        (orthExtend hUW g : V →ₗ[K] V) (r (u : V) + r (w : V)) := by
          rw [map_add (f := r)]
    _ = (orthExtend hUW g : V →ₗ[K] V) (r (u : V)) +
          (orthExtend hUW g : V →ₗ[K] V) (r (w : V)) := by
          rw [map_add (f := (orthExtend hUW g : V →ₗ[K] V))]
    _ = (orthExtend hUW g : V →ₗ[K] V) (rU u : V) +
          (orthExtend hUW g : V →ₗ[K] V) (rW w : V) := by
          rw [hrU u, hrW w]
    _ = (g (rU u) : V) + (rW w : V) := by rw [hgU (rU u), hgW (rW w)]
    _ = (rU (g u) : V) + (rW w : V) := by rw [hpoint u]
    _ = r (g u : V) + r (w : V) := by rw [hrU (g u), hrW w]
    _ = r ((g u : V) + (w : V)) := by rw [map_add (f := r)]
    _ = r ((orthExtend hUW g : V →ₗ[K] V) (u : V) +
          (orthExtend hUW g : V →ₗ[K] V) (w : V)) := by
          congr 1
          rw [← hgU u]
          conv_lhs => rw [← hgW w]
    _ = r ((orthExtend hUW g : V →ₗ[K] V) ((u : V) + (w : V))) := by
          rw [map_add (f := (orthExtend hUW g : V →ₗ[K] V))]

theorem exists_card_eq_sixtyFour_commute_of_finrank_range_eq_one (hF : ∀ a : F, a = 0 ∨ a = 1)
    {W E : Submodule F (ι → F)} (hWE : IsCompl W E) (hW : Module.finrank F W = 4)
    {r₀ : Matrix.SpecialLinearGroup ι F}
    (hrW : ∀ w ∈ W, (r₀ : Matrix ι ι F).mulVec w ∈ W)
    (hrE : ∀ e ∈ E, (r₀ : Matrix ι ι F).mulVec e = e) (hsq : r₀ * r₀ = 1)
    (hrank : Module.finrank F (LinearMap.range (Matrix.toLin' ((r₀ : Matrix ι ι F) - 1))) = 1) :
    ∃ T : Subgroup (Matrix.SpecialLinearGroup ι F),
      (∀ t ∈ T, (∀ w ∈ W, (t : Matrix ι ι F).mulVec w ∈ W) ∧
        ∀ e ∈ E, (t : Matrix ι ι F).mulVec e = e) ∧
      (∀ t ∈ T, t * r₀ = r₀ * t) ∧ Nat.card T = 64 := by
  classical
  have hF2 : Nat.card F = 2 := by
    refine Nat.card_eq_two_iff.mpr ⟨0, 1, zero_ne_one, ?_⟩
    rw [Set.eq_univ_iff_forall]
    intro a
    rcases hF a with h | h <;> simp [h]
  have hsq' : (r₀ : Matrix ι ι F) * (r₀ : Matrix ι ι F) = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using
      congrArg (fun g : Matrix.SpecialLinearGroup ι F => (g : Matrix ι ι F)) hsq
  have hM2 : ((r₀ : Matrix ι ι F) - 1) * ((r₀ : Matrix ι ι F) - 1) = 0 := by
    have h2 : (2 : Matrix ι ι F) = 0 := by
      ext i j
      rw [Matrix.ofNat_apply]
      by_cases h : i = j
      · rw [if_pos h]
        exact CharP.cast_eq_zero F 2
      · rw [if_neg h]
        simp
    have h11 : (1 : Matrix ι ι F) + 1 = 0 := by
      have h := congrArg (fun x : Matrix ι ι F => x * 1) h2
      rw [← two_mul]
      simpa using h
    have hrr : (r₀ : Matrix ι ι F) + (r₀ : Matrix ι ι F) = 0 := by
      have h := congrArg (fun x : Matrix ι ι F => x * (r₀ : Matrix ι ι F)) h2
      rw [← two_mul]
      simpa using h
    calc ((r₀ : Matrix ι ι F) - 1) * ((r₀ : Matrix ι ι F) - 1)
        = (r₀ : Matrix ι ι F) * (r₀ : Matrix ι ι F)
            - (r₀ : Matrix ι ι F) - (r₀ : Matrix ι ι F) + 1 := by
          noncomm_ring
      _ = 1 - (r₀ : Matrix ι ι F) - (r₀ : Matrix ι ι F) + 1 := by rw [hsq']
      _ = (1 + 1) - ((r₀ : Matrix ι ι F) + (r₀ : Matrix ι ι F)) := by noncomm_ring
      _ = 0 := by rw [h11, hrr]; simp
  let rV : (ι → F) →ₗ[F] (ι → F) := Matrix.toLin' (r₀ : Matrix ι ι F)
  let NV : (ι → F) →ₗ[F] (ι → F) := Matrix.toLin' ((r₀ : Matrix ι ι F) - 1)
  have hNV_eq : NV = rV - 1 := by
    simp only [NV, rV, map_sub, Matrix.toLin'_one]
    rfl
  have hNV2 : NV * NV = 0 := by
    have hNV : NV = Matrix.toLin' ((r₀ : Matrix ι ι F) - 1) := rfl
    rw [hNV]
    have h : Matrix.toLin' ((r₀ : Matrix ι ι F) - 1) *
        Matrix.toLin' ((r₀ : Matrix ι ι F) - 1) =
        Matrix.toLin' (((r₀ : Matrix ι ι F) - 1) * ((r₀ : Matrix ι ι F) - 1)) := by
      simp [Module.End.mul_eq_comp]
    rw [h, hM2, map_zero]
  have hEker : E ≤ LinearMap.ker NV := by
    intro e he
    rw [LinearMap.mem_ker]
    have h1 : NV (e : ι → F) = rV (e : ι → F) - (e : ι → F) := by
      simp [hNV_eq]
    rw [h1]
    have h2 : rV (e : ι → F) = (e : ι → F) := by
      rw [show rV = Matrix.toLin' (r₀ : Matrix ι ι F) from rfl, Matrix.toLin'_apply]
      exact hrE e he
    rw [h2, sub_self]
  have hcodisj : Codisjoint W (LinearMap.ker NV) := by
    rw [codisjoint_iff, eq_top_iff]
    calc ⊤ = W ⊔ E := hWE.sup_eq_top.symm
      _ ≤ W ⊔ LinearMap.ker NV := sup_le_sup_left hEker W
  let rW : W →ₗ[F] W := LinearMap.codRestrict W (rV.domRestrict W) (fun w => by
    simpa [rV, Matrix.toLin'_apply] using hrW (w : ι → F) w.2)
  let NW : W →ₗ[F] W := LinearMap.codRestrict W (NV.domRestrict W) (fun w => by
    have hrv : rV (w : ι → F) ∈ W := by
      simpa [rV, Matrix.toLin'_apply] using hrW (w : ι → F) w.2
    have hnv : NV (w : ι → F) = rV (w : ι → F) - (w : ι → F) := by
      simp [hNV_eq]
    change NV (w : ι → F) ∈ W
    rw [hnv]
    exact W.sub_mem hrv w.2)
  have hNW_eq : NW = rW - 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [NW, rW, hNV_eq, LinearMap.sub_apply]
  have hNW2 : NW * NW = 0 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have hcoe : ∀ x : W, ((NW x : W) : ι → F) = NV (x : ι → F) := fun x => rfl
    rw [Module.End.mul_apply, hcoe (NW w), hcoe w]
    have := congrArg (fun f : (ι → F) →ₗ[F] (ι → F) => f (w : ι → F)) hNV2
    simpa [Module.End.mul_apply] using this
  have hle : LinearMap.range NW ≤ LinearMap.ker NW := by
    rintro y ⟨x, rfl⟩
    have := congrArg (fun f : W →ₗ[F] W => f x) hNW2
    simpa [Module.End.mul_apply] using this
  have hrange : Module.finrank F (LinearMap.range NW) = 1 := by
    have hmap : (LinearMap.range NW).map W.subtype = LinearMap.range (NV.domRestrict W) := by
      ext y
      constructor
      · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
        exact ⟨w, rfl⟩
      · rintro ⟨w, rfl⟩
        exact ⟨NW w, ⟨w, rfl⟩, rfl⟩
    rw [← Submodule.finrank_map_subtype_eq W (LinearMap.range NW), hmap,
      LinearMap.range_domRestrict_eq_range_iff.mpr hcodisj, hrank]
  have hker : Module.finrank F (LinearMap.ker NW) = 3 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (f := NW)
    rw [hrange, hW] at hrn
    omega
  have hWquot : Module.finrank F (W ⧸ LinearMap.ker NW) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank (M := W) (N := LinearMap.ker NW)
    rw [hker, hW] at h
    omega
  have hFreeRange : Module.Free F ↥(LinearMap.range NW) :=
    Module.Free.of_divisionRing F ↥(LinearMap.range NW)
  have hFreeW : Module.Free F W := Module.Free.of_divisionRing F W
  let bR : Module.Basis (Fin 1) F (LinearMap.range NW) :=
    Module.finBasisOfFinrankEq F (LinearMap.range NW) hrange
  let w1 : W := (bR 0 : LinearMap.range NW)
  have hw1mem : w1 ∈ LinearMap.range NW := (bR 0).2
  have hw1ne : w1 ≠ 0 := by
    intro h0
    have : (bR 0 : LinearMap.range NW) = 0 := Subtype.ext h0
    exact bR.ne_zero 0 this
  have hw1ker : w1 ∈ LinearMap.ker NW := hle hw1mem
  let Kbar : Submodule F (W ⧸ LinearMap.range NW) :=
    (LinearMap.ker NW).map (Submodule.mkQ (LinearMap.range NW))
  have hQ : Module.finrank F (W ⧸ LinearMap.range NW) = 3 := by
    have h := Submodule.finrank_quotient_add_finrank (M := W) (N := LinearMap.range NW)
    rw [hrange, hW] at h
    omega
  have hKbarquot : Module.finrank F ((W ⧸ LinearMap.range NW) ⧸ Kbar) = 1 := by
    have h := (Submodule.quotientQuotientEquivQuotient (S := LinearMap.range NW)
      (T := LinearMap.ker NW) hle).finrank_eq
    simpa [Kbar, hWquot] using h
  have hKbar : Module.finrank F Kbar = 2 := by
    have h := Submodule.finrank_quotient_add_finrank (M := W ⧸ LinearMap.range NW)
      (N := Kbar)
    rw [hKbarquot, hQ] at h
    omega
  have hFreeKbar : Module.Free F Kbar := Module.Free.of_divisionRing F Kbar
  have hFreeQquot : Module.Free F ((W ⧸ LinearMap.range NW) ⧸ Kbar) :=
    Module.Free.of_divisionRing F _
  let bKbar : Module.Basis (Fin 2) F Kbar :=
    Module.finBasisOfFinrankEq F Kbar hKbar
  let bQquot : Module.Basis (Fin 1) F ((W ⧸ LinearMap.range NW) ⧸ Kbar) :=
    Module.finBasisOfFinrankEq F ((W ⧸ LinearMap.range NW) ⧸ Kbar) hKbarquot
  let bQ : Module.Basis (Fin 3) F (W ⧸ LinearMap.range NW) :=
    (Module.Basis.sumQuot bKbar bQquot).reindex (finSumFinEquiv (m := 2) (n := 1))
  let bW : Module.Basis (Fin 4) F W :=
    (Module.Basis.sumQuot bR bQ).reindex (finSumFinEquiv (m := 1) (n := 3))
  have hbW0 : bW 0 = w1 := by
    rw [show bW = (Module.Basis.sumQuot bR bQ).reindex
        (finSumFinEquiv (m := 1) (n := 3)) from rfl, Module.Basis.reindex_apply]
    rw [show (finSumFinEquiv (m := 1) (n := 3)).symm (0 : Fin 4) = Sum.inl 0 from by
      rw [show (0 : Fin 4) = Fin.castAdd 3 (0 : Fin 1) from rfl,
        finSumFinEquiv_symm_apply_castAdd]]
    rw [Module.Basis.sumQuot_inl]
  have hbW1 : bW 1 = (Module.Basis.sumQuot bR bQ) (Sum.inr 0) := by
    rw [show bW = (Module.Basis.sumQuot bR bQ).reindex
        (finSumFinEquiv (m := 1) (n := 3)) from rfl, Module.Basis.reindex_apply]
    rw [show (finSumFinEquiv (m := 1) (n := 3)).symm (1 : Fin 4) = Sum.inr 0 from by
      rw [show (1 : Fin 4) = Fin.natAdd 1 (0 : Fin 3) from rfl,
        finSumFinEquiv_symm_apply_natAdd]]
  have hbW2 : bW 2 = (Module.Basis.sumQuot bR bQ) (Sum.inr 1) := by
    rw [show bW = (Module.Basis.sumQuot bR bQ).reindex
        (finSumFinEquiv (m := 1) (n := 3)) from rfl, Module.Basis.reindex_apply]
    rw [show (finSumFinEquiv (m := 1) (n := 3)).symm (2 : Fin 4) = Sum.inr 1 from by
      rw [show (2 : Fin 4) = Fin.natAdd 1 (1 : Fin 3) from rfl,
        finSumFinEquiv_symm_apply_natAdd]]
  have hbW3 : bW 3 = (Module.Basis.sumQuot bR bQ) (Sum.inr 2) := by
    rw [show bW = (Module.Basis.sumQuot bR bQ).reindex
        (finSumFinEquiv (m := 1) (n := 3)) from rfl, Module.Basis.reindex_apply]
    rw [show (finSumFinEquiv (m := 1) (n := 3)).symm (3 : Fin 4) = Sum.inr 2 from by
      rw [show (3 : Fin 4) = Fin.natAdd 1 (2 : Fin 3) from rfl,
        finSumFinEquiv_symm_apply_natAdd]]
  have hbQ0 : bQ 0 = bKbar 0 := by
    rw [show bQ = (Module.Basis.sumQuot bKbar bQquot).reindex
        (finSumFinEquiv (m := 2) (n := 1)) from rfl, Module.Basis.reindex_apply]
    rw [show (finSumFinEquiv (m := 2) (n := 1)).symm (0 : Fin 3) = Sum.inl 0 from by
      rw [show (0 : Fin 3) = Fin.castAdd 1 (0 : Fin 2) from rfl,
        finSumFinEquiv_symm_apply_castAdd]]
    rw [Module.Basis.sumQuot_inl]
  have hbQ1 : bQ 1 = bKbar 1 := by
    rw [show bQ = (Module.Basis.sumQuot bKbar bQquot).reindex
        (finSumFinEquiv (m := 2) (n := 1)) from rfl, Module.Basis.reindex_apply]
    rw [show (finSumFinEquiv (m := 2) (n := 1)).symm (1 : Fin 3) = Sum.inl 1 from by
      rw [show (1 : Fin 3) = Fin.castAdd 1 (1 : Fin 2) from rfl,
        finSumFinEquiv_symm_apply_castAdd]]
    rw [Module.Basis.sumQuot_inl]
  have hbQ2 : bQ 2 = (Module.Basis.sumQuot bKbar bQquot) (Sum.inr 0) := by
    rw [show bQ = (Module.Basis.sumQuot bKbar bQquot).reindex
        (finSumFinEquiv (m := 2) (n := 1)) from rfl, Module.Basis.reindex_apply]
    rw [show (finSumFinEquiv (m := 2) (n := 1)).symm (2 : Fin 3) = Sum.inr 0 from by
      rw [show (2 : Fin 3) = Fin.natAdd 2 (0 : Fin 1) from rfl,
        finSumFinEquiv_symm_apply_natAdd]]
  have hbW1q : Submodule.mkQ (LinearMap.range NW) (bW 1) = bQ 0 := by
    rw [hbW1]
    simpa only [Submodule.mkQ_apply] using
      (Module.Basis.sumQuot_inr (bW := bR) (bQ := bQ) 0)
  have hbW2q : Submodule.mkQ (LinearMap.range NW) (bW 2) = bQ 1 := by
    rw [hbW2]
    simpa only [Submodule.mkQ_apply] using
      (Module.Basis.sumQuot_inr (bW := bR) (bQ := bQ) 1)
  have hbW3q : Submodule.mkQ (LinearMap.range NW) (bW 3) = bQ 2 := by
    rw [hbW3]
    simpa only [Submodule.mkQ_apply] using
      (Module.Basis.sumQuot_inr (bW := bR) (bQ := bQ) 2)
  have hcomap : Kbar.comap (Submodule.mkQ (LinearMap.range NW)) = LinearMap.ker NW := by
    simpa only [Kbar, Submodule.ker_mkQ] using
      (Submodule.comap_map_eq_self (f := Submodule.mkQ (LinearMap.range NW))
        (p := LinearMap.ker NW) (by simpa only [Submodule.ker_mkQ] using hle))
  have hbW1ker : bW 1 ∈ LinearMap.ker NW := by
    rw [← hcomap, Submodule.mem_comap, hbW1q, hbQ0]
    exact (bKbar 0).2
  have hbW2ker : bW 2 ∈ LinearMap.ker NW := by
    rw [← hcomap, Submodule.mem_comap, hbW2q, hbQ1]
    exact (bKbar 1).2
  have hbQ2not : bQ 2 ∉ Kbar := by
    intro hmem
    have hzero : Submodule.Quotient.mk (bQ 2) = 0 :=
      (Submodule.Quotient.mk_eq_zero (p := Kbar)).mpr hmem
    rw [hbQ2, Module.Basis.sumQuot_inr] at hzero
    exact bQquot.ne_zero 0 hzero
  have hbW3notker : bW 3 ∉ LinearMap.ker NW := by
    intro hmem
    have hmemK : Submodule.mkQ (LinearMap.range NW) (bW 3) ∈ Kbar := by
      rw [← hcomap] at hmem
      exact Submodule.mem_comap.mp hmem
    rw [hbW3q] at hmemK
    exact hbQ2not hmemK
  have hNW_bW0 : NW (bW 0) = 0 := by rw [hbW0]; exact hw1ker
  have hNW_bW1 : NW (bW 1) = 0 := LinearMap.mem_ker.mp hbW1ker
  have hNW_bW2 : NW (bW 2) = 0 := LinearMap.mem_ker.mp hbW2ker
  have hNW3mem : NW (bW 3) ∈ LinearMap.range NW :=
    LinearMap.mem_range.mpr ⟨bW 3, rfl⟩
  have hNW3ne : NW (bW 3) ≠ 0 := by
    intro h0
    exact hbW3notker (LinearMap.mem_ker.mpr h0)
  have hNW_bW3 : NW (bW 3) = bW 0 := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
      (V := ↥(LinearMap.range NW)) hrange (bR.ne_zero 0)
      (⟨NW (bW 3), hNW3mem⟩ : LinearMap.range NW)
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hNW3ne (congrArg Subtype.val hc).symm
    have hc1 : c = 1 := by
      rcases hF c with h | h
      · exact absurd h hc0
      · exact h
    have hy : (⟨NW (bW 3), hNW3mem⟩ : LinearMap.range NW) = bR 0 := by
      rw [← hc, hc1, one_smul]
    have hNW3 : NW (bW 3) = w1 := by
      simpa [w1] using congrArg (fun x : LinearMap.range NW => (x : W)) hy
    rw [hNW3, hbW0]
  have hmatNW : LinearMap.toMatrix bW bW NW = Matrix.single 0 3 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hNW_bW0, hNW_bW1, hNW_bW2, hNW_bW3]
  have hmatR : LinearMap.toMatrix bW bW rW = 1 + Matrix.single 0 3 1 := by
    have hrW_eq : rW = NW + 1 := by rw [hNW_eq]; abel
    rw [hrW_eq, map_add, hmatNW, LinearMap.toMatrix_one]
    abel
  let ext : (W ≃ₗ[F] W) →* ((ι → F) ≃ₗ[F] (ι → F)) :=
    orthExtend (K := F) (V := ι → F) (U := W) (W := E) hWE
  let extSL : SpecialLinearGroup F W →* SpecialLinearGroup F (ι → F) :=
    { toFun := fun g => ⟨ext (g : W ≃ₗ[F] W), by
        have hdet : LinearEquiv.det (ext (g : W ≃ₗ[F] W)) =
            LinearEquiv.det (g : W ≃ₗ[F] W) := by
          dsimp only [ext]
          dsimp only [orthExtend]
          change LinearEquiv.det ((Submodule.prodEquivOfIsCompl W E hWE).symm ≪≫ₗ
            ((g : W ≃ₗ[F] W).prodCongr (LinearEquiv.refl F E)) ≪≫ₗ
            (Submodule.prodEquivOfIsCompl W E hWE)) = LinearEquiv.det (g : W ≃ₗ[F] W)
          rw [LinearEquiv.det_conj]
          refine Units.ext ?_
          rw [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap,
            show LinearMap.det (↑(LinearEquiv.refl F E) : E →ₗ[F] E) = 1 from LinearMap.det_id,
            mul_one, LinearEquiv.coe_det]
        rw [hdet, SpecialLinearGroup.det_coe]⟩
      map_one' := Subtype.ext (by
        simp)
      map_mul' := fun g h => Subtype.ext (by
        simp [SpecialLinearGroup.coe_mul]) }
  let eW : Matrix.SpecialLinearGroup (Fin 4) F ≃* SpecialLinearGroup F W :=
    Matrix.SpecialLinearGroup.toLin_equiv bW
  let φ : Matrix.SpecialLinearGroup (Fin 4) F →* SpecialLinearGroup F (ι → F) :=
    extSL.comp eW.toMonoidHom
  let eStd : Matrix.SpecialLinearGroup ι F ≃* SpecialLinearGroup F (ι → F) :=
    Matrix.SpecialLinearGroup.toLin'_equiv
  let Φ : Matrix.SpecialLinearGroup (Fin 4) F →* Matrix.SpecialLinearGroup ι F :=
    eStd.symm.toMonoidHom.comp φ
  let T : Subgroup (Matrix.SpecialLinearGroup ι F) := (LinearFlag.unitriangular 4 F).map Φ
  have hinj_orth : Function.Injective
      (ext : (W ≃ₗ[F] W) → ((ι → F) ≃ₗ[F] (ι → F))) := by
    intro g h hgh
    apply LinearEquiv.ext
    intro w
    have h1 : ext g (w : ι → F) = ext h (w : ι → F) := by rw [hgh]
    rw [show ext g (w : ι → F) = ((g w : W) : ι → F) from by
          dsimp only [ext]
          simpa using orthExtend_apply (K := F) (V := ι → F) (U := W) (W := E) hWE g w 0,
        show ext h (w : ι → F) = ((h w : W) : ι → F) from by
          dsimp only [ext]
          simpa using orthExtend_apply (K := F) (V := ι → F) (U := W) (W := E) hWE h w 0] at h1
    exact Subtype.ext h1
  have hinj_ext : Function.Injective extSL := by
    intro g h hgh
    apply Subtype.ext
    apply hinj_orth
    exact congrArg (fun e : SpecialLinearGroup F (ι → F) =>
      (e : (ι → F) ≃ₗ[F] (ι → F))) hgh
  have hinj_φ : Function.Injective φ := by
    intro A B h
    exact eW.injective (hinj_ext h)
  have hinj_Φ : Function.Injective Φ := by
    intro A B h
    apply hinj_φ
    have := congrArg (fun x : Matrix.SpecialLinearGroup ι F => eStd x) h
    simpa [Φ] using this
  have hcard : Nat.card T = 64 := by
    rw [show T = (LinearFlag.unitriangular 4 F).map Φ from rfl,
      Subgroup.card_map_of_injective (f := Φ) hinj_Φ,
      LinearFlag.card_unitriangular (K := F) 4, hF2]
    norm_num
  have htoLin : ∀ A : Matrix.SpecialLinearGroup (Fin 4) F,
      Matrix.toLin' ((Φ A : Matrix ι ι F)) = ext ((eW A : SpecialLinearGroup F W) :
        W ≃ₗ[F] W) := by
    intro A
    rw [← Matrix.SpecialLinearGroup.toLin'_to_linearMap (Φ A)]
    have h1 : Matrix.SpecialLinearGroup.toLin' (Φ A) = φ A := by
      change ((eStd (Φ A) : SpecialLinearGroup F (ι → F)) :
        (ι → F) ≃ₗ[F] (ι → F)) = (φ A : (ι → F) ≃ₗ[F] (ι → F))
      simp [Φ]
    rw [h1]
    rfl
  have htW : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) F) (w : W),
      Matrix.toLin' ((Φ A : Matrix ι ι F)) (w : ι → F) =
        (((eW A : SpecialLinearGroup F W) : W ≃ₗ[F] W) w : W) := by
    intro A w
    rw [htoLin A]
    dsimp only [ext]
    simpa using orthExtend_apply (K := F) (V := ι → F) (U := W) (W := E) hWE
      ((eW A : SpecialLinearGroup F W) : W ≃ₗ[F] W) w 0
  have htE : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) F) (e : E),
      Matrix.toLin' ((Φ A : Matrix ι ι F)) (e : ι → F) = (e : ι → F) := by
    intro A e
    rw [htoLin A]
    dsimp only [ext]
    simpa using orthExtend_apply (K := F) (V := ι → F) (U := W) (W := E) hWE
      ((eW A : SpecialLinearGroup F W) : W ≃ₗ[F] W) (0 : W) e
  have hcommV : ∀ A : Matrix.SpecialLinearGroup (Fin 4) F, A ∈ LinearFlag.unitriangular 4 F →
      Matrix.toLin' ((Φ A : Matrix ι ι F)) * rV =
        rV * Matrix.toLin' ((Φ A : Matrix ι ι F)) := by
    intro A hA
    rw [htoLin A]
    let a : W ≃ₗ[F] W := (eW A : SpecialLinearGroup F W)
    have haW : ∀ w : W, (ext a : (ι → F) →ₗ[F] (ι → F)) (w : ι → F) = (a w : ι → F) := by
      intro w
      dsimp only [ext]
      simpa using orthExtend_apply (K := F) (V := ι → F) (U := W) (W := E) hWE a w 0
    have haE : ∀ e : E, (ext a : (ι → F) →ₗ[F] (ι → F)) (e : ι → F) = (e : ι → F) := by
      intro e
      dsimp only [ext]
      simpa using orthExtend_apply (K := F) (V := ι → F) (U := W) (W := E) hWE a (0 : W) e
    have hmatA : LinearMap.toMatrix bW bW (a : W →ₗ[F] W) =
        (A : Matrix (Fin 4) (Fin 4) F) := by
      change LinearMap.toMatrix bW bW
        ((eW A : SpecialLinearGroup F W) : W →ₗ[F] W) = (A : Matrix (Fin 4) (Fin 4) F)
      rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq bW A,
        LinearMap.toMatrix_toLin]
    have hA1 : ∀ i j : Fin 4, j < i → (A : Matrix (Fin 4) (Fin 4) F) i j = 0 :=
      (LinearFlag.mem_unitriangular.mp hA).1
    have hA2 : ∀ i : Fin 4, (A : Matrix (Fin 4) (Fin 4) F) i i = 1 :=
      (LinearFlag.mem_unitriangular.mp hA).2
    have hAE : (A : Matrix (Fin 4) (Fin 4) F) * Matrix.single 0 3 1 =
        Matrix.single 0 3 1 := by
      ext i j
      by_cases hj : j = 3
      · subst hj
        rw [Matrix.mul_single_apply_same, mul_one]
        by_cases hi : i = 0
        · subst hi
          rw [Matrix.single_apply]
          simp [hA2]
        · rw [Matrix.single_apply]
          have h0i : (0 : Fin 4) ≠ i := fun h => hi h.symm
          simp [h0i, hA1 i 0 (Fin.pos_iff_ne_zero.mpr hi)]
      · rw [Matrix.mul_single_apply_of_ne (i := 0) (j := 3) (a := i) (b := j)
            (hbj := hj) (M := (A : Matrix (Fin 4) (Fin 4) F))]
        rw [Matrix.single_apply]
        have h3j : (3 : Fin 4) ≠ j := fun h => hj h.symm
        simp [h3j]
    have hEA : Matrix.single 0 3 1 * (A : Matrix (Fin 4) (Fin 4) F) =
        Matrix.single 0 3 1 := by
      ext i j
      by_cases hi : i = 0
      · subst hi
        rw [Matrix.single_mul_apply_same, one_mul]
        by_cases hj : j = 3
        · subst hj
          rw [Matrix.single_apply]
          simp [hA2]
        · rw [Matrix.single_apply]
          have h3j : (3 : Fin 4) ≠ j := fun h => hj h.symm
          have h3jlt : j < 3 := by
            rw [Fin.lt_def]
            have hjne : j.val ≠ 3 := fun h => hj (Fin.ext h)
            omega
          simp [h3j, hA1 3 j h3jlt]
      · rw [Matrix.single_mul_apply_of_ne (i := 0) (j := 3) (a := i) (b := j)
            (h := hi) (M := (A : Matrix (Fin 4) (Fin 4) F))]
        rw [Matrix.single_apply]
        have h0i : (0 : Fin 4) ≠ i := fun h => hi h.symm
        simp [h0i]
    have hmat : LinearMap.toMatrix bW bW (a * rW) =
        LinearMap.toMatrix bW bW (rW * a) := by
      rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hmatA, hmatR]
      calc (A : Matrix (Fin 4) (Fin 4) F) * (1 + Matrix.single 0 3 1)
          = (A : Matrix (Fin 4) (Fin 4) F) + Matrix.single 0 3 1 := by
            rw [Matrix.mul_add, Matrix.mul_one, hAE]
        _ = (1 + Matrix.single 0 3 1) * (A : Matrix (Fin 4) (Fin 4) F) := by
            rw [Matrix.add_mul, Matrix.one_mul, hEA]
    have hrW_coe : ∀ w : W, rV (w : ι → F) = (rW w : ι → F) := fun w => rfl
    have hrE' : ∀ e : E, rV (e : ι → F) = (e : ι → F) := by
      intro e
      change Matrix.toLin' (r₀ : Matrix ι ι F) (e : ι → F) = (e : ι → F)
      rw [Matrix.toLin'_apply]
      exact hrE e e.2
    exact orthExtend_comm_of_comm (K := F) (V := ι → F) (U := W) (W := E)
      hWE a rV rW LinearMap.id bW hmat hrW_coe hrE' haW haE
  refine ⟨T, ?_, ?_, hcard⟩
  · intro t ht
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ht
    constructor
    · intro w hw
      rw [← Matrix.toLin'_apply, htW A ⟨w, hw⟩]
      exact (((eW A : SpecialLinearGroup F W) : W ≃ₗ[F] W) ⟨w, hw⟩).2
    · intro e he
      rw [← Matrix.toLin'_apply, htE A ⟨e, he⟩]
  · intro t ht
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ht
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    simpa [Module.End.mul_eq_comp, rV] using hcommV A hA

end CFSG.LinearAlgebra
