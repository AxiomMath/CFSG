module

public import CFSG.LargeExtraspecial.S10SixA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

variable (S g) in
@[expose] noncomputable def fixModVSub (t : S.O) (K : Subgroup S.O) :
    Submodule (ZMod 2) S.Qt where
  carrier := {w | w ∈ Wt S g t ∧ ∀ l ∈ K, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t}
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨add_mem hv hw, fun l hl => ?_⟩
    have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (v + w) - (v + w) =
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
      rw [map_add]
      abel
    rw [e]
    exact add_mem (hv' l hl) (hw' l hl)
  zero_mem' := ⟨zero_mem _, fun l _ => by simp⟩
  smul_mem' := by
    rintro c w ⟨hw, hw'⟩
    refine ⟨Submodule.smul_mem _ c hw, fun l hl => ?_⟩
    have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (c • w) - c • w =
        c • ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
      rw [map_smul, smul_sub]
    rw [e]
    exact Submodule.smul_mem _ c (hw' l hl)

theorem finrank_fixModVSub_le (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    finrank (ZMod 2) (fixModVSub S g t (S.Lbar g)) ≤ S.width := by
  obtain ⟨k, hk, hβ, -⟩ := X.exists_pair
  have hR := (timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk hβ).1
  have hmap : (fixModVSub S g t (S.Lbar g)).map
      ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap ≤
      fixModVSub S g t (S.Lbar ((k : G) * g)) := by
    rintro _ ⟨w, ⟨hw, hw'⟩, rfl⟩
    refine ⟨apply_mem_Wt X.H hk hw, fun l hl => ?_⟩
    rw [mem_Lbar_mul_iff] at hl
    have h1 := apply_mem_Vt_of_mem_Rbar X.haQ hk (hw' _ hl)
    have e : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((S.ρ k)⁻¹ * l * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
          ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
      simp only [map_sub, Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply_O]
    rw [e] at h1
    exact h1
  have hinf : fixModVSub S g t (S.Lbar g) ⊓ fixModVSub S g t (S.Lbar ((k : G) * g)) ≤
      Vt S g t := by
    rintro w ⟨⟨hw, hwa⟩, -, hwb⟩
    have hle : Rbar S g t ≤ fixModV X w := by
      rw [hR]
      exact sup_le (fun l hl => ⟨Lbar_le_Rbar X.ht hl, hwa l hl⟩)
        (fun l hl => ⟨Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar X.H X.ht hk) hl, hwb l hl⟩)
    exact mem_Vt_of_fix_Wstar hCE X hw fun r hr => (hle hr).2
  have hsup : fixModVSub S g t (S.Lbar g) ⊔ fixModVSub S g t (S.Lbar ((k : G) * g)) ≤
      Wt S g t := sup_le (fun w hw => hw.1) (fun w hw => hw.1)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixModVSub S g t (S.Lbar g))
    (fixModVSub S g t (S.Lbar ((k : G) * g)))
  have h2 := Submodule.finrank_mono hsup
  have h3 := Submodule.finrank_mono hinf
  have h4 := Submodule.finrank_mono hmap
  rw [LinearEquiv.finrank_map_eq] at h4
  have hW := finrank_Wt (S := S) (g := g) (t := t)
  have hn := S.finrank_Qt_eq_two_mul_width
  rw [X.h4] at h3 hW
  omega

variable (S g) in
@[expose] noncomputable def commWtL (t : S.O) : Submodule (ZMod 2) S.Qt :=
  Vt S g t ⊔ Submodule.span (ZMod 2)
    {v | ∃ l ∈ S.Lbar g, ∃ w ∈ Wt S g t, v = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w}

theorem orthogonal_commWtL_le :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (commWtL S g t) ≤
      fixModVSub S g t (S.Lbar g) := by
  intro w hw
  have hwV : w ∈ Wt S g t := mem_Wt.mpr fun u hu => by
    have := hw u (Submodule.mem_sup_left hu)
    rwa [polarBilin_apply_apply] at this
  refine ⟨hwV, fun l hl => ?_⟩
  rw [← orthogonal_Wt (g := g) t]
  intro w' hw'
  have hsp : (((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w') ∈ commWtL S g t :=
    Submodule.mem_sup_right (Submodule.subset_span ⟨l⁻¹, inv_mem hl, w', hw', rfl⟩)
  have h1 := hw _ hsp
  rw [polarBilin_apply_apply] at h1 ⊢
  have h2 : polar S.q w' ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      polar S.q (((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w') w := by
    rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup l.2
      (((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w') w, apply_inv_apply_O]
  rw [polar_sub_right, h2, ← polar_sub_left]
  exact h1

theorem commWtL_eq (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    commWtL S g t = (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t := by
  have hle : commWtL S g t ≤ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t := by
    refine sup_le le_sup_right (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, hl, w, hw, rfl⟩
    refine Submodule.mem_sup_left
      ⟨?_, sub_mem (apply_mem_Wt X.H (Lbar_le_Rbar X.ht hl) hw) hw⟩
    obtain ⟨x, hxQ, rfl⟩ := S.exists_cl w
    have hxa : x * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * x := by
      rw [← S.polar_cl_eq_zero_iff hxQ X.haQ, polar_comm]
      exact (mem_Wt.mp hw) _ (cl_a_mem_Vt X.ht)
    exact X.C.comm_le x ⟨hxQ, mem_centralizer_singleton_iff.mpr hxa⟩ l hl
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have h1 := finrank_sup_Vt X.H X.C X.ht X.ht1 X.hVQ
  have h2 := Submodule.finrank_mono (orthogonal_commWtL_le (S := S) (g := g) (t := t))
  have h3 := finrank_fixModVSub_le hCE X
  have h4 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (commWtL S g t)
  have hn := S.finrank_Qt_eq_two_mul_width
  have h5 := Submodule.finrank_le (commWtL S g t)
  rw [h1]
  omega

theorem fix_Wt_of_fix (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) (hb : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa g) {y : S.O}
    (hyL : ∀ l ∈ S.Lbar g, y * l = l * y)
    (hyV : ∀ v ∈ Vt S g t, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hyP : ∀ q ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t,
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) q = q) :
    ∀ w ∈ Wt S g t, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  obtain ⟨hdec, -, -, -, -⟩ := timmesfeld_10_1_two hCE X hk hb
  have hspan : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt X.ht)
  have hKF : commWtL S g t ≤ fixSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    refine sup_le (fun v hv => mem_fixSpace.mpr (hyV v hv)) (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, hl, w, hw, rfl⟩
    rw [← hdec] at hw
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
    have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + q) - (p + q) =
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) := by
      rw [map_add]
      abel
    rw [SetLike.mem_coe, e]
    refine add_mem (mem_fixSpace.mpr (hyV _ (hspan (Lbar_apply_sub_mem_span' X.haQ hp.1 hl))))
      (mem_fixSpace.mpr ?_)
    have hyl : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) q) =
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) q) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, hyL l hl]
    rw [map_sub, hyl, hyP q hq]
  intro w hw
  rw [← hdec] at hw
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add, hyP q hq]
  congr 1
  have hpK : p ∈ commWtL S g t := by
    rw [commWtL_eq hCE X]
    exact Submodule.mem_sup_left hp
  exact mem_fixSpace.mp (hKF hpK)

end CFSG.LargeExtraspecial.S10
