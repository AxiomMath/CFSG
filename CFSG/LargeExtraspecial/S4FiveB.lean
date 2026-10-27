module

public import CFSG.LargeExtraspecial.S4One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Rbar_eq_of_Vt_le (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hle : Vt S g t ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) : Rbar S g t = S.Lbar g := by
  refine le_antisymm (sSup_le fun X ⟨h, hX, hth⟩ => ?_) (Lbar_le_Rbar ht)
  subst hX
  have hmem := hle (cl_mem_Vt hth)
  rcases mem_span_cl_iff.mp hmem with h0 | h1
  · exact absurd h0 (cl_conj_ne_zero H h)
  · exact (Lbar_eq_of_cl_eq S H.conj_mem H.conj_ne (conj_mem_QG' S h.2 H.conj_mem) h1).le

theorem polar_cl_eq_zero_of_mem (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) {h k : S.M}
    (hth : t ∈ S.Lbar ((h : G) * g)) (htk : t ∈ S.Lbar ((k : G) * g)) :
    polar S.q (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹))
      (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) = 0 :=
  (S.polar_cl_eq_zero_iff (conj_mem_QG' S h.2 H.conj_mem) (conj_mem_QG' S k.2 H.conj_mem)).mpr
    (commute_of_mem_Dset H ht1 hth htk)

theorem polar_eq_zero_of_mem_Vt (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) {v w : S.Qt}
    (hv : v ∈ Vt S g t) (hw : w ∈ Vt S g t) : polar S.q v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hth, rfl⟩ := hv
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, htk, rfl⟩ := hw
      exact polar_cl_eq_zero_of_mem H ht1 hth htk
    | zero => exact polar_zero_right _ _
    | add u w _ _ hu hw => rw [polar_add_right, hu, hw, add_zero]
    | smul c u _ hu => rw [polar_smul_right, hu, smul_zero]
  | zero => exact polar_zero_left _ _
  | add u u' _ _ hu hu' => rw [polar_add_left, hu, hu', add_zero]
  | smul c u _ hu => rw [polar_smul_left, hu, smul_zero]

theorem q_eq_zero_of_mem_Vt (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) {v : S.Qt}
    (hv : v ∈ Vt S g t) : S.q v = 0 := by
  have hv' := hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, -, rfl⟩ := hv
    exact q_cl_conj_z S (conj_mem_QG' S h.2 H.conj_mem)
  | zero => exact map_zero _
  | add u w hu hw ihu ihw =>
    rw [map_add_eq, ihu hu, ihw hw, polar_eq_zero_of_mem_Vt H ht1 hu hw, add_zero,
      add_zero]
  | smul c u hu ihu => rw [QuadraticMap.map_smul, ihu hu, smul_zero]

theorem isElementaryAbelian_V (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) :
    CFSG.IsElementaryAbelian 2 (V S g t) where
  is_comm := ⟨fun x y => Subtype.ext ((S.polar_cl_eq_zero_iff x.2.1 y.2.1).mp
    (polar_eq_zero_of_mem_Vt H ht1 x.2.2 y.2.2))⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using (S.q_cl_eq_zero_iff x.2.1).mp (q_eq_zero_of_mem_Vt H ht1 x.2.2))

theorem V_le_QG {t : S.O} : V S g t ≤ S.QG := S.clPre_le_QG _

theorem z_mem_V {t : S.O} : S.z ∈ V S g t := S.z_mem_clPre _

theorem clSub_V {t : S.O} : S.clSub (V S g t) = Vt S g t := S.clSub_clPre _

theorem conj_mem_V (H : Hyp4 S g) {t : S.O} {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    (h : G) * g * S.z * ((h : G) * g)⁻¹ ∈ V S g t :=
  ⟨conj_mem_QG' S h.2 H.conj_mem, cl_mem_Vt hth⟩

theorem conj_mem_V_of_commute (H : Hyp4 S g) {t : S.O} {k : S.M} (hk : S.ρ k * t = t * S.ρ k)
    {x : G} (hx : x ∈ V S g t) : (k : G) * x * (k : G)⁻¹ ∈ V S g t := by
  refine ⟨S.conj_mem_QG k.2 hx.1, ?_⟩
  rw [← S.ρ_cl k hx.1]
  exact apply_mem_Vt H.conj_mem hk hx.2

end CFSG.LargeExtraspecial.S4
