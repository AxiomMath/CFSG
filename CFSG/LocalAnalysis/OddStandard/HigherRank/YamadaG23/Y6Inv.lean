module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6PtsA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

theorem y6_fix_z (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G} (hx : x ∈ normalizer (V : Set G)) :
    x * z * x⁻¹ = z := by
  have huV : u ∈ V := by rw [h.hV]; exact Subgroup.mem_zpowers u
  have hcuV : x * u * x⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.mp hx u).mp huV
  have hcuC0 : x * u * x⁻¹ ∈ C0 := y6_V_le_C0 h hcuV
  have hcuC : x * u * x⁻¹ ∈ closure ({u, t} : Set G) := by rwa [← h.hC0]
  have hord : orderOf (x * u * x⁻¹) = 4 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.u_ord]
  have hgoal : x * z * x⁻¹ = (x * u * x⁻¹) ^ 2 := by
    rw [← h.u_sq, ← MulAut.conj_apply x (u ^ 2), map_pow, MulAut.conj_apply]
  rcases y6_d8_ord4 h.u_ord h.t_ord h.t_inv (x * u * x⁻¹) hcuC hord with hc | hc
  · rw [hgoal, hc]
    exact h.u_sq
  · have hz2 : z * z = 1 := by rw [← pow_two]; exact h.rel.z_sq
    rw [hgoal, hc, inv_pow, h.u_sq]
    exact inv_eq_of_mul_eq_one_left hz2

private lemma y6_conj_mem_AV_forward (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G))
    (hx2 : x ∈ normalizer (V : Set G)) :
    ∀ w, w ∈ A ⊔ V → x * w * x⁻¹ ∈ A ⊔ V := by
  intro w hw
  have hwC1 : w ∈ A ⊔ C0 := sup_le_sup_left (y6_V_le_C0 h) A hw
  have hcC1 : x * w * x⁻¹ ∈ A ⊔ C0 :=
    (Subgroup.mem_set_normalizer_iff.mp hx1 w).mp hwC1
  rw [← (y6_cent_C1_V h (x * w * x⁻¹) hcC1)]
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V := by
    simpa using (Subgroup.mem_set_normalizer_iff.mp (Subgroup.inv_mem _ hx2) v).mp hv
  have hcomm : Commute w (x⁻¹ * v * x) :=
    (y6_cent_C1_V h w hwC1).mpr hw (x⁻¹ * v * x) hv'
  have hxv : (MulAut.conj x) (x⁻¹ * v * x) = v := by
    rw [MulAut.conj_apply]
    simp [mul_assoc]
  have hmap : Commute ((MulAut.conj x) w) ((MulAut.conj x) (x⁻¹ * v * x)) :=
    hcomm.map (MulAut.conj x)
  rw [hxv, MulAut.conj_apply] at hmap
  exact hmap.eq

theorem y6_conj_mem_AV (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hx2 : x ∈ normalizer (V : Set G)) :
    ∀ w, w ∈ A ⊔ V ↔ x * w * x⁻¹ ∈ A ⊔ V := by
  intro w
  constructor
  · exact y6_conj_mem_AV_forward h hx1 hx2 w
  · intro hw
    have hw' := y6_conj_mem_AV_forward h (Subgroup.inv_mem _ hx1) (Subgroup.inv_mem _ hx2)
      (x * w * x⁻¹) hw
    simpa [mul_assoc] using hw'

theorem y6_conj_Um (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hx2 : x ∈ normalizer (V : Set G)) :
    ∀ w ∈ y6Um A V z t, x * w * x⁻¹ ∈ y6Um A V z t := by
  intro w hw
  simp only [y6_mem_Um_iff h] at hw ⊢
  obtain ⟨hwC1, hwAV, hwz⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · exact (Subgroup.mem_set_normalizer_iff.mp hx1 w).mp hwC1
  · intro hconj
    exact hwAV ((y6_conj_mem_AV h hx1 hx2 w).mpr hconj)
  · rw [← MulAut.conj_apply x w, ← map_pow, hwz, MulAut.conj_apply]
    exact y6_fix_z h hx2

theorem y6_conj_Up (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx1 : x ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hx2 : x ∈ normalizer (V : Set G)) :
    ∀ w ∈ y6Up A V t, x * w * x⁻¹ ∈ y6Up A V t := by
  intro w hw
  obtain ⟨hwC1, hwAV⟩ := y6_Up_sub h w hw
  have hsq : (x * w * x⁻¹) ^ 2 = 1 := by
    rw [← MulAut.conj_apply x w, ← map_pow, y6_sq_Up h w hw, map_one]
  have hcC1 : x * w * x⁻¹ ∈ A ⊔ C0 :=
    (Subgroup.mem_set_normalizer_iff.mp hx1 w).mp hwC1
  have hcAV : x * w * x⁻¹ ∉ A ⊔ V := fun hconj =>
    hwAV ((y6_conj_mem_AV h hx1 hx2 w).mpr hconj)
  rcases y6_C1_split h (x * w * x⁻¹) hcC1 with h' | h' | h'
  · exact absurd h' hcAV
  · exfalso
    have hz1 : z = 1 := by rw [← y6_sq_Um h (x * w * x⁻¹) h', hsq]
    exact h.z_ne hz1
  · exact h'

end CFSG.OddStandard.HigherRank.YamadaG23
