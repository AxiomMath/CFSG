module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4ZtA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4ZtC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Q8

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem b1_cent_V (c : Ctx4 s e) :
    s.fr.b₁ ∈ Subgroup.centralizer (cen s.fr.B : Set G) := by
  rw [y4_cenB_eq c, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · have hb2 : s.fr.b₂ * s.fr.b₁ = s.fr.b₁ * s.fr.b₂ :=
      (commutatorElement_eq_one_iff_commute.mp c.hRel.b1b2).symm
    calc (s.fr.b₁ * s.fr.b₂) * s.fr.b₁ = s.fr.b₁ * (s.fr.b₂ * s.fr.b₁) := by group
      _ = s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) := by rw [hb2]
  · exact (y4_z_comm_S c (s3_b₁_mem_S s)).symm

theorem y4_V_le_Zt' (c : Ctx4 s e) : cen s.fr.B ≤ y4Zt' c := by
  intro v hv
  rw [y4_mem_Zt']
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact y4_S_le_T2 s (s3_B_le_S s (s3_cenB_le_B s hv))
  · intro y hy
    have hconj : y * v⁻¹ * y⁻¹ ∈ cen s.fr.B :=
      y4_T2_normV c y hy v⁻¹ ((cen s.fr.B).inv_mem hv)
    have hcomm : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]; group
    rw [hcomm]
    exact (cen s.fr.B).mul_mem hv hconj
  · intro w hw
    exact y4_V_comm c hw hv

theorem y4_t_mem_Zt' (c : Ctx4 s e) : s.t ∈ y4Zt' c := by
  rw [y4_mem_Zt']
  refine ⟨⟨y4_t_mem_T2 s, ?_⟩, ?_⟩
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := f3_tX_sub c.toF33 y (y4_T2_le_X c hy)
    have hyv : ⁅y, s.t⁆ = v := by
      rw [commutatorElement_def, hvy]; group
    rw [← commutatorElement_inv y s.t, hyv]
    exact (cen s.fr.B).inv_mem hv
  · intro v hv
    exact s3_comm_t_of_mem_L s (s3_S_le_L s (s3_B_le_S s (s3_cenB_le_B s hv)))

theorem y4_Zt'_comm_t (c : Ctx4 s e) {x : G} (hx : x ∈ y4Zt' c) : x * s.t = s.t * x := by
  have hxZ : x ∈ y4Zt c := (y4_mem_Zt c x).mpr ((y4_mem_Zt' c x).mp hx).1
  obtain ⟨a, ha, u, hu, rfl⟩ := y4_Zt_decomp c hxZ
  have hat : a * s.t = s.t * a := s3_comm_t_of_mem_A s ha
  have hut : u * s.t = s.t * u := y4_zt_comm_T c hu (s3_t_mem_T s)
  calc (a * u) * s.t = a * (u * s.t) := by group
    _ = a * (s.t * u) := by rw [hut]
    _ = (a * s.t) * u := by group
    _ = (s.t * a) * u := by rw [hat]
    _ = s.t * (a * u) := by group

theorem y4_b_mem_Zt' (c : Ctx4 s e) : s.fr.b₁ ∈ y4Zt' c ∧ s.fr.b₂ ∈ y4Zt' c := by
  have hb1 : s.fr.b₁ ∈ y4Zt' c := by
    rw [y4_mem_Zt']
    exact ⟨(y4_mem_Zt c s.fr.b₁).mp (y4_b1_mem_Zt c), fun v hv =>
      Subgroup.mem_centralizer_iff.mp (b1_cent_V c) v hv⟩
  have hw : s.fr.b₁ * s.fr.b₂ ∈ y4Zt' c := y4_V_le_Zt' c (y4_w_mem_V c)
  have hb2 : s.fr.b₂ ∈ y4Zt' c := by
    have hmem : s.fr.b₁⁻¹ * (s.fr.b₁ * s.fr.b₂) ∈ y4Zt' c :=
      (y4Zt' c).mul_mem ((y4Zt' c).inv_mem hb1) hw
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at hmem
  exact ⟨hb1, hb2⟩

theorem y4_omega1_cen_Zt' (c : Ctx4 s e) :
    omega1 (cen (y4Zt' c)) = cen s.fr.B ⊔ zpowers s.t := by
  apply le_antisymm
  · rw [omega1, Subgroup.closure_le]
    rintro x ⟨hxcen, hxsq⟩
    have hxZ' : x ∈ y4Zt' c := (Subgroup.mem_inf.mp hxcen).1
    have hxcent := (Subgroup.mem_inf.mp hxcen).2
    have hxZ : x ∈ y4Zt c := (y4_mem_Zt c x).mpr ((y4_mem_Zt' c x).mp hxZ').1
    obtain ⟨a, ha, u, hu, rfl⟩ := y4_Zt_decomp c hxZ
    have hb1Z' : s.fr.b₁ ∈ y4Zt' c := (y4_b_mem_Zt' c).1
    have hb2Z' : s.fr.b₂ ∈ y4Zt' c := (y4_b_mem_Zt' c).2
    have hxcent_b1 : s.fr.b₁ * (a * u) = (a * u) * s.fr.b₁ :=
      Subgroup.mem_centralizer_iff.mp hxcent s.fr.b₁ hb1Z'
    have hxcent_b2 : s.fr.b₂ * (a * u) = (a * u) * s.fr.b₂ :=
      Subgroup.mem_centralizer_iff.mp hxcent s.fr.b₂ hb2Z'
    have hu_b1 : u * s.fr.b₁ = s.fr.b₁ * u :=
      y4_zt_comm_T c hu (s3_S_le_T s (s3_b₁_mem_S s))
    have hu_b2 : u * s.fr.b₂ = s.fr.b₂ * u :=
      y4_zt_comm_T c hu (s3_S_le_T s (s3_b₂_mem_S s))
    have hab1 : a * s.fr.b₁ = s.fr.b₁ * a := by
      apply mul_right_cancel (b := u)
      calc (a * s.fr.b₁) * u = a * (s.fr.b₁ * u) := by group
        _ = a * (u * s.fr.b₁) := by rw [hu_b1]
        _ = (a * u) * s.fr.b₁ := by group
        _ = s.fr.b₁ * (a * u) := hxcent_b1.symm
        _ = (s.fr.b₁ * a) * u := by group
    have hab2 : a * s.fr.b₂ = s.fr.b₂ * a := by
      apply mul_right_cancel (b := u)
      calc (a * s.fr.b₂) * u = a * (s.fr.b₂ * u) := by group
        _ = a * (u * s.fr.b₂) := by rw [hu_b2]
        _ = (a * u) * s.fr.b₂ := by group
        _ = s.fr.b₂ * (a * u) := hxcent_b2.symm
        _ = (s.fr.b₂ * a) * u := by group
    have ha1 : ⁅a, s.fr.b₁⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hab1
    have ha2 : ⁅a, s.fr.b₂⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hab2
    have ha_sq : a ^ 2 = 1 := by
      have hau : u * a = a * u := y4_zt_comm_T c hu (s3_A_le_T s ha)
      have hsq : (a * u) ^ 2 = a ^ 2 * u ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        calc (a * u) * (a * u) = a * (u * a) * u := by group
          _ = a * (a * u) * u := by rw [hau]
          _ = a * a * (u * u) := by group
      simpa [hsq, y4_zt_sq c hu] using hxsq
    have haV : a ∈ cen s.fr.B := y4_A_cent_b_mem_V c ha ha1 ha2 ha_sq
    have hu_sup : u ∈ cen s.fr.B ⊔ zpowers s.t := by
      rcases (s3_mem_zt_iff s c.hA).mp hu with rfl | rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.one_mem _)
      · exact Subgroup.mem_sup_left (y4_z_mem_V c)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (y4_z_mem_V c))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haV) hu_sup
  · apply sup_le
    · intro v hv
      refine Subgroup.subset_closure ⟨?_, y4_V_sq c hv⟩
      refine Subgroup.mem_inf.mpr ⟨y4_V_le_Zt' c hv, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (((y4_mem_Zt' c x).mp hx).2 v hv).symm
    · rw [Subgroup.zpowers_le]
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨y4_t_mem_Zt' c, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact y4_Zt'_comm_t c hx
      · simpa [s.t_order] using pow_orderOf_eq_one s.t

end CFSG.OddStandard.HigherRank.YamadaG23
