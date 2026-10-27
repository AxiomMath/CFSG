module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4ZtB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GCentA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private lemma mul_eq_scalar_mul {x y z : G} (h : ⁅x, y⁆ = z) : x * y = z * (y * x) := by
  rw [commutatorElement_def] at h
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = z * (y * x) := by rw [h]

private lemma conj_eq_scalar_mul {x y z : G} (h : ⁅x, y⁆ = z) : x * y * x⁻¹ = z * y := by
  rw [commutatorElement_def] at h
  calc x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    _ = z * y := by rw [h]

private lemma conj_z_of_mem_S (c : Ctx4 s e) {a : G} (ha : a ∈ s.fr.S) :
    a * s.fr.z * a⁻¹ = s.fr.z := by
  rw [y4_z_comm_S c ha]; group

private lemma commutator_z_of_mem_S (c : Ctx4 s e) {a : G} (ha : a ∈ s.fr.S) :
    ⁅s.fr.z, a⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (y4_z_comm_S c ha).symm

private lemma mul_sq_eq_z {z x y : G} (hx : x * x = z) (hy : y * y = z)
    (hz2 : z * z = 1) (hzy : z * y = y * z) (hxy : x * y = z * (y * x)) :
    (x * y) ^ 2 = z := by
  rw [pow_two]
  calc x * y * (x * y) = z * (y * x) * (x * y) := by rw [hxy]
    _ = z * (y * (x * x) * y) := by group
    _ = z * (y * z * y) := by rw [hx]
    _ = z * (z * y * y) := by rw [← hzy]
    _ = z * (z * (y * y)) := by group
    _ = z := by rw [← mul_assoc, hz2, one_mul, hy]

private lemma sq_a1b1 (c : Ctx4 s e) : (s.fr.a₁ * s.fr.b₁) ^ 2 = s.fr.z := by
  have hz2 : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact c.hRel.z_sq
  have hzy : s.fr.z * s.fr.b₁ = s.fr.b₁ * s.fr.z :=
    (y4_z_comm_S c (Subgroup.subset_closure (by simp))).symm
  exact mul_sq_eq_z (by rw [← pow_two]; exact c.hRel.a1_sq) (by rw [SFrame.z, pow_two])
    hz2 hzy (mul_eq_scalar_mul c.hRel.comm1)

private lemma sq_a2b2 (c : Ctx4 s e) : (s.fr.a₂ * s.fr.b₂) ^ 2 = s.fr.z := by
  have hz2 : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact c.hRel.z_sq
  have hzy : s.fr.z * s.fr.b₂ = s.fr.b₂ * s.fr.z :=
    (y4_z_comm_S c (Subgroup.subset_closure (by simp))).symm
  exact mul_sq_eq_z (by rw [← pow_two]; exact c.hRel.a2_sq) (by rw [← pow_two]; exact c.hRel.b2_sq)
    hz2 hzy (mul_eq_scalar_mul c.hRel.comm2)

private lemma conj_w_b1 (c : Ctx4 s e) :
    s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹ = s.fr.b₁ * s.fr.b₂ := by
  have h : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp c.hRel.b1b2
  calc s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹
      = s.fr.b₁ * (s.fr.b₂ * s.fr.b₁) * s.fr.b₁⁻¹ := by rw [h]
    _ = s.fr.b₁ * s.fr.b₂ := by group

private lemma conj_w_b2 (c : Ctx4 s e) :
    s.fr.b₂ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₂⁻¹ = s.fr.b₁ * s.fr.b₂ := by
  have h : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp c.hRel.b1b2
  have h' : s.fr.b₁ * s.fr.b₂⁻¹ = s.fr.b₂⁻¹ * s.fr.b₁ :=
    (commutatorElement_eq_one_iff_commute.mp c.hRel.b1b2).inv_right.eq
  calc s.fr.b₂ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₂⁻¹
      = s.fr.b₂ * (s.fr.b₂ * s.fr.b₁) * s.fr.b₂⁻¹ := by rw [h]
    _ = s.fr.b₂ * s.fr.b₂ * (s.fr.b₁ * s.fr.b₂⁻¹) := by group
    _ = s.fr.b₂ * s.fr.b₂ * (s.fr.b₂⁻¹ * s.fr.b₁) := by rw [h']
    _ = s.fr.b₂ * s.fr.b₁ := by group
    _ = s.fr.b₁ * s.fr.b₂ := h.symm

private lemma conj_w_a1 (c : Ctx4 s e) :
    s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹
      = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  have hb1 : s.fr.a₁ * s.fr.b₁ * s.fr.a₁⁻¹ = s.fr.z * s.fr.b₁ :=
    conj_eq_scalar_mul c.hRel.comm1
  have hb2 : s.fr.a₁ * s.fr.b₂ * s.fr.a₁⁻¹ = s.fr.b₂ := by
    rw [commutatorElement_eq_one_iff_mul_comm.mp c.hRel.a1b2]; group
  calc s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹
      = (s.fr.a₁ * s.fr.b₁ * s.fr.a₁⁻¹) * (s.fr.a₁ * s.fr.b₂ * s.fr.a₁⁻¹) := by group
    _ = (s.fr.z * s.fr.b₁) * s.fr.b₂ := by rw [hb1, hb2]
    _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by group

private lemma conj_w_a2 (c : Ctx4 s e) :
    s.fr.a₂ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₂⁻¹
      = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  have hb1 : s.fr.a₂ * s.fr.b₁ * s.fr.a₂⁻¹ = s.fr.b₁ := by
    rw [← commutatorElement_eq_one_iff_mul_comm.mp c.hRel.b1a2]; group
  have hb2 : s.fr.a₂ * s.fr.b₂ * s.fr.a₂⁻¹ = s.fr.z * s.fr.b₂ :=
    conj_eq_scalar_mul c.hRel.comm2
  have hzb1 : s.fr.z * s.fr.b₁ = s.fr.b₁ * s.fr.z :=
    (y4_z_comm_S c (Subgroup.subset_closure (by simp))).symm
  calc s.fr.a₂ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₂⁻¹
      = (s.fr.a₂ * s.fr.b₁ * s.fr.a₂⁻¹) * (s.fr.a₂ * s.fr.b₂ * s.fr.a₂⁻¹) := by group
    _ = s.fr.b₁ * (s.fr.z * s.fr.b₂) := by rw [hb1, hb2]
    _ = (s.fr.b₁ * s.fr.z) * s.fr.b₂ := by rw [mul_assoc]
    _ = (s.fr.z * s.fr.b₁) * s.fr.b₂ := by rw [← hzb1]
    _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by rw [mul_assoc]

private lemma conj_w_a1b1 (c : Ctx4 s e) :
    (s.fr.a₁ * s.fr.b₁) * (s.fr.b₁ * s.fr.b₂) * (s.fr.a₁ * s.fr.b₁)⁻¹
      = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  calc (s.fr.a₁ * s.fr.b₁) * (s.fr.b₁ * s.fr.b₂) * (s.fr.a₁ * s.fr.b₁)⁻¹
      = s.fr.a₁ * (s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹) * s.fr.a₁⁻¹ := by group
    _ = s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹ := by rw [conj_w_b1 c]
    _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := conj_w_a1 c

private lemma conj_w_a2b2 (c : Ctx4 s e) :
    (s.fr.a₂ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂) * (s.fr.a₂ * s.fr.b₂)⁻¹
      = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  calc (s.fr.a₂ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂) * (s.fr.a₂ * s.fr.b₂)⁻¹
      = s.fr.a₂ * (s.fr.b₂ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₂⁻¹) * s.fr.a₂⁻¹ := by group
    _ = s.fr.a₂ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₂⁻¹ := by rw [conj_w_b2 c]
    _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := conj_w_a2 c

private lemma comm_eq_one_or_z (c : Ctx4 s e) {x a : G}
    (hxT : x ∈ s.T₂) (hcomm : ∀ y ∈ s.T₂, ⁅x, y⁆ ∈ cen s.fr.B)
    (haT : a ∈ s.T₂) (ha_sq : a * a = s.fr.z)
    (haz : a * s.fr.z * a⁻¹ = s.fr.z)
    (haw : a * (s.fr.b₁ * s.fr.b₂) * a⁻¹ = s.fr.z * (s.fr.b₁ * s.fr.b₂)) :
    ⁅x, a⁆ = 1 ∨ ⁅x, a⁆ = s.fr.z := by
  have hv : ⁅x, a⁆ ∈ cen s.fr.B := hcomm a haT
  have hvv : ⁅x, a⁆ * ⁅x, a⁆ = 1 := by rw [← pow_two]; exact y4_V_sq c hv
  have hsq : (⁅x, a⁆ * a) ^ 2 = s.fr.z := by
    have h1 : x * a * x⁻¹ = ⁅x, a⁆ * a := by rw [commutatorElement_def]; group
    rw [← h1, pow_two]
    calc (x * a * x⁻¹) * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
      _ = x * s.fr.z * x⁻¹ := by rw [ha_sq]
      _ = s.fr.z := f3_T2_fix_z c.toF33 x hxT
  have h2 : (⁅x, a⁆ * a) ^ 2 = a ^ 2 := by
    rw [hsq, pow_two]
    exact ha_sq.symm
  have h3 : ⁅x, a⁆ * a * ⁅x, a⁆ = a := by
    refine mul_right_cancel (b := a) ?_
    calc (⁅x, a⁆ * a * ⁅x, a⁆) * a = (⁅x, a⁆ * a) ^ 2 := by rw [pow_two]; group
      _ = a ^ 2 := h2
      _ = a * a := by rw [pow_two]
  have h4 : a * ⁅x, a⁆ = ⁅x, a⁆ * a := by
    calc a * ⁅x, a⁆ = (⁅x, a⁆ * a * ⁅x, a⁆) * ⁅x, a⁆ := by rw [h3]
      _ = ⁅x, a⁆ * (a * (⁅x, a⁆ * ⁅x, a⁆)) := by group
      _ = ⁅x, a⁆ * a := by rw [hvv, mul_one]
  have hav : a * ⁅x, a⁆ * a⁻¹ = ⁅x, a⁆ := by rw [h4]; group
  have hazw : a * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * a⁻¹ = s.fr.b₁ * s.fr.b₂ := by
    calc a * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * a⁻¹
        = (a * s.fr.z * a⁻¹) * (a * (s.fr.b₁ * s.fr.b₂) * a⁻¹) := by group
      _ = s.fr.z * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by rw [haz, haw]
      _ = s.fr.b₁ * s.fr.b₂ := by rw [← mul_assoc, ← pow_two, c.hRel.z_sq, one_mul]
  rcases y4_V_enum c hv with h1 | hz | hw | hzw
  · left; exact h1
  · right; exact hz
  · exfalso
    have h : s.fr.b₁ * s.fr.b₂ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
      calc s.fr.b₁ * s.fr.b₂ = ⁅x, a⁆ := hw.symm
        _ = a * ⁅x, a⁆ * a⁻¹ := hav.symm
        _ = a * (s.fr.b₁ * s.fr.b₂) * a⁻¹ := by rw [hw]
        _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := haw
    refine y4_z_ne_one c (mul_right_cancel (b := s.fr.b₁ * s.fr.b₂) ?_)
    rw [← h, one_mul]
  · exfalso
    have h : s.fr.b₁ * s.fr.b₂ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
      calc s.fr.b₁ * s.fr.b₂ = a * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * a⁻¹ := hazw.symm
        _ = a * ⁅x, a⁆ * a⁻¹ := by rw [← hzw]
        _ = ⁅x, a⁆ := hav
        _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := hzw
    refine y4_z_ne_one c (mul_right_cancel (b := s.fr.b₁ * s.fr.b₂) ?_)
    rw [← h, one_mul]

private lemma comm_of_mul_eq_z (c : Ctx4 s e) {x u v : G}
    (hu : ⁅x, u⁆ = 1 ∨ ⁅x, u⁆ = s.fr.z)
    (huv : ⁅x, u * v⁆ = 1 ∨ ⁅x, u * v⁆ = s.fr.z)
    (hzu : s.fr.z * u = u * s.fr.z) :
    ⁅x, v⁆ = 1 ∨ ⁅x, v⁆ = s.fr.z := by
  have hz2 : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact c.hRel.z_sq
  have hzinv : s.fr.z⁻¹ = s.fr.z := inv_eq_of_mul_eq_one_right hz2
  have ht : ⁅x, v⁆ = u⁻¹ * (⁅x, u⁆⁻¹ * ⁅x, u * v⁆) * u := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    group
  have hw : ⁅x, u⁆⁻¹ * ⁅x, u * v⁆ = 1 ∨ ⁅x, u⁆⁻¹ * ⁅x, u * v⁆ = s.fr.z := by
    rcases hu with hu | hu <;> rcases huv with huv | huv
    · left; rw [hu, huv]; group
    · right; rw [hu, huv]; group
    · right; rw [hu, hzinv, huv]; group
    · left; rw [hu, hzinv, huv]; exact hz2
  rcases hw with hw | hw
  · left
    rw [ht, hw]; group
  · right
    rw [ht, hw]
    calc u⁻¹ * s.fr.z * u = u⁻¹ * (s.fr.z * u) := by group
      _ = u⁻¹ * (u * s.fr.z) := by rw [hzu]
      _ = s.fr.z := by group

theorem y4_Zt_comm_sq (c : Ctx4 s e) {x : G} (hx : x ∈ y4Zt c) :
    ∀ a ∈ ({s.fr.a₁, s.fr.a₂, s.fr.a₁ * s.fr.b₁, s.fr.a₂ * s.fr.b₂} : Set G),
      ⁅x, a⁆ = 1 ∨ ⁅x, a⁆ = s.fr.z := by
  obtain ⟨hxT, hcomm⟩ := (y4_mem_Zt c x).mp hx
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact comm_eq_one_or_z c hxT hcomm
      (y4_A_le_T2 s (Subgroup.subset_closure (by simp)))
      (by rw [← pow_two]; exact c.hRel.a1_sq)
      (conj_z_of_mem_S c (Subgroup.subset_closure (by simp))) (conj_w_a1 c)
  · exact comm_eq_one_or_z c hxT hcomm
      (y4_A_le_T2 s (Subgroup.subset_closure (by simp)))
      (by rw [← pow_two]; exact c.hRel.a2_sq)
      (conj_z_of_mem_S c (Subgroup.subset_closure (by simp))) (conj_w_a2 c)
  · exact comm_eq_one_or_z c hxT hcomm
      (y4_A_le_T2 s (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))))
      (by rw [← sq_a1b1 c, pow_two])
      (conj_z_of_mem_S c (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))))
      (conj_w_a1b1 c)
  · exact comm_eq_one_or_z c hxT hcomm
      (y4_A_le_T2 s (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))))
      (by rw [← sq_a2b2 c, pow_two])
      (conj_z_of_mem_S c (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))))
      (conj_w_a2b2 c)

theorem y4_Zt_comm_gens (c : Ctx4 s e) {x : G} (hx : x ∈ y4Zt c) :
    ∀ a ∈ ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂} : Set G), ⁅x, a⁆ = 1 ∨ ⁅x, a⁆ = s.fr.z := by
  have hsq := y4_Zt_comm_sq c hx
  intro a ha
  have h1 := hsq s.fr.a₁ (by simp)
  have h1b1 := hsq (s.fr.a₁ * s.fr.b₁) (by simp)
  have h2 := hsq s.fr.a₂ (by simp)
  have h2b2 := hsq (s.fr.a₂ * s.fr.b₂) (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact h1
  · exact comm_of_mul_eq_z c h1 h1b1
      (y4_z_comm_S c (Subgroup.subset_closure (by simp))).symm
  · exact h2
  · exact comm_of_mul_eq_z c h2 h2b2
      (y4_z_comm_S c (Subgroup.subset_closure (by simp))).symm

theorem y4_Zt_decomp (c : Ctx4 s e) {x : G} (hx : x ∈ y4Zt c) :
    ∃ a ∈ s.fr.A, ∃ u ∈ zt s, x = a * u := by
  obtain ⟨a, haA, hcent⟩ := y4_central_aut (a₁ := s.fr.a₁) (b₁ := s.fr.b₁)
    (a₂ := s.fr.a₂) (b₂ := s.fr.b₂) (z := s.fr.z) (y := x)
    c.hRel.z_sq
    (commutator_z_of_mem_S c (Subgroup.subset_closure (by simp)))
    (commutator_z_of_mem_S c (Subgroup.subset_closure (by simp)))
    (commutator_z_of_mem_S c (Subgroup.subset_closure (by simp)))
    (commutator_z_of_mem_S c (Subgroup.subset_closure (by simp)))
    c.hRel.comm1 c.hRel.comm2 c.hRel.a1a2 c.hRel.a1b2 c.hRel.b1a2 c.hRel.b1b2
    (y4_Zt_comm_gens c hx)
  have haA' : a ∈ s.fr.A := by simpa [SFrame.A] using haA
  have hcent' : a⁻¹ * x ∈ centralizer (s.fr.A : Set G) := by
    simpa [SFrame.A] using hcent
  have haT1 : a ∈ e.T₁ := c.h32.1.1 haA'
  have hxT1 : x ∈ e.T₁ := y4_Zt_le_T1 c hx
  have hprod : a⁻¹ * x ∈ e.T₁ := Subgroup.mul_mem e.T₁ (Subgroup.inv_mem e.T₁ haT1) hxT1
  have huC0 : a⁻¹ * x ∈ C0 e := Subgroup.mem_inf.mpr ⟨hprod, hcent'⟩
  have hu : a⁻¹ * x ∈ zt s := by
    rw [← c.hBr]
    exact huC0
  exact ⟨a, haA', a⁻¹ * x, hu, by group⟩

end CFSG.OddStandard.HigherRank.YamadaG23
