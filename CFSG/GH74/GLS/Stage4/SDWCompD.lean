module

public import CFSG.GroupTheory.QuasiDihedralFusion.Structure

public section

namespace CFSG.GH74.GLS.Stage4.Rest

section Aux

variable {G : Type*} [Group G]

private theorem sdwD_aux_conj_zpow {i j : G} (hji : j * i * j⁻¹ = i⁻¹) (c : ℤ) :
    j * i ^ c = i ^ (-c) * j := by
  have h : j * i ^ c * j⁻¹ = i ^ (-c) := by
    rw [← conj_zpow, hji, inv_zpow']
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem sdwD_aux_mul_jj {i j : G} (hji : j * i * j⁻¹ = i⁻¹) (hjj : j * j = i * i)
    (a c : ℤ) : (i ^ a * j) * (i ^ c * j) = i ^ (a - c + 2) := by
  calc (i ^ a * j) * (i ^ c * j) = i ^ a * (j * i ^ c) * j := by simp only [mul_assoc]
    _ = i ^ a * (i ^ (-c) * j) * j := by rw [sdwD_aux_conj_zpow hji]
    _ = i ^ a * i ^ (-c) * (j * j) := by simp only [mul_assoc]
    _ = i ^ (a + -c) * (i * i) := by rw [hjj, ← zpow_add]
    _ = i ^ (a - c + 2) := by rw [← zpow_two, ← zpow_add, sub_eq_add_neg]

private theorem sdwD_aux_exists_isPGroup {i j : G} (hi4 : i ^ 4 = 1) (hji : j * i * j⁻¹ = i⁻¹)
    (hjj : j * j = i * i) : ∃ Q : Subgroup G, i ∈ Q ∧ j ∈ Q ∧ IsPGroup 2 Q := by
  have hmul : ∀ a c : ℤ, (i ^ a * j) * (i ^ c * j) = i ^ (a - c + 2) :=
    sdwD_aux_mul_jj hji hjj
  let Q : Subgroup G :=
    { carrier := {g | ∃ a : ℤ, g = i ^ a ∨ g = i ^ a * j}
      mul_mem' := by
        rintro _ _ ⟨a, rfl | rfl⟩ ⟨c, rfl | rfl⟩
        · exact ⟨a + c, Or.inl (zpow_add i a c).symm⟩
        · exact ⟨a + c, Or.inr (by rw [zpow_add, mul_assoc])⟩
        · refine ⟨a - c, Or.inr ?_⟩
          rw [mul_assoc, sdwD_aux_conj_zpow hji, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
        · exact ⟨a - c + 2, Or.inl (hmul a c)⟩
      one_mem' := ⟨0, Or.inl (zpow_zero i).symm⟩
      inv_mem' := by
        rintro _ ⟨a, rfl | rfl⟩
        · exact ⟨-a, Or.inl (zpow_neg i a).symm⟩
        · refine ⟨a + 2, Or.inr (inv_eq_of_mul_eq_one_right ?_)⟩
          have h0 : a - (a + 2) + 2 = 0 := by ring
          rw [hmul, h0, zpow_zero] }
  refine ⟨Q, ⟨1, Or.inl (zpow_one i).symm⟩, ⟨0, Or.inr (by rw [zpow_zero, one_mul])⟩, ?_⟩
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  obtain ⟨a, ha | ha⟩ := g.2
  · have h4 : (g : G) ^ 4 = 1 := by
      rw [ha, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hi4, one_zpow]
    simpa using h4
  · have hgg : (g : G) * g = i * i := by
      rw [ha, hmul, sub_self, zero_add, zpow_two]
    have hsq : ∀ x : G, x ^ 4 = (x * x) * (x * x) := fun x => by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    have h4 : (g : G) ^ 4 = 1 := by
      rw [hsq, hgg, ← hsq, hi4]
    simpa using h4

private theorem sdwD_aux_exists_sylow {i j : G} (hi4 : i ^ 4 = 1) (hji : j * i * j⁻¹ = i⁻¹)
    (hjj : j * j = i * i) : ∃ P : Sylow 2 G, i ∈ P ∧ j ∈ P := by
  obtain ⟨Q, hiQ, hjQ, hQ⟩ := sdwD_aux_exists_isPGroup hi4 hji hjj
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  exact ⟨P, hP hiQ, hP hjQ⟩

private theorem sdwD_aux_dihedral_commute {P : Sylow 2 G} {m : ℕ}
    (e : ↥P ≃* DihedralGroup (2 ^ m)) {i j : G} (hi : i ∈ P) (hj : j ∈ P) (hii : i * i ≠ 1)
    (hjj : j * j ≠ 1) : i * j = j * i := by
  have hrot : ∀ g : G, (hg : g ∈ P) → g * g ≠ 1 → ∃ a, e ⟨g, hg⟩ = DihedralGroup.r a := by
    intro g hg hgg
    rcases h : e ⟨g, hg⟩ with a | a
    · exact ⟨a, rfl⟩
    · exfalso
      apply hgg
      have h1 : (⟨g, hg⟩ * ⟨g, hg⟩ : ↥P) = 1 :=
        e.injective (by rw [map_mul, h, DihedralGroup.sr_mul_self, map_one])
      simpa using congrArg Subtype.val h1
  obtain ⟨a, ha⟩ := hrot i hi hii
  obtain ⟨b, hb⟩ := hrot j hj hjj
  have h1 : (⟨i, hi⟩ * ⟨j, hj⟩ : ↥P) = ⟨j, hj⟩ * ⟨i, hi⟩ :=
    e.injective (by
      rw [map_mul, map_mul, ha, hb, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm])
  exact congrArg Subtype.val h1

private theorem sdwD_aux_not_commute {i j : G} (hi4 : orderOf i = 4) (hji : j * i * j⁻¹ = i⁻¹) :
    i * j ≠ j * i := by
  intro h
  have h1 : j * i * j⁻¹ = i := by rw [← h, mul_inv_cancel_right]
  rw [h1] at hji
  have h2 : i * i = 1 := mul_eq_one_iff_eq_inv.mpr hji
  have h3 : orderOf i ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rw [hi4] at h3
  omega

private theorem sdwD_aux_mul_self_ne_one {i : G} (hi4 : orderOf i = 4) : i * i ≠ 1 := by
  intro h
  have h3 : orderOf i ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rw [hi4] at h3
  omega

end Aux

theorem sdw_not_isDGroup {X : Type} [Group X] [Finite X]
    (hS : CFSG.QuasiDihedralFusion.HasQDOrWreathedSylow X)
    {K : Subgroup X}
    (hK2 : ∀ (P : Type) [Group P], IsPGroup 2 P → ∀ φ : ↥K →* P, φ = 1)
    {i j : X} (hi : i ∈ K) (hj : j ∈ K) (hi4 : orderOf i = 4) (hji : j * i * j⁻¹ = i⁻¹)
    (hjj : j * j = i * i) : ¬ CFSG.QuasiDihedralFusion.IsDGroup X := by
  rintro (⟨hD, -⟩ | ⟨K₀, hK₀⟩)
  · obtain ⟨h, hh⟩ := hS
    rcases hh with ⟨-, n, hn⟩ | hW
    · exact CFSG.QuasiDihedralFusion.not_hasSemidihedralSylow_and_dihedral hn hD
    · exact CFSG.QuasiDihedralFusion.not_hasWreathedSylow_and_dihedral hW hD
  · have := hK₀.normal
    have hKK₀ : K ≤ K₀ := by
      have hP : IsPGroup 2 (X ⧸ K₀) :=
        IsPGroup.of_card (n := 1)
          (by rw [pow_one, ← Subgroup.index_eq_card]; exact hK₀.index_eq_two)
      intro k hk
      have h := congrArg (fun φ => φ ⟨k, hk⟩)
        (hK2 (X ⧸ K₀) hP ((QuotientGroup.mk' K₀).comp K.subtype))
      simpa using h
    set i₀ : ↥K₀ := ⟨i, hKK₀ hi⟩
    set j₀ : ↥K₀ := ⟨j, hKK₀ hj⟩
    have hi4' : i₀ ^ 4 = 1 := by
      apply Subtype.ext
      simpa using (hi4 ▸ pow_orderOf_eq_one i)
    have hji' : j₀ * i₀ * j₀⁻¹ = i₀⁻¹ := Subtype.ext hji
    have hjj' : j₀ * j₀ = i₀ * i₀ := Subtype.ext hjj
    obtain ⟨P, hiP, hjP⟩ := sdwD_aux_exists_sylow hi4' hji' hjj'
    have hii : i * i ≠ 1 := sdwD_aux_mul_self_ne_one hi4
    have hjj1 : j * j ≠ 1 := by rw [hjj]; exact hii
    have hii' : i₀ * i₀ ≠ 1 := fun h => hii (by simpa using congrArg Subtype.val h)
    have hjj1' : j₀ * j₀ ≠ 1 := fun h => hjj1 (by simpa using congrArg Subtype.val h)
    have hcomm : i₀ * j₀ = j₀ * i₀ := by
      rcases hK₀.sylow with ⟨n, -, hD⟩ | ⟨n, -, hab⟩
      · obtain ⟨m, -, ⟨e⟩⟩ := hD P
        exact sdwD_aux_dihedral_commute e hiP hjP hii' hjj1'
      · have h1 := isMulCommutative_iff.mp (hab P) ⟨i₀, hiP⟩ ⟨j₀, hjP⟩
        exact congrArg Subtype.val h1
    exact sdwD_aux_not_commute hi4 hji (congrArg Subtype.val hcomm)

end CFSG.GH74.GLS.Stage4.Rest
