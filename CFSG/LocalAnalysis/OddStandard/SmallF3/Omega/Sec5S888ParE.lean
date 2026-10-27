module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1a

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma s888_corr_triv {p A : G} (h1 : A = p ∨ A = p * z) :
    p⁻¹ * A = 1 ∨ p⁻¹ * A = z := by
  rcases h1 with h1 | h1 <;> rw [h1]
  · left; group
  · right; group

private lemma s888_corr_nt {p q A : G} (hac : p⁻¹ * q * p = q * z) (hz2 : z * z = 1)
    (h1 : A = q * p ∨ A = q * p * z) :
    p⁻¹ * A = q * z ∨ p⁻¹ * A = q := by
  rcases h1 with h1 | h1 <;> rw [h1]
  · left
    calc p⁻¹ * (q * p) = p⁻¹ * q * p := by group
      _ = q * z := hac
  · right
    calc p⁻¹ * (q * p * z) = (p⁻¹ * q * p) * z := by group
      _ = (q * z) * z := by rw [hac]
      _ = q := by rw [mul_assoc, hz2, mul_one]

private lemma s888_r_eq_cd {a b g : G} (hab : Commute a b)
    (hcomm : b⁻¹ * (g⁻¹ * a * g) = (g⁻¹ * a * g) * b⁻¹) :
    (a * b)⁻¹ * (g⁻¹ * (a * b) * g) =
      (a⁻¹ * (g⁻¹ * a * g)) * (b⁻¹ * (g⁻¹ * b * g)) := by
  rw [hab.inv]
  rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group]
  calc (a⁻¹ * b⁻¹) * ((g⁻¹ * a * g) * (g⁻¹ * b * g))
      = a⁻¹ * (b⁻¹ * (g⁻¹ * a * g)) * (g⁻¹ * b * g) := by group
    _ = a⁻¹ * ((g⁻¹ * a * g) * b⁻¹) * (g⁻¹ * b * g) := by rw [hcomm]
    _ = (a⁻¹ * (g⁻¹ * a * g)) * (b⁻¹ * (g⁻¹ * b * g)) := by group

private lemma s888_r_ff {c d r : G} (hr : r = c * d) (hc : c = 1 ∨ c = z)
    (hd : d = 1 ∨ d = z) (hz2 : z * z = 1) : r = 1 ∨ z * r = 1 := by
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · left; rw [hr, hc, hd, one_mul]
  · right; rw [hr, hc, hd, one_mul, hz2]
  · right; rw [hr, hc, hd, mul_one, hz2]
  · left; rw [hr, hc, hd, hz2]

private lemma s888_r_tt {q q' c d r : G} (hr : r = c * d) (hzq : Commute z q)
    (hzq' : Commute z q') (hz2 : z * z = 1) (hc : c = q * z ∨ c = q)
    (hd : d = q' * z ∨ d = q') : r = q * q' ∨ z * r = q * q' := by
  have hzqq' : z * (q * q') = (q * q') * z := (hzq.mul_right hzq').eq
  have hzqq'z : z * (q * q' * z) = q * q' := by
    calc z * (q * q' * z) = (z * (q * q')) * z := by group
      _ = ((q * q') * z) * z := by rw [hzqq']
      _ = q * q' := by rw [mul_assoc, hz2, mul_one]
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · left
    rw [hr, hc, hd]
    calc (q * z) * (q' * z) = q * (z * q') * z := by group
      _ = q * (q' * z) * z := by rw [hzq'.eq]
      _ = q * q' * (z * z) := by group
      _ = q * q' := by rw [hz2, mul_one]
  · right
    rw [hr, hc, hd]
    have hqzq' : (q * z) * q' = q * q' * z := by
      calc (q * z) * q' = q * (z * q') := by group
        _ = q * (q' * z) := by rw [hzq'.eq]
        _ = q * q' * z := by group
    rw [hqzq', hzqq'z]
  · right
    rw [hr, hc, hd]
    have hqq'z : q * (q' * z) = q * q' * z := by group
    rw [hqq'z, hzqq'z]
  · left
    rw [hr, hc, hd]

private lemma s888_z_mul_q_z {q : G} (hzq : Commute z q) (hz2 : z * z = 1) :
    z * (q * z) = q := by
  calc z * (q * z) = (z * q) * z := by group
    _ = (q * z) * z := by rw [hzq.eq]
    _ = q := by rw [mul_assoc, hz2, mul_one]

private lemma s888_r_tf {q c d r : G} (hr : r = c * d) (hzq : Commute z q)
    (hz2 : z * z = 1) (hc : c = q * z ∨ c = q) (hd : d = 1 ∨ d = z) :
    (r = q ∨ r = q * z) ∧ (z * r = q ∨ z * r = q * z) := by
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · have hr' : r = q * z := by rw [hr, hc, hd, mul_one]
    exact ⟨Or.inr hr', Or.inl (by rw [hr', s888_z_mul_q_z hzq hz2])⟩
  · have hr' : r = q := by rw [hr, hc, hd, mul_assoc, hz2, mul_one]
    exact ⟨Or.inl hr', Or.inr (by rw [hr', hzq.eq])⟩
  · have hr' : r = q := by rw [hr, hc, hd, mul_one]
    exact ⟨Or.inl hr', Or.inr (by rw [hr', hzq.eq])⟩
  · have hr' : r = q * z := by rw [hr, hc, hd]
    exact ⟨Or.inr hr', Or.inl (by rw [hr', s888_z_mul_q_z hzq hz2])⟩

private lemma s888_r_ft {q c d r : G} (hr : r = c * d) (hzq : Commute z q)
    (hz2 : z * z = 1) (hc : c = 1 ∨ c = z) (hd : d = q * z ∨ d = q) :
    (r = q ∨ r = q * z) ∧ (z * r = q ∨ z * r = q * z) := by
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · have hr' : r = q * z := by rw [hr, hc, hd, one_mul]
    exact ⟨Or.inr hr', Or.inl (by rw [hr', s888_z_mul_q_z hzq hz2])⟩
  · have hr' : r = q := by rw [hr, hc, hd, one_mul]
    exact ⟨Or.inl hr', Or.inr (by rw [hr', hzq.eq])⟩
  · have hr' : r = q := by rw [hr, hc, hd, s888_z_mul_q_z hzq hz2]
    exact ⟨Or.inl hr', Or.inr (by rw [hr', hzq.eq])⟩
  · have hr' : r = q * z := by rw [hr, hc, hd, hzq.eq]
    exact ⟨Or.inr hr', Or.inl (by rw [hr', s888_z_mul_q_z hzq hz2])⟩

private lemma s888_notD_mem (hq : Sec5B517Quad K z) {i j : Fin 4} {D : Subgroup G} {q p ab : G}
    (hqq : q * q = z) (hpp : p * p = z) (hz1 : z ≠ 1) (hprod : q * p = ab)
    (hcomm : Commute q ab)
    (hD : ∀ x ∈ Sec5B517Q8.pair hq i j, x * ab = ab * x → x ∈ D → x = 1 ∨ x = ab)
    (hpair : q ∈ Sec5B517Q8.pair hq i j) : q ∉ D := by
  intro hmem
  rcases hD q hpair hcomm.eq hmem with h1 | h1
  · rw [h1] at hqq
    exact hz1 (by simpa using hqq.symm)
  · have hp1 : p = 1 := by
      have h : q * 1 = q * p := by rw [mul_one]; exact h1.trans hprod.symm
      exact (mul_left_cancel h).symm
    rw [hp1] at hpp
    exact hz1 (by simpa using hpp.symm)

private lemma s888_notD_z_mem (hq : Sec5B517Quad K z) {i j : Fin 4} {D : Subgroup G}
    {q p ab : G} (hqq : q * q = z) (hpp : p * p = z) (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hprod : q * p = ab) (hcomm : Commute (q * z) ab)
    (hD : ∀ x ∈ Sec5B517Q8.pair hq i j, x * ab = ab * x → x ∈ D → x = 1 ∨ x = ab)
    (hpair : q * z ∈ Sec5B517Q8.pair hq i j) : q * z ∉ D := by
  intro hmem
  rcases hD (q * z) hpair hcomm.eq hmem with h1 | h1
  · have hqz : q = z := by
      calc q = q * (z * z) := by rw [hz2, mul_one]
        _ = (q * z) * z := by group
        _ = 1 * z := by rw [h1]
        _ = z := one_mul z
    rw [hqz] at hqq
    exact hz1 (by rw [hz2] at hqq; exact hqq.symm)
  · have hpz : p = z := (mul_left_cancel (h1.trans hprod.symm)).symm
    rw [hpz] at hpp
    exact hz1 (by rw [hz2] at hpp; exact hpp.symm)

private lemma s888_notD (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {a b : G}
    (ha : a ∈ K i) (hb : b ∈ K j) (ha2 : a * a = z) (hb2 : b * b = z) (D : Subgroup G)
    (hD : ∀ x ∈ Sec5B517Q8.pair hq i j, x * (a * b) = (a * b) * x → x ∈ D →
      x = 1 ∨ x = a * b) :
    a ∉ D ∧ a * z ∉ D ∧ b ∉ D ∧ b * z ∉ D := by
  have hz2 : z * z = 1 := hq.z_sq
  have hab : Commute a b := hq.comm i j hij a ha b hb
  have hza : Commute z a := hq.z_comm ha
  have hzb : Commute z b := hq.z_comm hb
  have hz4 : z ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hz2, one_mul]
  have ha4 : a ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ha2, hz2]
  have hb4 : b ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hb2, hz2]
  have haz4 : (a * z) ^ 4 = 1 := hq.pow4_mul ha (hq.z_mem i) ha4 hz4
  have hbz4 : (b * z) ^ 4 = 1 := hq.pow4_mul hb (hq.z_mem j) hb4 hz4
  have ha_pair : a ∈ Sec5B517Q8.pair hq i j :=
    ⟨Sec5B517Q8.mem_of_mem hq ha ha4, Subgroup.mem_sup_left ha⟩
  have haz_pair : a * z ∈ Sec5B517Q8.pair hq i j :=
    ⟨Sec5B517Q8.mem_of_mem hq ((K i).mul_mem ha (hq.z_mem i)) haz4,
      Subgroup.mem_sup_left ((K i).mul_mem ha (hq.z_mem i))⟩
  have hb_pair : b ∈ Sec5B517Q8.pair hq i j :=
    ⟨Sec5B517Q8.mem_of_mem hq hb hb4, Subgroup.mem_sup_right hb⟩
  have hbz_pair : b * z ∈ Sec5B517Q8.pair hq i j :=
    ⟨Sec5B517Q8.mem_of_mem hq ((K j).mul_mem hb (hq.z_mem j)) hbz4,
      Subgroup.mem_sup_right ((K j).mul_mem hb (hq.z_mem j))⟩
  have ha_comm : Commute a (a * b) := (Commute.refl a).mul_right hab
  have haz_comm : Commute (a * z) (a * b) :=
    ((Commute.refl a).mul_left hza).mul_right (hab.mul_left hzb)
  have hb_comm : Commute b (a * b) := hab.symm.mul_right (Commute.refl b)
  have hbz_comm : Commute (b * z) (a * b) := hb_comm.mul_left (hza.mul_right hzb)
  exact ⟨s888_notD_mem hq ha2 hb2 hq.z_ne rfl ha_comm hD ha_pair,
    s888_notD_z_mem hq ha2 hb2 hq.z_ne hz2 rfl haz_comm hD haz_pair,
    s888_notD_mem hq hb2 ha2 hq.z_ne hab.eq.symm hb_comm hD hb_pair,
    s888_notD_z_mem hq hb2 ha2 hq.z_ne hz2 hab.eq.symm hbz_comm hD hbz_pair⟩

private lemma s888_ne_mul_z {p q : G} (h : p ≠ q * z) (hz2 : z * z = 1) : q ≠ p * z := by
  intro hpq
  exact h (by
    calc p = p * (z * z) := by rw [hz2, mul_one]
      _ = (p * z) * z := by group
      _ = q * z := by rw [← hpq])

theorem par_xor_iff [Finite G] (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j)
    {a₀ b₀ a₁ b₁ g : G} (D : Subgroup G) (ha₀ : a₀ ∈ K i) (hb₀ : b₀ ∈ K j) (ha₁ : a₁ ∈ K i)
    (hb₁ : b₁ ∈ K j) (ha₀2 : a₀ * a₀ = z) (hb₀2 : b₀ * b₀ = z) (ha₁2 : a₁ * a₁ = z)
    (hb₁2 : b₁ * b₁ = z) (ha : a₁ ≠ a₀) (ha' : a₁ ≠ a₀ * z) (hb : b₁ ≠ b₀)
    (hb' : b₁ ≠ b₀ * z) (hgz : g * z = z * g) (hgi : CFSG.conjugate (K i) g = K i)
    (hgj : CFSG.conjugate (K j) g = K j) (hg₀ : g⁻¹ * a₀ * g = a₀ ∨ g⁻¹ * a₀ * g = a₀ * z)
    (hg₀' : g⁻¹ * b₀ * g = b₀ ∨ g⁻¹ * b₀ * g = b₀ * z) (htD : a₀ * b₀ ∈ D)
    (hD : ∀ x ∈ Sec5B517Q8.pair hq i j, x * (a₀ * b₀) = (a₀ * b₀) * x → x ∈ D →
      x = 1 ∨ x = a₀ * b₀) :
    (((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D ∧
        ((a₁ * b₁) * z)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D) ↔
      Xor' (ParNt K z g i) (ParNt K z g j)) := by
  have hz2 : z * z = 1 := hq.z_sq
  have hba' : a₀ ≠ a₁ * z := s888_ne_mul_z ha' hz2
  have hbb' : b₀ ≠ b₁ * z := s888_ne_mul_z hb' hz2
  have hac_a : a₁⁻¹ * a₀ * a₁ = a₀ * z := by
    have h := par_anticomm_sq hq i ha₁ ha₀ ha₁2 ha₀2 (Ne.symm ha) hba'
    calc a₁⁻¹ * a₀ * a₁ = a₁⁻¹ * (a₀ * a₁) := by group
      _ = a₁⁻¹ * (a₁ * a₀ * z) := by rw [h]
      _ = a₀ * z := by group
  have hac_b : b₁⁻¹ * b₀ * b₁ = b₀ * z := by
    have h := par_anticomm_sq hq j hb₁ hb₀ hb₁2 hb₀2 (Ne.symm hb) hbb'
    calc b₁⁻¹ * b₀ * b₁ = b₁⁻¹ * (b₀ * b₁) := by group
      _ = b₁⁻¹ * (b₁ * b₀ * z) := by rw [h]
      _ = b₀ * z := by group
  have hAi := par_plane_dich hq i ha₀ ha₁ ha₀2 ha₁2 ha ha' hgz hgi hg₀
  have hBj := par_plane_dich hq j hb₀ hb₁ hb₀2 hb₁2 hb hb' hgz hgj hg₀'
  have hA_mem : g⁻¹ * a₁ * g ∈ K i := by
    have h : (MulAut.conj g⁻¹) a₁ ∈ K i := by
      rw [← hgi]
      exact Subgroup.mem_map_of_mem _ ha₁
    simpa [MulAut.conj_apply] using h
  have hB_mem : g⁻¹ * b₁ * g ∈ K j := by
    have h : (MulAut.conj g⁻¹) b₁ ∈ K j := by
      rw [← hgj]
      exact Subgroup.mem_map_of_mem _ hb₁
    simpa [MulAut.conj_apply] using h
  have hcomm_bA : b₁⁻¹ * (g⁻¹ * a₁ * g) = (g⁻¹ * a₁ * g) * b₁⁻¹ :=
    hq.comm j i hij.symm b₁⁻¹ ((K j).inv_mem hb₁) (g⁻¹ * a₁ * g) hA_mem
  have hr : (a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) =
      (a₁⁻¹ * (g⁻¹ * a₁ * g)) * (b₁⁻¹ * (g⁻¹ * b₁ * g)) :=
    s888_r_eq_cd (hq.comm i j hij a₁ ha₁ b₁ hb₁) hcomm_bA
  have hzr_eq : ((a₁ * b₁) * z)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) =
      z * ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g)) := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hz2]
    group
  have notD := s888_notD hq hij ha₀ hb₀ ha₀2 hb₀2 D hD
  have hza₀ : Commute z a₀ := hq.z_comm ha₀
  have hzb₀ : Commute z b₀ := hq.z_comm hb₀
  have hxor : Xor' (ParNt K z g i) (ParNt K z g j) ↔
      (ParNt K z g i ∧ ¬ ParNt K z g j) ∨ (ParNt K z g j ∧ ¬ ParNt K z g i) :=
    Iff.rfl
  have hxor : Xor' (ParNt K z g i) (ParNt K z g j) ↔
      (ParNt K z g i ∧ ¬ ParNt K z g j) ∨ (ParNt K z g j ∧ ¬ ParNt K z g i) :=
    Iff.rfl
  rcases hAi with ⟨hni, h1⟩ | ⟨hyi, h1⟩
  · rcases hBj with ⟨hnj, h2⟩ | ⟨hyj, h2⟩
    · have hff : (a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) = 1 ∨
          z * ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g)) = 1 :=
        s888_r_ff hr (s888_corr_triv h1) (s888_corr_triv h2) hz2
      have hnotX : ¬ Xor' (ParNt K z g i) (ParNt K z g j) := by
        rw [hxor]
        rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hni h
        · exact hnj h
      have hnotout : ¬ ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D ∧
          ((a₁ * b₁) * z)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D) := by
        rintro ⟨hrD, hzrD⟩
        rcases hff with h | h
        · exact hrD (h.symm ▸ D.one_mem)
        · exact hzrD (by rw [hzr_eq, h]; exact D.one_mem)
      exact iff_of_false hnotout hnotX
    · have hft : ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) = b₀ ∨
            (a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) = b₀ * z) ∧
          (z * ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g)) = b₀ ∨
            z * ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g)) = b₀ * z) :=
        s888_r_ft hr hzb₀ hz2 (s888_corr_triv h1) (s888_corr_nt hac_b hz2 h2)
      have hX : Xor' (ParNt K z g i) (ParNt K z g j) := by
        rw [hxor]; exact Or.inr ⟨hyj, hni⟩
      have hout : (a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D ∧
          ((a₁ * b₁) * z)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D := by
        rw [hzr_eq]
        refine ⟨?_, ?_⟩
        · rintro hmem
          rcases hft.1 with h | h
          · exact notD.2.2.1 (h ▸ hmem)
          · exact notD.2.2.2 (h ▸ hmem)
        · rintro hmem
          rcases hft.2 with h | h
          · exact notD.2.2.1 (h ▸ hmem)
          · exact notD.2.2.2 (h ▸ hmem)
      exact iff_of_true hout hX
  · rcases hBj with ⟨hnj, h2⟩ | ⟨hyj, h2⟩
    · have htf : ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) = a₀ ∨
            (a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) = a₀ * z) ∧
          (z * ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g)) = a₀ ∨
            z * ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g)) = a₀ * z) :=
        s888_r_tf hr hza₀ hz2 (s888_corr_nt hac_a hz2 h1) (s888_corr_triv h2)
      have hX : Xor' (ParNt K z g i) (ParNt K z g j) := by
        rw [hxor]; exact Or.inl ⟨hyi, hnj⟩
      have hout : (a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D ∧
          ((a₁ * b₁) * z)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D := by
        rw [hzr_eq]
        refine ⟨?_, ?_⟩
        · rintro hmem
          rcases htf.1 with h | h
          · exact notD.1 (h ▸ hmem)
          · exact notD.2.1 (h ▸ hmem)
        · rintro hmem
          rcases htf.2 with h | h
          · exact notD.1 (h ▸ hmem)
          · exact notD.2.1 (h ▸ hmem)
      exact iff_of_true hout hX
    · have htt : (a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) = a₀ * b₀ ∨
          z * ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g)) = a₀ * b₀ :=
        s888_r_tt hr hza₀ hzb₀ hz2 (s888_corr_nt hac_a hz2 h1) (s888_corr_nt hac_b hz2 h2)
      have hnotX : ¬ Xor' (ParNt K z g i) (ParNt K z g j) := by
        rw [hxor]
        rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact h hyj
        · exact h hyi
      have hnotout : ¬ ((a₁ * b₁)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D ∧
          ((a₁ * b₁) * z)⁻¹ * (g⁻¹ * (a₁ * b₁) * g) ∉ D) := by
        rintro ⟨hrD, hzrD⟩
        rcases htt with h | h
        · exact hrD (h.symm ▸ htD)
        · exact hzrD (by rw [hzr_eq, h]; exact htD)
      exact iff_of_false hnotout hnotX

end CFSG.OddStandard.SmallF3.Omega
