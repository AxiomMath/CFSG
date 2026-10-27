module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParS2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1a

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma s888parG_inter (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {u : G}
    (hui : u ∈ K i) (huj : u ∈ K j) : u = 1 ∨ u = z :=
  hq.eq_of_central hui (fun v hv => hq.comm j i hij.symm u huj v hv)

private lemma s888parG_sq_false (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {u : G}
    (hui : u ∈ K i) (huj : u ∈ K j) (h : u * u = z) : False := by
  rcases s888parG_inter hq hij hui huj with h1 | h1
  · rw [h1, one_mul] at h
    exact hq.z_ne h.symm
  · rw [h1] at h
    exact hq.z_ne (h.symm.trans hq.z_sq)

private lemma s888parG_pow4 (hq : Sec5B517Quad K z) {a : G} (ha2 : a * a = z) : a ^ 4 = 1 := by
  have h : a ^ 4 = (a * a) * (a * a) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h, ha2, hq.z_sq]

private lemma s888parG_z_mem_pair (hq : Sec5B517Quad K z) {i j : Fin 4} :
    z ∈ Sec5B517Q8.pair hq i j := by
  refine ⟨Sec5B517Q8.mem_of_mem hq (hq.z_mem i) ?_, Subgroup.mem_sup_left (hq.z_mem i)⟩
  have h : z ^ 4 = (z * z) * (z * z) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h, hq.z_sq, one_mul]

theorem par_mul_cancel (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {a a' b b' : G}
    (ha : a ∈ K i) (ha' : a' ∈ K i) (hb : b ∈ K j) (hb' : b' ∈ K j) (h : a * b = a' * b') :
    a' = a ∨ a' = a * z := by
  have hu_i : a'⁻¹ * a ∈ K i := (K i).mul_mem ((K i).inv_mem ha') ha
  have hu_j : a'⁻¹ * a ∈ K j := by
    have e : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    rw [e]
    exact (K j).mul_mem hb' ((K j).inv_mem hb)
  rcases s888parG_inter hq hij hu_i hu_j with h1 | h1
  · left
    simpa [inv_mul_eq_one] using h1
  · right
    have h2 : a = a' * z := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' * z := by rw [h1]
    calc a' = a' * (z * z) := by rw [hq.z_sq, mul_one]
      _ = (a' * z) * z := by rw [mul_assoc]
      _ = a * z := by rw [← h2]

theorem par_t_props (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {a b : G} (ha : a ∈ K i)
    (hb : b ∈ K j) (ha2 : a * a = z) (hb2 : b * b = z) :
    a * b ∈ Sec5B517Q8.pair hq i j ∧ (a * b) * (a * b) = 1 ∧ a * b ≠ 1 ∧ a * b ≠ z := by
  have ha4 := s888parG_pow4 hq ha2
  have hb4 := s888parG_pow4 hq hb2
  have hcomm : a * b = b * a := hq.comm i j hij a ha b hb
  refine ⟨⟨(Sec5B517Q8 hq).mul_mem (Sec5B517Q8.mem_of_mem hq ha ha4)
    (Sec5B517Q8.mem_of_mem hq hb hb4), Subgroup.mul_mem_sup ha hb⟩, ?_, ?_, ?_⟩
  · calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, hq.z_sq]
  · intro h1
    have e : a = b⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact s888parG_sq_false hq hij ha (e ▸ (K j).inv_mem hb) ha2
  · intro h1
    have hbi : b ∈ K i := by
      have e : b = a⁻¹ * z := by
        calc b = a⁻¹ * (a * b) := by group
          _ = a⁻¹ * z := by rw [h1]
      rw [e]
      exact (K i).mul_mem ((K i).inv_mem ha) (hq.z_mem i)
    exact s888parG_sq_false hq hij hbi hb hb2

theorem par_y_props (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {a₀ b₀ a₁ b₁ : G}
    (ha₀ : a₀ ∈ K i) (hb₀ : b₀ ∈ K j) (ha₁ : a₁ ∈ K i) (hb₁ : b₁ ∈ K j) (ha₀2 : a₀ * a₀ = z)
    (hb₀2 : b₀ * b₀ = z) (ha₁2 : a₁ * a₁ = z) (hb₁2 : b₁ * b₁ = z) (ha : a₁ ≠ a₀)
    (ha' : a₁ ≠ a₀ * z) (hb : b₁ ≠ b₀) (hb' : b₁ ≠ b₀ * z) :
    a₁ * b₁ ∈ Sec5B517Q8.pair hq i j ∧ a₁ * b₁ * z ∈ Sec5B517Q8.pair hq i j ∧
      (a₁ * b₁) * (a₁ * b₁) = 1 ∧ (a₁ * b₁) * (a₀ * b₀) = (a₀ * b₀) * (a₁ * b₁) ∧
      a₁ * b₁ ≠ 1 ∧ a₁ * b₁ ≠ a₀ * b₀ ∧ a₁ * b₁ * z ≠ 1 ∧ a₁ * b₁ * z ≠ a₀ * b₀ := by
  obtain ⟨hy_mem, hy_sq, hy_ne1, hy_nez⟩ := par_t_props hq hij ha₁ hb₁ ha₁2 hb₁2
  have hA : a₁ * a₀ = a₀ * a₁ * z := par_anticomm_sq hq i ha₀ ha₁ ha₀2 ha₁2 ha ha'
  have hB : b₁ * b₀ = b₀ * b₁ * z := par_anticomm_sq hq j hb₀ hb₁ hb₀2 hb₁2 hb hb'
  have hzb₀ : z * b₀ = b₀ * z := hq.z_comm hb₀
  have hzb₁ : z * b₁ = b₁ * z := hq.z_comm hb₁
  have hnt : ∀ {x y : G}, x ∈ K i → y ∈ K j → x * y = a₀ * b₀ →
      a₀ = x ∨ a₀ = x * z := fun hx hy hxy =>
    par_mul_cancel hq hij hx ha₀ hy hb₀ hxy
  have hsq_z : ∀ {x : G}, x * z * z = x := fun {x} => by
    rw [mul_assoc, hq.z_sq, mul_one]
  have hnot : a₁ * b₁ ≠ a₀ * b₀ := by
    intro h
    rcases hnt ha₁ hb₁ h with h1 | h1
    · exact ha h1.symm
    · apply ha'
      rw [h1, hsq_z]
  have hyz_mem : a₁ * b₁ * z ∈ Sec5B517Q8.pair hq i j :=
    (Sec5B517Q8.pair hq i j).mul_mem hy_mem (s888parG_z_mem_pair hq)
  refine ⟨hy_mem, hyz_mem, hy_sq, ?_, hy_ne1, hnot, ?_, ?_⟩
  · calc a₁ * b₁ * (a₀ * b₀) = a₁ * (b₁ * a₀) * b₀ := by group
      _ = a₁ * (a₀ * b₁) * b₀ := by rw [hq.comm i j hij a₀ ha₀ b₁ hb₁]
      _ = (a₁ * a₀) * (b₁ * b₀) := by group
      _ = (a₀ * a₁ * z) * (b₀ * b₁ * z) := by rw [hA, hB]
      _ = (a₀ * a₁) * (z * b₀) * (b₁ * z) := by group
      _ = (a₀ * a₁) * (b₀ * z) * (b₁ * z) := by rw [hzb₀]
      _ = (a₀ * a₁) * b₀ * (z * b₁) * z := by group
      _ = (a₀ * a₁) * b₀ * (b₁ * z) * z := by rw [hzb₁]
      _ = (a₀ * a₁) * (b₀ * b₁) * (z * z) := by group
      _ = (a₀ * a₁) * (b₀ * b₁) := by rw [hq.z_sq, mul_one]
      _ = a₀ * (a₁ * b₀) * b₁ := by group
      _ = a₀ * (b₀ * a₁) * b₁ := by rw [hq.comm i j hij a₁ ha₁ b₀ hb₀]
      _ = (a₀ * b₀) * (a₁ * b₁) := by group
  · intro h
    apply hy_nez
    calc a₁ * b₁ = a₁ * b₁ * (z * z) := by rw [hq.z_sq, mul_one]
      _ = (a₁ * b₁ * z) * z := by rw [mul_assoc (a₁ * b₁)]
      _ = z := by rw [h, one_mul]
  · intro h
    have h' : a₁ * (b₁ * z) = a₀ * b₀ := by rw [← mul_assoc]; exact h
    rcases hnt ha₁ ((K j).mul_mem hb₁ (hq.z_mem j)) h' with h1 | h1
    · exact ha h1.symm
    · apply ha'
      rw [h1, hsq_z]

end CFSG.OddStandard.SmallF3.Omega
