module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Cent

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

@[expose] def Mm (t a₀ b₀ : G) : Subgroup G :=
  zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ⊔ zpowers a₀

theorem comm_mem_of_normalizing {N : Subgroup G} {α α' n n' : G} (hn : n ∈ N) (hn' : n' ∈ N)
    (hα : ∀ x ∈ N, α * x * α⁻¹ ∈ N) (hα' : ∀ x ∈ N, α' * x * α'⁻¹ ∈ N) (hcomm : α * α' = α' * α) :
    (n * α) * (n' * α') * (n * α)⁻¹ * (n' * α')⁻¹ ∈ N := by
  have e1 : n * α * (n' * α') = n * (α * n' * α⁻¹) * (α * α') := by group
  have e2 : n' * α' * (n * α) = n' * (α' * n * α'⁻¹) * (α' * α) := by group
  have e3 : (n * α) * (n' * α') * (n * α)⁻¹ * (n' * α')⁻¹ =
      (n * α * (n' * α')) * (n' * α' * (n * α))⁻¹ := by group
  rw [e3, e1, e2, hcomm]
  have : n * (α * n' * α⁻¹) * (α' * α) * (n' * (α' * n * α'⁻¹) * (α' * α))⁻¹ =
      n * (α * n' * α⁻¹) * (α' * n * α'⁻¹)⁻¹ * n'⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem (mul_mem hn (hα n' hn')) (Subgroup.inv_mem _ (hα' n hn))) (Subgroup.inv_mem _ hn')

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem zpowers_r_le_D1 (_h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ≤ D1 a₀ (t * a₀ * t⁻¹) t := le_sup_left

omit [Finite G] in
theorem L_comm (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ g ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹), ∀ g' ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
      g * g' = g' * g :=
  fun g hg g' hg' => h.rel.D1_D2_comm g (h.zpowers_r_le_D1 hg) g' hg'

omit [Finite G] in
theorem mem_L_iff (h : Canon S P₁ P₂ z t a a₀ b₀ M) {g : G} :
    g ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ↔
      ∃ i : ℤ, ∃ d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
        g = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d := by
  rw [mem_sup_iff_of_commute h.L_comm]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hp
    exact ⟨i, q, hq, rfl⟩
  · rintro ⟨i, d, hd, rfl⟩
    exact ⟨_, mem_zpowers_iff.2 ⟨i, rfl⟩, d, hd, rfl⟩

omit [Finite G] in
theorem a_conj_refl2 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (j : ℤ) :
    a₀ * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀⁻¹ =
      (a₀ * (t * a₀ * t⁻¹)) ^ (j + 1) * (b₀ * (t * b₀ * t⁻¹) * t) := by
  have hc : a₀ * (a₀ * (t * a₀ * t⁻¹)) ^ j * a₀⁻¹ = (a₀ * (t * a₀ * t⁻¹)) ^ j :=
    mul_inv_eq_iff_eq_mul.2 ((h.rel.commute_dl2_a.symm.zpow_right j).eq)
  calc a₀ * ((a₀ * (t * a₀ * t⁻¹)) ^ j * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀⁻¹
      = (a₀ * (a₀ * (t * a₀ * t⁻¹)) ^ j * a₀⁻¹) * (a₀ * (b₀ * (t * b₀ * t⁻¹) * t) * a₀⁻¹) := by
        group
    _ = (a₀ * (t * a₀ * t⁻¹)) ^ j * ((a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹) * t)) := by
        rw [hc, h.rel.a_s2_a_inv]
    _ = (a₀ * (t * a₀ * t⁻¹)) ^ (j + 1) * (b₀ * (t * b₀ * t⁻¹) * t) := by
        rw [zpow_add_one]; exact (mul_assoc _ _ _).symm

omit [Finite G] in
theorem a_inv_conj_D2 (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ g ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
      a₀⁻¹ * g * a₀ ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  have hc : a₀⁻¹ * (a₀ * (t * a₀ * t⁻¹)) * a₀ = a₀ * (t * a₀ * t⁻¹) := by
    have := h.rel.commute_dl2_a.eq
    calc a₀⁻¹ * (a₀ * (t * a₀ * t⁻¹)) * a₀ = a₀⁻¹ * ((a₀ * (t * a₀ * t⁻¹)) * a₀) := mul_assoc _ _ _
      _ = a₀⁻¹ * (a₀ * (a₀ * (t * a₀ * t⁻¹))) := by rw [this]
      _ = a₀ * (t * a₀ * t⁻¹) := inv_mul_cancel_left _ _
  have hs : a₀⁻¹ * (b₀ * (t * b₀ * t⁻¹) * t) * a₀ =
      (a₀ * (t * a₀ * t⁻¹))⁻¹ * (b₀ * (t * b₀ * t⁻¹) * t) := by
    have e := h.rel.a_s2_a_inv
    have e2 : a₀⁻¹ * ((a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀ =
        b₀ * (t * b₀ * t⁻¹) * t := by
      rw [← e]; group
    have e3 : a₀⁻¹ * ((a₀ * (t * a₀ * t⁻¹)) * (b₀ * (t * b₀ * t⁻¹) * t)) * a₀ =
        (a₀⁻¹ * (a₀ * (t * a₀ * t⁻¹)) * a₀) * (a₀⁻¹ * (b₀ * (t * b₀ * t⁻¹) * t) * a₀) := by group
    rw [e3, hc] at e2
    exact (eq_inv_mul_iff_mul_eq.2 e2)
  have hgen : ∀ x ∈ zpowers (a₀ * (t * a₀ * t⁻¹)) ⊔ zpowers (b₀ * (t * b₀ * t⁻¹) * t),
      a₀⁻¹ * x * a₀⁻¹⁻¹ ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
    refine conj_le_of_gens (H := D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) a₀⁻¹ ?_ ?_
    · rw [inv_inv, hc]; exact Rel.dl2_mem_D2 _ _ _ _ _
    · rw [inv_inv, hs]
      exact mul_mem (Subgroup.inv_mem _ (Rel.dl2_mem_D2 _ _ _ _ _)) (Rel.s2_mem_D2 _ _ _ _ _)
  intro g hg
  have := hgen g hg
  rwa [inv_inv] at this

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem a_conj_L (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ g ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
      a₀ * g * a₀⁻¹ ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  intro g hg
  obtain ⟨i, d, hd, rfl⟩ := h.mem_L_iff.1 hg
  have hc : a₀ * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀⁻¹ = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i :=
    mul_inv_eq_iff_eq_mul.2 ((h.rel.commute_dl1_a.symm.zpow_right i).eq)
  have e : a₀ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d) * a₀⁻¹ =
      (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * d * a₀⁻¹) := by
    calc a₀ * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d) * a₀⁻¹
        = (a₀ * (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀⁻¹) * (a₀ * d * a₀⁻¹) := by group
      _ = _ := by rw [hc]
  rw [e]
  exact h.mem_L_iff.2 ⟨i, _, h.rel.a_conj_D2 d hd, rfl⟩

omit [Finite G] in
theorem a_sq_L (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    a₀ * a₀ ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  have : a₀ * a₀ = (a₀ * (t * a₀ * t⁻¹)⁻¹) * (a₀ * (t * a₀ * t⁻¹)) := by
    have hc := h.rel.commute_a_a'
    calc a₀ * a₀ = a₀ * ((t * a₀ * t⁻¹)⁻¹ * (t * a₀ * t⁻¹)) * a₀ := by group
      _ = a₀ * (t * a₀ * t⁻¹)⁻¹ * ((t * a₀ * t⁻¹) * a₀) := by group
      _ = (a₀ * (t * a₀ * t⁻¹)⁻¹) * (a₀ * (t * a₀ * t⁻¹)) := by rw [← hc.eq]
  rw [this]
  exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (Rel.dl2_mem_D2 _ _ _ _ _))

omit [Finite G] in
theorem mem_Mm_iff (h : Canon S P₁ P₂ z t a a₀ b₀ M) {g : G} :
    g ∈ Mm t a₀ b₀ ↔
      g ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ∨
        ∃ k ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
          g = k * a₀ :=
  mem_sup_zpowers_iff h.a_conj_L h.a_sq_L

omit [Finite G] in
theorem L_le_K (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤
      D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
  sup_le (h.zpowers_r_le_D1.trans le_sup_left) le_sup_right

omit [Finite G] in
theorem L_le_Mm (_h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤ Mm t a₀ b₀ :=
  le_sup_left

omit [Finite G] in
theorem Mm_le_HH (h : Canon S P₁ P₂ z t a a₀ b₀ M) : Mm t a₀ b₀ ≤ HH t a₀ b₀ :=
  sup_le (sup_le (h.zpowers_r_le_D1.trans (D1_le_HH t a₀ b₀)) (D2_le_HH t a₀ b₀))
    (a_le_HH t a₀ b₀)

omit [Finite G] in
theorem Mm_inter_K (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∀ g ∈ Mm t a₀ b₀,
      g ∈ D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t →
      g ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  intro g hgM hgK
  rcases (h.mem_Mm_iff).1 hgM with hL | ⟨k, hk, rfl⟩
  · exact hL
  · exfalso
    apply h.rel.a_not_mem_sup
    have h' := mul_mem (Subgroup.inv_mem _ (h.L_le_K hk)) hgK
    rwa [inv_mul_cancel_left] at h'

omit [Finite G] in
theorem t_not_mem_Mm (h : Canon S P₁ P₂ z t a a₀ b₀ M) : t ∉ Mm t a₀ b₀ := by
  intro ht
  have htL := h.Mm_inter_K t ht (mem_sup_left (Rel.t_mem_D1 _ _ _))
  obtain ⟨i, d, hd, e⟩ := (h.mem_L_iff).1 htL
  have hu := h.unique_decomp (Rel.t_mem_D1 _ _ _)
    (h.zpowers_r_le_D1 (zpow_mem (mem_zpowers _) i)) (one_mem _) hd (by rw [mul_one]; exact e)
  apply h.rel.t_not_mem_dl1
  have hmem := zpow_mem (mem_zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹)) i
  rw [← hu.1] at hmem
  exact hmem

omit [Finite G] in
theorem HH_nf (h : Canon S P₁ P₂ z t a a₀ b₀ M) {g : G} (hg : g ∈ HH t a₀ b₀) :
    (∃ i : ℤ, ∃ d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
        g = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d) ∨
    (∃ i : ℤ, ∃ d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
        g = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * d) ∨
    (∃ i : ℤ, ∃ d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
        g = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d * a₀) ∨
    (∃ i : ℤ, ∃ d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
        g = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * d * a₀) := by
  rcases h.mem_HH_iff.1 hg with hK | ⟨k, hk, rfl⟩
  · obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := h.mem_K_iff.1 hK
    obtain ⟨i, e | e⟩ := h.dih1.mem_iff.1 hd₁
    · left; exact ⟨i, d₂, hd₂, by rw [e]⟩
    · right; left; exact ⟨i, d₂, hd₂, by rw [e]⟩
  · obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := h.mem_K_iff.1 hk
    obtain ⟨i, e | e⟩ := h.dih1.mem_iff.1 hd₁
    · right; right; left; exact ⟨i, d₂, hd₂, by rw [e]⟩
    · right; right; right; exact ⟨i, d₂, hd₂, by rw [e]⟩

end Canon

end Fin

theorem form2_mul_t {R t d : G} (htd : t * d = d * t) (htt : t * t = 1) : R * t * d * t = R * d := by
  calc R * t * d * t = R * (t * d) * t := by simp only [mul_assoc]
    _ = R * (d * t) * t := by rw [htd]
    _ = R * d * (t * t) := by simp only [mul_assoc]
    _ = R * d := by rw [htt, mul_one]

theorem form4_mul_t {R t d a r : G} (hat : a * t = r * t * a) (hdr : d * r = r * d)
    (hdt : d * t = t * d) (htrt : t * r * t = r⁻¹) :
    R * t * d * a * t = R * r⁻¹ * d * a := by
  have e1 : d * r * t = r * t * d := by
    calc d * r * t = r * d * t := by rw [hdr]
      _ = r * (d * t) := mul_assoc _ _ _
      _ = r * (t * d) := by rw [hdt]
      _ = r * t * d := (mul_assoc _ _ _).symm
  calc R * t * d * a * t = R * t * d * (a * t) := by simp only [mul_assoc]
    _ = R * t * d * (r * t * a) := by rw [hat]
    _ = R * t * (d * r * t) * a := by simp only [mul_assoc]
    _ = R * t * (r * t * d) * a := by rw [e1]
    _ = R * (t * r * t) * d * a := by simp only [mul_assoc]
    _ = R * r⁻¹ * d * a := by rw [htrt]

theorem sq_aux {ρ ρ' a σ r r2 : G} (F1 : a * ρ = ρ' * a) (F2 : σ * ρ = ρ * σ)
    (F3 : a * σ = (r2 * σ) * a) (F4 : a * a = r * r2) (F5 : ρ * ρ' = r⁻¹)
    (F6 : r * σ = σ * r) (F6' : r * r2 = r2 * r) (F7 : r2 * σ * r2 * σ = 1) :
    (ρ * a * σ) * (ρ * a * σ) = 1 := by
  calc ρ * a * σ * (ρ * a * σ) = ρ * a * (σ * ρ) * a * σ := by simp only [mul_assoc]
    _ = ρ * a * (ρ * σ) * a * σ := by rw [F2]
    _ = ρ * (a * ρ) * σ * a * σ := by simp only [mul_assoc]
    _ = ρ * (ρ' * a) * σ * a * σ := by rw [F1]
    _ = (ρ * ρ') * (a * σ) * a * σ := by simp only [mul_assoc]
    _ = r⁻¹ * ((r2 * σ) * a) * a * σ := by rw [F5, F3]
    _ = r⁻¹ * (r2 * σ) * (a * a) * σ := by simp only [mul_assoc]
    _ = r⁻¹ * (r2 * σ) * (r * r2) * σ := by rw [F4]
    _ = r⁻¹ * (r2 * (σ * r) * r2 * σ) := by simp only [mul_assoc]
    _ = r⁻¹ * (r2 * (r * σ) * r2 * σ) := by rw [F6]
    _ = r⁻¹ * ((r2 * r) * σ * r2 * σ) := by simp only [mul_assoc]
    _ = r⁻¹ * ((r * r2) * σ * r2 * σ) := by rw [F6']
    _ = r⁻¹ * (r * (r2 * σ * r2 * σ)) := by simp only [mul_assoc]
    _ = 1 := by rw [F7, mul_one, inv_mul_cancel]

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem a_t_eq (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    a₀ * t = (a₀ * (t * a₀ * t⁻¹)⁻¹) * t * a₀ := by
  have := h.rel.a_t_a_inv
  exact mul_inv_eq_iff_eq_mul.1 this

omit [Finite G] in
theorem t_r_t (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    t * (a₀ * (t * a₀ * t⁻¹)⁻¹) * t = (a₀ * (t * a₀ * t⁻¹)⁻¹)⁻¹ := by
  exact (congrArg (fun x : G => t * (a₀ * (t * a₀ * t⁻¹)⁻¹) * x) h.rel.t_inv).symm.trans
    h.rel.t_dl1

omit [Finite G] in
theorem D2_comm_r (h : Canon S P₁ P₂ z t a a₀ b₀ M) {d : G}
    (hd : d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) :
    d * (a₀ * (t * a₀ * t⁻¹)⁻¹) = (a₀ * (t * a₀ * t⁻¹)⁻¹) * d :=
  (h.rel.D1_D2_comm _ (Rel.dl1_mem_D1 _ _ _) d hd).symm

omit [Finite G] in
theorem D2_comm_t (h : Canon S P₁ P₂ z t a a₀ b₀ M) {d : G}
    (hd : d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) : d * t = t * d :=
  (h.rel.D1_D2_comm _ (Rel.t_mem_D1 _ _ _) d hd).symm

omit [Finite G] in
theorem a_sq_eq (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    a₀ * a₀ = (a₀ * (t * a₀ * t⁻¹)⁻¹) * (a₀ * (t * a₀ * t⁻¹)) := by
  have hc := h.rel.commute_a_a'
  calc a₀ * a₀ = a₀ * ((t * a₀ * t⁻¹)⁻¹ * (t * a₀ * t⁻¹)) * a₀ := by group
    _ = a₀ * (t * a₀ * t⁻¹)⁻¹ * ((t * a₀ * t⁻¹) * a₀) := by group
    _ = (a₀ * (t * a₀ * t⁻¹)⁻¹) * (a₀ * (t * a₀ * t⁻¹)) := by rw [← hc.eq]

omit [Finite G] in
theorem refl_a_s2_sq (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) :
    ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * a₀ * (b₀ * (t * b₀ * t⁻¹) * t)) *
      ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * a₀ * (b₀ * (t * b₀ * t⁻¹) * t)) = 1 := by
  refine sq_aux (ρ' := (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (i + 1) * t) (r := a₀ * (t * a₀ * t⁻¹)⁻¹)
    (r2 := a₀ * (t * a₀ * t⁻¹)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact mul_inv_eq_iff_eq_mul.1 (h.a_conj_refl i)
  · exact (h.rel.D1_D2_comm _ (h.refl_mem_D1 i) _ (Rel.s2_mem_D2 _ _ _ _ _)).symm
  · exact mul_inv_eq_iff_eq_mul.1 h.rel.a_s2_a_inv
  · exact h.a_sq_eq
  · rw [h.dih1.refl_mul_refl, show i - (i + 1) = -1 by ring, zpow_neg_one]
  · exact (h.rel.D1_D2_comm _ (Rel.dl1_mem_D1 _ _ _) _ (Rel.s2_mem_D2 _ _ _ _ _))
  · exact h.rel.commute_dl1_dl2.eq
  · calc a₀ * (t * a₀ * t⁻¹) * (b₀ * (t * b₀ * t⁻¹) * t) * (a₀ * (t * a₀ * t⁻¹)) *
        (b₀ * (t * b₀ * t⁻¹) * t)
        = (a₀ * (t * a₀ * t⁻¹)) * ((b₀ * (t * b₀ * t⁻¹) * t) * (a₀ * (t * a₀ * t⁻¹)) *
            (b₀ * (t * b₀ * t⁻¹) * t)) := by simp only [mul_assoc]
      _ = 1 := by
        have e := h.rel.s2_dl2
        rw [h.rel.s2_inv] at e
        rw [e]
        exact mul_inv_cancel _

end Canon

end Fin

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem rpow_mem_L (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) {d : G}
    (hd : d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d ∈
      zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
  h.mem_L_iff.2 ⟨i, d, hd, rfl⟩

omit [Finite G] in
theorem mem_Mm_of_form1 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) {d : G}
    (hd : d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d ∈ Mm t a₀ b₀ := h.L_le_Mm (h.rpow_mem_L i hd)

omit [Finite G] in
theorem mem_Mm_of_form3 (h : Canon S P₁ P₂ z t a a₀ b₀ M) (i : ℤ) {d : G}
    (hd : d ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t) :
    (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * d * a₀ ∈ Mm t a₀ b₀ :=
  h.mem_Mm_iff.2 (Or.inr ⟨_, h.rpow_mem_L i hd, rfl⟩)

omit [Finite G] in
theorem relIndex_Mm (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    (Mm t a₀ b₀).relIndex (HH t a₀ b₀) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  have ht : t ∈ HH t a₀ b₀ := D1_le_HH t a₀ b₀ (Rel.t_mem_D1 _ _ _)
  refine ⟨t, ht, fun g hg => ?_⟩
  by_cases hM : g ∈ Mm t a₀ b₀
  · right
    refine ⟨hM, fun hgt => h.t_not_mem_Mm ?_⟩
    have h' := mul_mem (Subgroup.inv_mem _ hM) hgt
    rwa [inv_mul_cancel_left] at h'
  · left
    refine ⟨?_, hM⟩
    rcases h.HH_nf hg with ⟨i, d, hd, rfl⟩ | ⟨i, d, hd, rfl⟩ | ⟨i, d, hd, rfl⟩ | ⟨i, d, hd, rfl⟩
    · exact absurd (h.mem_Mm_of_form1 i hd) hM
    · rw [form2_mul_t (h.D2_comm_t hd).symm h.rel.t_sq]
      exact h.mem_Mm_of_form1 i hd
    · exact absurd (h.mem_Mm_of_form3 i hd) hM
    · rw [form4_mul_t h.a_t_eq (h.D2_comm_r hd) (h.D2_comm_t hd) h.t_r_t, mul_assoc,
        ← zpow_sub_one] 
      rw [← mul_assoc]
      exact h.mem_Mm_of_form3 (i - 1) hd

omit [Finite G] in
theorem Mm_der (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ⁅Mm t a₀ b₀, Mm t a₀ b₀⁆ ≤ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
  rw [Subgroup.commutator_le]
  have hrz : ∀ i : ℤ, (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i ∈ zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹) :=
    fun i => zpow_mem (mem_zpowers _) i
  have hform : ∀ g ∈ Mm t a₀ b₀, ∃ n ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t, ∃ α : G,
      g = n * α ∧ ∃ i : ℤ, α = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i ∨
        α = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀ := by
    intro g hg
    rcases h.mem_Mm_iff.1 hg with hL | ⟨k, hk, rfl⟩
    · obtain ⟨i, d, hd, rfl⟩ := h.mem_L_iff.1 hL
      exact ⟨d, hd, _, h.L_comm _ (hrz i) d hd, i, Or.inl rfl⟩
    · obtain ⟨i, d, hd, rfl⟩ := h.mem_L_iff.1 hk
      refine ⟨d, hd, (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀, ?_, i, Or.inr rfl⟩
      rw [← mul_assoc, h.L_comm _ (hrz i) d hd, mul_assoc]
  have hnorm : ∀ α : G, (∃ i : ℤ, α = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i ∨
      α = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀) →
      ∀ x ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t,
        α * x * α⁻¹ ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := by
    rintro α ⟨i, rfl | rfl⟩ x hx
    · rw [mul_inv_eq_iff_eq_mul.2 (h.L_comm _ (hrz i) x hx)]
      exact hx
    · have e : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀ * x * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀)⁻¹ =
          (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * (a₀ * x * a₀⁻¹) * ((a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i)⁻¹ := by
        group
      rw [e, mul_inv_eq_iff_eq_mul.2 (h.L_comm _ (hrz i) _ (h.rel.a_conj_D2 x hx))]
      exact h.rel.a_conj_D2 x hx
  have hcomm : ∀ α α' : G, (∃ i : ℤ, α = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i ∨
      α = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * a₀) →
      (∃ j : ℤ, α' = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ j ∨ α' = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ j * a₀) →
      α * α' = α' * α := by
    have hra : Commute (a₀ * (t * a₀ * t⁻¹)⁻¹) a₀ := h.rel.commute_dl1_a
    rintro α α' ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
    · exact (((Commute.refl _).zpow_zpow i j)).eq
    · exact ((((Commute.refl _).zpow_zpow i j).mul_right (hra.zpow_left i))).eq
    · exact ((((Commute.refl _).zpow_zpow i j).mul_left (hra.zpow_left j).symm)).eq
    · exact ((((Commute.refl _).zpow_zpow i j).mul_right (hra.zpow_left i)).mul_left
        ((hra.zpow_left j).symm.mul_right (Commute.refl a₀))).eq
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨n, hn, α, rfl, hα⟩ := hform g₁ hg₁
  obtain ⟨n', hn', α', rfl, hα'⟩ := hform g₂ hg₂
  rw [commutatorElement_def]
  exact comm_mem_of_normalizing hn hn' (hnorm α hα) (hnorm α' hα') (hcomm α α' hα hα')

omit [Finite G] in
theorem Mm_cos (h : Canon S P₁ P₂ z t a a₀ b₀ M) {w : G} (hw : w ∈ HH t a₀ b₀)
    (hwM : w ∉ Mm t a₀ b₀) :
    ∃ e ∈ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t, (w * e) * (w * e) = 1 := by
  rcases h.HH_nf hw with ⟨i, d, hd, rfl⟩ | ⟨i, d, hd, rfl⟩ | ⟨i, d, hd, rfl⟩ | ⟨i, d, hd, rfl⟩
  · exact absurd (h.mem_Mm_of_form1 i hd) hwM
  · refine ⟨d⁻¹, Subgroup.inv_mem _ hd, ?_⟩
    rw [mul_inv_cancel_right]
    exact h.dih1.refl_sq i
  · exact absurd (h.mem_Mm_of_form3 i hd) hwM
  · refine ⟨a₀⁻¹ * d⁻¹ * a₀ * (b₀ * (t * b₀ * t⁻¹) * t),
      mul_mem (h.a_inv_conj_D2 _ (Subgroup.inv_mem _ hd)) (Rel.s2_mem_D2 _ _ _ _ _), ?_⟩
    have e : (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * d * a₀ *
        (a₀⁻¹ * d⁻¹ * a₀ * (b₀ * (t * b₀ * t⁻¹) * t)) =
        (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ i * t * a₀ * (b₀ * (t * b₀ * t⁻¹) * t) := by
      group
    rw [e]
    exact h.refl_a_s2_sq i

end Canon

end Fin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
