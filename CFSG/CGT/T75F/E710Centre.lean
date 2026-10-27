module

public import CFSG.CGT.T75F.E710Defs

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem closure_D_eq_top : Subgroup.closure D = ⊤ := by
  obtain ⟨y, hy, hyM⟩ := h.exists_out
  have h1 := h.gen y hy hyM
  rw [eq_top_iff, ← h1]
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · have : x ∈ Subgroup.closure (D ∩ (M : Set X)) := by
      rw [h.M_gen]; exact hx
    exact Subgroup.closure_mono Set.inter_subset_left this
  · rw [Set.mem_singleton_iff.1 hx]
    exact Subgroup.subset_closure hy

theorem mem_center_of_commute_D {c : X} (hc : ∀ d ∈ D, d * c = c * d) :
    c ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure D := by rw [h.closure_D_eq_top]; exact Subgroup.mem_top g
  have hle : Subgroup.closure D ≤ Subgroup.centralizer ({c} : Set X) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hc x hx
  have := hle hg
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem mem_center_of_commute {c e : X} (he : e ∈ D) (heM : e ∉ M)
    (hM : ∀ m ∈ M, m * c = c * m) (hec : e * c = c * e) : c ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure ((M : Set X) ∪ {e}) := by
    rw [h.gen e he heM]; exact Subgroup.mem_top g
  have hle : Subgroup.closure ((M : Set X) ∪ {e}) ≤ Subgroup.centralizer ({c} : Set X) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with hx | hx
    · exact hM x hx
    · rw [Set.mem_singleton_iff.1 hx]; exact hec
  have := hle hg
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem centre_of_order_two_mul {e β : X} (he : e ∈ D) (heM : e ∉ M) (hβ : β ∈ D) (hβM : β ∈ M)
    {k : ℕ} (ho : orderOf (e * β) = 2 * k) :
    (e * β) ^ k ∈ M ∧ (e * β) ^ k ∈ Subgroup.center X := by
  have he2 := h.sq_eq_one e he
  have hβ2 := h.sq_eq_one β hβ
  have hr : (e * β) ^ (2 * k) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  obtain ⟨hec, hβc⟩ := dihedral_center_comm he2 hβ2 hr
  obtain ⟨-, hcβD⟩ := dihedral_center_mul_mem (S := D) (fun g x hx => h.conj_mem x hx g) he2 hβ2 hr
    he hβ
  have hcβ : (e * β) ^ k * β * β = β * ((e * β) ^ k * β) := by
    calc (e * β) ^ k * β * β = (β * (e * β) ^ k) * β := by rw [hβc]
      _ = β * ((e * β) ^ k * β) := by group
  have hmem : (e * β) ^ k * β ∈ M := h.H3 β hβ hβM _ hcβD hcβ
  have hcM : (e * β) ^ k ∈ M := by
    have : (e * β) ^ k * β * β ∈ M := M.mul_mem hmem hβM
    rwa [mul_assoc, hβ2, mul_one] at this
  exact ⟨hcM, h.mem_center_of_commute he heM (fun m hm => h.M_comm m hm _ hcM) hec⟩

theorem exists_conj_mul_center {e β : X} (he : e ∈ D) (heM : e ∉ M) (hβ : β ∈ D)
    (hβM : β ∈ M) : ∃ g : X, ∃ c ∈ Subgroup.center X, β = g * e * g⁻¹ * c := by
  have he2 := h.sq_eq_one e he
  have hβ2 := h.sq_eq_one β hβ
  obtain ⟨k, hk, hk3, hcase⟩ := h.order_cases he heM hβ hβM
  rcases hcase with ho | ho
  ·
    have hk1 : (e * β) ^ k = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    have hr : (e * β) ^ (2 * k) = 1 := by rw [pow_mul', hk1, one_pow]
    have hc := dihedral_center_mul_conj he2 hβ2 hk hr
    rw [hk1, one_mul] at hc
    set g := (e * β) ^ ((k + 1) / 2) with hg
    refine ⟨g⁻¹, 1, Subgroup.one_mem _, ?_⟩
    calc β = g⁻¹ * (g * β * g⁻¹) * g := by group
      _ = g⁻¹ * e * g := by rw [← hc]
      _ = g⁻¹ * e * (g⁻¹)⁻¹ * 1 := by rw [inv_inv, mul_one]
  ·
    obtain ⟨-, hcZ⟩ := h.centre_of_order_two_mul he heM hβ hβM ho
    have hr : (e * β) ^ (2 * k) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    have hc := dihedral_center_mul_conj he2 hβ2 hk hr
    set g := (e * β) ^ ((k + 1) / 2) with hg
    set c := (e * β) ^ k with hcdef
    refine ⟨g⁻¹, c, hcZ, ?_⟩
    have hcg : g * c = c * g := ((Commute.refl (e * β)).pow_pow _ _).eq
    have hce : c * e = e * c := (Subgroup.mem_center_iff.1 hcZ e).symm
    calc β = g⁻¹ * (g * β * g⁻¹) * g := by group
      _ = g⁻¹ * (c * e) * g := by rw [← hc]
      _ = g⁻¹ * e * (c * g) := by rw [hce]; group
      _ = g⁻¹ * e * (g * c) := by rw [hcg]
      _ = g⁻¹ * e * (g⁻¹)⁻¹ * c := by rw [inv_inv]; group

theorem single_class {d d' : X} (hd : d ∈ D) (hd' : d' ∈ D) :
    ∃ g : X, ∃ c ∈ Subgroup.center X, d' = g * d * g⁻¹ * c := by
  obtain ⟨y, hy, hyM⟩ := h.exists_out
  obtain ⟨a, ha⟩ := h.exists_conj_mem hd
  obtain ⟨a', ha'⟩ := h.exists_conj_mem hd'
  have hu : a⁻¹ * d * a ∈ D := by simpa using h.conj_mem d hd a⁻¹
  have hu' : a'⁻¹ * d' * a' ∈ D := by simpa using h.conj_mem d' hd' a'⁻¹
  obtain ⟨g₁, c₁, hc₁, h₁⟩ := h.exists_conj_mul_center hy hyM hu ha
  obtain ⟨g₂, c₂, hc₂, h₂⟩ := h.exists_conj_mul_center hy hyM hu' ha'
  have c₁comm : ∀ x : X, c₁ * x = x * c₁ := fun x => (Subgroup.mem_center_iff.1 hc₁ x).symm
  have c₂comm : ∀ x : X, c₂ * x = x * c₂ := fun x => (Subgroup.mem_center_iff.1 hc₂ x).symm
  have hy1 : y = g₁⁻¹ * (a⁻¹ * d * a) * g₁ * c₁⁻¹ := by
    have : a⁻¹ * d * a * c₁⁻¹ = g₁ * y * g₁⁻¹ := by
      rw [h₁]
      have hcc : g₁ * y * g₁⁻¹ * c₁ * c₁⁻¹ = g₁ * y * g₁⁻¹ := by group
      exact hcc
    calc y = g₁⁻¹ * (a⁻¹ * d * a * c₁⁻¹) * g₁ := by rw [this]; group
      _ = g₁⁻¹ * (a⁻¹ * d * a) * g₁ * c₁⁻¹ := by
          have hci : c₁⁻¹ * g₁ = g₁ * c₁⁻¹ := by
            have := c₁comm g₁
            calc c₁⁻¹ * g₁ = c₁⁻¹ * (g₁ * c₁) * c₁⁻¹ := by group
              _ = c₁⁻¹ * (c₁ * g₁) * c₁⁻¹ := by rw [this]
              _ = g₁ * c₁⁻¹ := by group
          calc g₁⁻¹ * (a⁻¹ * d * a * c₁⁻¹) * g₁ = g₁⁻¹ * (a⁻¹ * d * a) * (c₁⁻¹ * g₁) := by group
            _ = g₁⁻¹ * (a⁻¹ * d * a) * (g₁ * c₁⁻¹) := by rw [hci]
            _ = g₁⁻¹ * (a⁻¹ * d * a) * g₁ * c₁⁻¹ := by group
  refine ⟨a' * g₂ * g₁⁻¹ * a⁻¹, c₁⁻¹ * c₂, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₁) hc₂
  · have hd'eq : d' = a' * (a'⁻¹ * d' * a') * a'⁻¹ := by group
    have hconj : a' * (g₂ * y * g₂⁻¹ * c₂) * a'⁻¹ = a' * g₂ * y * g₂⁻¹ * a'⁻¹ * c₂ := by
      have := c₂comm (a'⁻¹)
      calc a' * (g₂ * y * g₂⁻¹ * c₂) * a'⁻¹ = a' * (g₂ * y * g₂⁻¹) * (c₂ * a'⁻¹) := by group
        _ = a' * (g₂ * y * g₂⁻¹) * (a'⁻¹ * c₂) := by rw [this]
        _ = a' * g₂ * y * g₂⁻¹ * a'⁻¹ * c₂ := by group
    calc d' = a' * (g₂ * y * g₂⁻¹ * c₂) * a'⁻¹ := by rw [← h₂]; exact hd'eq
      _ = a' * g₂ * y * g₂⁻¹ * a'⁻¹ * c₂ := hconj
      _ = a' * g₂ * (g₁⁻¹ * (a⁻¹ * d * a) * g₁ * c₁⁻¹) * g₂⁻¹ * a'⁻¹ * c₂ := by rw [← hy1]
      _ = (a' * g₂ * g₁⁻¹ * a⁻¹) * d * (a' * g₂ * g₁⁻¹ * a⁻¹)⁻¹ * (c₁⁻¹ * c₂) := by
          have := c₁comm (g₂⁻¹ * a'⁻¹)
          have hc1i : c₁⁻¹ * (g₂⁻¹ * a'⁻¹) = (g₂⁻¹ * a'⁻¹) * c₁⁻¹ := by
            calc c₁⁻¹ * (g₂⁻¹ * a'⁻¹) = c₁⁻¹ * (g₂⁻¹ * a'⁻¹) * c₁ * c₁⁻¹ := by group
              _ = c₁⁻¹ * (c₁ * (g₂⁻¹ * a'⁻¹)) * c₁⁻¹ := by rw [this]; group
              _ = (g₂⁻¹ * a'⁻¹) * c₁⁻¹ := by group
          calc a' * g₂ * (g₁⁻¹ * (a⁻¹ * d * a) * g₁ * c₁⁻¹) * g₂⁻¹ * a'⁻¹ * c₂
              = a' * g₂ * (g₁⁻¹ * (a⁻¹ * d * a) * g₁) * (c₁⁻¹ * (g₂⁻¹ * a'⁻¹)) * c₂ := by group
            _ = a' * g₂ * (g₁⁻¹ * (a⁻¹ * d * a) * g₁) * ((g₂⁻¹ * a'⁻¹) * c₁⁻¹) * c₂ := by
                rw [hc1i]
            _ = (a' * g₂ * g₁⁻¹ * a⁻¹) * d * (a' * g₂ * g₁⁻¹ * a⁻¹)⁻¹ * (c₁⁻¹ * c₂) := by group

theorem not_mem_center {d : X} (hd : d ∈ D) : d ∉ Subgroup.center X := by
  intro hz
  obtain ⟨y, hy, hyM⟩ := h.exists_out
  obtain ⟨a, ha⟩ := h.exists_conj_mem hd
  have hdM : d ∈ M := by
    have : a⁻¹ * d * a = d := by
      have := Subgroup.mem_center_iff.1 hz a
      calc a⁻¹ * d * a = a⁻¹ * (d * a) := by group
        _ = a⁻¹ * (a * d) := by rw [this]
        _ = d := by group
    rwa [this] at ha
  refine hyM (h.H3 d hd hdM y hy ?_)
  exact (Subgroup.mem_center_iff.1 hz y)

theorem mem_M_of_mul_center {d m z : X} (hd : d ∈ D) (hm : m ∈ M) (hz : z ∈ Subgroup.center X)
    (hdmz : d = m * z) : d ∈ M := by
  obtain ⟨β, hβ, hβM⟩ := h.exists_mem_delta
  refine h.H3 β hβ hβM d hd ?_
  rw [hdmz]
  calc m * z * β = m * (z * β) := by group
    _ = m * (β * z) := by rw [(Subgroup.mem_center_iff.1 hz β).symm]
    _ = (m * β) * z := by group
    _ = (β * m) * z := by rw [h.M_comm m hm β hβM]
    _ = β * (m * z) := by group

end Endgame710

end CFSG.CGT.T75F
