module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
import CFSG.ClassicalInvolution.Asc77.AscT8RepEng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8V

section Alg

open scoped Classical in
theorem exists_mul_self_eq_of_cyclic {G : Type} [Group G] (U : Subgroup G) [IsCyclic ↥U]
    (hU : IsPGroup 2 ↥U) (h4 : 4 ≤ Nat.card ↥U) {z : G} (hzU : z ∈ U) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : ∃ g ∈ U, g * g = z := by
  have : Finite ↥U := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype ↥U := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := ↥U)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hU
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k ≤ 1 := by omega
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hord : orderOf u = 2 ^ k := by rw [orderOf_eq_card_of_forall_mem_zpowers hu, hk]
  set g : ↥U := u ^ (2 ^ (k - 2)) with hg
  have hgg : g * g = u ^ (2 ^ (k - 1)) := by
    rw [hg, ← pow_add]
    congr 1
    have : 2 ^ (k - 2) + 2 ^ (k - 2) = 2 ^ (k - 1) := by
      have h1 : k - 1 = (k - 2) + 1 := by omega
      rw [h1, pow_succ]; ring
    exact this
  have hz0ord : orderOf (g * g) = 2 := by
    rw [hgg, orderOf_pow' _ (by positivity), hord]
    have : Nat.gcd (2 ^ k) (2 ^ (k - 1)) = 2 ^ (k - 1) := by
      apply Nat.gcd_eq_right
      exact Nat.pow_dvd_pow 2 (by omega)
    have h1 : k - (k - 1) = 1 := by omega
    rw [this, Nat.pow_div (by omega) (by norm_num), h1]
  have hsol : ∀ x : ↥U, x * x = 1 → x = 1 ∨ x = g * g := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hS : (Finset.univ.filter fun a : ↥U => a ^ 2 = 1).card ≤ 2 :=
      IsCyclic.card_pow_eq_one_le (by norm_num)
    have h3 : ({1, x, g * g} : Finset ↥U) ⊆ Finset.univ.filter fun a : ↥U => a ^ 2 = 1 := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl | rfl
      · simp
      · rwa [pow_two]
      · have : (g * g) ^ 2 = 1 := by
          have := pow_orderOf_eq_one (g * g)
          rwa [hz0ord] at this
        exact this
    have hne1 : (1 : ↥U) ≠ g * g := by
      intro h
      rw [← h] at hz0ord
      simp at hz0ord
    have hcard : ({1, x, g * g} : Finset ↥U).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hcon.2
      · simp [Ne.symm hcon.1, hne1]
    have := Finset.card_le_card h3
    omega
  refine ⟨(g : G), g.2, ?_⟩
  have hzs : (⟨z, hzU⟩ : ↥U) * ⟨z, hzU⟩ = 1 := Subtype.ext hz2
  rcases hsol _ hzs with h | h
  · exact absurd (congrArg Subtype.val h) hz1
  · have := congrArg Subtype.val h
    simpa using this.symm

theorem mul_inv_inv_sq {G : Type} [Group G] {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) :
    (a * b⁻¹ * c⁻¹) * (a * b⁻¹ * c⁻¹) = (a * a) * ((b * b)⁻¹ * (c * c)⁻¹) := by
  exact mul_inv_inv_sqE hab hac hbc

end Alg

section Rel

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem centralizes_of_comm_r (c : Ctx p f Ω W) (ρ : Rep Ω W) {y : G} (hyW : y ∈ W)
    (hry : ρ.r * y = y * ρ.r) : ∀ x ∈ ρ.R, x * y = y * x := by
  exact centralizes_of_comm_rE (RepHooks.ofCtx c) ρ hyW hry

theorem exists_sq_root (c : Ctx p f Ω W) (ρ : Rep Ω W) {z : G} (hz : IsUniqueInvolution ρ.K z) :
    ∃ g : G, g ∈ ρ.K ⊓ W ∧ g ∈ ρ.R ∧ g * g = z := by
  obtain ⟨h1, -, hcyc, h4, -⟩ := inf_W_of_mem_D c.hp c.hq c.hΩ c.hW ρ.hR ρ.hK ρ.hRK
  have hzKW : z ∈ ρ.K ⊓ W :=
    uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hz
  have hzU : z ∈ ρ.R ⊓ W := h1 ▸ hzKW
  have hU2 : IsPGroup 2 ↥(ρ.R ⊓ W) := (isPGroup_of_mem_WSet c.hW).to_inf_right
  obtain ⟨g, hg, hgg⟩ := exists_mul_self_eq_of_cyclic (ρ.R ⊓ W) hU2 h4 hzU hz.sq hz.ne_one
  exact ⟨g, h1 ▸ hg, hg.1, hgg⟩

theorem centralizes_vg (c : Ctx p f Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K)
    (hnot : σ.K ∉ omegaNbr Ω ρ.K) {z v g : G} (hz : IsUniqueInvolution ρ.K z)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ.K ⊓ W) (hgg : g * g = z) :
    v * g⁻¹ ∈ W ∧ (∀ x ∈ ρ.R, x * (v * g⁻¹) = (v * g⁻¹) * x) ∧
      (v * g⁻¹) * (v * g⁻¹) = z := by
  exact centralizes_vgE (RepHooks.ofCtx c) ρ σ hne hnot hz hv hg hgg

theorem centralizes_mem_inf_W (c : Ctx p f Ω W) (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω ρ.K)
    {g : G} (hg : g ∈ σ.K ⊓ W) : ∀ x ∈ ρ.R, x * g = g * x :=
  centralizes_of_comm_r c ρ hg.2 (c.centralizes ρ σ hnbr hg)

theorem centralizes_inv_of_nbr (c : Ctx p f Ω W) (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω ρ.K)
    {v : G} (hv : IsUniqueInvolution σ.K v) : ∀ x ∈ ρ.R, x * v = v * x := by
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (T8.rep_le_centralizer c ρ σ (Or.inr hnbr) hv hx)

theorem exists_y_left (c : Ctx p f Ω W) (ρ₁ ρ₂ σ : Rep Ω W) {z₁ v g : G}
    (hn21 : ρ₁.K ∈ omegaNbr Ω ρ₂.K) (hne : ρ₁.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ₁.K)
    (hσ₂ : σ.K ∈ omegaNbr Ω ρ₂.K) (hz : IsUniqueInvolution ρ₁.K z₁)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ₁.K ⊓ W) (hgg : g * g = z₁) :
    ∃ y ∈ W, y * y = z₁ ∧ (∀ x ∈ ρ₁.R, x * y = y * x) ∧ (∀ x ∈ ρ₂.R, x * y = y * x) := by
  obtain ⟨hyW, hy1, hyy⟩ := centralizes_vg c ρ₁ σ hne hnot hz hv hg hgg
  refine ⟨v * g⁻¹, hyW, hyy, hy1, fun x hx => ?_⟩
  have h1 : Commute x v := centralizes_inv_of_nbr c ρ₂ σ hσ₂ hv x hx
  have h2 : Commute x g := centralizes_mem_inf_W c ρ₂ ρ₁ hn21 hg x hx
  exact (h1.mul_right h2.inv_right)

theorem exists_y_both (c : Ctx p f Ω W) (ρ₁ ρ₂ σ : Rep Ω W) {z₁ z₂ v g h : G}
    (hn12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K) (hn21 : ρ₁.K ∈ omegaNbr Ω ρ₂.K) (hne1 : ρ₁.K ≠ σ.K)
    (hne2 : ρ₂.K ≠ σ.K) (hnot1 : σ.K ∉ omegaNbr Ω ρ₁.K) (hnot2 : σ.K ∉ omegaNbr Ω ρ₂.K)
    (hz₁ : IsUniqueInvolution ρ₁.K z₁) (hz₂ : IsUniqueInvolution ρ₂.K z₂)
    (hv : IsUniqueInvolution σ.K v) (hg : g ∈ ρ₁.K ⊓ W) (hgg : g * g = z₁)
    (hh : h ∈ ρ₂.K ⊓ W) (hhh : h * h = z₂) :
    ∃ y ∈ W, y = v * g⁻¹ * h⁻¹ ∧ y * y = z₁ * z₂ ∧ (∀ x ∈ ρ₁.R, x * y = y * x) ∧
      (∀ x ∈ ρ₂.R, x * y = y * x) := by
  exact exists_y_bothE (RepHooks.ofCtx c) ρ₁ ρ₂ σ hn12 hn21 hne1 hne2 hnot1 hnot2 hz₁ hz₂ hv hg
    hgg hh hhh

end Rel

end T8V

end CFSG.ClassicalInvolution.Asc77
