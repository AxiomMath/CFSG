module

public import CFSG.ClassicalInvolution.Asc77.AscSCH02

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open scoped commutatorElement

variable {E J : Type*} [Group E] [Group J]

theorem comm_lift_congr (π : E →* J) (hC : π.ker ≤ Subgroup.center E) {x y x' y' : E}
    (hx : π x' = π x) (hy : π y' = π y) : ⁅x', y'⁆ = ⁅x, y⁆ := by
  have h1 : x' * x⁻¹ ∈ Subgroup.center E := hC (by rw [MonoidHom.mem_ker, map_mul, map_inv, hx,
    mul_inv_cancel])
  have h2 : y' * y⁻¹ ∈ Subgroup.center E := hC (by rw [MonoidHom.mem_ker, map_mul, map_inv, hy,
    mul_inv_cancel])
  have := CFSG.RankThree.Classical.commutatorElement_central_mul' (a := x) (b := y) h1 h2
  simpa only [inv_mul_cancel_right] using this

theorem comm_conj_lift (π : E →* J) (hC : π.ker ≤ Subgroup.center E) {x y : E}
    (hxy : ⁅π x, π y⁆ = 1) (g : E) : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = ⁅x, y⁆ := by
  refine CFSG.RankThree.Classical.commutatorElement_conj_of_mem_center (hC ?_) g
  rw [MonoidHom.mem_ker, map_commutatorElement, hxy]

theorem comm_inv_left_of_central {x y : E} (h : ⁅x, y⁆ ∈ Subgroup.center E) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have hcinv : ⁅x, y⁆⁻¹ ∈ Subgroup.center E := Subgroup.inv_mem _ h
  have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by simp only [commutatorElement_def]; group
  rw [e, Subgroup.mem_center_iff.1 hcinv x⁻¹, inv_mul_cancel_right]

theorem comm_inv_inv_of_central {x y : E} (h : ⁅x, y⁆ ∈ Subgroup.center E) :
    ⁅x⁻¹, y⁻¹⁆ = ⁅x, y⁆ :=
  CFSG.SectionRank.OddCover.commutatorElement_inv_inv_of_mem_center h

theorem comm_eq_one_of_swap {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (π : E →* J)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker)
    {x y : E} (hxy : ⁅π x, π y⁆ = 1) (w : J)
    (hw1 : w * π x * w⁻¹ = π y) (hw2 : w * π y * w⁻¹ = π x) : ⁅x, y⁆ = 1 := by
  set w' : E := Function.surjInv hπ w with hw'
  have hπw : π w' = w := Function.surjInv_eq hπ w
  have hcK : ⁅x, y⁆ ∈ π.ker := by rw [MonoidHom.mem_ker, map_commutatorElement, hxy]
  have h1 : ⁅w' * x * w'⁻¹, w' * y * w'⁻¹⁆ = ⁅y, x⁆ :=
    comm_lift_congr π hC (by rw [map_mul, map_mul, map_inv, hπw, hw1])
      (by rw [map_mul, map_mul, map_inv, hπw, hw2])
  have h2 := comm_conj_lift π hC hxy w'
  have : ⁅x, y⁆ = ⁅x, y⁆⁻¹ := calc
    ⁅x, y⁆ = ⁅w' * x * w'⁻¹, w' * y * w'⁻¹⁆ := h2.symm
    _ = ⁅y, x⁆ := h1
    _ = ⁅x, y⁆⁻¹ := (commutatorElement_inv x y).symm
  exact eq_one_of_central_inv hp2 π hCp hcK this

theorem comm_eq_one_of_inv_left {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (π : E →* J)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker)
    {x y : E} (hxy : ⁅π x, π y⁆ = 1) (w : J)
    (hw1 : w * π x * w⁻¹ = (π x)⁻¹) (hw2 : w * π y * w⁻¹ = π y) : ⁅x, y⁆ = 1 := by
  set w' : E := Function.surjInv hπ w with hw'
  have hπw : π w' = w := Function.surjInv_eq hπ w
  have hcK : ⁅x, y⁆ ∈ π.ker := by rw [MonoidHom.mem_ker, map_commutatorElement, hxy]
  have h1 : ⁅w' * x * w'⁻¹, w' * y * w'⁻¹⁆ = ⁅x⁻¹, y⁆ :=
    comm_lift_congr π hC (by rw [map_mul, map_mul, map_inv, hπw, hw1, map_inv])
      (by rw [map_mul, map_mul, map_inv, hπw, hw2])
  have h2 := comm_conj_lift π hC hxy w'
  have : ⁅x, y⁆ = ⁅x, y⁆⁻¹ := calc
    ⁅x, y⁆ = ⁅w' * x * w'⁻¹, w' * y * w'⁻¹⁆ := h2.symm
    _ = ⁅x⁻¹, y⁆ := h1
    _ = ⁅x, y⁆⁻¹ := comm_inv_left_of_central (hC hcK)
  exact eq_one_of_central_inv hp2 π hCp hcK this

theorem comm_eq_one_of_swap_inv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (π : E →* J)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker)
    {x y : E} (hxy : ⁅π x, π y⁆ = 1) (w : J)
    (hw1 : w * π x * w⁻¹ = (π y)⁻¹) (hw2 : w * π y * w⁻¹ = (π x)⁻¹) : ⁅x, y⁆ = 1 := by
  set w' : E := Function.surjInv hπ w with hw'
  have hπw : π w' = w := Function.surjInv_eq hπ w
  have hcK : ⁅x, y⁆ ∈ π.ker := by rw [MonoidHom.mem_ker, map_commutatorElement, hxy]
  have h1 : ⁅w' * x * w'⁻¹, w' * y * w'⁻¹⁆ = ⁅y⁻¹, x⁻¹⁆ :=
    comm_lift_congr π hC (by rw [map_mul, map_mul, map_inv, hπw, hw1, map_inv])
      (by rw [map_mul, map_mul, map_inv, hπw, hw2, map_inv])
  have h2 := comm_conj_lift π hC hxy w'
  have hyx : ⁅y, x⁆ ∈ Subgroup.center E := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hC hcK)
  have : ⁅x, y⁆ = ⁅x, y⁆⁻¹ := calc
    ⁅x, y⁆ = ⁅w' * x * w'⁻¹, w' * y * w'⁻¹⁆ := h2.symm
    _ = ⁅y⁻¹, x⁻¹⁆ := h1
    _ = ⁅y, x⁆ := comm_inv_inv_of_central hyx
    _ = ⁅x, y⁆⁻¹ := (commutatorElement_inv x y).symm
  exact eq_one_of_central_inv hp2 π hCp hcK this

theorem commutative_comap_closure (π : E →* J) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (S : Set J)
    (hS : ∀ s ∈ S, ∀ t ∈ S, ∀ s' t' : E, π s' = s → π t' = t → s' * t' = t' * s') :
    ∀ x ∈ (Subgroup.closure S).comap π, ∀ y ∈ (Subgroup.closure S).comap π, x * y = y * x := by
  classical
  set G : Set E := {x | π x ∈ S} with hG
  set A : Subgroup E := Subgroup.closure G with hA
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy => hS _ hx _ hy x y rfl rfl
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h1 : A ≤ Subgroup.centralizer (G : Set E) := by
      rw [hA, Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      exact hGcomm h hh g hg
    have hx' : ∀ g ∈ G, g * x = x * g := fun g hg => Subgroup.mem_centralizer_iff.1 (h1 hx) g hg
    have h2 : A ≤ Subgroup.centralizer ({x} : Set E) := by
      rw [hA, Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hx' g hg).symm
    exact Subgroup.mem_centralizer_iff.1 (h2 hy) x rfl
  have hlift : ∀ u ∈ Subgroup.closure S, ∃ a ∈ A, π a = u := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem u hu => exact ⟨Function.surjInv hπ u, Subgroup.subset_closure (by
        show π (Function.surjInv hπ u) ∈ S
        rw [Function.surjInv_eq hπ]; exact hu), Function.surjInv_eq hπ u⟩
    | one => exact ⟨1, A.one_mem, map_one π⟩
    | mul u v _ _ hu hv =>
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a * b, A.mul_mem ha hb, map_mul π a b⟩
    | inv u _ hu =>
      obtain ⟨a, ha, rfl⟩ := hu
      exact ⟨a⁻¹, A.inv_mem ha, map_inv π a⟩
  have hdec : ∀ x ∈ (Subgroup.closure S).comap π, ∃ z ∈ π.ker, ∃ a ∈ A, x = z * a := by
    intro x hx
    obtain ⟨a, ha, hπa⟩ := hlift (π x) (Subgroup.mem_comap.1 hx)
    refine ⟨x * a⁻¹, ?_, a, ha, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπa, mul_inv_cancel]
  intro x hx y hy
  obtain ⟨z₁, hz₁, a₁, ha₁, rfl⟩ := hdec x hx
  obtain ⟨z₂, hz₂, a₂, ha₂, rfl⟩ := hdec y hy
  have c1 := Subgroup.mem_center_iff.1 (hC hz₁)
  have c2 := Subgroup.mem_center_iff.1 (hC hz₂)
  calc z₁ * a₁ * (z₂ * a₂) = z₁ * (a₁ * z₂) * a₂ := by group
    _ = z₁ * (z₂ * a₁) * a₂ := by rw [← c2 a₁]
    _ = z₁ * z₂ * (a₁ * a₂) := by group
    _ = z₁ * z₂ * (a₂ * a₁) := by rw [hAcomm a₁ ha₁ a₂ ha₂]
    _ = z₂ * z₁ * (a₂ * a₁) := by rw [c1 z₂]
    _ = z₂ * (z₁ * a₂) * a₁ := by group
    _ = z₂ * (a₂ * z₁) * a₁ := by rw [c1 a₂]
    _ = z₂ * a₂ * (z₁ * a₁) := by group

theorem comm_eq_one_of_same {π : E →* J} (hC : π.ker ≤ Subgroup.center E) {s t : E}
    (h : π s = π t) : ⁅s, t⁆ = 1 := by
  rw [comm_lift_congr π hC (x := t) (y := t) h rfl, commutatorElement_self]

theorem ker_eq_bot_of_swap {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite E] [Group.IsPerfect E]
    (π : E →* J) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) (x₁ x₂ w : J) (h12 : x₁ * x₂ = x₂ * x₁)
    (hw₁ : w * x₁ * w⁻¹ = x₂) (hw₂ : w * x₂ * w⁻¹ = x₁)
    (hord : (Nat.card J).factorization p ≤
      (Nat.card (Subgroup.closure ({x₁, x₂} : Set J))).factorization p) :
    π.ker = ⊥ := by
  have hcomm : ∀ s' t' : E, π s' = x₁ → π t' = x₂ → s' * t' = t' * s' := by
    intro s' t' hs ht
    have hxy : ⁅π s', π t'⁆ = 1 := by
      rw [hs, ht]; exact commutatorElement_eq_one_iff_mul_comm.2 h12
    exact commutatorElement_eq_one_iff_mul_comm.1
      (comm_eq_one_of_swap hp2 π hπ hC hCp hxy w (by rw [hs, ht]; exact hw₁)
        (by rw [hs, ht]; exact hw₂))
  have hcomm' : ∀ s' t' : E, π s' = x₂ → π t' = x₁ → s' * t' = t' * s' := fun s' t' hs ht =>
    (hcomm t' s' ht hs).symm
  have hTab := commutative_comap_closure π hπ hC ({x₁, x₂} : Set J) (by
    intro s hs t ht s' t' hs' ht'
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · exact commutatorElement_eq_one_iff_mul_comm.1 (comm_eq_one_of_same hC (by rw [hs', ht']))
    · rw [Set.mem_singleton_iff.1 ht] at ht'
      exact hcomm s' t' hs' ht'
    · rw [Set.mem_singleton_iff.1 hs] at hs'
      exact hcomm' s' t' hs' ht'
    · rw [Set.mem_singleton_iff.1 hs] at hs'
      rw [Set.mem_singleton_iff.1 ht] at ht'
      exact commutatorElement_eq_one_iff_mul_comm.1 (comm_eq_one_of_same hC (by rw [hs', ht'])))
  refine ker_eq_bot_of_torus hp2 π hπ hC hCp (Subgroup.closure ({x₁, x₂} : Set J)) 1 1 hTab
    (Subgroup.one_mem _) (by group) (fun t _ _ => by group) ?_
  rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq]
  exact hord

theorem comm_comap_closure_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (π : E →* J) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) (y₁ y₂ y₃ : J)
    (h12 : y₁ * y₂ = y₂ * y₁) (h13 : y₁ * y₃ = y₃ * y₁) (h23 : y₂ * y₃ = y₃ * y₂)
    (w₀₂ w₁₃ w₀₁ : J)
    (hw12a : w₀₂ * y₁ * w₀₂⁻¹ = y₂⁻¹) (hw12b : w₀₂ * y₂ * w₀₂⁻¹ = y₁⁻¹)
    (hw23a : w₁₃ * y₂ * w₁₃⁻¹ = y₃⁻¹) (hw23b : w₁₃ * y₃ * w₁₃⁻¹ = y₂⁻¹)
    (hw13a : w₀₁ * y₁ * w₀₁⁻¹ = y₁⁻¹) (hw13b : w₀₁ * y₃ * w₀₁⁻¹ = y₃) :
    ∀ x ∈ (Subgroup.closure ({y₁, y₂, y₃} : Set J)).comap π,
      ∀ y ∈ (Subgroup.closure ({y₁, y₂, y₃} : Set J)).comap π, x * y = y * x := by
  have e12 : ∀ s' t' : E, π s' = y₁ → π t' = y₂ → s' * t' = t' * s' := by
    intro s' t' hs ht
    have hxy : ⁅π s', π t'⁆ = 1 := by
      rw [hs, ht]; exact commutatorElement_eq_one_iff_mul_comm.2 h12
    exact commutatorElement_eq_one_iff_mul_comm.1
      (comm_eq_one_of_swap_inv hp2 π hπ hC hCp hxy w₀₂ (by rw [hs, ht]; exact hw12a)
        (by rw [hs, ht]; exact hw12b))
  have e23 : ∀ s' t' : E, π s' = y₂ → π t' = y₃ → s' * t' = t' * s' := by
    intro s' t' hs ht
    have hxy : ⁅π s', π t'⁆ = 1 := by
      rw [hs, ht]; exact commutatorElement_eq_one_iff_mul_comm.2 h23
    exact commutatorElement_eq_one_iff_mul_comm.1
      (comm_eq_one_of_swap_inv hp2 π hπ hC hCp hxy w₁₃ (by rw [hs, ht]; exact hw23a)
        (by rw [hs, ht]; exact hw23b))
  have e13 : ∀ s' t' : E, π s' = y₁ → π t' = y₃ → s' * t' = t' * s' := by
    intro s' t' hs ht
    have hxy : ⁅π s', π t'⁆ = 1 := by
      rw [hs, ht]; exact commutatorElement_eq_one_iff_mul_comm.2 h13
    exact commutatorElement_eq_one_iff_mul_comm.1
      (comm_eq_one_of_inv_left hp2 π hπ hC hCp hxy w₀₁ (by rw [hs]; exact hw13a)
        (by rw [ht]; exact hw13b))
  have hsame : ∀ s' t' : E, π s' = π t' → s' * t' = t' * s' := fun s' t' h =>
    commutatorElement_eq_one_iff_mul_comm.1 (comm_eq_one_of_same hC h)
  exact commutative_comap_closure π hπ hC ({y₁, y₂, y₃} : Set J) (by
    intro s hs t ht s' t' hs' ht'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;>
      rw [hs] at hs' <;> rw [ht] at ht'
    all_goals first
      | exact hsame s' t' (hs'.trans ht'.symm)
      | exact e12 s' t' hs' ht'
      | exact e13 s' t' hs' ht'
      | exact e23 s' t' hs' ht'
      | exact (e12 t' s' ht' hs').symm
      | exact (e13 t' s' ht' hs').symm
      | exact (e23 t' s' ht' hs').symm)

theorem ker_eq_bot_of_torus_three_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite E]
    [Group.IsPerfect E] (π : E →* J) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) (y₁ y₂ y₃ c g : J)
    (h12 : y₁ * y₂ = y₂ * y₁) (h13 : y₁ * y₃ = y₃ * y₁) (h23 : y₂ * y₃ = y₃ * y₂)
    (w₀₂ w₁₃ w₀₁ : J)
    (hw12a : w₀₂ * y₁ * w₀₂⁻¹ = y₂⁻¹) (hw12b : w₀₂ * y₂ * w₀₂⁻¹ = y₁⁻¹)
    (hw23a : w₁₃ * y₂ * w₁₃⁻¹ = y₃⁻¹) (hw23b : w₁₃ * y₃ * w₁₃⁻¹ = y₂⁻¹)
    (hw13a : w₀₁ * y₁ * w₀₁⁻¹ = y₁⁻¹) (hw13b : w₀₁ * y₃ * w₀₁⁻¹ = y₃)
    (T : Subgroup J) (hT : T ≤ Subgroup.closure ({y₁, y₂, y₃} : Set J))
    (hc : c ∈ Subgroup.normalizer (T : Set J)) (hgc : g * c * g⁻¹ = c⁻¹)
    (hgT : ∀ t ∈ T, c * t * c⁻¹ = t → g * t * g⁻¹ = t)
    (hord : (Nat.card J).factorization p ≤
      (Nat.card ↥(T ⊔ Subgroup.zpowers c)).factorization p) :
    π.ker = ⊥ := by
  have hTab := comm_comap_closure_three hp2 π hπ hC hCp y₁ y₂ y₃ h12 h13 h23 w₀₂ w₁₃ w₀₁ hw12a
    hw12b hw23a hw23b hw13a hw13b
  exact ker_eq_bot_of_torus hp2 π hπ hC hCp T c g
    (fun x hx y hy => hTab x (Subgroup.comap_mono hT hx) y (Subgroup.comap_mono hT hy)) hc hgc
    hgT hord

end CFSG.ClassicalInvolution.Asc77.SCH
