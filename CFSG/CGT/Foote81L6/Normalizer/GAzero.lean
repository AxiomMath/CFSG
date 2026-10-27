module

public import CFSG.CGT.Foote81L6.T0Sylow
public import CFSG.CGT.Foote81L6.TStruct.TypeT

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup TStruct

variable {G : Type*} [Group G] {T : Subgroup G} {n : ℕ} (D : FooteCore G T 2 n)

private theorem mem_zpowers_of_mul_self {z x : G} (hz : z * z = 1) :
    x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx
    rw [zpow_eq_zpow_emod' j (show z ^ 2 = 1 by rw [sq]; exact hz)]
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem conj_t_of_mem_A {u : G} (hu : u ∈ D.A) (hu1 : u ≠ 1) (hua : u ≠ D.a) :
    D.t * u * D.t⁻¹ = D.a * u := by
  have htu : D.t * u * D.t⁻¹ ∈ D.A := D.conj_t_A u hu
  set c := u⁻¹ * (D.t * u * D.t⁻¹) with hc
  have hcA : c ∈ D.A := mul_mem (inv_mem hu) htu
  have hc2 : c * c = 1 := D.mul_self_of_two hcA
  have htinv : D.t⁻¹ = D.t := D.t_inv
  have hct : c * D.t = D.t * c := by
    have h1 : D.t * c * D.t⁻¹ = c⁻¹ := by
      rw [hc]
      calc D.t * (u⁻¹ * (D.t * u * D.t⁻¹)) * D.t⁻¹
          = (D.t * u * D.t⁻¹)⁻¹ * ((D.t * D.t) * u * (D.t * D.t)⁻¹) := by group
        _ = (D.t * u * D.t⁻¹)⁻¹ * u := by rw [D.t_mul_t, one_mul, inv_one, mul_one]
        _ = (u⁻¹ * (D.t * u * D.t⁻¹))⁻¹ := by group
    have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    calc c * D.t = D.t * (D.t⁻¹ * c * D.t) := by group
      _ = D.t * (D.t * c * D.t⁻¹) := by rw [htinv]
      _ = D.t * c := by rw [h1, h2]
  rcases D.eq_one_or_a_of_comm_t hcA hct with h | h
  · exfalso
    apply hu1
    have h' : D.t * u * D.t⁻¹ = u := by
      have := congrArg (fun x => u * x) h
      simpa [hc] using this
    have hut : u * D.t = D.t * u := by
      calc u * D.t = (D.t * u * D.t⁻¹) * D.t := by rw [h']
        _ = D.t * u := by group
    rcases D.eq_one_or_a_of_comm_t hu hut with h2 | h2
    · exact h2
    · exact absurd h2 hua
  · calc D.t * u * D.t⁻¹ = u * c := by rw [hc]; group
      _ = u * D.a := by rw [h]
      _ = D.a * u := D.A_comm_of_two hu D.a_mem

theorem mem_Z_iff {x : G} :
    x ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) ↔
      ∃ u ∈ D.A, x = u ∨ x = u * D.b₀ ∨ x = u * D.b₁ ∨ x = u * D.b := by
  have hBle : zpowers D.b₀ ⊔ zpowers D.b₁ ≤ D.B :=
    sup_le (zpowers_le.2 D.b₀_mem_B) (zpowers_le.2 D.b₁_mem_B)
  constructor
  · intro hx
    obtain ⟨u, hu, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer
      (le_normalizer_of_comm fun x hx y hy => D.A_comm_B x hx y (hBle hy))).1 hx
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := (mem_sup_iff_of_le_normalizer
      (le_normalizer_of_comm fun x hx y hy => D.B₀_comm_B₁ x (zpowers_le.2 D.b₀_mem hx) y
        (zpowers_le.2 D.b₁_mem hy))).1 hw
    refine ⟨u, hu, ?_⟩
    rcases (mem_zpowers_of_mul_self D.b₀_mul_b₀).1 hw₀ with rfl | rfl <;>
      rcases (mem_zpowers_of_mul_self D.b₁_mul_b₁).1 hw₁ with rfl | rfl
    · left; group
    · right; right; left; group
    · right; left; group
    · right; right; right; rfl
  · rintro ⟨u, hu, rfl | rfl | rfl | rfl⟩
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_sup_left (mem_zpowers _)))
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_sup_right (mem_zpowers _)))
    · exact mul_mem (mem_sup_left hu) (mem_sup_right
        (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))))

theorem eq_A_or_eq_Astar {A₀ : Subgroup G} (hle : A₀ ≤ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁))
    (hcard : Nat.card A₀ = 4) (hb : A₀ ⊓ (zpowers D.b₀ ⊔ zpowers D.b₁) = ⊥)
    (hs : ∀ x ∈ A₀, D.s * x * D.s⁻¹ ∈ A₀) (ht : ∀ x ∈ A₀, D.t * x * D.t⁻¹ ∈ A₀) :
    A₀ = D.A ∨ A₀ = D.Astar := by
  classical
  haveI : Finite A₀ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hbZ : D.b ∈ zpowers D.b₀ ⊔ zpowers D.b₁ :=
    mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  have hbA₀ : D.b ∉ A₀ := fun h => D.b_ne_one (by
    have : D.b ∈ A₀ ⊓ (zpowers D.b₀ ⊔ zpowers D.b₁) := mem_inf.2 ⟨h, hbZ⟩
    rwa [hb, mem_bot] at this)
  have hsu : ∀ {u : G}, u ∈ D.A → D.s * u * D.s⁻¹ = u := fun hu => by
    rw [← D.A_comm_B _ hu _ D.s_mem_B, mul_inv_cancel_right]
  have htb : D.t * D.b * D.t⁻¹ = D.b := by rw [D.b_comm_T D.t_mem_T, mul_inv_cancel_right]
  have hform : ∀ x ∈ A₀, ∃ u ∈ D.A, x = u ∨ x = u * D.b := by
    intro x hx
    obtain ⟨u, hu, h⟩ := (mem_Z_iff D).1 (hle hx)
    refine ⟨u, hu, ?_⟩
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have h1 := mul_mem (inv_mem hx) (hs _ hx)
      have e : (u * D.b₀)⁻¹ * (D.s * (u * D.b₀) * D.s⁻¹) = D.b := by
        calc (u * D.b₀)⁻¹ * (D.s * (u * D.b₀) * D.s⁻¹)
            = D.b₀⁻¹ * u⁻¹ * ((D.s * u * D.s⁻¹) * (D.s * D.b₀ * D.s⁻¹)) := by group
          _ = D.b₀ * D.b₁ := by
            rw [hsu hu, D.conj_s_b₀, inv_eq_of_mul_eq_one_right D.b₀_mul_b₀]; group
      exact hbA₀ (e ▸ h1)
    · exfalso
      have h1 := mul_mem (inv_mem hx) (hs _ hx)
      have e : (u * D.b₁)⁻¹ * (D.s * (u * D.b₁) * D.s⁻¹) = D.b := by
        calc (u * D.b₁)⁻¹ * (D.s * (u * D.b₁) * D.s⁻¹)
            = D.b₁⁻¹ * u⁻¹ * ((D.s * u * D.s⁻¹) * (D.s * D.b₁ * D.s⁻¹)) := by group
          _ = D.b₁ * D.b₀ := by
            rw [hsu hu, D.conj_s_b₁, inv_eq_of_mul_eq_one_right D.b₁_mul_b₁]; group
          _ = D.b := (D.B₀_comm_B₁ _ D.b₀_mem _ D.b₁_mem).symm
      exact hbA₀ (e ▸ h1)
    · exact Or.inr rfl
  have hconj_a : ∀ {u y : G}, u ∈ D.A → u ≠ 1 → u ≠ D.a → (y = u ∨ y = u * D.b) →
      y⁻¹ * (D.t * y * D.t⁻¹) = D.a := by
    intro u y hu hu1 hua hy
    have htu := conj_t_of_mem_A D hu hu1 hua
    have hau : u⁻¹ * (D.a * u) = D.a := by
      rw [D.A_comm_of_two D.a_mem hu, inv_mul_cancel_left]
    rcases hy with rfl | rfl
    · rw [htu, hau]
    · calc (u * D.b)⁻¹ * (D.t * (u * D.b) * D.t⁻¹)
          = D.b⁻¹ * (u⁻¹ * (D.t * u * D.t⁻¹)) * (D.t * D.b * D.t⁻¹) := by group
        _ = D.b⁻¹ * D.a * D.b := by rw [htu, hau, htb]
        _ = D.a := by rw [mul_assoc, D.A_comm_B _ D.a_mem _ D.b_mem_B, inv_mul_cancel_left]
  have haA₀ : D.a ∈ A₀ := by
    by_contra haA₀
    have hsub : (A₀ : Set G) ⊆ {1, D.a * D.b} := by
      intro x hx
      obtain ⟨u, hu, hxu⟩ := hform x hx
      by_cases hu1 : u = 1
      · rcases hxu with hxu | hxu
        · exact Or.inl (hxu.trans hu1)
        · exact absurd (by rw [hxu, hu1, one_mul] at hx; exact hx) hbA₀
      by_cases hua : u = D.a
      · rcases hxu with hxu | hxu
        · exact absurd (by rw [hxu, hua] at hx; exact hx) haA₀
        · exact Or.inr (Set.mem_singleton_iff.2 (by rw [hxu, hua]))
      exfalso
      apply haA₀
      have h1 := mul_mem (inv_mem hx) (ht _ hx)
      rwa [hconj_a hu hu1 hua hxu] at h1
    have hcard' : Nat.card A₀ ≤ 2 := by
      have e : Nat.card ↥A₀ = (A₀ : Set G).ncard := Nat.card_coe_set_eq _
      rw [e]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    omega
  by_cases hA : A₀ ≤ D.A
  · left
    haveI := D.finite_A
    exact eq_of_le_of_card_ge hA (by rw [D.card_A, hcard]; norm_num)
  · right
    obtain ⟨x₁, hx₁, hx₁A⟩ := SetLike.not_le_iff_exists.1 hA
    obtain ⟨u₁, hu₁, hx₁u⟩ := hform x₁ hx₁
    have hx₁eq : x₁ = u₁ * D.b := hx₁u.resolve_left (fun h => hx₁A (h ▸ hu₁))
    have hu₁1 : u₁ ≠ 1 := fun h => hbA₀ (by rw [hx₁eq, h, one_mul] at hx₁; exact hx₁)
    have hu₁a : u₁ ≠ D.a := fun h => hbA₀ (by
      have := mul_mem (inv_mem haA₀) hx₁
      rwa [hx₁eq, h, inv_mul_cancel_left] at this)
    have hgen : ∀ {u : G}, u ∈ D.A → u ≠ 1 → u ≠ D.a → u * D.b ∈ D.Astar := fun hu hu1 hua =>
      subset_closure ⟨_, hu, orderOf_eq_prime (by rw [sq]; exact D.mul_self_of_two hu) hu1,
        hua, rfl⟩
    have hle' : A₀ ≤ D.Astar := by
      intro y hy
      obtain ⟨u, hu, hyu⟩ := hform y hy
      rcases hyu with hyu | hyu
      · by_cases hu1 : u = 1
        · rw [hyu, hu1]; exact one_mem _
        by_cases hua : u = D.a
        · rw [hyu, hua]; exact D.a_mem_Astar
        exfalso
        rw [hyu] at hy
        have hay : D.a * u ∈ A₀ := mul_mem haA₀ hy
        have hsub : ({1, D.a, u, D.a * u, x₁} : Set G) ⊆ (A₀ : Set G) := by
          intro z hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact one_mem _
          · exact haA₀
          · exact hy
          · exact hay
          · exact hx₁
        have hay1 : D.a * u ≠ 1 := fun h => hua (by
          rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right D.a_mul_a])
        have haya : D.a * u ≠ D.a := fun h => hu1 (mul_left_cancel (h.trans (mul_one _).symm))
        have hayy : D.a * u ≠ u := fun h => D.a_ne_one (mul_right_cancel (h.trans (one_mul _).symm))
        have hx₁1 : x₁ ≠ 1 := fun h => hx₁A (h ▸ one_mem _)
        have hx₁a : x₁ ≠ D.a := fun h => hx₁A (h ▸ D.a_mem)
        have hx₁u' : x₁ ≠ u := fun h => hx₁A (h ▸ hu)
        have hx₁au : x₁ ≠ D.a * u := fun h => hx₁A (h ▸ mul_mem D.a_mem hu)
        have hcard5 : ({1, D.a, u, D.a * u, x₁} : Set G).ncard = 5 := by
          rw [Set.ncard_insert_of_notMem (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨D.a_ne_one.symm, Ne.symm hu1, hay1.symm, hx₁1.symm⟩),
            Set.ncard_insert_of_notMem (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨Ne.symm hua, haya.symm, hx₁a.symm⟩),
            Set.ncard_insert_of_notMem (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨hayy.symm, hx₁u'.symm⟩),
            Set.ncard_pair hx₁au.symm]
        have e : Nat.card ↥A₀ = (A₀ : Set G).ncard := Nat.card_coe_set_eq _
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
      · have hu1 : u ≠ 1 := fun h => hbA₀ (by rw [hyu, h, one_mul] at hy; exact hy)
        have hua : u ≠ D.a := fun h => hbA₀ (by
          have := mul_mem (inv_mem haA₀) hy
          rwa [hyu, h, inv_mul_cancel_left] at this)
        rw [hyu]
        exact hgen hu hu1 hua
    have hcAs : Nat.card D.Astar = 4 := by
      rw [show Nat.card D.Astar = Nat.card D.star.A from rfl, D.star.card_A]; norm_num
    haveI : Finite D.Astar := Nat.finite_of_card_ne_zero (by rw [hcAs]; norm_num)
    exact eq_of_le_of_card_ge hle' (by rw [hcAs, hcard])

theorem exists_E64_s {W : Subgroup G} (hW : IsFourIn D.B₀ W) :
    ∃ E : Subgroup G, IsE64 T E ∧ D.s ∈ normalizer (E : Set G) := by
  have hW₁ := D.isFourIn_sConj₀ hW
  obtain ⟨hle, hsq, hcard⟩ := D.elem64_of_four (le_refl D.A) hW.1 hW₁.1
    (fun x hx => D.mul_self_of_two hx) hW.2.1 hW₁.2.1 (by rw [D.card_A]; norm_num) hW.2.2
    hW₁.2.2
  refine ⟨D.A ⊔ (W ⊔ D.sConj W), ⟨hle.trans D.T₁_le_T, isElemAbelian_two_iff.2 hsq, hcard⟩,
    mem_normalizer_of_involution D.s_mul_s fun x hx => ?_⟩
  have hle' : D.A ⊔ (W ⊔ D.sConj W) ≤
      (D.A ⊔ (W ⊔ D.sConj W)).comap (MulAut.conj D.s).toMonoidHom := by
    refine sup_le (fun u hu => ?_) (sup_le (fun w hw => ?_) (fun w hw => ?_))
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← D.A_comm_B _ hu _ D.s_mem_B, mul_inv_cancel_right]
      exact mem_sup_left hu
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_right (mem_sup_right ⟨w, hw, rfl⟩)
    · obtain ⟨v, hv, rfl⟩ := hw
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show D.s * (D.s * v * D.s⁻¹) * D.s⁻¹ = (D.s * D.s) * v * (D.s * D.s)⁻¹ by group,
        D.s_mul_s, one_mul, inv_one, mul_one]
      exact mem_sup_right (mem_sup_left hv)
  exact hle' hx

theorem exists_E64_t {W : Subgroup G} (hW : IsFourIn D.B₀ W) :
    ∃ E : Subgroup G, IsE64 T E ∧ D.t ∈ normalizer (E : Set G) := by
  have hPle := D.pairT_le hW.1
  have hPB : D.pairT W ≤ D.B := hPle.trans D.B₀B₁_le_B
  have hcA : ∀ x ∈ D.A, ∀ y ∈ D.pairT W, x * y = y * x := fun x hx y hy =>
    D.A_comm_B x hx y (hPB hy)
  have hi : D.A ⊓ D.pairT W = ⊥ := eq_bot_iff.2 ((inf_le_inf_left _ hPB).trans D.A_inf_B.le)
  have hcard : Nat.card ↥(D.A ⊔ D.pairT W) = 2 ^ 6 := by
    rw [card_sup_of_le_normalizer (le_normalizer_of_comm hcA) hi, D.card_A, D.card_pairT hW]
    norm_num
  have hsq : ∀ x ∈ D.A ⊔ D.pairT W, x * x = 1 := fun x hx =>
    mul_self_of_mem_sup (fun y hy => D.mul_self_of_two hy) (D.mul_self_pairT hW) hcA hx
  refine ⟨D.A ⊔ D.pairT W, ⟨sup_le D.A_le_T (hPB.trans D.B_le_T), isElemAbelian_two_iff.2 hsq,
    hcard⟩, mem_normalizer_of_involution D.t_mul_t fun x hx => ?_⟩
  have hle' : D.A ⊔ D.pairT W ≤ (D.A ⊔ D.pairT W).comap (MulAut.conj D.t).toMonoidHom := by
    refine sup_le (fun u hu => ?_) (fun w hw => ?_)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left (D.conj_t_A u hu)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_right ((mem_normalizer_iff.1 (D.t_mem_normalizer_pairT W) w).1 hw)
  exact hle' hx

end CFSG.CGT.Foote81L6.Normalizer
