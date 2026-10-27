module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym

open CFSG.Open Subgroup

@[expose] def IsSymThree {R : Type*} [Group R] (X : Subgroup R) : Prop :=
  Nonempty (↥X ≃* Equiv.Perm (Fin 3))

@[expose] def c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem c3_pow_three : c3 ^ 3 = 1 := by decide

theorem c3_ne_one : c3 ≠ 1 := by decide

theorem perm3_invol_inv :
    ∀ x : Equiv.Perm (Fin 3), x ^ 2 = 1 → x ≠ 1 → x * c3 * x⁻¹ = c3⁻¹ := by decide

theorem perm3_cases : ∀ x : Equiv.Perm (Fin 3), x ^ 2 = 1 → x ≠ 1 → ∀ g : Equiv.Perm (Fin 3),
    g = 1 ∨ g = c3 ∨ g = c3 ^ 2 ∨ g = x ∨ g = c3 * x ∨ g = c3 ^ 2 * x := by decide

theorem perm3_order_three :
    ∀ b : Equiv.Perm (Fin 3), b ^ 3 = 1 → b ≠ 1 → b = c3 ∨ b = c3⁻¹ := by decide

theorem perm3_exists_invol : ∃ x : Equiv.Perm (Fin 3), x ^ 2 = 1 ∧ x ≠ 1 :=
  ⟨Equiv.swap 0 1, by decide, by decide⟩

section Data

variable {R : Type*} [Group R]

theorem symThree_data {X : Subgroup R} (hX : IsSymThree X) :
    ∃ a ∈ X, a ≠ 1 ∧ a ^ 3 = 1 ∧
      (∀ s ∈ X, s ^ 2 = 1 → s ≠ 1 → s * a * s⁻¹ = a⁻¹ ∧ X = closure {a, s}) ∧
      (∃ s ∈ X, s ^ 2 = 1 ∧ s ≠ 1) ∧ (∀ b ∈ X, b ^ 3 = 1 → b ≠ 1 → b = a ∨ b = a⁻¹) := by
  obtain ⟨e⟩ := hX
  have hcoe1 : ∀ x : ↥X, (x : R) = 1 → x = 1 := fun x hx => Subtype.ext hx
  have hcoe2 : ∀ x : ↥X, x = 1 → (x : R) = 1 := fun x hx => by rw [hx]; rfl
  refine ⟨((e.symm c3 : ↥X) : R), (e.symm c3).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := hcoe1 _ h
    exact c3_ne_one (e.symm.injective (by rw [h1, map_one]))
  · have h : (e.symm c3) ^ 3 = 1 := by rw [← map_pow, c3_pow_three, map_one]
    have h' := congrArg Subtype.val h
    simpa using h'
  · intro s hs hs2 hs1
    set σ : ↥X := ⟨s, hs⟩ with hσ
    have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa [hσ] using hs2)
    have hσ1 : σ ≠ 1 := fun h => hs1 (by simpa [hσ] using congrArg Subtype.val h)
    set x : Equiv.Perm (Fin 3) := e σ with hx
    have hx2 : x ^ 2 = 1 := by rw [hx, ← map_pow, hσ2, map_one]
    have hx1 : x ≠ 1 := fun h => hσ1 (e.injective (by rw [← hx, h, map_one]))
    have hconj := perm3_invol_inv x hx2 hx1
    constructor
    · have h1 : σ * e.symm c3 * σ⁻¹ = (e.symm c3)⁻¹ := by
        apply e.injective
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
        rw [← hx]
        exact hconj
      have h1' := congrArg Subtype.val h1
      simpa [hσ] using h1'
    · apply le_antisymm
      · intro y hy
        set cl : Subgroup R := closure ({((e.symm c3 : ↥X) : R), s} : Set R) with hcl
        have ha : ((e.symm c3 : ↥X) : R) ∈ cl := subset_closure (by simp)
        have hs' : s ∈ cl := subset_closure (by simp)
        have hsymm : e.symm x = σ := by rw [hx, MulEquiv.symm_apply_apply]
        have key : ∀ g : Equiv.Perm (Fin 3),
            (g = 1 ∨ g = c3 ∨ g = c3 ^ 2 ∨ g = x ∨ g = c3 * x ∨ g = c3 ^ 2 * x) →
            ((e.symm g : ↥X) : R) ∈ cl := by
          rintro g (h | h | h | h | h | h) <;> subst h
          · simp only [map_one, OneMemClass.coe_one]
            exact one_mem _
          · exact ha
          · rw [map_pow]
            simp only [SubmonoidClass.coe_pow]
            exact pow_mem ha 2
          · rw [hsymm]
            exact hs'
          · rw [map_mul, hsymm]
            simp only [Subgroup.coe_mul]
            exact mul_mem ha hs'
          · rw [map_mul, map_pow, hsymm]
            simp only [Subgroup.coe_mul, SubmonoidClass.coe_pow]
            exact mul_mem (pow_mem ha 2) hs'
        have h := key _ (perm3_cases x hx2 hx1 (e ⟨y, hy⟩))
        rw [MulEquiv.symm_apply_apply] at h
        exact h
      · rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl
        · exact (e.symm c3).2
        · exact hs
  · obtain ⟨x, hx2, hx1⟩ := perm3_exists_invol
    refine ⟨((e.symm x : ↥X) : R), (e.symm x).2, ?_, ?_⟩
    · have h : (e.symm x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
      simpa using congrArg Subtype.val h
    · intro h
      exact hx1 (e.symm.injective (by rw [hcoe1 _ h, map_one]))
  · intro b hb hb3 hb1
    set β : ↥X := ⟨b, hb⟩ with hβ
    have hβ3 : β ^ 3 = 1 := Subtype.ext (by simpa [hβ] using hb3)
    have hβ1 : β ≠ 1 := fun h => hb1 (by simpa [hβ] using congrArg Subtype.val h)
    have hg3 : (e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
    have hg1 : e β ≠ 1 := fun h => hβ1 (e.injective (by rw [h, map_one]))
    rcases perm3_order_three _ hg3 hg1 with h | h
    · left
      have : β = e.symm c3 := by rw [← h, MulEquiv.symm_apply_apply]
      simpa [hβ] using congrArg Subtype.val this
    · right
      have : β = e.symm c3⁻¹ := by rw [← h, MulEquiv.symm_apply_apply]
      rw [map_inv] at this
      simpa [hβ] using congrArg Subtype.val this

end Data

section Closure

variable {R : Type*} [Group R]

theorem eq_of_subnormal_of_forall_normal {H K : Subgroup R} (h : IsSubnormal H K)
    (hN : ∀ N : Subgroup R, H ≤ N → N ≤ K → (N.subgroupOf K).Normal → N = K) : H = K := by
  induction h with
  | refl H => rfl
  | step hHM hnorm hMK ih =>
    rename_i H M K
    have hM : M = K := ih (fun N hMN hNK hNn => hN N (hHM.trans hMN) hNK hNn)
    subst hM
    exact hN H le_rfl hHM hnorm

theorem card_symThree {X : Subgroup R} (hX : IsSymThree X) : Nat.card X = 6 := by
  obtain ⟨e⟩ := hX
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem finite_symThree {X : Subgroup R} (hX : IsSymThree X) : Finite X :=
  Nat.finite_of_card_ne_zero (by rw [card_symThree hX]; norm_num)

theorem symThree_of_order_three {X : Subgroup R} (hX : IsSymThree X) {a : R} (ha : a ∈ X)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    (∀ s ∈ X, s ^ 2 = 1 → s ≠ 1 → s * a * s⁻¹ = a⁻¹ ∧ X = closure {a, s}) ∧
      (∃ s ∈ X, s ^ 2 = 1 ∧ s ≠ 1) := by
  obtain ⟨b, hb, hb1, hb3, hbs, hex, hord⟩ := symThree_data hX
  refine ⟨fun s hs hs2 hs1 => ?_, hex⟩
  obtain ⟨hinv, hXeq⟩ := hbs s hs hs2 hs1
  rcases hord a ha ha3 ha1 with rfl | rfl
  · exact ⟨hinv, hXeq⟩
  · refine ⟨?_, ?_⟩
    · have : s * b⁻¹ * s⁻¹ = (s * b * s⁻¹)⁻¹ := by group
      rw [this, hinv, inv_inv]
    · rw [hXeq]
      have hbm : b ∈ closure ({b⁻¹, s} : Set R) := by
        have : b⁻¹⁻¹ ∈ closure ({b⁻¹, s} : Set R) := inv_mem (subset_closure (by simp))
        simpa using this
      have hbm' : b⁻¹ ∈ closure ({b, s} : Set R) := inv_mem (subset_closure (by simp))
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro y hy
        rcases hy with h | h
        · rw [h]; exact hbm
        · rw [h]; exact subset_closure (by simp)
      · rw [Subgroup.closure_le]
        intro y hy
        rcases hy with h | h
        · rw [h]; exact hbm'
        · rw [h]; exact subset_closure (by simp)

theorem mem_of_inv_involution {X : Subgroup R} (hX : IsSymThree X) (hXs : IsSubnormal X ⊤)
    {s a' : R} (hs : s ∈ X) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (ha'3 : a' ^ 3 = 1)
    (hinv' : s * a' * s⁻¹ = a'⁻¹) : a' ∈ X := by
  obtain ⟨a, ha, ha1, ha3, hXa, -, -⟩ := symThree_data hX
  obtain ⟨hinv, hXeq⟩ := hXa s hs hs2 hs1
  set W : Subgroup R := closure ({a, a', s} : Set R) with hW
  have haW : a ∈ W := subset_closure (by simp)
  have ha'W : a' ∈ W := subset_closure (by simp)
  have hsW : s ∈ W := subset_closure (by simp)
  have hXW : X ≤ W := by
    rw [hXeq, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact haW
    · exact hsW
  have hsubW : IsSubnormal X W := by
    have h := hXs.inf_of_le (le_top : W ≤ ⊤)
    rwa [inf_eq_left.2 hXW] at h
  have hXeqW : X = W := by
    refine eq_of_subnormal_of_forall_normal hsubW fun N hXN hNW hNn => ?_
    have hconj := (Subgroup.normal_subgroupOf_iff hNW).1 hNn
    have hsN : s ∈ N := hXN hs
    have haN : a ∈ N := hXN ha
    have ha'N : a' ∈ N := by
      have h1 : a' * s * a'⁻¹ ∈ N := hconj s a' hsN ha'W
      have h2 : a' * s * a'⁻¹ * s⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem hsN)
      have h3 : a' * s * a'⁻¹ * s⁻¹ = a' ^ 2 := by
        have e2 : s * a'⁻¹ * s⁻¹ = a' := by
          have : s * a'⁻¹ * s⁻¹ = (s * a' * s⁻¹)⁻¹ := by group
          rw [this, hinv', inv_inv]
        calc a' * s * a'⁻¹ * s⁻¹ = a' * (s * a'⁻¹ * s⁻¹) := by group
          _ = a' ^ 2 := by rw [e2, pow_two]
      rw [h3] at h2
      have h4 : (a' ^ 2) ^ 2 = a' := by
        calc (a' ^ 2) ^ 2 = a' ^ 3 * a' := by group
          _ = a' := by rw [ha'3, one_mul]
      rw [← h4]
      exact pow_mem h2 2
    apply le_antisymm hNW
    have hWle : W ≤ N := by
      rw [hW, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact haN
      · exact ha'N
      · exact hsN
    exact hWle
  rw [hXeqW]
  exact ha'W

theorem eq_of_shared_involution {X X' : Subgroup R} (hX : IsSymThree X) (hX' : IsSymThree X')
    (hXs : IsSubnormal X ⊤) {s : R} (hs : s ∈ X) (hs' : s ∈ X') (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) : X = X' := by
  obtain ⟨a', ha', ha1', ha3', hXa', -, -⟩ := symThree_data hX'
  obtain ⟨hinv', hXeq'⟩ := hXa' s hs' hs2 hs1
  have ha'X : a' ∈ X := mem_of_inv_involution hX hXs hs hs2 hs1 ha3' hinv'
  have hX'X : X' ≤ X := by
    rw [hXeq', Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact ha'X
    · exact hs
  haveI := finite_symThree hX
  exact (Subgroup.eq_of_le_of_card_ge hX'X (by rw [card_symThree hX, card_symThree hX'])).symm

theorem mem_normalizer_zpowers_of_comm {v g : R} (h : g * v * g⁻¹ = v) :
    g ∈ normalizer ((zpowers v : Subgroup R) : Set R) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc : ∀ k : ℤ, g * v ^ k * g⁻¹ = v ^ k := fun k => by
    rw [← conj_zpow, h]
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [hc k]
    exact Subgroup.zpow_mem_zpowers v k
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hy' : y = v ^ k := by
      have h2 : g * v ^ k = v ^ k * g := by
        have := hc k
        rwa [mul_inv_eq_iff_eq_mul] at this
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * v ^ k * g := by rw [← hk]
        _ = g⁻¹ * (v ^ k * g) := by rw [mul_assoc]
        _ = g⁻¹ * (g * v ^ k) := by rw [h2]
        _ = v ^ k := by group
    rw [hy']
    exact Subgroup.zpow_mem_zpowers v k

theorem mem_normalizer_zpowers_of_inv {v g : R} (h : g * v * g⁻¹ = v⁻¹) :
    g ∈ normalizer ((zpowers v : Subgroup R) : Set R) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc : ∀ k : ℤ, g * v ^ k * g⁻¹ = (v ^ k)⁻¹ := fun k => by
    rw [← conj_zpow, h, inv_zpow]
  have hinv1 : g⁻¹ * v * g = v⁻¹ := by
    have h3 : (g⁻¹ * v * g)⁻¹ = v := by
      calc (g⁻¹ * v * g)⁻¹ = g⁻¹ * v⁻¹ * g := by group
        _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [h]
        _ = v := by group
    exact inv_eq_iff_eq_inv.1 h3
  have hc' : ∀ k : ℤ, g⁻¹ * v ^ k * g = (v ^ k)⁻¹ := fun k => by
    have := conj_zpow (a := g⁻¹) (b := v) (i := k)
    rw [inv_inv, hinv1, inv_zpow] at this
    exact this.symm
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [hc k]
    exact inv_mem (Subgroup.zpow_mem_zpowers v k)
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hy' : y = (v ^ k)⁻¹ := by
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * v ^ k * g := by rw [← hk]
        _ = (v ^ k)⁻¹ := hc' k
    rw [hy']
    exact inv_mem (Subgroup.zpow_mem_zpowers v k)

end Closure

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym
