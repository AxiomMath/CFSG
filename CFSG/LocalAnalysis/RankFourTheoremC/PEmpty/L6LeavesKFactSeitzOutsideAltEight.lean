module

public import Mathlib.GroupTheory.Sylow
public import CFSG.GF2Type.Smith1979W3.CaseD.Jordan
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutsideDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KSeitz

open Equiv Equiv.Perm Subgroup

@[expose] def c3 (a b c : Fin 8) : Perm (Fin 8) := swap a b * swap a c

theorem c3_apply_of_ne {a b c i : Fin 8} (h1 : i ≠ a) (h2 : i ≠ b) (h3 : i ≠ c) :
    c3 a b c i = i := by
  unfold c3
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]

theorem c3_mem_alt {a b c : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c3 a b c ∈ alternatingGroup (Fin 8) :=
  (isThreeCycle_swap_mul_swap_same hab hac hbc).mem_alternatingGroup

theorem disjoint_c3 {x y z p q r : Fin 8}
    (h : ∀ i, (i = x ∨ i = y ∨ i = z) → i ≠ p ∧ i ≠ q ∧ i ≠ r) :
    (c3 x y z).Disjoint (c3 p q r) := by
  intro i
  by_cases hi : i = x ∨ i = y ∨ i = z
  · right
    obtain ⟨h1, h2, h3⟩ := h i hi
    exact c3_apply_of_ne h1 h2 h3
  · left
    push Not at hi
    exact c3_apply_of_ne hi.1 hi.2.1 hi.2.2

@[expose] def a₀ : alternatingGroup (Fin 8) :=
  ⟨c3 0 1 2, c3_mem_alt (by decide) (by decide) (by decide)⟩

@[expose] def b₀ : alternatingGroup (Fin 8) :=
  ⟨c3 3 4 5, c3_mem_alt (by decide) (by decide) (by decide)⟩

@[expose] def E₀ : Subgroup (alternatingGroup (Fin 8)) := Subgroup.closure {a₀, b₀}

theorem orderOf_a₀ : orderOf a₀ = 3 := by
  have h := (isThreeCycle_swap_mul_swap_same (a := (0 : Fin 8)) (b := 1) (c := 2) (by decide)
    (by decide) (by decide)).orderOf
  rw [← h, ← Subgroup.orderOf_coe]
  rfl

theorem orderOf_b₀ : orderOf b₀ = 3 := by
  have h := (isThreeCycle_swap_mul_swap_same (a := (3 : Fin 8)) (b := 4) (c := 5) (by decide)
    (by decide) (by decide)).orderOf
  rw [← h, ← Subgroup.orderOf_coe]
  rfl

theorem card_E₀ : Nat.card E₀ = 9 := by
  have hmap : E₀.map (alternatingGroup (Fin 8)).subtype =
      Subgroup.closure ({c3 0 1 2, c3 3 4 5} : Set (Perm (Fin 8))) := by
    rw [E₀, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hd : (c3 0 1 2).Disjoint (c3 3 4 5) := by
    refine disjoint_c3 fun i hi => ?_
    rcases hi with rfl | rfl | rfl <;> decide
  have h9 := CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles
    (isThreeCycle_swap_mul_swap_same (a := (0 : Fin 8)) (b := 1) (c := 2) (by decide)
      (by decide) (by decide))
    (isThreeCycle_swap_mul_swap_same (a := (3 : Fin 8)) (b := 4) (c := 5) (by decide)
      (by decide) (by decide)) hd
  rw [← Subgroup.card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective, hmap]
  exact h9

theorem mem_hset_E₀_of_commute_a {k : alternatingGroup (Fin 8)} (hk : a₀ * k = k * a₀) :
    k ∈ hset 3 E₀ := by
  have hle : Subgroup.zpowers a₀ ≤ E₀ :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  refine mem_hset hle ?_ ?_
  · have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers a₀) (K := E₀)
    rw [inf_eq_left.mpr hle, Nat.card_zpowers, orderOf_a₀, card_E₀] at h
    omega
  · intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (show Commute a₀ k from hk) n).eq)

theorem mem_hset_E₀_of_commute_b {k : alternatingGroup (Fin 8)} (hk : b₀ * k = k * b₀) :
    k ∈ hset 3 E₀ := by
  have hle : Subgroup.zpowers b₀ ≤ E₀ :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  refine mem_hset hle ?_ ?_
  · have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers b₀) (K := E₀)
    rw [inf_eq_left.mpr hle, Nat.card_zpowers, orderOf_b₀, card_E₀] at h
    omega
  · intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (show Commute b₀ k from hk) n).eq)

@[expose] def Hp : Subgroup (Perm (Fin 8)) :=
  (Subgroup.closure (hset 3 E₀)).map (alternatingGroup (Fin 8)).subtype

theorem c3_mem_Hp {x y z : Fin 8} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hT : (3 ≤ x.val ∧ 3 ≤ y.val ∧ 3 ≤ z.val) ∨
      ((x.val < 3 ∨ 6 ≤ x.val) ∧ (y.val < 3 ∨ 6 ≤ y.val) ∧ (z.val < 3 ∨ 6 ≤ z.val))) :
    c3 x y z ∈ Hp := by
  have hmem : c3 x y z ∈ alternatingGroup (Fin 8) := c3_mem_alt hxy hxz hyz
  refine ⟨⟨c3 x y z, hmem⟩, ?_, rfl⟩
  apply Subgroup.subset_closure
  rcases hT with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine mem_hset_E₀_of_commute_a ?_
    apply Subtype.ext
    have hd : (c3 0 1 2).Disjoint (c3 x y z) := by
      refine disjoint_c3 fun i hi => ?_
      rcases hi with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h <;>
        simp_all
    exact hd.commute.eq
  · refine mem_hset_E₀_of_commute_b ?_
    apply Subtype.ext
    have hd : (c3 3 4 5).Disjoint (c3 x y z) := by
      refine disjoint_c3 fun i hi => ?_
      rcases hi with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h <;>
        simp_all
    exact hd.commute.eq


@[expose] def bT (x : Fin 8) : Fin 8 :=
  if x.val < 3 then 6 else if x.val = 3 then 4 else 3

@[expose] def bS (x : Fin 8) : Fin 8 :=
  if x.val < 3 then (if x.val = 0 then 1 else 0) else (if x.val = 3 then 4 else 3)

theorem exists_mem_Hp_apply_seven (x : Fin 8) : ∃ g ∈ Hp, g 7 = x := by
  by_cases hx : x = 7
  · exact ⟨1, one_mem _, by simp [hx]⟩
  · have hc : ∀ x : Fin 8, x ≠ 7 → c3 7 (bT x) x 7 = x := by decide
    have hs : ∀ x : Fin 8, x ≠ 7 →
        (7 : Fin 8) ≠ bT x ∧ (7 : Fin 8) ≠ x ∧ bT x ≠ x ∧
        ((3 ≤ (7 : Fin 8).val ∧ 3 ≤ (bT x).val ∧ 3 ≤ x.val) ∨
          (((7 : Fin 8).val < 3 ∨ 6 ≤ (7 : Fin 8).val) ∧ ((bT x).val < 3 ∨ 6 ≤ (bT x).val) ∧
            (x.val < 3 ∨ 6 ≤ x.val))) := by decide
    obtain ⟨h1, h2, h3, h4⟩ := hs x hx
    exact ⟨c3 7 (bT x) x, c3_mem_Hp h1 h2 h3 h4, hc x hx⟩

theorem exists_mem_Hp_apply_eq_six (x : Fin 8) (hx : x ≠ 7) :
    ∃ g ∈ Hp, g 7 = 7 ∧ g x = 6 := by
  by_cases h6 : x = 6
  · exact ⟨1, one_mem _, by simp, by simp [h6]⟩
  · have hc : ∀ x : Fin 8, x ≠ 7 → x ≠ 6 → c3 x (bS x) 6 7 = 7 ∧ c3 x (bS x) 6 x = 6 := by
      decide
    have hs : ∀ x : Fin 8, x ≠ 7 → x ≠ 6 →
        x ≠ bS x ∧ x ≠ 6 ∧ bS x ≠ 6 ∧
        ((3 ≤ x.val ∧ 3 ≤ (bS x).val ∧ 3 ≤ (6 : Fin 8).val) ∨
          ((x.val < 3 ∨ 6 ≤ x.val) ∧ ((bS x).val < 3 ∨ 6 ≤ (bS x).val) ∧
            ((6 : Fin 8).val < 3 ∨ 6 ≤ (6 : Fin 8).val))) := by decide
    obtain ⟨h1, h2, h3, h4⟩ := hs x hx h6
    exact ⟨c3 x (bS x) 6, c3_mem_Hp h1 h2 h3 h4, (hc x hx h6).1, (hc x hx h6).2⟩

theorem isMultiplyPretransitive_Hp : MulAction.IsMultiplyPretransitive Hp (Fin 8) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  have key : ∀ a b : Fin 8, a ≠ b → ∃ h ∈ Hp, h a = 7 ∧ h b = 6 := by
    intro a b hab
    obtain ⟨g₁, hg₁, hg₁a⟩ := exists_mem_Hp_apply_seven a
    have hx : g₁⁻¹ b ≠ 7 := by
      intro h
      apply hab
      rw [← hg₁a]
      exact (Perm.inv_eq_iff_eq.mp h).symm
    obtain ⟨g₂, hg₂, hg₂7, hg₂x⟩ := exists_mem_Hp_apply_eq_six _ hx
    refine ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁), ?_, ?_⟩
    · rw [Perm.mul_apply, ← hg₁a]
      simpa using hg₂7
    · rw [Perm.mul_apply]
      exact hg₂x
  intro a b c d hab hcd
  obtain ⟨h₁, hh₁, h₁a, h₁b⟩ := key a b hab
  obtain ⟨h₂, hh₂, h₂c, h₂d⟩ := key c d hcd
  refine ⟨⟨h₂⁻¹ * h₁, mul_mem (inv_mem hh₂) hh₁⟩, ?_, ?_⟩
  · show (h₂⁻¹ * h₁) a = c
    rw [Perm.mul_apply, h₁a, ← h₂c]
    simp
  · show (h₂⁻¹ * h₁) b = d
    rw [Perm.mul_apply, h₁b, ← h₂d]
    simp

theorem alternatingGroup_le_Hp : alternatingGroup (Fin 8) ≤ Hp := by
  haveI : MulAction.IsPreprimitive Hp (Fin 8) :=
    MulAction.isPreprimitive_of_is_two_pretransitive isMultiplyPretransitive_Hp
  have h3 : (c3 3 4 5).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (a := (3 : Fin 8)) (b := 4) (c := 5) (by decide)
      (by decide) (by decide)
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem (G := Hp) inferInstance h3
    (c3_mem_Hp (by decide) (by decide) (by decide) (Or.inl (by decide)))

theorem closure_hset_E₀ : Subgroup.closure (hset 3 E₀) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : Perm (Fin 8)) ∈ Hp := alternatingGroup_le_Hp x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  exact this ▸ hy


theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem isPGroup_three_of_card_nine {E : Subgroup (alternatingGroup (Fin 8))}
    (hE : Nat.card E = 9) : IsPGroup 3 E ∧ ¬ 3 ∣ E.index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨IsPGroup.of_card (n := 2) (by rw [hE]; norm_num), ?_⟩
  have h := Subgroup.card_mul_index E
  rw [hE, card_alt_eight] at h
  have : E.index = 2240 := by omega
  rw [this]
  decide

theorem closure_hset_alt_eight {E : Subgroup (alternatingGroup (Fin 8))} (hE : Nat.card E = 9) :
    Subgroup.closure (hset 3 E) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE3, hEi⟩ := isPGroup_three_of_card_nine hE
  obtain ⟨hE03, hE0i⟩ := isPGroup_three_of_card_nine card_E₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8))
    (hE03.toSylow hE0i) (hE3.toSylow hEi)
  have hconj : E = E₀.map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • hE03.toSylow hE0i : Sylow 3 (alternatingGroup (Fin 8))) :
        Subgroup (alternatingGroup (Fin 8))) = E := by
      rw [hg, IsPGroup.toSylow_coe]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [hconj]
  exact (closure_hset_map_eq_top_iff (MulAut.conj g) 3 E₀).mpr closure_hset_E₀

end KSeitz

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
