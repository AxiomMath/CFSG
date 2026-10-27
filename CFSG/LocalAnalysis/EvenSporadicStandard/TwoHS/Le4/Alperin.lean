module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

section Computation

variable {G : Type*} [Group G]

theorem alperin_rel {p q r β : G} (hpq : p * q = q * p) (hq : β⁻¹ * p * β = q)
    (hr : β⁻¹ * q * β = r) (hc : (p⁻¹ * q) * β = β * (p⁻¹ * q)) : r = p⁻¹ * (q * q) := by
  have h1 : β⁻¹ * (p⁻¹ * q) * β = p⁻¹ * q := by
    calc β⁻¹ * (p⁻¹ * q) * β = β⁻¹ * ((p⁻¹ * q) * β) := by group
      _ = β⁻¹ * (β * (p⁻¹ * q)) := by rw [hc]
      _ = p⁻¹ * q := by group
  have h2 : β⁻¹ * (p⁻¹ * q) * β = q⁻¹ * r := by
    have : β⁻¹ * (p⁻¹ * q) * β = (β⁻¹ * p * β)⁻¹ * (β⁻¹ * q * β) := by group
    rw [this, hq, hr]
  rw [h2] at h1
  have h3 : r = q * (p⁻¹ * q) := by
    calc r = q * (q⁻¹ * r) := by group
      _ = q * (p⁻¹ * q) := by rw [h1]
  rw [h3]
  have hqp : q * p⁻¹ = p⁻¹ * q := by
    calc q * p⁻¹ = p⁻¹ * (p * q) * p⁻¹ := by group
      _ = p⁻¹ * (q * p) * p⁻¹ := by rw [hpq]
      _ = p⁻¹ * q := by group
  calc q * (p⁻¹ * q) = (q * p⁻¹) * q := by group
    _ = (p⁻¹ * q) * q := by rw [hqp]
    _ = p⁻¹ * (q * q) := by rw [mul_assoc]

theorem alperin_commute {α β : G} (hα : orderOf α = 4)
    (hpq : α * (β⁻¹ * α * β) = (β⁻¹ * α * β) * α)
    (hYβ : β * (α⁻¹ * β * α) = (α⁻¹ * β * α) * β)
    (h4b : β * β * (α * α) = α * α * (β * β) →
      β * β * α * (β * β)⁻¹ = α ∨ β * β * α * (β * β)⁻¹ = α⁻¹)
    (h4a : β * (α * α) = α * α * β → β * α * β⁻¹ = α ∨ β * α * β⁻¹ = α⁻¹)
    (h4c : α * (β * β) = β * β * α → α * β * α⁻¹ = β ∨ α * β * α⁻¹ = β⁻¹)
    (h3 : α * α = β * β → β = α ∨ β = α⁻¹) : α * β = β * α := by
  have hα4 : α * α * (α * α) = 1 := by
    have := pow_orderOf_eq_one α
    rw [hα] at this
    calc α * α * (α * α) = α ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := this
  have hα2 : α * α ≠ 1 := fun h => by
    have h2 : α ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hα] at this
    omega
  set q : G := β⁻¹ * α * β with hqdef
  set r : G := β⁻¹ * q * β with hrdef
  have hαq : α⁻¹ * q = q * α⁻¹ := by
    calc α⁻¹ * q = α⁻¹ * (q * α) * α⁻¹ := by group
      _ = α⁻¹ * (α * q) * α⁻¹ := by rw [← hpq]
      _ = q * α⁻¹ := by group
  have hc : (α⁻¹ * q) * β = β * (α⁻¹ * q) := by
    have h1 : β * (α⁻¹ * β * α)⁻¹ = (α⁻¹ * β * α)⁻¹ * β :=
      (Commute.inv_right (a := β) (b := α⁻¹ * β * α) hYβ).eq
    calc (α⁻¹ * q) * β = (α⁻¹ * β * α)⁻¹ * β * β := by rw [hqdef]; group
      _ = β * (α⁻¹ * β * α)⁻¹ * β := by rw [h1]
      _ = β * (α⁻¹ * q) := by rw [hqdef]; group
  have hr : r = α⁻¹ * (q * q) := alperin_rel hpq rfl rfl hc
  have hq4 : q * q * (q * q) = 1 := by
    calc q * q * (q * q) = β⁻¹ * (α * α * (α * α)) * β := by rw [hqdef]; group
      _ = 1 := by rw [hα4]; group
  have hα22 : α⁻¹ * α⁻¹ = α * α := by
    have h1 : (α * α)⁻¹ = α * α := inv_eq_of_mul_eq_one_right hα4
    rw [← h1]; group
  have hqqα : q * q * α⁻¹ = α⁻¹ * (q * q) := by
    calc q * q * α⁻¹ = q * (q * α⁻¹) := by group
      _ = q * (α⁻¹ * q) := by rw [hαq]
      _ = (q * α⁻¹) * q := by group
      _ = (α⁻¹ * q) * q := by rw [hαq]
      _ = α⁻¹ * (q * q) := by group
  have hr2 : r * r = α * α := by
    rw [hr]
    calc α⁻¹ * (q * q) * (α⁻¹ * (q * q)) = α⁻¹ * ((q * q) * α⁻¹) * (q * q) := by group
      _ = α⁻¹ * (α⁻¹ * (q * q)) * (q * q) := by rw [hqqα]
      _ = α⁻¹ * α⁻¹ * (q * q * (q * q)) := by group
      _ = α * α := by rw [hq4, mul_one, hα22]
  have hrx : r = (β * β)⁻¹ * α * (β * β) := by rw [hrdef, hqdef]; group
  have hcomm2 : (β * β) * (α * α) = (α * α) * (β * β) := by
    have h1 : (β * β)⁻¹ * (α * α) * (β * β) = α * α := by
      have : (β * β)⁻¹ * α * (β * β) * ((β * β)⁻¹ * α * (β * β)) =
          (β * β)⁻¹ * (α * α) * (β * β) := by group
      rw [← hrx, hr2] at this
      exact this.symm
    calc (β * β) * (α * α) = (β * β) * ((β * β)⁻¹ * (α * α) * (β * β)) := by rw [h1]
      _ = (α * α) * (β * β) := by group
  have hq2' : q * q = β⁻¹ * (α * α) * β := by rw [hqdef]; group
  rcases h4b hcomm2 with hA | hA
  · have hαβ2 : α * (β * β) = (β * β) * α := by
      calc α * (β * β) = (β * β) * α * (β * β)⁻¹ * (β * β) := by rw [hA]
        _ = (β * β) * α := by group
    have hrα : r = α := by
      rw [hrx]
      calc (β * β)⁻¹ * α * (β * β) = (β * β)⁻¹ * (α * (β * β)) := by group
        _ = (β * β)⁻¹ * ((β * β) * α) := by rw [hαβ2]
        _ = α := by group
    have hqα : q * q = α * α := by
      calc q * q = α * (α⁻¹ * (q * q)) := by group
        _ = α * r := by rw [← hr]
        _ = α * α := by rw [hrα]
    have hβα2 : β * (α * α) = (α * α) * β := by
      have h1 : β⁻¹ * (α * α) * β = α * α := by rw [← hq2']; exact hqα
      calc β * (α * α) = β * (β⁻¹ * (α * α) * β) := by rw [h1]
        _ = (α * α) * β := by group
    rcases h4a hβα2 with h1 | h1
    · have : β * α = α * β := by
        calc β * α = β * α * β⁻¹ * β := by group
          _ = α * β := by rw [h1]
      exact this.symm
    rcases h4c hαβ2 with h2 | h2
    · have : α * β = β * α := by
        calc α * β = α * β * α⁻¹ * α := by group
          _ = β * α := by rw [h2]
      exact this
    · have e1 : β * α = α⁻¹ * β := by
        calc β * α = (β * α * β⁻¹) * β := by group
          _ = α⁻¹ * β := by rw [h1]
      have e2 : α * β = β⁻¹ * α := by
        calc α * β = (α * β * α⁻¹) * α := by group
          _ = β⁻¹ * α := by rw [h2]
      have e3 : α * β * α = β := by
        calc α * β * α = α * (β * α) := by group
          _ = β := by rw [e1]; group
      have e4 : β = β⁻¹ * α * α := by
        calc β = α * β * α := e3.symm
          _ = β⁻¹ * α * α := by rw [e2]
      have e5 : β * β = α * α := by
        calc β * β = β * (β⁻¹ * α * α) := by rw [← e4]
          _ = α * α := by group
      rcases h3 e5.symm with h | h
      · rw [h]
      · rw [h]; group
  · exfalso
    have h5 : (β * β) * α⁻¹ * (β * β)⁻¹ = α := by
      calc (β * β) * α⁻¹ * (β * β)⁻¹ = ((β * β) * α * (β * β)⁻¹)⁻¹ := by simp [mul_assoc]
        _ = (α⁻¹)⁻¹ := by rw [hA]
        _ = α := inv_inv α
    have e : (β * β)⁻¹ * α * (β * β) = α⁻¹ := by
      calc (β * β)⁻¹ * α * (β * β) = (β * β)⁻¹ * ((β * β) * α⁻¹ * (β * β)⁻¹) * (β * β) := by
            rw [h5]
        _ = α⁻¹ := by group
    have hq2 : q * q = 1 := by
      have : α⁻¹ * (q * q) = α⁻¹ * 1 := by rw [← hr, hrx, e, mul_one]
      exact mul_left_cancel this
    apply hα2
    calc α * α = β * (β⁻¹ * (α * α) * β) * β⁻¹ := by group
      _ = 1 := by rw [← hq2', hq2]; group

end Computation

section Cyclic

variable {G : Type*} [Group G] [Finite G]

theorem mem_zpowers_of_mem_closure_conj {T : Subgroup G} [Group.IsNilpotent T] {l : G} (hl : l ∈ T)
    (h : ∀ x ∈ T, x ∈ closure {y | ∃ t ∈ T, y = t * l * t⁻¹}) : ∀ x ∈ T, x ∈ zpowers l := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hxT, hxl⟩ := hne
  have hlt : (zpowers (⟨l, hl⟩ : T)) ≠ ⊤ := by
    intro htop
    have : (⟨x, hxT⟩ : T) ∈ zpowers (⟨l, hl⟩ : T) := by rw [htop]; exact mem_top _
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 this
    apply hxl
    exact mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (zpowers (⟨l, hl⟩ : T))).resolve_left hlt
  have hMn : M.Normal := Group.normalizerCondition_of_isNilpotent.normal_of_coatom M hM
  have hlM : (⟨l, hl⟩ : T) ∈ M := hle (mem_zpowers _)
  have hsub : ∀ x ∈ T, x ∈ M.map T.subtype := by
    intro x hx
    refine (closure_le (M.map T.subtype)).2 ?_ (h x hx)
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩ * ⟨l, hl⟩ * ⟨t, ht⟩⁻¹, hMn.conj_mem _ hlM _, ?_⟩
    simp
  apply hM.1
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := hsub y.1 y.2
  have : z = y := Subtype.ext hzy
  rwa [this] at hz

end Cyclic

section Induction

variable {G : Type*} [Group G] [Finite G]

theorem alperin_aux : ∀ (n : ℕ) (T : Subgroup G) (Λ : Set G), Nat.card T = n → IsPGroup 2 T →
    (∀ l ∈ Λ, l ∈ T ∧ orderOf l = 4) → (∀ l ∈ Λ, ∀ t ∈ T, t * l * t⁻¹ ∈ Λ) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, l * l = m * m → m = l ∨ m = l⁻¹) →
    (∀ l ∈ Λ, ∀ x ∈ T, x * (l * l) = (l * l) * x → x * l * x⁻¹ = l ∨ x * l * x⁻¹ = l⁻¹) →
    ∀ l ∈ Λ, ∀ m ∈ Λ, l * m = m * l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T Λ hn hT hΛT hΛinv hH3 hH4
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : ∀ l ∈ Λ, ∀ x ∈ closure {y | ∃ t ∈ T, y = t * l * t⁻¹},
      ∀ y ∈ closure {y | ∃ t ∈ T, y = t * l * t⁻¹}, x * y = y * x := by
    intro l hl
    set S : Set G := {y | ∃ t ∈ T, y = t * l * t⁻¹} with hS
    have hlT : l ∈ T := (hΛT l hl).1
    have hST : S ⊆ T := by
      rintro _ ⟨t, ht, rfl⟩
      exact T.mul_mem (T.mul_mem ht hlT) (T.inv_mem ht)
    have hXT : closure S ≤ T := (closure_le T).2 hST
    by_cases hXeq : closure S = T
    · have : Group.IsNilpotent T := hT.isNilpotent
      have hmem := mem_zpowers_of_mem_closure_conj hlT (fun x hx => by rw [← hS, hXeq]; exact hx)
      intro x hx y hy
      rw [hXeq] at hx hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (hmem x hx)
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (hmem y hy)
      exact (Commute.zpow_zpow_self l i j).eq
    · have hlt : closure S < T := lt_of_le_of_ne hXT hXeq
      have hcard : Nat.card (closure S) < n := hn ▸ Subgroup.card_lt_of_lt hlt
      have hSΛ : ∀ y ∈ S, y ∈ Λ ∧ y ∈ closure S := by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨hΛinv l hl t ht, subset_closure ⟨t, ht, rfl⟩⟩
      have hcomm := ih (Nat.card (closure S)) hcard (closure S) {y | y ∈ Λ ∧ y ∈ closure S} rfl
        (hT.to_le hXT)
        (fun m hm => ⟨hm.2, (hΛT m hm.1).2⟩)
        (fun m hm t ht => ⟨hΛinv m hm.1 t (hXT ht),
          (closure S).mul_mem ((closure S).mul_mem ht hm.2) ((closure S).inv_mem ht)⟩)
        (fun m hm m' hm' h => hH3 m hm.1 m' hm'.1 h)
        (fun m hm x hx h => hH4 m hm.1 x (hXT hx) h)
      have hSc : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := fun s hs s' hs' =>
        hcomm s (hSΛ s hs) s' (hSΛ s' hs')
      have h1 : ∀ s ∈ S, ∀ x ∈ closure S, x * s = s * x := by
        intro s hs x hx
        have : closure S ≤ centralizer {s} := (closure_le _).2 fun s' hs' =>
          mem_centralizer_singleton_iff.2 (hSc s' hs' s hs)
        exact mem_centralizer_singleton_iff.1 (this hx)
      intro x hx y hy
      have : closure S ≤ centralizer {x} := (closure_le _).2 fun s hs =>
        mem_centralizer_singleton_iff.2 (h1 s hs x hx).symm
      exact (mem_centralizer_singleton_iff.1 (this hy)).symm
  intro l hl m hm
  obtain ⟨hlT, hl4⟩ := hΛT l hl
  obtain ⟨hmT, hm4⟩ := hΛT m hm
  have hpq : l * (m⁻¹ * l * m) = (m⁻¹ * l * m) * l :=
    hX l hl l (subset_closure ⟨1, T.one_mem, by simp⟩) (m⁻¹ * l * m)
      (subset_closure ⟨m⁻¹, T.inv_mem hmT, by simp⟩)
  have hYβ : m * (l⁻¹ * m * l) = (l⁻¹ * m * l) * m :=
    hX m hm m (subset_closure ⟨1, T.one_mem, by simp⟩) (l⁻¹ * m * l)
      (subset_closure ⟨l⁻¹, T.inv_mem hlT, by simp⟩)
  exact alperin_commute hl4 hpq hYβ (hH4 l hl (m * m) (T.mul_mem hmT hmT)) (hH4 l hl m hmT)
    (hH4 m hm l hlT) (hH3 l hl m hm)

end Induction

section Paper

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four {l g : G} (hl : orderOf l = 4)
    (hg : g ∈ zpowers l) (hg4 : orderOf g = 4) : g = l ∨ g = l⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
  have hl4 : l ^ 4 = 1 := by simpa [hl] using pow_orderOf_eq_one l
  have hmod : l ^ (i % (4 : ℤ)) = l ^ i := by simpa [hl] using zpow_mod_orderOf l i
  rw [← hmod] at hg4 ⊢
  have hj : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hj with h | h | h | h
  · rw [h] at hg4
    simp at hg4
  · left
    rw [h]; simp
  · exfalso
    rw [h] at hg4
    have h2 : (l ^ (2 : ℤ)) ^ 2 = 1 := by
      simp only [zpow_ofNat]
      rw [← pow_mul]; exact hl4
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hg4] at this
    omega
  · right
    rw [h]
    have : l ^ (3 : ℤ) * l = 1 := by
      simp only [zpow_ofNat]
      rw [← pow_succ]; exact hl4
    exact eq_inv_of_mul_eq_one_left this

end Paper

end CFSG.EvenSporadicStandard.TwoHS
