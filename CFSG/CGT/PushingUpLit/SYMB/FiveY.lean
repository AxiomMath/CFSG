module

public import CFSG.CGT.PushingUpLit.SYMB.ProdCard
public import CFSG.CGT.PushingUpLit.SYMB.SymMaxSwap

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}

theorem exists_points (S : SymSetting G T V 5 φ ψ T') :
    ∃ a b c d : Fin 5, a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      T' = {Equiv.swap a b, Equiv.swap c d} := by
  classical
  have hcard : T'.ncard = 2 := symSetting_ncard (m := 2) (le_refl 2) S
  obtain ⟨x, y, hxy, hT⟩ := Set.ncard_eq_two.1 hcard
  have hx : x ∈ T' := hT ▸ Set.mem_insert _ _
  have hy : y ∈ T' := hT ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨a, b, hab, rfl⟩ := S.swaps x hx
  obtain ⟨c, d, hcd, rfl⟩ := S.swaps y hy
  have hd := disjoint_support_of_commute (S.swaps _ hx) (S.swaps _ hy) (S.comm _ hx _ hy) hxy
  rw [Equiv.Perm.support_swap hab, Equiv.Perm.support_swap hcd] at hd
  have hac : a ≠ c := fun h =>
    (Finset.disjoint_left.1 hd (show a ∈ ({a, b} : Finset (Fin 5)) by simp)) (by simp [h])
  have had : a ≠ d := fun h =>
    (Finset.disjoint_left.1 hd (show a ∈ ({a, b} : Finset (Fin 5)) by simp)) (by simp [h])
  have hbc : b ≠ c := fun h =>
    (Finset.disjoint_left.1 hd (show b ∈ ({a, b} : Finset (Fin 5)) by simp)) (by simp [h])
  have hbd : b ≠ d := fun h =>
    (Finset.disjoint_left.1 hd (show b ∈ ({a, b} : Finset (Fin 5)) by simp)) (by simp [h])
  exact ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd, hT⟩

section Pair

variable {M : Type*} [Group M] {u v : M}

theorem zpow_of_mul_self {w : M} (hw : w * w = 1) (i : ℤ) : w ^ i = 1 ∨ w ^ i = w := by
  have h2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
  rcases Int.even_or_odd' i with ⟨k, hk | hk⟩
  · left
    rw [hk, zpow_mul, h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, zpow_one, h2, one_zpow, one_mul]

theorem mem_zpowers_sup_pair (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) {x : M} :
    x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
  constructor
  · intro hx
    have hn : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v : Set M) := by
      refine le_normalizer_of_commute fun c hc d hd => ?_
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact ((Commute.zpow_zpow (show Commute u v from huv) i j).eq)
    have hx' : x ∈ ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup M) : Set M) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rcases zpow_of_mul_self hu i with h1 | h1 <;> rcases zpow_of_mul_self hv j with h2 | h2 <;>
      simp [h1, h2]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem closure_pair_eq_sup (u v : M) :
    Subgroup.closure ({u, v} : Set M) = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  rfl

theorem subgroup_of_pair (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) {P : Subgroup M}
    (hP : P ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    P = ⊥ ∨ P = Subgroup.zpowers u ∨ P = Subgroup.zpowers v ∨ P = Subgroup.zpowers (u * v) ∨
      P = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  have hmem := fun {x : M} (hx : x ∈ P) => (mem_zpowers_sup_pair hu hv huv).1 (hP hx)
  by_cases h1 : u ∈ P <;> by_cases h2 : v ∈ P
  · exact Or.inr (Or.inr (Or.inr (Or.inr (le_antisymm hP
      (sup_le (Subgroup.zpowers_le.2 h1) (Subgroup.zpowers_le.2 h2))))))
  · have h3 : u * v ∉ P := fun h => h2 (by
      have := P.mul_mem (P.inv_mem h1) h
      rwa [inv_mul_cancel_left] at this)
    refine Or.inr (Or.inl (le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 h1)))
    rcases hmem hx with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers u
    · exact absurd (h ▸ hx) h2
    · exact absurd (h ▸ hx) h3
  · have h3 : u * v ∉ P := fun h => h1 (by
      have := P.mul_mem h (P.inv_mem h2)
      rwa [mul_inv_cancel_right] at this)
    refine Or.inr (Or.inr (Or.inl (le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 h2))))
    rcases hmem hx with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hx) h1
    · rw [h]; exact Subgroup.mem_zpowers v
    · exact absurd (h ▸ hx) h3
  · by_cases h3 : u * v ∈ P
    · refine Or.inr (Or.inr (Or.inr (Or.inl (le_antisymm (fun x hx => ?_)
        (Subgroup.zpowers_le.2 h3)))))
      rcases hmem hx with h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · exact absurd (h ▸ hx) h1
      · exact absurd (h ▸ hx) h2
      · rw [h]; exact Subgroup.mem_zpowers _
    · refine Or.inl (le_antisymm (fun x hx => ?_) bot_le)
      rcases hmem hx with h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · exact absurd (h ▸ hx) h1
      · exact absurd (h ▸ hx) h2
      · exact absurd (h ▸ hx) h3

theorem card_zpowers_invol (hu : u * u = 1) (hu1 : u ≠ 1) :
    Nat.card ↥(Subgroup.zpowers u) = 2 := by
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hu) hu1

theorem zpowers_inf_zpowers (hu : u * u = 1) (hv : v * v = 1) (hne : u ≠ v) (hu1 : u ≠ 1) :
    Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := Subgroup.mem_inf.1 hx
  simp only at hi hj
  rw [Subgroup.mem_bot]
  rcases zpow_of_mul_self hu i with h | h
  · rw [← hi, h]
  · exfalso
    rw [h] at hi
    rcases zpow_of_mul_self hv j with h' | h'
    · rw [h'] at hj
      exact hu1 (hi.trans hj.symm)
    · rw [h'] at hj
      exact hne (hi.trans hj.symm)

theorem card_pair (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) (hne : u ≠ v)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) = 4 := by
  have h := card_sup_mul_card_inf_of_commute (C := Subgroup.zpowers u) (D := Subgroup.zpowers v)
    (fun c hc d hd => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact (Commute.zpow_zpow (show Commute u v from huv) i j).eq)
  rw [zpowers_inf_zpowers hu hv hne hu1, card_zpowers_invol hu hu1, card_zpowers_invol hv hv1] at h
  have h1 : Nat.card ↥(⊥ : Subgroup M) = 1 := Subgroup.card_bot
  rw [h1] at h
  omega

theorem sup_zpowers_cases {P : Subgroup M} {τ σ : M} (hτ : τ * τ = 1)
    (hc : ∀ p ∈ P, p * τ = τ * p) (hσ : σ ∈ P ⊔ Subgroup.zpowers τ) : σ ∈ P ∨ σ * τ ∈ P := by
  have hn : Subgroup.zpowers τ ≤ Subgroup.normalizer (P : Set M) :=
    le_normalizer_of_commute (C := Subgroup.zpowers τ) (D := P) fun c hc' d hd => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      rcases zpow_of_mul_self hτ j with h | h
      · rw [h, one_mul, mul_one]
      · rw [h]; exact (hc d hd).symm
  have hx' : σ ∈ ((Subgroup.zpowers τ ⊔ P : Subgroup M) : Set M) := by
    rw [sup_comm]; exact hσ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hx'
  obtain ⟨a, ha, p, hp, rfl⟩ := hx'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rcases zpow_of_mul_self hτ j with h | h
  · left
    simp only [h, one_mul]
    exact hp
  · right
    simp only [h]
    have e : τ * p * τ = p := by
      calc τ * p * τ = τ * (p * τ) := by rw [mul_assoc]
        _ = τ * (τ * p) := by rw [hc p hp]
        _ = (τ * τ) * p := by rw [mul_assoc]
        _ = p := by rw [hτ, one_mul]
    rw [e]
    exact hp

end Pair

end CFSG.CGT.PushingUpLit.SYMB
