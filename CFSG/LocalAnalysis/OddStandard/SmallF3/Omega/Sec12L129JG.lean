module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

theorem sec12J_card_inf_mul_relIndex {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (K ⊓ H : Subgroup G) * H.relIndex K = Nat.card K := by
  have h1 : Nat.card (H.subgroupOf K) = Nat.card (K ⊓ H : Subgroup G) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [← h1]
  exact Subgroup.card_mul_index (H.subgroupOf K)

theorem sec12J_card_inf_ker_mul {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) :
    Nat.card (K ⊓ f.ker : Subgroup G) * Nat.card (K.map f) = Nat.card K := by
  rw [← Subgroup.relIndex_ker K f]
  exact sec12J_card_inf_mul_relIndex f.ker K

theorem sec12J_card_subtype_le {α : Type*} [Finite α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    Nat.card {a // P a} ≤ Nat.card {a // Q a} :=
  Nat.card_le_card_of_injective (fun a => ⟨a.1, h a.1 a.2⟩)
    (fun _ _ hab => Subtype.ext (congrArg (fun z : {a // Q a} => z.1) hab))

theorem sec12J_card_two_pow {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsElemAbelian 2 P) : ∃ n : ℕ, Nat.card P = 2 ^ n :=
  IsPGroup.iff_card.mp hP.isPGroup

theorem sec12J_relIndex_le_two {Γ : Type*} [Group Γ] [Finite Γ] (E F : Subgroup Γ) [E.Normal]
    (hE : E.index = 2 ∨ E.index = 6) (hF : IsPGroup 2 F) : E.relIndex F ≤ 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hF
  have h1 : E.relIndex F ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card E F
  have h2 : E.relIndex F ∣ E.index := Subgroup.relIndex_dvd_index_of_normal E F
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  by_contra hlt
  push Not at hlt
  have hk2 : 2 ≤ k := by
    by_contra hk'
    push Not at hk'
    interval_cases k <;> simp_all
  have h4 : 4 ∣ E.relIndex F := by
    rw [hk]
    exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
  have h5 : 4 ∣ E.index := h4.trans h2
  rcases hE with h | h <;> rw [h] at h5 <;> omega

theorem sec12J_two_pow_dvd_sixty {k : ℕ} (h : 2 ^ k ∣ 60) : k ≤ 2 := by
  by_contra hk
  push Not at hk
  have h1 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk
  have h2 : 8 ∣ 60 := by simpa using h1.trans h
  omega

theorem sec12J_two_pow_dvd {k : ℕ} (h : 2 ^ k ∣ 3600) : k ≤ 4 := by
  by_contra hk
  push Not at hk
  have h1 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 hk
  have h2 : 32 ∣ 3600 := by simpa using h1.trans h
  omega

end CFSG.OddStandard.SmallF3.Omega
