module

public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Quasithin.H13.GoldschmidtU43ModInputs
public import Certificates.Data.U43ModelWords

public section

namespace CFSG.KS.U43Mod

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.H13.U43

section Closure

variable {G : Type*} [Group G] [Finite G]

theorem closure_subset_of_left {S Y : Set G} (h1 : (1 : G) ∈ Y)
    (hY : ∀ s ∈ S, ∀ y ∈ Y, s * y ∈ Y) : (Subgroup.closure S : Set G) ⊆ Y := by
  intro x hx
  refine Subgroup.closure_induction_left (p := fun y _ => y ∈ Y) h1
    (fun s hs y _ hy => hY s hs y hy) (fun s hs y _ hy => ?_) hx
  have hpow : ∀ m : ℕ, s ^ m * y ∈ Y := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih =>
      rw [pow_succ', mul_assoc]
      exact hY s hs _ ih
  have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]
  rw [hinv]
  exact hpow _

theorem conj_subset_of_conj {S Y : Set G} {a : G} (ha : a ∈ Y)
    (hY : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) {c : G} (hc : c ∈ Subgroup.closure S) :
    c * a * c⁻¹ ∈ Y := by
  have h := closure_subset_of_left (S := S) (Y := {c | c * a * c⁻¹ ∈ Y}) (by simpa using ha)
    (fun s hs y hy => by
      have e : s * y * a * (s * y)⁻¹ = s * (y * a * y⁻¹) * s⁻¹ := by group
      change s * y * a * (s * y)⁻¹ ∈ Y
      rw [e]
      exact hY s hs _ hy) hc
  exact h

end Closure

section Words

variable {K : Type*} [Group K]

theorem evalG_cons' (g : ℕ → K) (l : ℕ × Bool) (w : List (ℕ × Bool)) :
    evalG g (l :: w) = letterVal g l * evalG g w := by
  simp [evalG]

theorem evalG_mem {g : ℕ → K} {H : Subgroup K} :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, g l.1 ∈ H) → evalG g w ∈ H
  | [], _ => by simp [evalG, H.one_mem]
  | l :: w, hw => by
    rw [evalG_cons']
    refine H.mul_mem ?_ (evalG_mem w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    unfold letterVal
    split_ifs
    · exact hw l List.mem_cons_self
    · exact H.inv_mem (hw l List.mem_cons_self)

theorem evalG_congr {g g' : ℕ → K} :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, g l.1 = g' l.1) → evalG g w = evalG g' w
  | [], _ => rfl
  | l :: w, hw => by
    rw [evalG_cons', evalG_cons', evalG_congr w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]
    unfold letterVal
    rw [hw l List.mem_cons_self]

end Words

theorem eqA_of_rep {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u g) : eqA n t u = true :=
  (eqA_iff ht hu).2 rfl

theorem any_of_get {α : Type} [Inhabited α] {L : Array α} {p : α → Bool} {i : ℕ}
    (hi : i < L.size) (h : p L[i]! = true) : L.any p = true := by
  rw [Array.any_eq_true]
  refine ⟨i, hi, ?_⟩
  rwa [getElem!_pos L i hi] at h

section Nine

variable {G : Type*} [Group G] [Finite G]

theorem nine_dvd_card {H : Subgroup G} {s t : G} (hs : s ∈ H) (ht : t ∈ H) (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) (ht3 : t ^ 3 = 1) (hst : s * t = t * s) (ht1 : t ≠ 1) (ht2 : t ≠ s)
    (ht4 : t ≠ s * s) : 9 ∣ Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hos : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hot : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  set A := Subgroup.zpowers s
  set B := Subgroup.zpowers t
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hos, pow_one])
  have hB : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hot, pow_one])
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      change s ^ k = t * s ^ k * t⁻¹
      rw [((Commute.zpow_left hst k).symm).eq, mul_inv_cancel_right]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      change s ^ k = h
      change s ^ k = t * h * t⁻¹ at hk
      have e : h = t⁻¹ * (t * h * t⁻¹) * t := by group
      rw [e, ← hk, mul_assoc, (Commute.zpow_left hst k).eq, inv_mul_cancel_left]
  have hK : IsPGroup 3 (B ⊔ A : Subgroup G) := hB.to_sup_of_normal_right' hA hBA
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hK
  have hlt : A < B ⊔ A := by
    refine lt_of_le_of_ne le_sup_right fun e => ?_
    have htA : t ∈ A := by
      rw [e]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hos] at htA
    simp only [Finset.mem_image, Finset.mem_range] at htA
    obtain ⟨k, hk, hkt⟩ := htA
    interval_cases k
    · exact ht1 (by rw [← hkt, pow_zero])
    · exact ht2 (by rw [← hkt, pow_one])
    · exact ht4 (by rw [← hkt, sq])
  have h3 : 3 < 3 ^ m := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [hm, Nat.card_zpowers, hos] at this
  have hm2 : 2 ≤ m := by
    by_contra hc
    interval_cases m <;> omega
  have hle : B ⊔ A ≤ H := sup_le ((Subgroup.zpowers_le).2 ht) ((Subgroup.zpowers_le).2 hs)
  have h9 : 9 ∣ Nat.card (B ⊔ A : Subgroup G) := by
    rw [hm]
    exact dvd_trans (by norm_num : 9 ∣ 3 ^ 2) (Nat.pow_dvd_pow 3 hm2)
  exact h9.trans (Subgroup.card_dvd_of_le hle)

end Nine

end CFSG.KS.U43Mod

end
