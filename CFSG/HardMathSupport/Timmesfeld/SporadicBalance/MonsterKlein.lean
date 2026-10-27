module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving Subgroup

theorem card_fix_modEq_two {X : Type*} [Finite X] (f : X → X) (hf : ∀ x, f (f x) = x) :
    Nat.card X ≡ Nat.card {x : X // f x = x} [MOD 2] := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Equiv.Perm.card_fixedPoints_modEq (α := X) (f := (f : Function.End X)) (p := 2)
    (n := 1) (by
      rw [pow_one]
      funext x
      exact hf x)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

theorem ncard_modEq_two_of_involutive {G : Type*} {T : Set G} (hT : T.Finite) (f : G → G)
    (hff : ∀ x, f (f x) = x) (hmaps : ∀ x ∈ T, f x ∈ T) :
    T.ncard ≡ {x ∈ T | f x = x}.ncard [MOD 2] := by
  have := hT.to_subtype
  let g : T → T := fun x => ⟨f x, hmaps x x.2⟩
  have hg : ∀ x, g (g x) = x := fun x => Subtype.ext (hff x)
  have h := card_fix_modEq_two g hg
  have e : {x : T // g x = x} ≃ ↥{x ∈ T | f x = x} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
  exact h

variable {G : Type*} [Group G]

theorem odd_natCard_of_klein [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {S : Subgroup G} (haS : ∀ x ∈ S, a * x * a⁻¹ ∈ S)
    (hbS : ∀ x ∈ S, b * x * b⁻¹ ∈ S)
    (hfix : ∀ x ∈ S, x * x = 1 → a * x = x * a → b * x = x * b → x = 1) :
    Odd (Nat.card S) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hinv : ∀ x : G, x⁻¹ = x ↔ x * x = 1 := fun x => inv_eq_iff_mul_eq_one
  set T0 : Set G := {x ∈ (S : Set G) | x⁻¹ = x} with hT0
  set T1 : Set G := {x ∈ T0 | a * x * a⁻¹ = x} with hT1
  set T2 : Set G := {x ∈ T1 | b * x * b⁻¹ = x} with hT2
  have h0 : (S : Set G).ncard ≡ T0.ncard [MOD 2] :=
    ncard_modEq_two_of_involutive (Set.toFinite _) (fun x => x⁻¹) (fun x => inv_inv x)
      (fun x hx => S.inv_mem hx)
  have hconj : ∀ (c : G), c * c = 1 → ∀ x : G, c * (c * x * c⁻¹) * c⁻¹ = x := by
    intro c hc x
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
    calc c * (c * x * c⁻¹) * c⁻¹ = (c * c) * x * (c⁻¹ * c⁻¹) := by group
      _ = x := by rw [hc, show c⁻¹ * c⁻¹ = (c * c)⁻¹ by group, hc]; group
  have h1 : T0.ncard ≡ T1.ncard [MOD 2] := by
    refine ncard_modEq_two_of_involutive (Set.toFinite _) (fun x => a * x * a⁻¹) (hconj a ha) ?_
    rintro x ⟨hxS, hx⟩
    refine ⟨haS x hxS, ?_⟩
    have : (a * x * a⁻¹)⁻¹ = a * x⁻¹ * a⁻¹ := by group
    rw [this, hx]
  have h2 : T1.ncard ≡ T2.ncard [MOD 2] := by
    refine ncard_modEq_two_of_involutive (Set.toFinite _) (fun x => b * x * b⁻¹) (hconj b hb) ?_
    rintro x ⟨⟨hxS, hx⟩, hxa⟩
    refine ⟨⟨hbS x hxS, ?_⟩, ?_⟩
    · have : (b * x * b⁻¹)⁻¹ = b * x⁻¹ * b⁻¹ := by group
      rw [this, hx]
    · have e : a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
        calc a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (b⁻¹ * a⁻¹) := by group
          _ = (b * a) * x * (a⁻¹ * b⁻¹) := by
            rw [hab, show b⁻¹ * a⁻¹ = (a * b)⁻¹ by group, hab]
            group
          _ = b * (a * x * a⁻¹) * b⁻¹ := by group
      show a * (b * x * b⁻¹) * a⁻¹ = b * x * b⁻¹
      rw [e, hxa]
  have hT2 : T2 = {1} := by
    ext x
    simp only [hT2, hT1, hT0, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨⟨hxS, hx⟩, hxa⟩, hxb⟩
      refine hfix x hxS ((hinv x).1 hx) ?_ ?_
      · calc a * x = (a * x * a⁻¹) * a := by group
          _ = x * a := by rw [hxa]
      · calc b * x = (b * x * b⁻¹) * b := by group
          _ = x * b := by rw [hxb]
    · rintro rfl
      refine ⟨⟨⟨S.one_mem, inv_one⟩, ?_⟩, ?_⟩ <;> group
  have h3 : (S : Set G).ncard ≡ 1 [MOD 2] := by
    refine ((h0.trans h1).trans h2).trans ?_
    rw [hT2, Set.ncard_singleton]
  have hc : Nat.card S = (S : Set G).ncard := Nat.card_coe_set_eq (S : Set G)
  rw [hc, Nat.odd_iff]
  exact h3

theorem eq_one_of_klein_fixedPointFree [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    {Q : Subgroup G} (haQ : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q)
    (hbQ : ∀ x ∈ Q, b * x * b⁻¹ ∈ Q) (hfa : ∀ x ∈ Q, a * x * a⁻¹ = x → x = 1)
    (hfb : ∀ x ∈ Q, b * x * b⁻¹ = x → x = 1)
    (hfab : ∀ x ∈ Q, (a * b) * x * (a * b)⁻¹ = x → x = 1) : ∀ x ∈ Q, x = 1 := by
  intro q hq
  have h1 := inv_of_fixedPointFree_involution ha haQ hfa q hq
  have h2 := inv_of_fixedPointFree_involution hb hbQ hfb q hq
  refine hfab q hq ?_
  calc (a * b) * q * (a * b)⁻¹ = a * (b * q * b⁻¹) * a⁻¹ := by group
    _ = a * q⁻¹ * a⁻¹ := by rw [h2]
    _ = (a * q * a⁻¹)⁻¹ := by group
    _ = q := by rw [h1, inv_inv]

theorem gLAPPrimeCoreOf_eq_bot_of_klein [Finite G] {p : ℕ} {s a b : G}
    (haC : a ∈ Subgroup.centralizer ({s} : Set G)) (hbC : b ∈ Subgroup.centralizer ({s} : Set G))
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hba : a ≠ b)
    (hQa : ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)),
      q * a = a * q → q = 1 ∨ q = a)
    (hQb : ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)),
      q * b = b * q → q = 1 ∨ q = b)
    (hQab : ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)),
      q * (a * b) = (a * b) * q → ∃ k : ℕ, q ^ (2 ^ k) = 1) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  set Q := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) with hQ
  have haQ : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx => GLAPPrimeCoreOf_conj_mem a haC x hx
  have hbQ : ∀ x ∈ Q, b * x * b⁻¹ ∈ Q := fun x hx => GLAPPrimeCoreOf_conj_mem b hbC x hx
  have hnotin : ∀ c : G, c * c = 1 → c ≠ 1 → c ∉ Q ∨ ¬ Odd (Nat.card Q) := by
    intro c hc hc1
    by_cases hcQ : c ∈ Q
    · right
      intro hodd
      have h2 : orderOf (⟨c, hcQ⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
      have hord : orderOf (⟨c, hcQ⟩ : Q) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [sq]; exact hc) hc1
      rw [hord] at h2
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
    · left
      exact hcQ
  have hodd : Odd (Nat.card Q) := by
    refine odd_natCard_of_klein ha hb hab haQ hbQ ?_
    intro x hx _ hxa hxb
    have h1 := hQa x hx hxa.symm
    have h2 := hQb x hx hxb.symm
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · rw [h1] at h2
        exact absurd h2 ha1
      · rw [h1] at h2
        exact absurd h2 hba
  have hfixed : ∀ (c : G), c * c = 1 → c ≠ 1 → (∀ q ∈ Q, q * c = c * q → q = 1 ∨ q = c) →
      ∀ x ∈ Q, c * x * c⁻¹ = x → x = 1 := by
    intro c hc hc1 hQc x hx hxc
    have hxc' : x * c = c * x := by
      calc x * c = (c * x * c⁻¹) * c := by rw [hxc]
        _ = c * x := by group
    rcases hQc x hx hxc' with h | h
    · exact h
    · exfalso
      rcases hnotin c hc hc1 with h' | h'
      · exact h' (h ▸ hx)
      · exact h' hodd
  have hQ' := eq_one_of_klein_fixedPointFree ha hb haQ hbQ (hfixed a ha ha1 hQa)
    (hfixed b hb hb1 hQb) (by
      intro x hx hxab
      obtain ⟨k, hk⟩ := hQab x hx (by
        calc x * (a * b) = ((a * b) * x * (a * b)⁻¹) * (a * b) := by rw [hxab]
          _ = (a * b) * x := by group)
      have hdvd : orderOf (⟨x, hx⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
      have hdvd2 : orderOf (⟨x, hx⟩ : Q) ∣ 2 ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact Subtype.ext hk
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
      have hoddd : Odd (orderOf (⟨x, hx⟩ : Q)) := Odd.of_dvd_nat hodd hdvd
      cases i with
      | zero =>
        rw [pow_zero, orderOf_eq_one_iff] at hi
        exact congrArg Subtype.val hi
      | succ i =>
        exfalso
        rw [hi, pow_succ] at hoddd
        exact (Nat.not_even_iff_odd.2 hoddd) (even_iff_two_dvd.2 (dvd_mul_left 2 _)))
  exact (Subgroup.eq_bot_iff_forall Q).2 hQ'

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
