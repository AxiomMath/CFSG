module

public import Mathlib.Data.FunLike.Fintype
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.TwoB

theorem card_modEq_card_fixedPoints_of_iterate_eq_id {α : Type*} [Finite α] {q : ℕ}
    (hq : q.Prime) {f : α → α} (hf : f^[q] = id) :
    Nat.card α ≡ Nat.card (Function.fixedPoints f) [MOD q] := by
  classical
  have := Fintype.ofFinite α
  have := Fact.mk hq
  have h := Equiv.Perm.card_fixedPoints_modEq (f := (f : Function.End α)) (p := q) (n := 1)
    (by rw [pow_one]; exact hf)
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

theorem exists_isFixedPt_of_not_dvd_card {α : Type*} [Finite α] {q : ℕ} (hq : q.Prime)
    {f : α → α} (hf : f^[q] = id) (hα : ¬ q ∣ Nat.card α) : ∃ a, f a = a := by
  by_contra hne
  have h := card_modEq_card_fixedPoints_of_iterate_eq_id hq hf
  have : IsEmpty (Function.fixedPoints f) := ⟨fun a => hne ⟨a.1, a.2⟩⟩
  have h0 : Nat.card (Function.fixedPoints f) = 0 := Nat.card_of_isEmpty
  rw [h0] at h
  exact hα (Nat.modEq_zero_iff_dvd.1 h)

theorem isFixedPt_of_card_lt {α : Type*} [Finite α] {q : ℕ} (hq : q.Prime) {f : α → α}
    (hf : f^[q] = id) (hα : Nat.card α < q) (a : α) : f a = a := by
  by_contra hne
  have hlt : Nat.card (Function.fixedPoints f) < Nat.card α :=
    Finite.card_subtype_lt (p := fun x => f x = x) hne
  have h := card_modEq_card_fixedPoints_of_iterate_eq_id hq hf
  exact hlt.ne' (h.eq_of_lt_of_lt hα (hlt.trans hα))

section TwoGroup

variable {X : Type*} [Group X] [Finite X]

theorem exists_hom_ker_eq_of_isCoatom (hX : IsPGroup 2 X) {M : Subgroup X} (hM : IsCoatom M) :
    ∃ φ : X →* Multiplicative (ZMod 2), φ.ker = M := by
  have : Group.IsNilpotent X := hX.isNilpotent
  have hidx : M.index = 2 := hX.isCoatom_iff_index_eq_prime.1 hM
  have : M.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (X ⧸ M) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  have hcard' : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  refine ⟨((mulEquivOfPrimeCardEq hcard hcard').toMonoidHom).comp (QuotientGroup.mk' M), ?_⟩
  ext x
  simp

theorem not_dvd_card_coset (hX : IsPGroup 2 X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (x : X) :
    ¬ q ∣ Nat.card {y : X | ∀ φ : X →* Multiplicative (ZMod 2), φ y = φ x} := by
  let Φ : Subgroup X := ⨅ φ : X →* Multiplicative (ZMod 2), φ.ker
  have hΦ : ∀ y, y ∈ Φ ↔ ∀ φ : X →* Multiplicative (ZMod 2), φ y = 1 := by
    intro y
    simp [Φ, Subgroup.mem_iInf, MonoidHom.mem_ker]
  have hS : ∀ y : X, (∀ φ : X →* Multiplicative (ZMod 2), φ y = φ x) ↔ x⁻¹ * y ∈ Φ := by
    intro y
    rw [hΦ]
    refine forall_congr' fun φ => ?_
    rw [map_mul, map_inv]
    exact eq_comm.trans inv_mul_eq_one.symm
  let e : {y : X | ∀ φ : X →* Multiplicative (ZMod 2), φ y = φ x} ≃ Φ :=
    Equiv.subtypeEquiv (Equiv.mulLeft x⁻¹) hS
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hX.to_subgroup Φ)
  rw [Nat.card_congr e, hn]
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem exists_fixed_mem_coset (hX : IsPGroup 2 X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {c : X →* X} (hc : (⇑c)^[q] = id)
    (hfix : ∀ (φ : X →* Multiplicative (ZMod 2)) (y : X), φ (c y) = φ y) (x : X) :
    ∃ y : X, c y = y ∧ ∀ φ : X →* Multiplicative (ZMod 2), φ y = φ x := by
  set S : Set X := {y | ∀ φ : X →* Multiplicative (ZMod 2), φ y = φ x} with hS
  have hmaps : ∀ y ∈ S, c y ∈ S := fun y hy φ => (hfix φ y).trans (hy φ)
  let g : S → S := fun y => ⟨c y, hmaps y y.2⟩
  have hg : ∀ (n : ℕ) (y : S), ((g^[n] y : S) : X) = (⇑c)^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
  have hgq : g^[q] = id := by
    funext y
    apply Subtype.ext
    rw [hg, hc]
    rfl
  obtain ⟨y, hy⟩ := exists_isFixedPt_of_not_dvd_card hq hgq (not_dvd_card_coset hX hq hq2 x)
  exact ⟨y, congrArg Subtype.val hy, y.2⟩

theorem apply_eq_self_of_card_hom_lt (hX : IsPGroup 2 X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {c : X →* X} (hc : (⇑c)^[q] = id)
    (hHom : Nat.card (X →* Multiplicative (ZMod 2)) < q) (x : X) : c x = x := by
  have : Finite (X →* Multiplicative (ZMod 2)) := FunLike.finite _
  have hfix : ∀ (φ : X →* Multiplicative (ZMod 2)) (y : X), φ (c y) = φ y := by
    let T : (X →* Multiplicative (ZMod 2)) → (X →* Multiplicative (ZMod 2)) := fun φ => φ.comp c
    have hT : ∀ (n : ℕ) (φ : X →* Multiplicative (ZMod 2)) (y : X),
        (T^[n] φ) y = φ ((⇑c)^[n] y) := by
      intro n
      induction n with
      | zero => intro φ y; rfl
      | succ n ih =>
        intro φ y
        rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply']
        rfl
    have hTq : T^[q] = id := by
      funext φ
      ext y
      rw [hT, hc]
      rfl
    intro φ y
    exact DFunLike.congr_fun (isFixedPt_of_card_lt hq hTq hHom φ) y
  have hC : MonoidHom.eqLocus c (MonoidHom.id X) = ⊤ := by
    rcases IsCoatomic.eq_top_or_exists_le_coatom (MonoidHom.eqLocus c (MonoidHom.id X)) with
      h | ⟨M, hM, hCM⟩
    · exact h
    · exfalso
      obtain ⟨φ, hφ⟩ := exists_hom_ker_eq_of_isCoatom hX hM
      refine hM.1 ((Subgroup.eq_top_iff' M).2 fun z => ?_)
      obtain ⟨y, hcy, hy⟩ := exists_fixed_mem_coset hX hq hq2 hc hfix z
      have hyM : y ∈ φ.ker := hφ ▸ hCM hcy
      rw [← hφ, MonoidHom.mem_ker, ← hy φ]
      exact hyM
  have : x ∈ MonoidHom.eqLocus c (MonoidHom.id X) := by rw [hC]; exact Subgroup.mem_top x
  exact this

end TwoGroup

theorem commute_of_card_hom_lt {G : Type*} [Group G] {X : Subgroup G} [Finite X]
    (hX : IsPGroup 2 X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {σ : G} (hσ : orderOf σ = q)
    (hnorm : ∀ x ∈ X, σ * x * σ⁻¹ ∈ X)
    (hHom : Nat.card (X →* Multiplicative (ZMod 2)) < q) :
    ∀ x ∈ X, σ * x = x * σ := by
  let c : X →* X :=
    { toFun := fun x => ⟨σ * x * σ⁻¹, hnorm x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hc : ∀ (n : ℕ) (x : X), (((⇑c)^[n] x : X) : G) = σ ^ n * x * (σ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      show σ * (((⇑c)^[n] x : X) : G) * σ⁻¹ = _
      rw [ih, pow_succ', mul_inv_rev]
      simp only [mul_assoc]
  have hcq : (⇑c)^[q] = id := by
    funext x
    apply Subtype.ext
    rw [hc, ← hσ, pow_orderOf_eq_one]
    simp
  intro x hx
  have h := congrArg Subtype.val (apply_eq_self_of_card_hom_lt hX hq hq2 hcq hHom ⟨x, hx⟩)
  exact mul_inv_eq_iff_eq_mul.1 h

end CFSG.EvenSporadicStandard.TwoB
