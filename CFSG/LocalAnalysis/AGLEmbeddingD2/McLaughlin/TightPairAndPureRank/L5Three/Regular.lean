module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Stab

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem mem_fixedPoints_zpowers {g : V ≃ₗ[ZMod 2] V} {v : V} :
    v ∈ MulAction.fixedPoints (Subgroup.zpowers g) V ↔ g v = v := by
  constructor
  · intro h
    exact h ⟨g, Subgroup.mem_zpowers g⟩
  · intro h a
    obtain ⟨a, k, rfl⟩ := a
    show (g ^ k) v = v
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one]
      show (g ^ (k : ℤ)) (g v) = v
      rw [h]; exact ih
    | pred k ih =>
      rw [zpow_sub_one]
      show (g ^ (-(k : ℤ))) (g⁻¹ v) = v
      have : g⁻¹ v = v := by
        have h' := congrArg (fun u => g⁻¹ u) h
        simpa using h'.symm
      rw [this]; exact ih

theorem no_fixed_of_prime_order {q : ℕ} [Fact q.Prime] (hV : Nat.card V = q + 1)
    {g : V ≃ₗ[ZMod 2] V} (hg : orderOf g = q) {v : V} (hv : g v = v) : v = 0 := by
  have hp : IsPGroup q (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have h := hp.card_modEq_card_fixedPoints V
  rw [hV] at h
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hle : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) ≤ q + 1 := by
    rw [← hV]; exact Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
  have hpos : 0 < Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) := by
    refine Nat.card_pos_iff.2 ⟨⟨⟨0, ?_⟩⟩, inferInstance⟩
    exact mem_fixedPoints_zpowers.2 (by simp)
  by_contra hv0
  have hfix : v ∈ MulAction.fixedPoints (Subgroup.zpowers g) V := mem_fixedPoints_zpowers.2 hv
  have hne : (0 : V) ∈ MulAction.fixedPoints (Subgroup.zpowers g) V := mem_fixedPoints_zpowers.2 (by simp)
  have h2 : 2 ≤ Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) := by
    have : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) ≠ 1 := by
      intro h1
      obtain ⟨u, hu⟩ := Nat.card_eq_one_iff_unique.1 h1 |>.2
      have e1 := (Nat.card_eq_one_iff_unique.1 h1).1
      exact hv0 (congrArg Subtype.val (e1.allEq ⟨v, hfix⟩ ⟨0, hne⟩))
    omega
  have hmod : (q + 1) % q = Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) % q := h
  have hq : (q + 1) % q = 1 := by
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hq1, Nat.mod_eq_of_lt hq1]
  have hf : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) = q + 1 := by
    set f := Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V)
    rw [hq] at hmod
    have := Nat.div_add_mod f q
    have hlt : f / q < 2 := by
      by_contra hc
      push Not at hc
      have : q * 2 ≤ q * (f / q) := Nat.mul_le_mul_left q hc
      omega
    interval_cases hd : f / q <;> omega
  have hall : ∀ u : V, g u = u := by
    have hcard : (MulAction.fixedPoints (Subgroup.zpowers g) V).ncard = (Set.univ : Set V).ncard := by
      rw [Set.ncard_univ, hV, ← hf, Nat.card_coe_set_eq]
    have := Set.eq_of_subset_of_ncard_le (Set.subset_univ (MulAction.fixedPoints (Subgroup.zpowers g) V))
      hcard.ge
    intro u
    have hu : u ∈ MulAction.fixedPoints (Subgroup.zpowers g) V := by rw [this]; trivial
    exact mem_fixedPoints_zpowers.1 hu
  have : g = 1 := LinearEquiv.ext hall
  rw [this, orderOf_one] at hg
  exact hq1.ne hg

theorem pow_fix_iff {q : ℕ} [Fact q.Prime] (hV : Nat.card V = q + 1) {x : V ≃ₗ[ZMod 2] V}
    (hx : orderOf x = q) {v : V} (hv : v ≠ 0) {m : ℕ} (hm : (x ^ m) v = v) : q ∣ m := by
  by_contra hqm
  have hcop : Nat.Coprime q m := (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).2 hqm
  have hm0 : m ≠ 0 := by
    rintro rfl; exact hqm (dvd_zero q)
  have hord : orderOf (x ^ m) = q := by
    rw [orderOf_pow' _ hm0, hx, hcop, Nat.div_one]
  exact hv (no_fixed_of_prime_order hV hord hm)

theorem regular_action {q : ℕ} [Fact q.Prime] (hV : Nat.card V = q + 1) {x : V ≃ₗ[ZMod 2] V}
    (hx : orderOf x = q) {v : V} (hv : v ≠ 0) {w : V} (hw : w ≠ 0) :
    ∃ k < q, (x ^ k) v = w := by
  have hne : ∀ k : ℕ, (x ^ k) v ≠ 0 := fun k h => hv (by
    have := congrArg (fun u => (x ^ k)⁻¹ u) h
    simpa using this)
  let f : Fin q → {u : V // u ≠ 0} := fun k => ⟨(x ^ (k : ℕ)) v, hne k⟩
  have hinj : Function.Injective f := by
    intro k l hkl
    have h : (x ^ (k : ℕ)) v = (x ^ (l : ℕ)) v := congrArg Subtype.val hkl
    have key : ∀ a b : ℕ, a < b → b < q → (x ^ a) v = (x ^ b) v → False := by
      intro a b hab hbq hh
      have h1 : (x ^ (b - a)) v = v := by
        have e1 : (x ^ b) v = (x ^ (b - a)) ((x ^ a) v) := by
          rw [← LinearEquiv.mul_apply, ← pow_add]; congr 2; omega
        have e2 : (x ^ (b - a)) ((x ^ a) v) = (x ^ a) ((x ^ (b - a)) v) := by
          rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_add, ← pow_add, add_comm]
        rw [e1, e2] at hh
        exact (x ^ a).injective hh.symm
      have := pow_fix_iff hV hx hv h1
      have := Nat.le_of_dvd (by omega) this
      omega
    apply Fin.ext
    by_contra hkl'
    rcases Nat.lt_or_gt_of_ne hkl' with hlt | hlt
    · exact key _ _ hlt l.2 h
    · exact key _ _ hlt k.2 h.symm
  have hcard : Nat.card {u : V // u ≠ 0} = q := by
    have : Nat.card {u : V // u ≠ 0} = Nat.card V - 1 := by
      classical
      have : Fintype V := Fintype.ofFinite V
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := V)]
      have := Fintype.card_subtype_compl (fun u : V => u = 0)
      simp only [Fintype.card_subtype_eq] at this
      convert this using 1
    omega
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])
  obtain ⟨k, hk⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨k, k.2, congrArg Subtype.val hk⟩

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
