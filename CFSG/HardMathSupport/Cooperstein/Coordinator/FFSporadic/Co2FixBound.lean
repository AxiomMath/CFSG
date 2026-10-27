module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.FixBound

open Finset

def eps (t : ZMod 2) : ℤ := if t = 0 then 1 else -1

theorem eps_add (s t : ZMod 2) : eps (s + t) = eps s * eps t := by
  fin_cases s <;> fin_cases t <;> decide

theorem eps_one : eps 1 = -1 := by decide

theorem eps_zero : eps 0 = 1 := by decide

theorem zmod2_eq_one : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide

section Dual

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

instance : Finite (Module.Dual (ZMod 2) V) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2)) DFunLike.coe_injective

noncomputable instance : Fintype (Module.Dual (ZMod 2) V) := Fintype.ofFinite _

theorem sum_eps_ne {z : V} (hz : z ≠ 0) :
    ∑ f : Module.Dual (ZMod 2) V, eps (f z) = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Free (ZMod 2) V := Module.Free.of_divisionRing (ZMod 2) V
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual (ZMod 2) V, g z ≠ 0 := by
    by_contra h
    push Not at h
    exact hz ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) z).1 h)
  have hg1 : g z = 1 := zmod2_eq_one _ hg
  have e : ∑ f : Module.Dual (ZMod 2) V, eps (f z) =
      ∑ f : Module.Dual (ZMod 2) V, eps ((f + g) z) :=
    (Fintype.sum_equiv (Equiv.addRight g) _ _ (fun _ => rfl)).symm
  simp only [LinearMap.add_apply, eps_add, hg1] at e
  rw [eps_one, ← Finset.sum_mul] at e
  linarith

theorem card_dual : Nat.card (Module.Dual (ZMod 2) V) = Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Free (ZMod 2) V := Module.Free.of_divisionRing (ZMod 2) V
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  exact Nat.card_congr (Module.Free.chooseBasis (ZMod 2) V).toDualEquiv.toEquiv.symm

theorem sum_eps_zero : ∑ f : Module.Dual (ZMod 2) V, eps (f 0) = Nat.card V := by
  simp only [map_zero, eps_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, card_dual]

theorem sum_sq (A : Finset V) :
    ∑ f : Module.Dual (ZMod 2) V, (∑ x ∈ A, eps (f x)) ^ 2 = Nat.card V * A.card := by
  classical
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    have : (2 : ZMod 2) • x = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [two_smul] at this
    exact this
  have e : ∀ f : Module.Dual (ZMod 2) V, (∑ x ∈ A, eps (f x)) ^ 2 =
      ∑ x ∈ A, ∑ y ∈ A, eps (f (x + y)) := by
    intro f
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_add, eps_add]
  simp only [e]
  rw [Finset.sum_comm]
  have e2 : ∀ x ∈ A, ∑ f : Module.Dual (ZMod 2) V, ∑ y ∈ A, eps (f (x + y)) = Nat.card V := by
    intro x hx
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single x]
    · rw [h2 x, sum_eps_zero]
    · intro y _ hyx
      apply sum_eps_ne
      intro h
      apply hyx
      have := congrArg (· + y) h
      simp only [zero_add] at this
      rw [add_assoc, h2 y, add_zero] at this
      exact this.symm
    · intro h
      exact absurd hx h
  rw [Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul, mul_comm]

end Dual

section Burnside

variable {H α : Type*} [Group H] [Fintype α] [DecidableEq α] (ρ : H →* Equiv.Perm α)

@[expose] def fixN (h : H) : ℕ :=(Finset.univ.filter fun i => ρ h i = i).card

theorem fixN_one : fixN ρ 1 = Fintype.card α := by
  simp [fixN]

theorem fixN_conj (g x : H) : fixN ρ (g * x * g⁻¹) = fixN ρ x := by
  unfold fixN
  have h1 : ∀ j, ρ g ((ρ g)⁻¹ j) = j := fun j => by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have h2 : ∀ j, (ρ g)⁻¹ (ρ g j) = j := fun j => by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  have e : ∀ j, ρ (g * x * g⁻¹) j = ρ g (ρ x ((ρ g)⁻¹ j)) := fun j => by
    rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  refine (Finset.card_nbij' (fun i => ρ g i) (fun i => (ρ g)⁻¹ i) ?_ ?_ ?_ ?_).symm
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    rw [e, h2, hi]
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    rw [e] at hi
    apply (ρ g).injective
    rw [hi, h1]
  · intro i _
    exact h2 i
  · intro i _
    exact h1 i

theorem card_dvd_sum (K : Subgroup H) [Fintype K] :
    Fintype.card K ∣ ∑ k : K, fixN ρ k := by
  classical
  letI : MulAction K α := MulAction.compHom α (ρ.comp K.subtype)
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group K α
  have e : ∀ k : K, Fintype.card (MulAction.fixedBy α k) = fixN ρ k := by
    intro k
    rw [fixN, ← Fintype.card_subtype]
    rfl
  simp only [e] at hb
  rw [hb]
  exact Dvd.intro_left _ rfl

end Burnside

section Bound

variable {H α : Type*} [Group H] [Fintype α] [DecidableEq α] (ρ : H →* Equiv.Perm α)

theorem arith (a af : ℤ) (h1 : (256 : ℤ) ∣ 15560 + 88 * a) (h2 : (128 : ℤ) ∣ 8904 + 88 * af) :
    121 ≤ (af - (a - af)) ^ 2 := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have : af - (a - af) ≥ 11 ∨ af - (a - af) ≤ -11 := by omega
  rcases this with h | h <;> nlinarith

theorem no_e256 (hα : Fintype.card α = 2300) (E : Subgroup H) [Fintype E]
    (hcard : Fintype.card E = 256) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) (hfix : ∀ x ∈ E, x ≠ 1 → fixN ρ x = 140 ∨ fixN ρ x = 52) :
    False := by
  classical
  letI : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (hcomm _ a.2 _ b.2) }
  letI : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) fun x => by
    change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
    rw [sq]
    exact congrArg Additive.ofMul (Subtype.ext (hsq _ (Additive.toMul x).2))
  have hV : Nat.card (Additive E) = 256 := by
    change Nat.card E = 256
    rw [Nat.card_eq_fintype_card, hcard]
  let ρE : E →* Equiv.Perm α := ρ.comp E.subtype
  let c : E → ℕ := fun h => fixN ρE h
  have hcE : ∀ h : E, c h = fixN ρ (h : H) := fun _ => rfl
  let A : Finset E := Finset.univ.filter fun h => c h = 140
  have hc : ∀ h : E, (c h : ℤ) = 52 + 88 * (if h ∈ A then 1 else 0) +
      2248 * (if h = 1 then 1 else 0) := by
    intro h
    by_cases h1 : h = 1
    · subst h1
      have h2300 : c 1 = 2300 := by
        rw [hcE, Subgroup.coe_one, fixN_one, hα]
      have hA : (1 : E) ∉ A := by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, h2300]
        decide
      rw [if_neg hA, if_pos rfl, h2300]
      norm_num
    · have hne : (h : H) ≠ 1 := fun e => h1 (Subtype.ext e)
      rcases hfix _ h.2 hne with e | e
      · have hA : h ∈ A := by
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hcE]
          exact e
        rw [if_pos hA, if_neg h1, hcE, e]
        norm_num
      · have hA : h ∉ A := by
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hcE, e]
          decide
        rw [if_neg hA, if_neg h1, hcE, e]
        norm_num
  have hsum : ∀ S : Finset E, (1 : E) ∈ S → (∑ h ∈ S, (c h : ℤ)) =
      52 * S.card + 88 * (S.filter (· ∈ A)).card + 2248 := by
    intro S hS
    rw [Finset.sum_congr rfl fun h _ => hc h, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
      Finset.filter_eq' S 1, if_pos hS, Finset.card_singleton, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  have hburn : ∀ K : Subgroup E, ((Finset.univ.filter (· ∈ K)).card : ℤ) ∣
      ∑ h ∈ Finset.univ.filter (· ∈ K), (c h : ℤ) := by
    intro K
    have h := card_dvd_sum ρE K
    have e1 : ∑ k : K, fixN ρE k = ∑ h ∈ Finset.univ.filter (· ∈ K), c h :=
      (Finset.sum_subtype (Finset.univ.filter (· ∈ K)) (by simp) c).symm
    have e2 : Fintype.card K = (Finset.univ.filter (· ∈ K)).card :=
      (Fintype.card_subtype _).trans rfl
    rw [e1, e2] at h
    exact_mod_cast h
  have hE : (256 : ℤ) ∣ 15560 + 88 * A.card := by
    have h := hburn ⊤
    have hf : Finset.univ.filter (fun h : E => h ∈ (⊤ : Subgroup E)) = Finset.univ :=
      Finset.filter_true_of_mem fun _ _ => Subgroup.mem_top _
    rw [hf, hsum _ (Finset.mem_univ _), Finset.card_univ, hcard] at h
    have hA : (Finset.univ.filter (· ∈ A)).card = A.card := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hA] at h
    have : (52 : ℤ) * ((256 : ℕ) : ℤ) + 88 * (A.card : ℤ) + 2248 = 15560 + 88 * A.card := by
      push_cast
      ring
    rw [this] at h
    exact_mod_cast h
  let D := Module.Dual (ZMod 2) (Additive E)
  let fv : D → E → ZMod 2 := fun f h => f (Additive.ofMul h)
  let s : D → ℤ := fun f => ∑ h ∈ A, eps (fv f h)
  have hs0 : s 0 = A.card := by
    have e : ∀ h ∈ A, eps (fv 0 h) = 1 := fun h _ => eps_zero
    change ∑ h ∈ A, eps (fv 0 h) = _
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hpars : ∑ f : D, s f ^ 2 = 256 * A.card := by
    have h := sum_sq (V := Additive E) (A.map Additive.ofMul.toEmbedding)
    rw [Finset.card_map, hV] at h
    simp only [Finset.sum_map] at h
    exact_mod_cast h
  have hK : ∀ f : D, f ≠ 0 → 121 ≤ s f ^ 2 := by
    intro f hf
    let K : Subgroup E :=
      { carrier := {h | fv f h = 0}
        mul_mem' := fun {a b} ha hb => by
          change f (Additive.ofMul a + Additive.ofMul b) = 0
          rw [map_add]
          change fv f a + fv f b = 0
          rw [show fv f a = 0 from ha, show fv f b = 0 from hb, add_zero]
        one_mem' := by
          change f 0 = 0
          exact map_zero f
        inv_mem' := fun {a} ha => by
          change f (-Additive.ofMul a) = 0
          rw [map_neg]
          change -fv f a = 0
          rw [show fv f a = 0 from ha, neg_zero] }
    have hmemK : ∀ h : E, h ∈ K ↔ fv f h = 0 := fun _ => Iff.rfl
    obtain ⟨v, hv⟩ : ∃ v : E, fv f v = 1 := by
      by_contra hno
      push Not at hno
      apply hf
      apply LinearMap.ext
      intro x
      have : fv f (Additive.toMul x) ≠ 1 := hno _
      have h01 : ∀ t : ZMod 2, t ≠ 1 → t = 0 := by decide
      exact h01 _ this
    have hcardK : (Finset.univ.filter (· ∈ K)).card = 128 := by
      have e0 : (Finset.univ.filter (· ∈ K)).card = (Finset.univ.filter (· ∉ K)).card := by
        refine Finset.card_nbij' (· * v) (· * v) ?_ ?_ ?_ ?_
        · intro h hh
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hmemK] at hh ⊢
          change f (Additive.ofMul h + Additive.ofMul v) ≠ 0
          rw [map_add]
          change fv f h + fv f v ≠ 0
          rw [hh, hv]
          decide
        · intro h hh
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hmemK] at hh ⊢
          change f (Additive.ofMul h + Additive.ofMul v) = 0
          rw [map_add]
          change fv f h + fv f v = 0
          rw [hv, zmod2_eq_one _ hh]
          decide
        · intro h _
          simp only [mul_assoc]
          rw [show v * v = 1 from Subtype.ext (hsq _ v.2), mul_one]
        · intro h _
          simp only [mul_assoc]
          rw [show v * v = 1 from Subtype.ext (hsq _ v.2), mul_one]
      have e1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (· ∈ K)
      rw [Finset.card_univ, hcard] at e1
      omega
    have hKb := hburn K
    rw [hsum _ (by simpa using K.one_mem), hcardK] at hKb
    have hKA : (Finset.univ.filter (· ∈ K)).filter (· ∈ A) = A.filter (fun h => fv f h = 0) := by
      ext h
      simp [hmemK, and_comm]
    rw [hKA] at hKb
    have hsf : s f = ((A.filter fun h => fv f h = 0).card : ℤ) -
        ((A.card : ℤ) - (A.filter fun h => fv f h = 0).card) := by
      have e := Finset.sum_filter_add_sum_filter_not A (fun h => fv f h = 0) (fun h => eps (fv f h))
      have e0 : ∑ h ∈ A.filter (fun h => fv f h = 0), eps (fv f h) =
          (A.filter fun h => fv f h = 0).card := by
        rw [Finset.sum_congr rfl fun h hh => by rw [(Finset.mem_filter.1 hh).2, eps_zero]]
        simp
      have e1 : ∑ h ∈ A.filter (fun h => ¬ fv f h = 0), eps (fv f h) =
          -((A.filter fun h => ¬ fv f h = 0).card : ℤ) := by
        rw [Finset.sum_congr rfl fun h hh => by
          rw [zmod2_eq_one _ (Finset.mem_filter.1 hh).2, eps_one]]
        simp
      have e2 := Finset.card_filter_add_card_filter_not (s := A) (fun h => fv f h = 0)
      change ∑ h ∈ A, eps (fv f h) = _
      rw [← e, e0, e1]
      have : ((A.filter fun h => ¬ fv f h = 0).card : ℤ) =
          (A.card : ℤ) - (A.filter fun h => fv f h = 0).card := by
        rw [← e2]
        push_cast
        ring
      rw [this]
      ring
    rw [hsf]
    apply arith _ _ hE
    have : (52 : ℤ) * ((128 : ℕ) : ℤ) + 88 * ((A.filter fun h => fv f h = 0).card : ℤ) + 2248 =
        8904 + 88 * (A.filter fun h => fv f h = 0).card := by
      push_cast
      ring
    rw [this] at hKb
    exact_mod_cast hKb
  have hcardD : Fintype.card D = 256 := by
    rw [← Nat.card_eq_fintype_card, card_dual, hV]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset D) (fun f => s f ^ 2) (Finset.mem_univ 0)
  have hlow : (121 : ℤ) * 255 ≤ ∑ f ∈ Finset.univ.erase (0 : D), s f ^ 2 := by
    have hc : (Finset.univ.erase (0 : D)).card = 255 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardD]
    have := Finset.card_nsmul_le_sum (Finset.univ.erase (0 : D)) (fun f => s f ^ 2) 121
      (fun f hf => hK f (Finset.ne_of_mem_erase hf))
    rw [hc, nsmul_eq_mul] at this
    push_cast at this
    linarith
  rw [hpars, hs0] at hsplit
  nlinarith [sq_nonneg ((A.card : ℤ) - 128)]

theorem card_le_of_fix (hα : Fintype.card α = 2300) (B : Subgroup H)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hfix : ∀ x ∈ B, x ≠ 1 → fixN ρ x = 140 ∨ fixN ρ x = 52) : Nat.card B ≤ 128 := by
  classical
  by_cases hfin : Finite B
  · have hp : IsPGroup 2 B := fun g => ⟨1, by
      rw [pow_one, sq]
      exact Subtype.ext (hsq _ g.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    by_contra hlt
    push Not at hlt
    have h8 : 8 ≤ n := by
      by_contra h
      push Not at h
      have : 2 ^ n ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdvd : 2 ^ 8 ∣ Nat.card B := by
      rw [hn]
      exact Nat.pow_dvd_pow 2 h8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    let E : Subgroup H := K.map B.subtype
    have hEB : ∀ x ∈ E, x ∈ B := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hEc : Nat.card E = 256 := by
      rw [Subgroup.card_map_of_injective B.subtype_injective, hK]
      norm_num
    have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
    let _ : Fintype E := Fintype.ofFinite _
    exact no_e256 ρ hα E (by rw [← Nat.card_eq_fintype_card, hEc])
      (fun x hx y hy => hcomm x (hEB x hx) y (hEB y hy)) (fun x hx => hsq x (hEB x hx))
      (fun x hx => hfix x (hEB x hx))
  · have : Infinite B := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    norm_num

end Bound

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.FixBound

end
