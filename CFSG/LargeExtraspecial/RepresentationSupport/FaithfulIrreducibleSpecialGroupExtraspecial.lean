module

public import CFSG.Foundations.Basic
public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.FaithfulIrreducibleSpecialGroupExtraspecial

open scoped commutatorElement

private lemma comm_pow_eq_one {E : Type*} [Group E] {q : ℕ}
    (hcomm : ∀ a b : E, ⁅a, b⁆ ∈ Subgroup.center E)
    (hpow : ∀ a : E, a ^ q ∈ Subgroup.center E) (a b : E) : ⁅a, b⁆ ^ q = 1 := by
  set c : E := ⁅a, b⁆ with hc
  have hcc : c ∈ Subgroup.center E := hcomm a b
  have hab : a * b = c * (b * a) := by
    rw [hc, commutatorElement_def]; group
  have key : ∀ n : ℕ, a ^ n * b = c ^ n * (b * a ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hz : ∀ m : ℕ, a * c ^ m = c ^ m * a := fun m =>
        ((Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hcc m)) a)
      calc a ^ (n + 1) * b = a * (a ^ n * b) := by rw [pow_succ']; group
        _ = a * (c ^ n * (b * a ^ n)) := by rw [ih]
        _ = c ^ n * (a * b) * a ^ n := by rw [← mul_assoc, hz n]; group
        _ = c ^ n * (c * (b * a)) * a ^ n := by rw [hab]
        _ = c ^ (n + 1) * (b * a ^ (n + 1)) := by rw [pow_succ, pow_succ']; group
  have h1 := key q
  have h2 : a ^ q * b = b * a ^ q := ((Subgroup.mem_center_iff.mp (hpow a)) b).symm
  rw [h2] at h1
  have : c ^ q * (b * a ^ q) = 1 * (b * a ^ q) := by rw [← h1]; group
  exact _root_.mul_right_cancel this

theorem extraspecial {F : Type*} [Field F] [IsAlgClosed F] {E : Type*} [Group E] [Finite E]
    {q : ℕ} (hq : q.Prime) (hE : IsPGroup q E) (hnc : ¬ IsMulCommutative E)
    (hZC : Subgroup.center E = commutator E) (hZF : Subgroup.center E = frattini E)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (σ : Representation F E V) (hfaith : Function.Injective σ) (hirr : σ.IsIrreducible) :
    CFSG.IsExtraspecialPGroup q E := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (IsPGroup q E) := ⟨hE⟩
  have hcommZ : ∀ a b : E, ⁅a, b⁆ ∈ Subgroup.center E := by
    intro a b
    rw [hZC]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hpowZ : ∀ a : E, a ^ q ∈ Subgroup.center E := by
    intro a
    rw [hZF]
    exact CFSG.pth_power_mem_frattini_of_isPGroup (p := q) a
  have hZq : ∀ z ∈ Subgroup.center E, z ^ q = 1 := by
    intro z hz
    rw [hZC, commutator_eq_closure] at hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact comm_pow_eq_one hcommZ hpowZ a b
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxc : x ∈ Subgroup.center E := by
        rw [hZC, commutator_eq_closure]; exact hx
      have : Commute x y := by
        have hyc : y ∈ Subgroup.center E := by
          rw [hZC, commutator_eq_closure]; exact hy
        exact ((Subgroup.mem_center_iff.mp hyc) x)
      rw [this.mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  obtain ⟨χ, hχ, -⟩ := CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter.exists_character σ hfaith hirr
  haveI : IsCyclic (Subgroup.center E) :=
    isCyclic_of_subgroup_isDomain ((Units.coeHom F).comp χ)
      (Units.val_injective.comp hχ)
  have hntriv : Nontrivial (Subgroup.center E) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : (⟨⁅a, b⁆, hcommZ a b⟩ : Subgroup.center E) = 1 := Subsingleton.elim _ _
    have h2 : ⁅a, b⁆ = 1 := congrArg Subtype.val h1
    rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    simpa [mul_assoc] using h2
  have hcard : Nat.card (Subgroup.center E) = q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Subgroup.center E)
    have hord : orderOf g = Nat.card (Subgroup.center E) := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgq : g ^ q = 1 := Subtype.ext (hZq g.1 g.2)
    have hdvd : Nat.card (Subgroup.center E) ∣ q := hord ▸ orderOf_dvd_of_pow_eq_one hgq
    rcases (Nat.dvd_prime hq).mp hdvd with h | h
    · exfalso
      have := Nat.card_eq_one_iff_unique.mp h
      exact not_subsingleton _ this.1
    · exact h
  exact ⟨hE, hZC.symm, hZF.symm, hcard⟩

end CFSG.LargeExtraspecial.RepresentationSupport.FaithfulIrreducibleSpecialGroupExtraspecial
