module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem exists_fixed_mod_of_odd_index {X A Z : Subgroup G}
    (hA : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hZA : Z ≤ A)
    (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hXZ : ∀ x ∈ X, ∀ c ∈ Z, x * c * x⁻¹ ∈ Z)
    {u : G} (hu : ∀ x ∈ X, u⁻¹ * (x * u * x⁻¹) ∈ A) {S : Subgroup ↥X}
    (hS : ∀ s ∈ S, u⁻¹ * ((s : G) * u * (s : G)⁻¹) ∈ Z) (hodd : Odd S.index) :
    ∃ a ∈ A, ∀ x ∈ X, (u * a)⁻¹ * (x * (u * a) * x⁻¹) ∈ Z := by
  classical
  let _ : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun a b => Subtype.ext (hAc _ a.2 _ b.2) }
  let Z' : Subgroup ↥A := Z.subgroupOf A
  have hZ'n : Z'.Normal := Subgroup.normal_of_comm Z'
  have hfin : S.FiniteIndex := ⟨by obtain ⟨k, hk⟩ := hodd; omega⟩
  have : Finite (↥X ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (↥X ⧸ S) := Fintype.ofFinite _
  let f₀ : ↥X → ↥A := fun x => ⟨u⁻¹ * (x * u * x⁻¹), hu x x.2⟩
  let f : ↥X → ↥A ⧸ Z' := fun x => (f₀ x : ↥A ⧸ Z')
  have hf_S : ∀ (x s : ↥X), s ∈ S → f (x * s) = f x := by
    intro x s hs
    show ((f₀ (x * s) : ↥A) : ↥A ⧸ Z') = ((f₀ x : ↥A) : ↥A ⧸ Z')
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (((f₀ (x * s))⁻¹ * f₀ x : ↥A) : G) =
        (x : G) * (u⁻¹ * ((s : G) * u * (s : G)⁻¹))⁻¹ * (x : G)⁻¹ := by
      show (u⁻¹ * (((x * s : ↥X) : G) * u * ((x * s : ↥X) : G)⁻¹))⁻¹ *
          (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) = _
      simp only [Subgroup.coe_mul]
      group
    rw [h1]
    exact hXZ x x.2 _ (Z.inv_mem (hS s hs))
  let F : ↥X ⧸ S → ↥A ⧸ Z' := fun q => Quotient.liftOn' q f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    have := hf_S a (a⁻¹ * b) hab
    simpa using this.symm)
  let c : ↥X → ↥A →* ↥A := fun x =>
    { toFun := fun a => ⟨(x : G) * a * (x : G)⁻¹, hXA x x.2 a a.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hcZ : ∀ x : ↥X, Z' ≤ Z'.comap (c x) := by
    intro x b hb
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hXZ x x.2 _ (Subgroup.mem_subgroupOf.mp hb)
  let φ : ↥X → (↥A ⧸ Z') →* (↥A ⧸ Z') := fun x => QuotientGroup.map Z' Z' (c x) (hcZ x)
  have hφF : ∀ (x : ↥X) (q : ↥X ⧸ S), φ x (F q) = (f x)⁻¹ * F (x • q) := by
    intro x q
    induction q using QuotientGroup.induction_on with
    | H y =>
      show ((c x (f₀ y) : ↥A) : ↥A ⧸ Z') =
        ((f₀ x : ↥A) : ↥A ⧸ Z')⁻¹ * ((f₀ (x * y) : ↥A) : ↥A ⧸ Z')
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show (x : G) * (u⁻¹ * ((y : G) * u * (y : G)⁻¹)) * (x : G)⁻¹ =
        (u⁻¹ * ((x : G) * u * (x : G)⁻¹))⁻¹ *
          (u⁻¹ * (((x * y : ↥X) : G) * u * ((x * y : ↥X) : G)⁻¹))
      simp only [Subgroup.coe_mul]
      group
  have hsq : ∀ b : ↥A ⧸ Z', b ^ 2 = 1 := by
    intro b
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_pow]
      have hb : b ^ 2 = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        exact hA _ b.2
      rw [hb, QuotientGroup.mk_one]
  set a : ↥A ⧸ Z' := ∏ q : ↥X ⧸ S, F q with ha
  have hn : Odd (Fintype.card (↥X ⧸ S)) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact hodd
  have hφa : ∀ x : ↥X, φ x a = (f x)⁻¹ * a := by
    intro x
    have h1 : φ x a = ∏ q : ↥X ⧸ S, φ x (F q) := map_prod (φ x) F Finset.univ
    have h2 : ∏ q : ↥X ⧸ S, φ x (F q) = ∏ q : ↥X ⧸ S, ((f x)⁻¹ * F (x • q)) :=
      Finset.prod_congr rfl fun q _ => hφF x q
    have h3 : ∏ q : ↥X ⧸ S, ((f x)⁻¹ * F (x • q)) =
        ((f x)⁻¹) ^ (Fintype.card (↥X ⧸ S)) * ∏ q : ↥X ⧸ S, F (x • q) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have h4 : ∏ q : ↥X ⧸ S, F (x • q) = a := by
      rw [ha]
      exact Equiv.prod_comp (MulAction.toPerm x) F
    obtain ⟨k, hk⟩ := hn
    have h5 : ((f x)⁻¹) ^ (Fintype.card (↥X ⧸ S)) = (f x)⁻¹ := by
      rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [h1, h2, h3, h4, h5]
  obtain ⟨a₀, ha₀⟩ := QuotientGroup.mk_surjective a
  refine ⟨(a₀ : G), a₀.2, fun x hx => ?_⟩
  have hx1 := hφa ⟨x, hx⟩
  rw [← ha₀] at hx1
  have hx2 : ((c ⟨x, hx⟩ a₀ : ↥A) : ↥A ⧸ Z') = ((f₀ ⟨x, hx⟩)⁻¹ * a₀ : ↥A) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hx1
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx2
  have hw : (x * (a₀ : G) * x⁻¹)⁻¹ * ((u⁻¹ * (x * u * x⁻¹))⁻¹ * (a₀ : G)) ∈ Z := hx2
  have h6 : (u * (a₀ : G))⁻¹ * (x * (u * (a₀ : G)) * x⁻¹) =
      ((x * (a₀ : G) * x⁻¹)⁻¹ * ((u⁻¹ * (x * u * x⁻¹))⁻¹ * (a₀ : G)))⁻¹ := by
    group
  rw [h6]
  exact Z.inv_mem hw

end CFSG.GroupTheory

end
