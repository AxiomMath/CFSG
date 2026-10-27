module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStartBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiTwist

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1

section Torus

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem translation_of_affine {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 2 ≤ f) {κ : K}
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) {A : Subgroup (Equiv.Perm K)}
    (hA : IsPGroup 2 A) (haff : ∀ a ∈ A, ∃ ℓ : K →+ K, ∀ c, a c = a 0 + ℓ c)
    {δ : Equiv.Perm K} (hδ : ∀ c, δ c = κ * c) (hδA : ∀ a ∈ A, δ⁻¹ * a * δ ∈ A) :
    ∀ a ∈ A, ∀ c, a c = a 0 + c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlin : ∀ a ∈ A, ∀ c c', a (c + c') - a 0 = (a c - a 0) + (a c' - a 0) := by
    intro a ha c c'
    obtain ⟨ℓ, hℓ⟩ := haff a ha
    rw [hℓ, hℓ c, hℓ c', map_add]
    ring
  let act : MulAction A K :=
    { smul := fun a c => (a : Equiv.Perm K) c - (a : Equiv.Perm K) 0
      one_smul := fun c => by
        show (1 : Equiv.Perm K) c - (1 : Equiv.Perm K) 0 = c
        simp
      mul_smul := fun a b c => by
        show ((a : Equiv.Perm K) * b) c - ((a : Equiv.Perm K) * b) 0 =
          (a : Equiv.Perm K) ((b : Equiv.Perm K) c - (b : Equiv.Perm K) 0) - (a : Equiv.Perm K) 0
        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        have e1 := hlin a a.2 ((b : Equiv.Perm K) 0)
          ((b : Equiv.Perm K) c - (b : Equiv.Perm K) 0)
        rw [show (b : Equiv.Perm K) 0 + ((b : Equiv.Perm K) c - (b : Equiv.Perm K) 0) =
          (b : Equiv.Perm K) c by ring] at e1
        linear_combination e1 }
  have hsmul : ∀ (a : A) (c : K), a • c = (a : Equiv.Perm K) c - (a : Equiv.Perm K) 0 :=
    fun _ _ => rfl
  have hdvd : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self 2 (by omega)
  have h0 : (0 : K) ∈ MulAction.fixedPoints A K := fun a => by rw [hsmul, sub_self]
  obtain ⟨c₁, hc₁, hne⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point K hdvd h0
  have hc₁0 : c₁ ≠ 0 := fun h => hne h.symm
  have hκ0 : κ ≠ 0 := ne_zero_of_forall_pow_eq_of_two_le hK hf hκ
  have hstab : ∀ c ∈ MulAction.fixedPoints A K, κ * c ∈ MulAction.fixedPoints A K := by
    intro c hc a
    have ha' : δ⁻¹ * (a : Equiv.Perm K) * δ ∈ A := hδA a a.2
    have hfix := hc ⟨_, ha'⟩
    rw [hsmul] at hfix
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hfix
    have hδinv : ∀ y, δ⁻¹ y = κ⁻¹ * y := fun y => by
      rw [Equiv.Perm.inv_eq_iff_eq, hδ, mul_inv_cancel_left₀ hκ0]
    rw [hδ, hδ, mul_zero, hδinv, hδinv] at hfix
    rw [hsmul]
    have e := congrArg (fun z => κ * z) hfix
    rw [mul_sub, mul_inv_cancel_left₀ hκ0, mul_inv_cancel_left₀ hκ0] at e
    exact e
  have hall : ∀ c, c ∈ MulAction.fixedPoints A K := by
    intro c
    by_cases hc : c = 0
    · rw [hc]
      exact h0
    obtain ⟨m, hm⟩ := hκ (c / c₁) (div_ne_zero hc hc₁0)
    have key : ∀ n : ℕ, κ ^ n * c₁ ∈ MulAction.fixedPoints A K := by
      intro n
      induction n with
      | zero => simpa using hc₁
      | succ n ih => rw [pow_succ', mul_assoc]; exact hstab _ ih
    have := key m
    rwa [hm, div_mul_cancel₀ c hc₁0] at this
  intro a ha c
  have hfix := hall c ⟨a, ha⟩
  rw [hsmul] at hfix
  linear_combination hfix

end Torus

section Conj

variable {G : Type*} [Group G]

theorem map_conj_mul (H : Subgroup G) (x y : G) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      H.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    rwa [inv_inv] at this

theorem mem_normalizer_of_map_le {H : Subgroup G} [Finite H] {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) := by
  have heq : H.map (MulAut.conj g).toMonoidHom = H := by
    have : Finite (H.map (MulAut.conj g).toMonoidHom) := Finite.of_injective _
      (Subgroup.inclusion_injective hg)
    exact Subgroup.eq_of_le_of_card_ge hg
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  have hx' : x ∈ H.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  exact hy

@[instance_reducible]
noncomputable def familyAction {N : Subgroup G} {K : Type*} (F : K → Subgroup G)
    (hinv : ∀ n ∈ N, ∀ c, ∃ c', (F c).map (MulAut.conj n).toMonoidHom = F c')
    (hinj : Function.Injective F) : MulAction N K where
  smul n c := (hinv n n.2 c).choose
  one_smul c := hinj (by
    show F (hinv _ (1 : N).2 c).choose = F c
    rw [← (hinv _ (1 : N).2 c).choose_spec]
    show (F c).map (MulAut.conj (1 : G)).toMonoidHom = F c
    rw [map_one]
    exact Subgroup.map_id _)
  mul_smul n m c := hinj (by
    show F (hinv _ (n * m).2 c).choose = F (hinv _ n.2 (hinv _ m.2 c).choose).choose
    rw [← (hinv _ (n * m).2 c).choose_spec, ← (hinv _ n.2 _).choose_spec,
      ← (hinv _ m.2 c).choose_spec, map_conj_mul]
    rfl)

noncomputable def familyPerm {N : Subgroup G} {K : Type*} (F : K → Subgroup G)
    (hinv : ∀ n ∈ N, ∀ c, ∃ c', (F c).map (MulAut.conj n).toMonoidHom = F c')
    (hinj : Function.Injective F) : N →* Equiv.Perm K :=
  @MulAction.toPermHom N K _ (familyAction F hinv hinj)

theorem familyPerm_spec {N : Subgroup G} {K : Type*} (F : K → Subgroup G)
    (hinv : ∀ n ∈ N, ∀ c, ∃ c', (F c).map (MulAut.conj n).toMonoidHom = F c')
    (hinj : Function.Injective F) (n : N) (c : K) :
    (F c).map (MulAut.conj (n : G)).toMonoidHom = F (familyPerm F hinv hinj n c) :=
  (hinv n n.2 c).choose_spec

end Conj

end SzC1

end CFSG.SeitzReduction.RankOne
