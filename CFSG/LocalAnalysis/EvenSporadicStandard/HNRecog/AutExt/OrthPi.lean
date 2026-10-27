module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthFin

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

private lemma pow_mod_two {C : Type*} [Group C] {y : C} (hy : y * y = 1) (n : ℕ) :
    y ^ (n % 2) = y ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul, pow_two, hy, one_pow, mul_one]

theorem exists_pi {G : Type} [Group G] {K M : Subgroup G}
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hsq : ∀ x ∈ M, x * x = 1)
    (hnorm : ∀ l : ↥K, ∀ x ∈ M, (l : G) * x * (l : G)⁻¹ ∈ M)
    {s : Fin 5 → G} (hs : ∀ i, s i ∈ M) {ρ : ↥K →* Perm (Fin 5)}
    (hρ : ∀ (l : ↥K) (i : Fin 5), (l : G) * s i * (l : G)⁻¹ = s (ρ l i)) :
    ∃ π : Fv5 → G, (∀ f, π f ∈ M) ∧ (∀ f g, π (f + g) = π f * π g) ∧
      (∀ i, π (Pi.single i 1) = s i) ∧
      ∀ (l : ↥K) (f : Fv5), (l : G) * π f * (l : G)⁻¹ = π (fv5Act (ρ l) f) := by
  classical
  letI : CommGroup ↥M :=
    { (inferInstance : Group ↥M) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let x : Fin 5 → ↥M := fun i => ⟨s i, hs i⟩
  have hx : ∀ i, x i * x i = 1 := fun i => Subtype.ext (hsq (s i) (hs i))
  let piM : Fv5 → ↥M := fun f => ∏ i, x i ^ (f i).val
  have hpiM_add : ∀ f g : Fv5, piM (f + g) = piM f * piM g := by
    intro f g
    show (∏ i, x i ^ ((f + g) i).val) =
      (∏ i, x i ^ (f i).val) * (∏ i, x i ^ (g i).val)
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Pi.add_apply, ZMod.val_add, pow_mod_two (hx i), pow_add]
  have hpiM_single : ∀ i : Fin 5, piM (Pi.single i 1) = x i := by
    intro i
    show (∏ j, x j ^ ((Pi.single i (1 : ZMod 2) : Fv5) j).val) = x i
    rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i) (fun b _ hb => by
      rw [Pi.single_eq_of_ne hb, ZMod.val_zero, pow_zero])]
    rw [Pi.single_eq_same, ZMod.val_one'' (n := 2) (by decide), pow_one]
  refine ⟨fun f => (piM f : G), fun f => (piM f).2, ?_, ?_, ?_⟩
  · intro f g
    change ((piM (f + g) : ↥M) : G) =
      ((piM f : ↥M) : G) * ((piM g : ↥M) : G)
    rw [hpiM_add f g]
    rfl
  · intro i
    change ((piM (Pi.single i 1) : ↥M) : G) = s i
    rw [hpiM_single i]
  · intro l f
    let c : ↥M →* ↥M :=
      { toFun := fun y => ⟨(l : G) * (y : G) * (l : G)⁻¹, hnorm l y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y z => Subtype.ext (by
          show (l : G) * ((y : G) * (z : G)) * (l : G)⁻¹ =
            ((l : G) * (y : G) * (l : G)⁻¹) * ((l : G) * (z : G) * (l : G)⁻¹)
          exact conj_mul.symm) }
    have hcx : ∀ i, c (x i) = x (ρ l i) := fun i => Subtype.ext (hρ l i)
    have hcpi : c (piM f) = piM (fv5Act (ρ l) f) := by
      calc c (piM f) = ∏ i, c (x i) ^ (f i).val := by
            show c (∏ i, x i ^ (f i).val) = ∏ i, c (x i) ^ (f i).val
            rw [map_prod]
            apply Finset.prod_congr rfl
            intro i _
            rw [map_pow]
        _ = ∏ i, x (ρ l i) ^ (f i).val := by
            apply Finset.prod_congr rfl
            intro i _
            rw [hcx i]
        _ = piM (fv5Act (ρ l) f) := by
            show (∏ i, x (ρ l i) ^ (f i).val) = ∏ j, x j ^ (f ((ρ l)⁻¹ j)).val
            simpa using Equiv.prod_comp (ρ l) (fun j => x j ^ (f ((ρ l)⁻¹ j)).val)
    change (l : G) * ((piM f : ↥M) : G) * (l : G)⁻¹ =
      ((piM (fv5Act (ρ l) f) : ↥M) : G)
    rw [← hcpi]
    rfl

end CFSG.EvenSporadicStandard.HNRecog.Section4
