module

public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p : ℕ} {R : Type*} [Group R]

theorem omega1Subgroup_top_eq_omega1 (p : ℕ) (R : Type*) [Group R] :
    omega1Subgroup p (⊤ : Subgroup R) = omega1 p R :=
  le_antisymm (omega1Subgroup_le fun _ _ hxp => mem_omega1_of_pow_eq_one hxp)
    (omega1_le fun _ hxp => mem_omega1Subgroup (Subgroup.mem_top _) hxp)

theorem inf_centralizer_omega1_eq_map_center (p : ℕ) (R : Type*) [Group R] :
    omega1 p R ⊓ centralizer (omega1 p R : Set R)
      = (center ↥(omega1 p R)).map (omega1 p R).subtype :=
  (map_center_subtype _).symm

theorem card_map_center_omega1 (hp : p.Prime) (hB : Nat.card ↥(omega1 p R) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(omega1 p R)) :
    Nat.card ↥((center ↥(omega1 p R)).map (omega1 p R).subtype) = p := by
  rw [← Nat.card_congr (equivMapOfInjective (center ↥(omega1 p R)) (omega1 p R).subtype
      (omega1 p R).subtype_injective).toEquiv]
  exact card_center_of_card_eq_prime_cube hp hB hnab

theorem mem_map_center_omega1_of_pow_eq_one {x : R}
    (hxC : x ∈ centralizer (omega1 p R : Set R)) (hxp : x ^ p = 1) :
    x ∈ (center ↥(omega1 p R)).map (omega1 p R).subtype := by
  rw [← inf_centralizer_omega1_eq_map_center]
  exact ⟨mem_omega1_of_pow_eq_one hxp, hxC⟩

theorem map_center_omega1_le_centralizer (p : ℕ) (R : Type*) [Group R] :
    (center ↥(omega1 p R)).map (omega1 p R).subtype ≤ centralizer (omega1 p R : Set R) := by
  rw [← inf_centralizer_omega1_eq_map_center]; exact inf_le_right

theorem map_center_omega1_le_omega1 (p : ℕ) (R : Type*) [Group R] :
    (center ↥(omega1 p R)).map (omega1 p R).subtype ≤ omega1 p R := by
  rw [← inf_centralizer_omega1_eq_map_center]; exact inf_le_left

theorem coe_pTorsion_centralizer_omega1 (hexp : ∀ b ∈ omega1 p R, b ^ p = 1) :
    {x ∈ (centralizer (omega1 p R : Set R) : Set R) | x ^ p = 1}
      = ((center ↥(omega1 p R)).map (omega1 p R).subtype : Set R) :=
  Set.Subset.antisymm (fun _ hx => mem_map_center_omega1_of_pow_eq_one hx.1 hx.2)
    fun x hx => ⟨map_center_omega1_le_centralizer p R hx,
      hexp x (map_center_omega1_le_omega1 p R hx)⟩

theorem omega1Subgroup_centralizer_omega1 (hexp : ∀ b ∈ omega1 p R, b ^ p = 1) :
    omega1Subgroup p (centralizer (omega1 p R : Set R))
      = (center ↥(omega1 p R)).map (omega1 p R).subtype := by
  rw [omega1Subgroup_eq_closure, coe_pTorsion_centralizer_omega1 hexp, Subgroup.closure_eq]

theorem nontrivial_centralizer_omega1 (hp : p.Prime) (hB : Nat.card ↥(omega1 p R) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(omega1 p R)) :
    Nontrivial ↥(centralizer (omega1 p R : Set R)) := by
  refine (Subgroup.nontrivial_iff_ne_bot _).2 fun hbot => ?_
  have h := Subgroup.card_dvd_of_le (map_center_omega1_le_centralizer p R)
  rw [card_map_center_omega1 hp hB hnab, hbot, Subgroup.card_bot] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

theorem isCyclic_centralizer_omega1 [Finite R] (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R)) :
    IsCyclic ↥(centralizer (omega1 p R : Set R)) := by
  by_contra hnc
  set C := centralizer (omega1 p R : Set R) with hC
  have hncTop : ¬ IsCyclic (⊤ : Subgroup ↥C) := fun _ =>
    hnc (isCyclic_of_surjective (⊤ : Subgroup ↥C).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
  obtain ⟨E, -, -, ⟨f⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd
    (hR.to_subgroup C) (⊤ : Subgroup ↥C) hncTop
  have hEexp : ∀ x : ↥C, ∀ hx : x ∈ E, ((x : ↥C) : R) ^ p = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥E) ^ p = 1 := by
      apply f.injective
      rw [map_pow, map_one, pow_eq_one_pi_multiplicative_zmod]
    exact congrArg (Subgroup.subtype C) (congrArg (Subgroup.subtype E) h1)
  have hle : E.map C.subtype ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype := by
    rintro y ⟨x, hx, rfl⟩
    exact mem_map_center_omega1_of_pow_eq_one x.2 (hEexp x hx)
  have hdvd : p ^ 2 ∣ p := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [← Nat.card_congr (equivMapOfInjective E C.subtype C.subtype_injective).toEquiv,
      Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod,
      card_map_center_omega1 hp hB hnab] at h
  have hle2 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
  have h2 := hp.two_le
  nlinarith

theorem characteristic_isCyclic_centralizer_omega1_of_card_eq_prime_cube [Finite R] (hp : p.Prime)
    (hodd : Odd p) (hR : IsPGroup p R) (hB : Nat.card ↥(omega1 p R) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(omega1 p R)) (hexp : ∀ b ∈ omega1 p R, b ^ p = 1) :
    (omega1 p R).Characteristic ∧ (centralizer (omega1 p R : Set R)).Characteristic ∧
      IsCyclic ↥(centralizer (omega1 p R : Set R)) ∧
      Nontrivial ↥(centralizer (omega1 p R : Set R)) ∧
      omega1 p R ⊓ centralizer (omega1 p R : Set R)
        = (center ↥(omega1 p R)).map (omega1 p R).subtype ∧
      omega1Subgroup p (centralizer (omega1 p R : Set R))
        = (center ↥(omega1 p R)).map (omega1 p R).subtype ∧
      Nat.card ↥((center ↥(omega1 p R)).map (omega1 p R).subtype) = p :=
  ⟨omega1_characteristic, Subgroup.characteristic_centralizer,
    isCyclic_centralizer_omega1 hp hodd hR hB hnab, nontrivial_centralizer_omega1 hp hB hnab,
    inf_centralizer_omega1_eq_map_center p R, omega1Subgroup_centralizer_omega1 hexp,
    card_map_center_omega1 hp hB hnab⟩

end

end CFSG.FeitThompson
