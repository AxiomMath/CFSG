module
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
import CFSG.FeitThompson.Local.ClassTwoProductPowers
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsOfPGroups
import Mathlib.Data.Rat.Floor
import Mathlib.Data.SetLike.Fintype

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {p n : ℕ} {X : Type*} [Group X]

private theorem card_lt_card_of_lt {H K : Subgroup X} [Finite K] (h : H < K) :
    Nat.card H < Nat.card K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun he =>
    absurd (Subgroup.eq_of_le_of_card_ge h.le he.ge) h.ne

theorem mul_pow_eq_one_of_mem_center_of_odd (hp : Odd p) {a b : X} (ha : a ^ p = 1)
    (hb : b ^ p = 1) (hcen : b⁻¹ * a⁻¹ * b * a ∈ Subgroup.center X) : (a * b) ^ p = 1 := by
  have hcp : (b⁻¹ * a⁻¹ * b * a) ^ p = 1 := by
    rw [← inv_mul_inv_mul_mul_pow_left_of_mem_center hcen p, hb]
    group
  have hdvd : 2 ∣ p - 1 := (Nat.Odd.sub_odd hp odd_one).two_dvd
  rw [mul_pow_of_mem_center hcen p, ha, hb, Nat.mul_div_assoc p hdvd, pow_mul, hcp]
  simp

private theorem pow_eq_one_aux (hpp : p.Prime) (hp : Odd p) [Finite X] (hX : IsPGroup p X)
    (hcent : ∀ c ∈ commutator X, c ^ p = 1 → c ∈ Subgroup.center X) :
    ∀ m : ℕ, ∀ U : Subgroup X, Nat.card U ≤ m →
      U ≤ Subgroup.closure {g : X | g ∈ U ∧ g ^ p = 1} → ∀ g ∈ U, g ^ p = 1 := by
  intro m
  induction m with
  | zero => exact fun U hcard => absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ m ih =>
    intro U _ hU
    have key : ∀ a ∈ U, ∀ b ∈ U, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 := by
      intro a ha b hb hap hbp
      obtain htop | ⟨M, hM, haM⟩ :=
        IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.zpowers (⟨a, ha⟩ : U))
      ·
        have hb' : (⟨b, hb⟩ : U) ∈ Subgroup.zpowers (⟨a, ha⟩ : U) := htop ▸ Subgroup.mem_top _
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
        have hab : a ^ k = b := by simpa using congrArg U.subtype hk
        have hcomm : Commute a b := hab ▸ (Commute.refl a).zpow_right k
        rw [hcomm.mul_pow, hap, hbp, one_mul]
      ·
        have hMn : M.Normal := normal_of_isCoatom_of_isPGroup hpp (hX.to_subgroup U) hM
        have hMxle : M.map U.subtype ≤ U := Subgroup.map_subtype_le M
        have hMxne : M.map U.subtype ≠ U := fun h =>
          hM.1 <| eq_top_iff.mpr fun z _ => by
            obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp (h.ge z.2)
            exact (Subtype.ext hwz : w = z) ▸ hw
        have hgen : ∀ u ∈ U,
            u⁻¹ * a * u ∈ Subgroup.closure ((fun u : X => u⁻¹ * a * u) '' (U : Set X)) :=
          fun u hu => Subgroup.subset_closure ⟨u, hu, rfl⟩
        have hconj : ∀ u : X, (u⁻¹ * a * u) ^ p = u⁻¹ * a ^ p * u := fun u => by
          simpa using conj_pow (a := u⁻¹) (b := a) (i := p)
        have hVMx : Subgroup.closure ((fun u : X => u⁻¹ * a * u) '' (U : Set X))
            ≤ M.map U.subtype := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro g ⟨u, hu, rfl⟩
          refine ⟨(⟨u, hu⟩ : U)⁻¹ * (⟨a, ha⟩ : U) * (⟨u, hu⟩ : U), ?_, by simp⟩
          simpa using hMn.conj_mem _ (haM (Subgroup.mem_zpowers _)) (⟨u, hu⟩ : U)⁻¹
        have hVU : Subgroup.closure ((fun u : X => u⁻¹ * a * u) '' (U : Set X)) < U :=
          lt_of_le_of_ne (hVMx.trans hMxle) fun h =>
            hMxne (le_antisymm hMxle (h.ge.trans hVMx))
        have hcardV : Nat.card (Subgroup.closure ((fun u : X => u⁻¹ * a * u) '' (U : Set X)))
            ≤ m := by have := card_lt_card_of_lt hVU; omega
        have hVtor : ∀ g ∈ Subgroup.closure ((fun u : X => u⁻¹ * a * u) '' (U : Set X)),
            g ^ p = 1 := by
          refine ih _ hcardV ((Subgroup.closure_le _).mpr ?_)
          rintro g ⟨u, hu, rfl⟩
          exact Subgroup.subset_closure ⟨hgen u hu, by rw [hconj u, hap]; simp⟩
        have hcV : b⁻¹ * a⁻¹ * b * a
            ∈ Subgroup.closure ((fun u : X => u⁻¹ * a * u) '' (U : Set X)) := by
          rw [show b⁻¹ * a⁻¹ * b * a = (b⁻¹ * a * b)⁻¹ * (1⁻¹ * a * 1) by group]
          exact mul_mem (inv_mem (hgen b hb)) (hgen 1 (one_mem U))
        have hcComm : b⁻¹ * a⁻¹ * b * a ∈ commutator X := by
          rw [← commutatorElement_inv_inv b a, _root_.commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        exact mul_pow_eq_one_of_mem_center_of_odd hp hap hbp (hcent _ hcComm (hVtor _ hcV))
    have hall : ∀ z ∈ Subgroup.closure {g : X | g ∈ U ∧ g ^ p = 1}, z ∈ U ∧ z ^ p = 1 := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem w hw => exact hw
      | one => exact ⟨one_mem _, one_pow p⟩
      | mul c d _ _ hc hd => exact ⟨mul_mem hc.1 hd.1, key c hc.1 d hd.1 hc.2 hd.2⟩
      | inv c _ hc => exact ⟨inv_mem hc.1, by rw [inv_pow, hc.2, inv_one]⟩
    exact fun g hg => (hall g (hU hg)).2

theorem pow_eq_one_of_le_closure (hpp : p.Prime) (hp : Odd p) [Finite X] (hX : IsPGroup p X)
    (hcent : ∀ c ∈ commutator X, c ^ p = 1 → c ∈ Subgroup.center X) {U : Subgroup X}
    (hU : U ≤ Subgroup.closure {g : X | g ∈ U ∧ g ^ p = 1}) {g : X} (hg : g ∈ U) : g ^ p = 1 :=
  pow_eq_one_aux hpp hp hX hcent (Nat.card U) U le_rfl hU g hg

theorem pow_eq_one_of_omega1_eq_top (hpp : p.Prime) (hp : Odd p) [Finite X] (hX : IsPGroup p X)
    (hgen : omega1 p X = ⊤)
    (hcent : ∀ c ∈ commutator X, c ^ p = 1 → c ∈ Subgroup.center X) (x : X) : x ^ p = 1 := by
  refine pow_eq_one_of_le_closure hpp hp hX hcent (U := ⊤) ?_ (Subgroup.mem_top x)
  refine le_trans (le_of_eq hgen.symm) ?_
  rw [omega1_eq_closure]
  exact Subgroup.closure_mono fun y hy => ⟨Subgroup.mem_top y, hy⟩

theorem pow_eq_one_of_card_eq_pow (hpp : p.Prime) (hp : Odd p) (hX : Nat.card X = p ^ n)
    (hgen : omega1 p X = ⊤)
    (hcent : ∀ c ∈ commutator X, c ^ p = 1 → c ∈ Subgroup.center X) (x : X) : x ^ p = 1 :=
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; exact pow_ne_zero _ hpp.pos.ne')
  pow_eq_one_of_omega1_eq_top hpp hp (IsPGroup.of_card hX) hgen hcent x

theorem exponent_dvd_of_omega1_eq_top (hpp : p.Prime) (hp : Odd p) [Finite X]
    (hX : IsPGroup p X) (hgen : omega1 p X = ⊤)
    (hcent : ∀ c ∈ commutator X, c ^ p = 1 → c ∈ Subgroup.center X) :
    Monoid.exponent X ∣ p :=
  Monoid.exponent_dvd_of_forall_pow_eq_one (pow_eq_one_of_omega1_eq_top hpp hp hX hgen hcent)

theorem setOf_pow_eq_one_eq_univ_of_omega1_eq_top (hpp : p.Prime) (hp : Odd p) [Finite X]
    (hX : IsPGroup p X) (hgen : omega1 p X = ⊤)
    (hcent : ∀ c ∈ commutator X, c ^ p = 1 → c ∈ Subgroup.center X) :
    {x : X | x ^ p = 1} = Set.univ :=
  Set.eq_univ_of_forall (pow_eq_one_of_omega1_eq_top hpp hp hX hgen hcent)

end CFSG.FeitThompson
