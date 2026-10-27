module

public import CFSG.ClassicalInvolution.Q3.TL3C11R

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic QuaternionGroup

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem not_tightActs3_of_four_le {r : ℕ} (hr : 4 ≤ r) (hd : TightDatum R S t)
    (hS : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) : ¬ TightActs3 R t := by
  rintro ⟨x, k, hxC, hx3, hxR⟩
  obtain ⟨e8⟩ := tl3_nonempty_mulEquiv_q8 S hd.quat hd.twoGroup hd.le_normalizer hxC hx3 hxR
  obtain ⟨e'⟩ := hS
  have hcard := Nat.card_congr (e8.symm.trans e').toEquiv
  have hne : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, QuaternionGroup.card,
    QuaternionGroup.card] at hcard
  have h2 : 2 ^ (r - 2) = 2 ^ 1 := by omega
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

theorem not_goodThreeElement_of_four_le {r : ℕ} (hr : 4 ≤ r) (hd : TightDatum R S t)
    (hS : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ¬ GoodThreeElement R t := by
  rintro ⟨x, k, hxC, hx3, hxR, -⟩
  exact not_tightActs3_of_four_le hr hd hS ⟨x, k, hxC, hx3, hxR⟩

theorem tightEx_of_edgeless {r : ℕ} (hr : 4 ≤ r) (hd : TightDatum R S t)
    (hc : TightClsR r Y R S t) (he : TightEdgeless R) : TightEx Y R S t :=
  Or.inr (Or.inl ⟨he, not_tightActs3_of_four_le hr hd hc.1⟩)

@[expose] def TightSmallBaseR (r : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t →
    TightClsR r Y R S t → ¬ TightInO2 t → TightFStarQuasisimple Y →
      TwoSubgroupsFourGenerated (genFittingFStar Y) → TightEdgeless R

theorem TightSmallBaseR.tightEx {r : ℕ} (hr : 4 ≤ r) (h : TightSmallBaseR r) (hd : TightDatum R S t)
    (hc : TightClsR r Y R S t) (hE2 : ¬ TightInO2 t) (hQ : TightFStarQuasisimple Y)
    (hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)) : TightEx Y R S t :=
  tightEx_of_edgeless hr hd hc (h Y R S t hd hc hE2 hQ hsmall)

@[expose] def NoDatum4 (F : Type) [Group F] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], Nonempty (↥N ≃* F) →
    Subgroup.centralizer (N : Set G) = ⊥ → TwoSubgroupsFourGenerated N →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → False

theorem NoDatum4.of_mulEquiv {F F' : Type} [Group F] [Group F'] (h : NoDatum4 F) (e : F' ≃* F) :
    NoDatum4 F' :=
  fun G _ _ N _ ⟨e'⟩ hC hgen R S t hD => h G N ⟨e'.trans e⟩ hC hgen R S t hD

theorem NoDatum4.of_nobq {F : Type} [Group F] (h : Nobq.NoDatum F) : NoDatum4 F := by
  intro G _ _ N _ e hC _ R S t hd
  obtain ⟨r, hr, hS⟩ := hd.quat
  exact h G N e hC R S r hr hS t hd.mem hd.order hd.cent hd.normal

@[expose] def SmallLeafR (r : ℕ) (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)],
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) →
    TwoSubgroupsFourGenerated ↥(genFittingFStar Y) → P ↥(genFittingFStar Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightClsR r Y R S t →
      ¬ TightInO2 t → TightEdgeless R

theorem SmallLeafR.of_noDatum4 {r : ℕ} {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → NoDatum4 F) : SmallLeafR r P := by
  intro Y _ _ _ hnab hG hPF R S t hd _ _
  exfalso
  have := genFittingFStar_normal Y
  exact h _ hPF Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) hG R S t hd

theorem quaternionGroup_a_inv {n : ℕ} (i : ZMod (2 * n)) :
    (a i : QuaternionGroup n)⁻¹ = a (-i) := rfl

theorem quaternionGroup_xa_inv {n : ℕ} (i : ZMod (2 * n)) :
    (xa i : QuaternionGroup n)⁻¹ = xa ((n : ZMod (2 * n)) + i) := rfl

theorem quaternionGroup_exists_conj_eq_inv {n : ℕ} [NeZero n] (hn : Even n)
    (g : QuaternionGroup n) : ∃ h : QuaternionGroup n, h * g * h⁻¹ = g⁻¹ := by
  obtain ⟨m, hm⟩ := hn
  have hnc : (n : ZMod (2 * n)) = (m : ZMod (2 * n)) + m := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (2 * n)) hm
  have h0 : (2 : ZMod (2 * n)) * (n : ZMod (2 * n)) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * n)
  cases g with
  | a i =>
    refine ⟨xa 0, ?_⟩
    rw [quaternionGroup_a_inv, quaternionGroup_xa_inv, xa_mul_a, xa_mul_xa]
    congr 1
    linear_combination h0
  | xa i =>
    refine ⟨a (m : ZMod (2 * n)), ?_⟩
    rw [quaternionGroup_a_inv, quaternionGroup_xa_inv, a_mul_xa, xa_mul_a]
    congr 1
    linear_combination (-1 : ZMod (2 * n)) * h0 + hnc

end CFSG.CGT.PushingUpLit.SolKNA.R4
