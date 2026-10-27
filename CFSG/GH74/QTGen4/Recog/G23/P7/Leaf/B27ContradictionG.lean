module

public import CFSG.GroupTheory.FourGroupOddOrderIdentity
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionA
public import CFSG.Quasithin.Recognition.G23TypeDefs
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A
open CFSG.GroupTheory

variable {G : Type} [Group G]

noncomputable def conjMDMA (E S : Subgroup G) (hE : ∀ a ∈ E, ∀ x ∈ S, a * x * a⁻¹ ∈ S) :
    MulDistribMulAction E S where
  smul a x := ⟨(a : G) * (x : G) * (a : G)⁻¹, hE a a.2 x x.2⟩
  one_smul x := by
    apply Subtype.ext
    show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
    simp
  mul_smul a b x := by
    apply Subtype.ext
    show ((a : G) * (b : G)) * (x : G) * ((a : G) * (b : G))⁻¹ =
      (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc, mul_inv_rev]
  smul_one a := by
    apply Subtype.ext
    show (a : G) * (1 : G) * (a : G)⁻¹ = 1
    simp
  smul_mul a x y := by
    apply Subtype.ext
    show (a : G) * ((x : G) * (y : G)) * (a : G)⁻¹ =
      ((a : G) * (x : G) * (a : G)⁻¹) * ((a : G) * (y : G) * (a : G)⁻¹)
    simp [mul_assoc]

theorem card_fixed_zpowers {E S : Subgroup G} [M : MulDistribMulAction E S]
    (hM : ∀ (a : E) (x : S), ((a • x : S) : G) = (a : G) * (x : G) * (a : G)⁻¹) (a : E) :
    Nat.card ↥(FixedPoints.subgroup (Subgroup.zpowers a) S) =
      Nat.card ↥(Subgroup.centralizer {(a : G)} ⊓ S) := by
  have key : ∀ x : S, x ∈ FixedPoints.subgroup (Subgroup.zpowers a) S ↔
      (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
    intro x
    rw [FixedPoints.mem_subgroup]
    constructor
    · intro h
      have h1 := h ⟨a, Subgroup.mem_zpowers a⟩
      have h2 : ((a • x : S) : G) = (x : G) := congrArg (fun y : S => (y : G)) h1
      rw [hM] at h2
      exact h2
    · intro h m
      apply Subtype.ext
      have hmx : ((m • x : S) : G) = ((((m : E)) • x : S) : G) := rfl
      rw [hmx, hM]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp m.2
      have hc : Commute (a : G) (x : G) := by
        show (a : G) * (x : G) = (x : G) * (a : G)
        exact mul_inv_eq_iff_eq_mul.mp h
      have hm : ((m : E) : G) = (a : G) ^ k := by
        rw [← hk]
        rfl
      rw [hm]
      have hcz : Commute ((a : G) ^ k) (x : G) := hc.zpow_left k
      rw [hcz.eq]
      group
  let f : FixedPoints.subgroup (Subgroup.zpowers a) S ≃
      ↥(Subgroup.centralizer {(a : G)} ⊓ S) :=
    { toFun := fun x => ⟨(x.1 : G), by
        refine Subgroup.mem_inf.mpr ⟨?_, x.1.2⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact mul_inv_eq_iff_eq_mul.mp ((key x.1).mp x.2)⟩
      invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).2⟩, by
        have hy := (Subgroup.mem_inf.mp y.2).1
        rw [Subgroup.mem_centralizer_iff] at hy
        exact (key ⟨(y : G), (Subgroup.mem_inf.mp y.2).2⟩).mpr
          (mul_inv_eq_iff_eq_mul.mpr (hy (a : G) (Set.mem_singleton _)))⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  exact Nat.card_congr f

theorem four_group_bw [Finite G] (E S : Subgroup G) (hE4 : Nat.card E = 4)
    (hEsq : ∀ x ∈ E, x * x = 1) (hnorm : ∀ a ∈ E, ∀ x ∈ S, a * x * a⁻¹ ∈ S)
    (hS : Odd (Nat.card S)) (hS729 : 729 ≤ Nat.card S)
    (hcent : ∀ a ∈ E, a ≠ 1 → Nat.card ↥(Subgroup.centralizer {a} ⊓ S) ∣ 9)
    (t : G) (ht : t ∈ E) (ht1 : t ≠ 1) :
    Nat.card S = 729 ∧ Nat.card ↥(Subgroup.centralizer {t} ⊓ S) = 9 := by
  classical
  letI M : MulDistribMulAction E S := conjMDMA E S hnorm
  have hM : ∀ (a : E) (x : S), ((a • x : S) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun a x => rfl
  haveI : IsKleinFour E := isKleinFour_of_sq hE4 (fun x => Subtype.ext (hEsq x.1 x.2))
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨hid, -⟩ := odd_group_four_group_centralizer_order_identity (A := E) (X := S) hS
  set f : E → ℕ := fun a => Nat.card ↥(FixedPoints.subgroup (Subgroup.zpowers a) S) with hf
  have hF : ∀ a : E, a ≠ 1 → f a ∣ 9 := by
    intro a ha
    rw [hf]
    dsimp only
    rw [card_fixed_zpowers hM a]
    exact hcent a a.2 (fun h => ha (Subtype.ext h))
  have hcard3 : (Finset.univ.erase (1 : E)).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hE4]
  have hle : ∀ a ∈ Finset.univ.erase (1 : E), f a ≤ 9 := by
    intro a ha
    exact Nat.le_of_dvd (by norm_num) (hF a (Finset.ne_of_mem_erase ha))
  have hprod_le : ∏ a ∈ Finset.univ.erase (1 : E), f a ≤ 9 ^ 3 := by
    have := Finset.prod_le_pow_card (Finset.univ.erase (1 : E)) f 9 hle
    rwa [hcard3] at this
  have hP : 729 ≤ ∏ a ∈ Finset.univ.erase (1 : E), f a := by
    have hid' : Nat.card ↥S * Nat.card ↥(FixedPoints.subgroup E S) ^ 2 =
        ∏ a ∈ Finset.univ.erase (1 : E), f a := hid
    have hc1 : 1 ≤ Nat.card ↥(FixedPoints.subgroup E S) := Nat.card_pos
    have hc2 : 1 ≤ Nat.card ↥(FixedPoints.subgroup E S) ^ 2 := Nat.one_le_pow _ _ hc1
    nlinarith
  have hSle : Nat.card ↥S ≤ 729 := by
    have hc1 : 1 ≤ Nat.card ↥(FixedPoints.subgroup E S) := Nat.card_pos
    have hc2 : 1 ≤ Nat.card ↥(FixedPoints.subgroup E S) ^ 2 := Nat.one_le_pow _ _ hc1
    have hid' : Nat.card ↥S * Nat.card ↥(FixedPoints.subgroup E S) ^ 2 =
        ∏ a ∈ Finset.univ.erase (1 : E), f a := hid
    nlinarith
  set tE : E := ⟨t, ht⟩ with htE
  have htmem : tE ∈ Finset.univ.erase (1 : E) :=
    Finset.mem_erase.mpr ⟨fun h => ht1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase (1 : E)) f htmem] at hP hprod_le
  have hrest : ∏ a ∈ (Finset.univ.erase (1 : E)).erase tE, f a ≤ 9 ^ 2 := by
    have := Finset.prod_le_pow_card ((Finset.univ.erase (1 : E)).erase tE) f 9
      (fun a ha => hle a (Finset.mem_of_mem_erase ha))
    have hc2 : ((Finset.univ.erase (1 : E)).erase tE).card = 2 := by
      rw [Finset.card_erase_of_mem htmem, hcard3]
    rwa [hc2] at this
  have hft : f tE ≤ 9 := hle tE htmem
  have hft9 : f tE = 9 := by
    have hpos : 0 < ∏ a ∈ (Finset.univ.erase (1 : E)).erase tE, f a := by
      apply Finset.prod_pos
      intro a ha
      have ha1 : a ≠ 1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha)
      exact Nat.card_pos
    nlinarith
  have hfix : Nat.card ↥(FixedPoints.subgroup (Subgroup.zpowers tE) S) =
      Nat.card ↥(Subgroup.centralizer {t} ⊓ S) := card_fixed_zpowers hM tE
  refine ⟨by omega, ?_⟩
  rw [← hfix]
  exact hft9

end CFSG.GH74.QTGen4.Recog.G23.P7
