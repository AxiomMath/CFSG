module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Prop
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2 SmallL3Ne3 SmallU3Ne3)
open scoped MatrixGroups commutatorElement

theorem false_of_aut_core_lu {r : ℕ} (hL3 : SocF4L3 r) (hU3 : SocF4U3 r) (hr : 4 ≤ r) {A : Type}
    [Group A] [Finite A] (T : Subgroup A) [T.Normal] (hT : IsSimpleGroup ↥T)
    (hab : ∃ a b : ↥T, a * b ≠ b * a) (hC : Subgroup.centralizer (T : Set A) = ⊥)
    (hE : EdgelessFamily ↥T) {R : Subgroup A} {S : Sylow 2 R} {z : A} (hd : TightDatum R S z)
    (hc : TightClsR r A R S z) (hnO : ¬ TightInO2 z) (hed : TightEdgeless R)
    (hLU : SmallL3Ne3 ↥T ∨ SmallU3Ne3 ↥T) {U N : Subgroup (MulAut ↥T)}
    (hNodd : Odd (Nat.card ↥N)) (hUN : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ N) {g : MulAut ↥T} (hgU : g ∈ U)
    (hgC : g ∈ autCentOf T (sylowSet S)) (hg8 : orderOf g = 8) {Hh : Subgroup (MulAut ↥T)}
    (hHU : ∀ h ∈ Hh, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (hSL : socSL T z ≤ Hh) : False := by
  classical
  have hcl : socSL T z ≤ autCentOf T (sylowSet S) ∧
      autCentOf T (sylowSet S) ≤ Subgroup.normalizer ((socSL T z : Subgroup (MulAut ↥T)) :
        Set (MulAut ↥T)) ∧
      Odd ((socSL T z).relIndex (autCentOf T (sylowSet S))) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧ 4 ≤ Nat.card K ∧
        Nonempty (↥(socSL T z) ≃* SL(2, K)) := by
    rcases hLU with hL3' | hU3'
    · exact hL3 hr A T hT hab hC hE R S z hd hc hnO hed hL3'
    · exact hU3 hr A T hT hab hC hE R S z hd hc hnO hed hU3'
  obtain ⟨hle, hnorm, hodd, K, _, _, hKodd, hK4, ⟨eE⟩⟩ := hcl
  have hg2 : g ^ 2 ^ 3 = 1 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hg8]
    exact pow_orderOf_eq_one g
  have hgS : g ∈ socSL T z := mem_of_odd_relIndex hnorm hodd hgC hg2
  have hMn : ((U ⊓ socSL T z).subgroupOf (socSL T z)).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxU, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact hHU _ (hSL y.2) _ hxU
    · exact (socSL T z).mul_mem ((socSL T z).mul_mem y.2 hxS) ((socSL T z).inv_mem y.2)
  have hordS : orderOf (⟨g, hgS⟩ : ↥(socSL T z)) = 8 := by rw [Subgroup.orderOf_mk, hg8]
  have hmem : (⟨g, hgS⟩ : ↥(socSL T z)) ∈ (U ⊓ socSL T z).subgroupOf (socSL T z) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hgU, hgS⟩)
  have hSLU : socSL T z ≤ U := by
    rcases normal_cases_of_equiv_sl2 hK4 eE _ hMn with h0 | hcn | htop
    · exfalso
      rw [h0, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hordS
      omega
    · exfalso
      rw [hcn] at hmem
      have h2 : orderOf (⟨(⟨g, hgS⟩ : ↥(socSL T z)), hmem⟩ : ↥(Subgroup.center ↥(socSL T z))) ∣ 2 := by
        rw [← natCard_center_of_equiv_sl2 hKodd eE]
        exact orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hordS] at h2
      omega
    · intro x hx
      have : (⟨x, hx⟩ : ↥(socSL T z)) ∈ (U ⊓ socSL T z).subgroupOf (socSL T z) :=
        htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).1
  haveI : Group.IsPerfect ↥(socSL T z) := isPerfect_of_equiv_sl2 hK4 eE
  have hSLN : socSL T z ≤ N := by
    have h1 : ⁅socSL T z, socSL T z⁆ = socSL T z := Subgroup.commutator_eq_self
    rw [← h1, Subgroup.commutator_le]
    intro a ha b hb
    exact hUN a (hSLU ha) b (hSLU hb)
  have hcard : Nat.card ↥(socSL T z) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hSLN
  have hSLodd : Odd (Nat.card ↥(socSL T z)) := hNodd.of_dvd_nat hcard
  have h2 : 2 ∣ Nat.card ↥(socSL T z) := by
    have ho : orderOf (eE.symm (-1 : SL(2, K))) = 2 :=
      (orderOf_eq_two_iff_of_equiv_sl2 hKodd eE _).mpr rfl
    rw [← ho]
    exact orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.mpr hSLodd) (even_iff_two_dvd.mpr h2)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
