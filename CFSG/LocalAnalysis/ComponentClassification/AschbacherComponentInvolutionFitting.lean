module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayer

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def fittingOddCoreImage (G : Type*) [Group G] : Subgroup G :=
  (_root_.CFSG.oddCore (Fitting.subgroup G)).map (Fitting.subgroup G).subtype

theorem fitting_odd_core_eq_native (G : Type*) [Group G] :
    fittingOddCoreImage G =
      (componentClassificationOddCore (Fitting.subgroup G)).map (Fitting.subgroup G).subtype := rfl

theorem fitting_odd_core_normal (G : Type*) [Group G] :
    (fittingOddCoreImage G).Normal := by
  let : (Fitting.subgroup G).Normal := Fitting.normal G
  let : (componentClassificationOddCore (Fitting.subgroup G)).Characteristic :=
    OddCore.characteristic _
  rw [fitting_odd_core_eq_native]
  exact ConjAct.normal_of_characteristic_of_normal

variable [Finite G]

theorem fitting_odd_core_odd (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (fittingOddCoreImage G)) := by
  rw [fitting_odd_core_eq_native, Subgroup.card_subtype]
  exact OddCore.odd_card _

theorem odd_prime_core_le_fitting_odd_core (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    PrimeCore.subgroup p G ≤ fittingOddCoreImage G := by
  let F := Fitting.subgroup G
  let Q := PrimeCore.subgroup p G
  have hQF : Q ≤ F := PrimeCore.le_fitting p G
  let : Q.Normal := PrimeCore.normal p G
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨n, hn⟩ := (PrimeCore.isPGroup p G).exists_card_eq
    rw [hn]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have hlocalOdd : Odd (Nat.card (Q.subgroupOf F)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQF).toEquiv]
    exact hQodd
  have hle := OddCore.maximal F (Q.subgroupOf F) inferInstance hlocalOdd
  have hmap := Subgroup.map_mono (f := F.subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hQF] at hmap
  exact hmap

theorem involution_component_centralizes_fitting (a : G) (ha : orderOf a = 2)
    (K : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hodd : ⁅K, fittingOddCoreImage G⁆ = ⊥) : ⁅K, Fitting.subgroup G⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply Subgroup.le_centralizer_iff.mpr
  rw [PrimeCore.fitting_eq_join]
  apply iSup_le
  intro p
  let : Fact p.val.Prime := ⟨p.property⟩
  by_cases hp : p.val = 2
  · rw [hp]
    let : (PrimeCore.subgroup 2 G).Normal := PrimeCore.normal 2 G
    have hle := InvolutionLayer.component_centralizes_normal_two a ha
      (PrimeCore.subgroup 2 G) (PrimeCore.isPGroup 2 G) (K.subgroupOf _) hK
    rw [Subgroup.map_subgroupOf_eq_of_le hKC] at hle
    exact Subgroup.le_centralizer_iff.mp hle
  · have hcommutes : K ≤ Subgroup.centralizer ((PrimeCore.subgroup p.val G : Subgroup G) : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hodd).trans
        (Subgroup.centralizer_le (odd_prime_core_le_fitting_odd_core p.val hp))
    exact Subgroup.le_centralizer_iff.mp hcommutes

theorem perfect_layer_centralizer_product_absorption (K : Subgroup G)
    [Group.IsPerfect K]
    (hproduct : K ≤ Layer.subgroup G ⊔ Subgroup.centralizer (Layer.subgroup G : Set G))
    (hKF : ⁅K, Fitting.subgroup G⁆ = ⊥) : K ≤ Layer.subgroup G := by
  let E := Layer.subgroup G
  let F := Fitting.subgroup G
  let : E.Normal := Layer.normal G
  let : F.Normal := Fitting.normal G
  let : Group.IsSolvable F := Fitting.solvable G
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact GeneralizedFitting.fitting_layer_commute G)
  have hKG : K ≤ GeneralizedFitting.subgroup G := by
    intro k hk
    obtain ⟨e, he, c, hc, hec⟩ := Subgroup.mem_sup_of_normal_left.mp (hproduct hk)
    have hcF : c ∈ Subgroup.centralizer (F : Set G) := by
      have hmem := (Subgroup.centralizer (F : Set G)).mul_mem
        ((Subgroup.centralizer (F : Set G)).inv_mem (hEF he))
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKF hk)
      rw [← hec] at hmem
      simpa only [inv_mul_cancel_left] using hmem
    have hcGeneralized : c ∈ Subgroup.centralizer (GeneralizedFitting.subgroup G : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      have hbound : F ⊔ E ≤ Subgroup.centralizer ({c} : Set G) := by
        apply sup_le
        · intro f hf
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hcF f hf)
        · intro e he
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hc e he)
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hbound hx)
    have hcFit := GeneralizedFitting.centralizer_le_fitting G hcGeneralized
    rw [← hec]
    exact (GeneralizedFitting.subgroup G).mul_mem
      ((le_sup_right : E ≤ GeneralizedFitting.subgroup G) he)
      ((le_sup_left : F ≤ GeneralizedFitting.subgroup G) hcFit)
  let q := QuotientGroup.mk' F
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    infer_instance
  apply SolvableKernelContainment.perfect_containment q K E
  have hmap := Subgroup.map_mono (f := q) hKG
  change K.map q ≤ (F ⊔ E).map q at hmap
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at hmap

end CFSG.ComponentClassification.AschbacherComponentInvolution
