module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem t5c_mem_twoRes_of_three_cycle {A : Type} [Group A] {H : Subgroup A} {t p : A}
    (ht : t ∈ H) (hp : p ∈ H) (hpodd : Odd (orderOf p)) (ht2 : t * t = 1)
    (h : t * (p * t * p⁻¹) = p * p * t * p⁻¹ * p⁻¹) : t ∈ twoRes H := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have huH : t * p * t⁻¹ ∈ H := mul_mem (mul_mem ht hp) (inv_mem ht)
  have huord : orderOf (t * p * t⁻¹) = orderOf p := by
    have h1 : orderOf ((MulAut.conj t) p) = orderOf p :=
      MulEquiv.orderOf_eq (MulAut.conj t) p
    rwa [MulAut.conj_apply] at h1
  have huodd : Odd (orderOf (t * p * t⁻¹)) := by rw [huord]; exact hpodd
  have h' : (t * p * t⁻¹) * p⁻¹ = p * p * t * p⁻¹ * p⁻¹ := by
    calc (t * p * t⁻¹) * p⁻¹ = t * (p * t * p⁻¹) := by rw [htinv]; group
      _ = p * p * t * p⁻¹ * p⁻¹ := h
  have hu : t * p * t⁻¹ = p * p * t * p⁻¹ := by
    calc t * p * t⁻¹ = (t * p * t⁻¹) * p⁻¹ * p := by group
      _ = (p * p * t * p⁻¹ * p⁻¹) * p := by rw [h']
      _ = p * p * t * p⁻¹ := by group
  have ht_eq : t = p⁻¹ * p⁻¹ * (t * p * t⁻¹) * p := by
    rw [hu]; group
  have hpS : p ∈ twoRes H := subset_closure ⟨hp, hpodd⟩
  have hpinvS : p⁻¹ ∈ twoRes H := subset_closure ⟨inv_mem hp, by rwa [orderOf_inv]⟩
  have huS : t * p * t⁻¹ ∈ twoRes H := subset_closure ⟨huH, huodd⟩
  rw [ht_eq]
  exact mul_mem (mul_mem (mul_mem hpinvS hpinvS) huS) hpS

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def CovModelI4 (hQ : Q.Nondegenerate) (g : OGroup Q) : Prop :=
  ∃ w ∈ twoRes (omegaGroup hQ ⊓ Subgroup.centralizer ({g} : Set (OGroup Q))), w * w = 1 ∧
    invType w = (4, 1) ∧ ∃ c ∈ omegaGroup hQ, c * g * c⁻¹ = w * g

theorem CovModelI4.conj (hQ : Q.Nondegenerate) {g : OGroup Q} (hg : CovModelI4 hQ g)
    (a : OGroup Q) : CovModelI4 hQ (a * g * a⁻¹) := by
  obtain ⟨w, hw, hww, hwt, c, hc, hcg⟩ := hg
  have hgen : a * w * a⁻¹ ∈ twoRes (omegaGroup hQ ⊓
      Subgroup.centralizer ({a * g * a⁻¹} : Set (OGroup Q))) := by
    refine Subgroup.closure_induction
      (k := {y : OGroup Q | y ∈ omegaGroup hQ ⊓
        Subgroup.centralizer ({g} : Set (OGroup Q)) ∧ Odd (orderOf y)})
      (p := fun y _ => a * y * a⁻¹ ∈ twoRes (omegaGroup hQ ⊓
        Subgroup.centralizer ({a * g * a⁻¹} : Set (OGroup Q)))) ?_ ?_ ?_ ?_ hw
    · intro x hx
      have hxL : x ∈ omegaGroup hQ ⊓ Subgroup.centralizer ({g} : Set (OGroup Q)) := hx.1
      have hxodd : Odd (orderOf x) := hx.2
      have hxcen : x * g = g * x := Subgroup.mem_centralizer_singleton_iff.mp hxL.2
      refine subset_closure ⟨⟨(omegaGroup_normal hQ).conj_mem x hxL.1 a, ?_⟩, ?_⟩
      · change (a * x * a⁻¹) ∈ Subgroup.centralizer ({a * g * a⁻¹} : Set (OGroup Q))
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [show (a * x * a⁻¹) * (a * g * a⁻¹) = a * (x * g) * a⁻¹ by group, hxcen]
        group
      · have h1 : orderOf ((MulAut.conj a) x) = orderOf x :=
          MulEquiv.orderOf_eq (MulAut.conj a) x
        rw [MulAut.conj_apply] at h1
        rw [h1]; exact hxodd
    · simp
    · intro x y hx hy ihx ihy
      rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
      exact mul_mem ihx ihy
    · intro x hx ih
      rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
      exact inv_mem ih
  refine ⟨a * w * a⁻¹, hgen, ?_, ?_, a * c * a⁻¹,
    (omegaGroup_normal hQ).conj_mem c hc a, ?_⟩
  · calc (a * w * a⁻¹) * (a * w * a⁻¹) = a * (w * w) * a⁻¹ := by group
      _ = 1 := by rw [hww]; group
  · rw [invType_conj hQ hww a, hwt]
  · calc (a * c * a⁻¹) * (a * g * a⁻¹) * (a * c * a⁻¹)⁻¹ =
        a * (c * g * c⁻¹) * a⁻¹ := by group
      _ = a * (w * g) * a⁻¹ := by rw [hcg]
      _ = (a * w * a⁻¹) * (a * g * a⁻¹) := by group

theorem covModelI4_of_isConj (hQ : Q.Nondegenerate) {g g' : OGroup Q} (hgg' : IsConj g g')
    (hg : CovModelI4 hQ g) : CovModelI4 hQ g' := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hgg'
  rw [← ha]
  exact hg.conj hQ a

theorem CovModelI4.exists_cover (hQ : Q.Nondegenerate) {g : OGroup Q} (hg : CovModelI4 hQ g) :
    ∃ w ∈ twoRes (omegaGroup hQ ⊓ fixSub (simAct Q (orthToSim Q g))), w * w = 1 ∧
      invType w = (4, 1) ∧ ∃ c : omegaGroup hQ,
        w = (c : OGroup Q) * simAct Q (orthToSim Q g) (c : OGroup Q)⁻¹ := by
  obtain ⟨w, hw, hww, hwt, c, hc, hcg⟩ := hg
  have hsub : omegaGroup hQ ⊓ Subgroup.centralizer ({g} : Set (OGroup Q)) =
      omegaGroup hQ ⊓ fixSub (simAct Q (orthToSim Q g)) := by
    ext y
    simp only [Subgroup.mem_inf, mem_fixSub_iff]
    constructor
    · rintro ⟨hy, hcen⟩
      refine ⟨hy, ?_⟩
      rw [simAct_orthToSim, mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hcen).symm
    · rintro ⟨hy, hfix⟩
      refine ⟨hy, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [simAct_orthToSim, mul_inv_eq_iff_eq_mul] at hfix
      exact hfix.symm
  refine ⟨w, ?_, hww, hwt, ⟨⟨c, hc⟩, ?_⟩⟩
  · rw [← hsub]; exact hw
  · rw [simAct_orthToSim]
    have h1 : c * g * c⁻¹ * g⁻¹ = w := by rw [hcg]; group
    rw [← h1]; group

end CFSG.OddStandard.SmallF3.Omega
