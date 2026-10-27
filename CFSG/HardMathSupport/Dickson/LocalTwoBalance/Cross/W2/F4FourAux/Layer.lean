module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

variable {C : Type*} [Group C]

theorem derivedCentralizer_le (x : C) :
    ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ ≤ centralizer ({x} : Set C) :=
  Subgroup.commutator_le.2 fun u hu v hv => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)

theorem map_centralizer_singleton_apply (η : MulAut C) (x : C) :
    (centralizer ({x} : Set C)).map η.toMonoidHom = centralizer ({η x} : Set C) := by
  ext y
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, ha]
  · intro hy
    refine ⟨η.symm y, ?_, by simp⟩
    apply η.injective
    rw [map_mul, map_mul]
    simpa using hy

theorem apply_mem_derivedCentralizer {η : MulAut C} {x : C} (hη : η x = x) {r : C}
    (hr : r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆) :
    η r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ := by
  have hY : (centralizer ({x} : Set C)).map η.toMonoidHom = centralizer ({x} : Set C) := by
    rw [map_centralizer_singleton_apply, hη]
  have h1 : η r ∈ ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆.map η.toMonoidHom :=
    ⟨r, hr, rfl⟩
  rwa [Subgroup.map_commutator, hY] at h1

theorem isComponent_image_derivedCentralizer
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {H : Subgroup (MulAut C)}
    (hH : innerAut C ≤ H) (x : C)
    (hq : CFSG.IsQuasisimple
      (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ : Subgroup C)) :
    (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆.map
        (MulAut.conj : C →* MulAut C)) ≤
        H ⊓ centralizer ({MulAut.conj x} : Set (MulAut C)) ∧
      CFSG.IsComponent
        (((⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆).map
          (MulAut.conj : C →* MulAut C)).subgroupOf
            (H ⊓ centralizer ({MulAut.conj x} : Set (MulAut C)))) := by
  set R : Subgroup C := ⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ with hR
  set M : Subgroup (MulAut C) := H ⊓ centralizer ({MulAut.conj x} : Set (MulAut C)) with hM
  have hRD : R ≤ centralizer ({x} : Set C) := derivedCentralizer_le x
  have hRM : R.map (MulAut.conj : C →* MulAut C) ≤ M := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨hH ⟨r, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_centralizer_singleton_iff.1 (hRD hr)
    rw [← map_mul, ← map_mul, this]
  refine ⟨hRM, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective R (MulAut.conj : C →* MulAut C) hinj).trans
      (Subgroup.subgroupOfEquivOfLe hRM).symm) hq, ?_⟩
  have hN : ((R.map (MulAut.conj : C →* MulAut C)).subgroupOf M).Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨r, hr, hrn⟩ := hn
    have hmx : (m : MulAut C) x = x := by
      apply hinj
      have h1 := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 m.2).2
      rw [← mul_conj_mul_inv, h1, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨(m : MulAut C) r, apply_mem_derivedCentralizer hmx hr, ?_⟩
    change MulAut.conj ((m : MulAut C) r) = (m : MulAut C) * ((n : M) : MulAut C) * (m : MulAut C)⁻¹
    rw [← mul_conj_mul_inv, hrn]
    rfl
  exact hN.isSubnormal

theorem fixes_of_mem_localDeltaIn [Finite C] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {H E : Subgroup (MulAut C)}
    (hH : innerAut C ≤ H) {z : MulAut C} (hz : z ∈ localDeltaIn p H E) {b : C}
    (hbE : MulAut.conj b ∈ E) (hb1 : b ≠ 1)
    (hq : CFSG.IsQuasisimple
      (⁅centralizer ({b} : Set C), centralizer ({b} : Set C)⁆ : Subgroup C))
    (hpR : ¬ Nat.Coprime p
      (Nat.card (⁅centralizer ({b} : Set C), centralizer ({b} : Set C)⁆ : Subgroup C))) :
    z b = b ∧ ∀ r ∈ ⁅centralizer ({b} : Set C), centralizer ({b} : Set C)⁆, z r = r := by
  have hb1' : MulAut.conj b ≠ 1 := fun h => hb1 (hinj (by rw [h, map_one]))
  obtain ⟨hTC, hcomp⟩ := isComponent_image_derivedCentralizer hinj hH b hq
  have hle := le_fixSub_of_component hp hinj hz hbE hb1' hTC hcomp hpR
  refine ⟨mem_fixSub_of_commute hinj (commute_of_mem_localDeltaIn hz hbE), fun r hr => ?_⟩
  exact hle hr

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
