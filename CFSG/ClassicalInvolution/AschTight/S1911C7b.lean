module

public import CFSG.ClassicalInvolution.AschTight.S1911C7a
public import CFSG.ClassicalInvolution.AschTight.S1911C10

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem oddCoreOf_le_oddCoreOf {M H : Subgroup G} (hMH : M ≤ H)
    (hHM : H ≤ Subgroup.normalizer (M : Set G)) : oddCoreOf M ≤ oddCoreOf H := by
  intro x hx
  have hxH : x ∈ H := hMH (oddCoreOf_le_self M hx)
  have h1 : (⟨x, hxH⟩ : H) ∈ classicalInvolutionOddCore H :=
    mem_oddCore_of_mem (K := H) (M := oddCoreOf M)
      (fun h hh => mem_normalizer_oddCoreOf_of_mem_normalizer (hHM hh))
      (oddCoreOf_odd_natCard M) hx
  exact ⟨⟨x, hxH⟩, h1, rfl⟩

theorem sec19X_le_normalizer_sup (hd : Sec19Data p f K z S W) :
    sec19X K z ≤ Subgroup.normalizer ((K ⊔ oddCoreOf (sec19X K z) : Subgroup G) : Set G) := by
  intro x hx
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
    exact Hall196.gammaGen_le_centralizer _ z hx
  have hxO : x ∈ Subgroup.normalizer (oddCoreOf (sec19X K z) : Set G) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hx)
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  calc conjSub x (K ⊔ oddCoreOf (sec19X K z))
      = conjSub x K ⊔ conjSub x (oddCoreOf (sec19X K z)) := Subgroup.map_sup _ _ _
    _ = K ⊔ oddCoreOf (sec19X K z) := by
      rw [conjSub_eq_of_mem_normalizer hxK, conjSub_eq_of_mem_normalizer hxO]

theorem sec19X_le_normalizer_member (hd : Sec19Data p f K z S W) :
    sec19X K z ≤ Subgroup.normalizer (K : Set G) := by
  rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
  exact Hall196.gammaGen_le_centralizer _ z

theorem classicalInvolutionOddCore_sup_eq (hd : Sec19Data p f K z S W) :
    classicalInvolutionOddCore ↥(K ⊔ oddCoreOf (sec19X K z)) =
      (oddCoreOf (sec19X K z)).subgroupOf (K ⊔ oddCoreOf (sec19X K z)) := by
  have hMX : K ⊔ oddCoreOf (sec19X K z) ≤ sec19X K z :=
    sup_le (le_sec19X_member hd) (oddCoreOf_le_self _)
  apply le_antisymm
  · intro m hm
    rw [Subgroup.mem_subgroupOf]
    exact oddCoreOf_le_oddCoreOf hMX (sec19X_le_normalizer_sup hd) ⟨m, hm, rfl⟩
  · intro m hm
    rw [Subgroup.mem_subgroupOf] at hm
    exact mem_oddCore_of_mem (fun x hx => mem_normalizer_oddCoreOf_of_mem_normalizer
      (Subgroup.le_normalizer (hMX hx))) (oddCoreOf_odd_natCard _) hm

theorem classicalInvolutionOddCore_member_eq (hd : Sec19Data p f K z S W) :
    (oddCoreOf (sec19X K z)).subgroupOf K = classicalInvolutionOddCore ↥K := by
  apply le_antisymm
  · intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    exact mem_oddCore_of_mem (fun x hx => mem_normalizer_oddCoreOf_of_mem_normalizer
      (Subgroup.le_normalizer (le_sec19X_member hd hx))) (oddCoreOf_odd_natCard _) hk
  · intro k hk
    rw [Subgroup.mem_subgroupOf]
    exact oddCoreOf_le_oddCoreOf (le_sec19X_member hd) (sec19X_le_normalizer_member hd)
      ⟨k, hk, rfl⟩

theorem isSL2ModOdd_sup_oddCore (hd : Sec19Data p f K z S W) :
    IsSL2ModOdd (K ⊔ oddCoreOf (sec19X K z)) (p ^ f) := by
  obtain ⟨p', e, hp', hp'2, he, hpe, ⟨φ⟩⟩ := isSL2ModOdd_member hd
  have hLE : K ≤ Subgroup.normalizer (oddCoreOf (sec19X K z) : Set G) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (le_sec19X_member hd hx))
  have := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  have e2 := QuotientGroup.quotientInfEquivProdNormalizerQuotient K (oddCoreOf (sec19X K z)) hLE
  have e1 := QuotientGroup.quotientMulEquivOfEq (classicalInvolutionOddCore_sup_eq hd)
  have e3 := QuotientGroup.quotientMulEquivOfEq (classicalInvolutionOddCore_member_eq hd)
  exact ⟨p', e, hp', hp'2, he, hpe, ⟨e1.trans (e2.symm.trans (e3.trans φ))⟩⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
