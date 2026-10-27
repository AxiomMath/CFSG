module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv9
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv6
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv8

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Sig2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def JKsub (hb : PAB G L t E W z) (a : PA7 L t E z) (K : Subgroup ↥(Cen a.ub)) :
    Subgroup ↥K := (JG hb a.toPA6.toPA5).subgroupOf K

@[expose] def Jtilde (hb : PAB G L t E W z) (a : PA7 L t E z) (K : Subgroup ↥(Cen a.ub)) :
    Subgroup (↥K ⧸ center ↥K) :=
  ((QuotientGroup.mk' (center ↥K)).comp (JKsub hb a K).subtype).range

variable (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem JG_le_K : JG hb a.toPA6.toPA5 ≤ K := by
  have := JG_le_layer hb a
  rwa [inv_layer hb a hK hcj hall] at this

theorem Jtilde_le : Jtilde hb a K ≤ autCentralizer (tauHat hb a hK hcj hall) := by
  rintro _ ⟨j, rfl⟩
  have hj : (j : ↥(Cen a.ub)) ∈ JG hb a.toPA6.toPA5 := j.2
  have h1 : (j : ↥(Cen a.ub)) * tG hb a.toPA6.toPA5 = tG hb a.toPA6.toPA5 * j :=
    JG_comm_t hb a.toPA6.toPA5 hj
  show tauHat hb a hK hcj hall (QuotientGroup.mk (j : ↥K)) = QuotientGroup.mk (j : ↥K)
  rw [tauHat_mk]
  congr 1
  apply Subtype.ext
  rw [sigmaK_apply]
  calc tG hb a.toPA6.toPA5 * ((j : ↥K) : ↥(Cen a.ub)) * (tG hb a.toPA6.toPA5)⁻¹
      = ((j : ↥(Cen a.ub)) * tG hb a.toPA6.toPA5) * (tG hb a.toPA6.toPA5)⁻¹ := by rw [h1]
    _ = (j : ↥(Cen a.ub)) := by group

theorem inv_comm_mem {x y : ↥K ⧸ center ↥K} (hx : x ∈ autCentralizer (tauHat hb a hK hcj hall))
    (hy : y ∈ autCentralizer (tauHat hb a hK hcj hall)) : ⁅x, y⁆ ∈ Jtilde hb a K := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have hk := (mem_autCent_iff hb a hK hcj hall k).1 hx
  have hl := (mem_autCent_iff hb a hK hcj hall l).1 hy
  obtain ⟨j, hjJ, zz, hzz, hcomm⟩ := inv_comm_decomp hb a hK hcj hall k l
    (inv_in_CT hb a hK hcj hall k hk) (inv_in_CT hb a hK hcj hall l hl)
  have hjG : j ∈ JG hb a.toPA6.toPA5 := hjJ
  have hjK : j ∈ K := JG_le_K hb a hK hcj hall hjG
  have hkl : ((⁅k, l⁆ : ↥K) : ↥(Cen a.ub)) = ⁅(k : ↥(Cen a.ub)), (l : ↥(Cen a.ub))⁆ := by
    simp [commutatorElement_def]
  have hzK : zz ∈ K := by
    have : zz = j⁻¹ * ((⁅k, l⁆ : ↥K) : ↥(Cen a.ub)) := by
      rw [hkl, hcomm]; group
    rw [this]
    exact K.mul_mem (K.inv_mem hjK) (⁅k, l⁆ : ↥K).2
  have hzc : (⟨zz, hzK⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    obtain ⟨i, rfl⟩ := hzz
    show (g : ↥(Cen a.ub)) * (ubG a.toPA6.toPA5) ^ i = (ubG a.toPA6.toPA5) ^ i * g
    exact ((Commute.zpow_left (show Commute (ubG a.toPA6.toPA5) g from
      ubG_central a.toPA6.toPA5 g) i).eq).symm
  have hklK : ⁅k, l⁆ = ⟨j, hjK⟩ * ⟨zz, hzK⟩ := by
    apply Subtype.ext
    rw [hkl, hcomm]; rfl
  have hmk : ⁅(QuotientGroup.mk k : ↥K ⧸ center ↥K), QuotientGroup.mk l⁆ =
      (QuotientGroup.mk ⁅k, l⁆ : ↥K ⧸ center ↥K) :=
    (map_commutatorElement (QuotientGroup.mk' (center ↥K)) k l).symm
  rw [hmk]
  refine ⟨⟨⟨j, hjK⟩, hjG⟩, ?_⟩
  show (QuotientGroup.mk (⟨j, hjK⟩ : ↥K) : ↥K ⧸ center ↥K) = QuotientGroup.mk ⁅k, l⁆
  have hz1 : (QuotientGroup.mk (⟨zz, hzK⟩ : ↥K) : ↥K ⧸ center ↥K) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hzc
  rw [hklK, QuotientGroup.mk_mul, hz1, mul_one]

end Sig2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
