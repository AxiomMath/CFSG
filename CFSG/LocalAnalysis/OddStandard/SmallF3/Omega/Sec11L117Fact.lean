module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Q8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BCard

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11_eq_neg_one_of_orderOf_eq_two {X : Subgroup G} (e : ↥X ≃* SL23) {z : G}
    (hz : z ∈ X) (hz2 : orderOf z = 2) : e ⟨z, hz⟩ = -1 := by
  have hsq : (⟨z, hz⟩ : ↥X) * ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    change z * z = (1 : G)
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hsq' : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by rw [← map_mul, hsq, map_one]
  rcases sl23_unique_involution _ hsq' with h | h
  · exfalso
    have hz1 : (⟨z, hz⟩ : ↥X) = 1 := by apply e.injective; rw [h, map_one]
    have hzG : z = 1 := by simpa using congrArg Subtype.val hz1
    have hone : orderOf z = 1 := by rw [hzG]; exact orderOf_one
    rw [hone] at hz2
    exact absurd hz2 (by decide)
  · exact h

private theorem sec11_mem_twoCoreIn_of_orderOf_eq_two {X : Subgroup G} (e : ↥X ≃* SL23) {z : G}
    (hz : z ∈ X) (hz2 : orderOf z = 2) : z ∈ twoCoreIn X := by
  rw [mem_twoCoreIn_iff_pCore hz]
  have hmem : e ⟨z, hz⟩ ∈ CFSG.pCore 2 SL23 := by
    rw [sec11_eq_neg_one_of_orderOf_eq_two e hz hz2]
    exact sl23_neg_one_mem_pCore
  rw [← CFSG.pCore_map_iso 2 e] at hmem
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
  have hy' : y = ⟨z, hz⟩ := e.injective hye
  rwa [hy'] at hy

private theorem sec11_z_mem_twoCoreIn_K1 [Finite G] (hp : Asc82Pre11) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    z ∈ twoCoreIn K1 := by
  obtain ⟨e1⟩ := (sec10KS_equiv hp.facts.pockets5 hp.facts.centZ5
    (hp.basic G t L S z hctx.toSec10Z).1 hctx).1
  exact sec11_mem_twoCoreIn_of_orderOf_eq_two e1 hctx.pocket1.1 hctx.toSec10Z.pocket.1

theorem sec11_Q8_K1 [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) : Sec11Q8 G z (twoCoreIn K1) := by
  have hP5 := hp.facts.pockets5
  have hC5 := hp.facts.centZ5
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  obtain ⟨e1⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  obtain ⟨-, hzsq, -, -, hzne⟩ := sec11_invols hctx
  have hle : twoCoreIn K1 ≤ secQ K1 K2 := by
    rw [sec10KS_twoCore_sup hP5 hC5 hpsp hctx]
    exact le_sup_left
  refine ⟨hzsq, hzne, sec11_z_mem_twoCoreIn_K1 hp hctx,
    sec10B_card_twoCoreIn K1 e1, ?_, ?_, ?_⟩
  · intro a ha b hb
    exact sec10KS_Qi_elem hP5 hC5 hpsp hctx a ha b hb
  · intro q hq
    exact (sec11_Q_facts hp hctx).2.2.2.1 q (hle hq)
  · exact sec10KS_Qi_center hP5 hC5 hpsp hctx

theorem sec11_Q8_K2 [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) : Sec11Q8 G z (twoCoreIn K2) :=
  sec11_Q8_K1 hp hctx.swap

theorem sec11_Q_eq_sup [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 :=
  sec10KS_twoCore_sup hp.facts.pockets5 hp.facts.centZ5
    (hp.basic G t L S z hctx.toSec10Z).1 hctx

theorem sec11_Q12_comm [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ p ∈ twoCoreIn K1, ∀ q ∈ twoCoreIn K2, p * q = q * p := by
  intro p hp1 q hq2
  exact sec10Z_comm hp.facts.pockets5 (hp.basic G t L S z hctx.toSec10Z).1 hctx p
    (twoCoreIn_le_self K1 hp1) q (twoCoreIn_le_self K2 hq2)

theorem sec11_Q12_inf [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    twoCoreIn K1 ⊓ twoCoreIn K2 = zpowers z := by
  refine le_antisymm ?_ ?_
  · calc twoCoreIn K1 ⊓ twoCoreIn K2 ≤ K1 ⊓ K2 :=
        inf_le_inf (twoCoreIn_le_self K1) (twoCoreIn_le_self K2)
      _ = zpowers z := (sec10KS_main hp.facts.pockets5 hp.facts.centZ5
          (hp.basic G t L S z hctx.toSec10Z).1 hctx).2.2
  · exact Subgroup.zpowers_le.mpr
      ⟨(sec11_Q8_K1 hp hctx).z_mem, (sec11_Q8_K2 hp hctx).z_mem⟩

theorem sec11_T_isPGroup [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : IsPGroup 2 T :=
  hctx.sylowT.2.1

theorem sec11_T_cent_z [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ T, g * z = z * g := by
  intro g hg
  have hnorm : g ∈ normalizer (secQ K1 K2 : Set G) := hctx.sylowR.1 (hctx.T_le hg)
  have hcen : g ∈ centralizer ({z} : Set G) :=
    sec11_normalizer_Q_le_centralizer_z hp hctx.toSec10Ctx hnorm
  exact Subgroup.mem_centralizer_singleton_iff.mp hcen

theorem sec11_T_normQ [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ T, ∀ q ∈ secQ K1 K2, g * q * g⁻¹ ∈ secQ K1 K2 := by
  intro g hg q hq
  exact (Subgroup.mem_normalizer_iff.mp (hctx.sylowR.1 (hctx.T_le hg)) q).mp hq

theorem sec11_Q1_le_T [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : twoCoreIn K1 ≤ T := by
  calc twoCoreIn K1 ≤ secQ K1 K2 := by
        rw [sec11_Q_eq_sup hp hctx.toSec10Ctx]
        exact le_sup_left
    _ ≤ S := (sec11_Q_facts hp hctx.toSec10Ctx).2.1
    _ ≤ T := hctx.S_le

theorem sec11_Q2_le_T [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : twoCoreIn K2 ≤ T := by
  calc twoCoreIn K2 ≤ secQ K1 K2 := by
        rw [sec11_Q_eq_sup hp hctx.toSec10Ctx]
        exact le_sup_right
    _ ≤ S := (sec11_Q_facts hp hctx.toSec10Ctx).2.1
    _ ≤ T := hctx.S_le

end CFSG.OddStandard.SmallF3.Omega
