module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Fact
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PX

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11_isElemAbelianMod_zpowers_of_sq {z u : G} (hu2 : u * u = 1)
    (huz : u * z = z * u) : IsElemAbelianMod z (zpowers u) := by
  have hu2z : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu2
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  refine ⟨?_, ?_⟩
  · have h1 : u ^ k * u ^ l * (u ^ k)⁻¹ * (u ^ l)⁻¹ = 1 := by group
    rw [h1]
    exact Subgroup.one_mem _
  · have h1 : u ^ k * u ^ k = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, hu2z, one_zpow]
    rw [h1]
    exact Subgroup.one_mem _

theorem sec11_z_mem_C [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : z ∈ secCTQ K1 K2 T := by
  refine Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_iff.mpr (fun q hq => ?_), hctx.S_le hctx.mem_S⟩
  exact (sec11_Q_facts hp hctx.toSec10Ctx).2.2.2.1 q hq

theorem sec11_C_Q {K1 K2 T : Subgroup G} :
    ∀ c ∈ secCTQ K1 K2 T, ∀ q ∈ secQ K1 K2, c * q = q * c := by
  intro c hc q hq
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).1 q hq).symm

theorem sec11_mem_C_of {K1 K2 T : Subgroup G} {g : G} (hg : g ∈ T)
    (hgQ : ∀ q ∈ secQ K1 K2, g * q = q * g) : g ∈ secCTQ K1 K2 T := by
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_iff.mpr (fun q hq => (hgQ q hq).symm), hg⟩

theorem sec11_C_inf [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    secCTQ K1 K2 T ⊓ secQ K1 K2 = zpowers z := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  refine le_antisymm ?_ ?_
  · intro c hc
    exact sec10KS_Q_center hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx c
      (Subgroup.mem_inf.mp hc).2 (fun q hq => sec11_C_Q c (Subgroup.mem_inf.mp hc).1 q hq)
  · exact Subgroup.zpowers_le.mpr
      ⟨sec11_z_mem_C hp hctx, (sec11_Q_facts hp hctx.toSec10Ctx).1⟩

theorem sec11_W_norm [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ T, ∀ w ∈ secCTQ K1 K2 T ⊔ secQ K1 K2, g * w * g⁻¹ ∈ secCTQ K1 K2 T ⊔ secQ K1 K2 := by
  intro g hg w hw
  obtain ⟨c, hc, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute sec11_C_Q hw
  have hCnorm : g * c * g⁻¹ ∈ secCTQ K1 K2 T := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr (fun q' hq' => ?_), ?_⟩
    · have hq'' : g⁻¹ * q' * g ∈ secQ K1 K2 := by
        have h := sec11_T_normQ hctx g⁻¹ (T.inv_mem hg) q' hq'
        simpa using h
      have hcq := sec11_C_Q c hc (g⁻¹ * q' * g) hq''
      exact (calc (g * c * g⁻¹) * q' = g * (c * (g⁻¹ * q' * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * q' * g) * c) * g⁻¹ := by rw [hcq]
        _ = q' * (g * c * g⁻¹) := by group).symm
    · exact T.mul_mem (T.mul_mem hg (Subgroup.mem_inf.mp hc).2) (T.inv_mem hg)
  have hprod : g * (c * q) * g⁻¹ = (g * c * g⁻¹) * (g * q * g⁻¹) := by group
  rw [hprod]
  exact Subgroup.mul_mem_sup hCnorm (sec11_T_normQ hctx g hg q hq)

theorem sec11_C_elemAb [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : IsElemAbelianMod z (secCTQ K1 K2 T) := by
  have h2 := (sec11_invols hctx.toSec10Ctx).2.1
  have htz := (sec11_invols hctx.toSec10Ctx).2.2.1
  have h1 := (sec11_invols hctx.toSec10Ctx).2.2.2.2
  have ht2 := (sec11_invols hctx.toSec10Ctx).1
  rcases r.l112 G t L S z K1 K2 T R hctx with ⟨-, hC⟩ | ⟨-, r0, -, hC, hD8, -⟩
  · rw [hC]
    refine sec11_isElemAbelianMod_sup ?_ ?_ ?_ ?_ ?_
    · intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow (show Commute t z from htz) k l).eq
    · intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (show Commute t z from htz).zpow_left k |>.eq
    · intro b hb
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.refl z).zpow_left l |>.eq
    · exact sec11_isElemAbelianMod_zpowers_of_sq ht2 htz
    · exact sec11_isElemAbelianMod_zpowers_of_sq h2 (by rfl)
  · exact sec11d2_isElemAbelianMod_of_isD8 hD8 (sec11_z_mem_C hp hctx) h2 h1
      (fun x hx => sec11_T_cent_z hp hctx x (Subgroup.mem_inf.mp hx).2)

theorem sec11_W_elemAb [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    IsElemAbelianMod z (secCTQ K1 K2 T ⊔ secQ K1 K2) := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  refine sec11_isElemAbelianMod_sup sec11_C_Q ?_ ?_ (sec11_C_elemAb hp r hctx) ?_
  · intro a ha
    exact sec11_T_cent_z hp hctx a (Subgroup.mem_inf.mp ha).2
  · intro b hb
    exact (sec11_Q_facts hp hctx.toSec10Ctx).2.2.2.1 b hb
  · exact (sec10KS_Q_elem hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx).2

end CFSG.OddStandard.SmallF3.Omega
