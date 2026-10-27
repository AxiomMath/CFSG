module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Fact

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11c_R_normD [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ R, ∀ d ∈ secD K1 K2 R, g * d * g⁻¹ ∈ secD K1 K2 R := by
  intro g hgR d hdD
  obtain ⟨hdC, hdR⟩ := Subgroup.mem_inf.mp hdD
  refine Subgroup.mem_inf.mpr ⟨?_, R.mul_mem (R.mul_mem hgR hdR) (R.inv_mem hgR)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : g⁻¹ * q * g ∈ secQ K1 K2 :=
    (Subgroup.mem_normalizer_iff''.mp (hctx.sylowR.1 hgR) q).mp hq
  have hdq := Subgroup.mem_centralizer_iff.mp hdC (g⁻¹ * q * g) hq'
  calc q * (g * d * g⁻¹) = g * ((g⁻¹ * q * g) * d) * g⁻¹ := by group
    _ = g * (d * (g⁻¹ * q * g)) * g⁻¹ := by rw [hdq]
    _ = (g * d * g⁻¹) * q := by group

theorem sec11c_R_normQ [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ R, ∀ q ∈ secQ K1 K2, g * q * g⁻¹ ∈ secQ K1 K2 := by
  intro g hgR q hq
  exact (Subgroup.mem_normalizer_iff.mp (hctx.sylowR.1 hgR) q).mp hq

theorem sec11c_R_z [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ R, g * z = z * g := by
  intro g hgR
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (sec11_normalizer_Q_le_centralizer_z hp hctx.toSec10Ctx (hctx.sylowR.1 hgR))

theorem sec11c_R_isPGroup [Finite G] {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : IsPGroup 2 R := by
  exact hctx.sylowR.2.1

theorem sec11c_D_Q {K1 K2 R : Subgroup G} :
    ∀ d ∈ secD K1 K2 R, ∀ q ∈ secQ K1 K2, d * q = q * d := by
  intro d hd q hq
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).1 q hq).symm

theorem sec11c_D_inf [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    secD K1 K2 R ⊓ secQ K1 K2 = zpowers z := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  refine le_antisymm ?_ ?_
  · intro c hc
    exact sec10KS_Q_center hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx c
      (Subgroup.mem_inf.mp hc).2 (fun q hq => sec11c_D_Q c (Subgroup.mem_inf.mp hc).1 q hq)
  · exact Subgroup.zpowers_le.mpr
      ⟨sec11_z_mem_D hp hctx, (sec11_Q_facts hp hctx.toSec10Ctx).1⟩

theorem sec11c_C_le_D {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    [Finite G] (hctx : Sec11Ctx G t L S z K1 K2 T R) : secCTQ K1 K2 T ≤ secD K1 K2 R := by
  exact inf_le_inf_left _ hctx.T_le

theorem sec11c_t_ne_z [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : t ≠ z := by
  intro h
  have htL : t ∉ L := (hp.basic G t L S z hctx.toSec10Z).2.2.1
  have hzL : z ∈ L := (sec11_Q_facts hp hctx.toSec10Ctx).2.2.1
    (sec11_Q_facts hp hctx.toSec10Ctx).1
  exact htL (h.symm ▸ hzL)

theorem sec11c_cl [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ R, g * t * g⁻¹ ∈ conjClassIn (secD K1 K2 R) t → g ∈ T ⊔ secD K1 K2 R := by
  intro g hgR hconj
  obtain ⟨d, hdD, hdg⟩ := hconj
  set c : G := d⁻¹ * g with hc
  have hdR : d ∈ R := (Subgroup.mem_inf.mp hdD).2
  have hcR : c ∈ R := by
    rw [hc]
    exact R.mul_mem (R.inv_mem hdR) hgR
  have hcct : c ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hc]
    have hfix : (d⁻¹ * g) * t * (d⁻¹ * g)⁻¹ = t := by
      calc (d⁻¹ * g) * t * (d⁻¹ * g)⁻¹ = d⁻¹ * (g * t * g⁻¹) * d := by group
        _ = d⁻¹ * (d * t * d⁻¹) * d := by rw [hdg]
        _ = t := by group
    calc (d⁻¹ * g) * t = (d⁻¹ * g) * t * (d⁻¹ * g)⁻¹ * (d⁻¹ * g) := by group
      _ = t * (d⁻¹ * g) := by rw [hfix]
  let P : Subgroup G := centralizer ({t} : Set G) ⊓ R
  have hSP : S ≤ P := fun s hs => Subgroup.mem_inf.mpr ⟨hctx.sylow.1 hs, hctx.T_le (hctx.S_le hs)⟩
  have hPct : P ≤ centralizer ({t} : Set G) := inf_le_left
  have hP2 : IsPGroup 2 P := hctx.sylowR.2.1.to_le inf_le_right
  have hPS : P ≤ S := by
    have hrel := Subgroup.relIndex_mul_relIndex (H := S) (K := P)
      (L := centralizer ({t} : Set G)) hSP hPct
    have hdiv : S.relIndex P ∣ S.relIndex (centralizer ({t} : Set G)) :=
      ⟨P.relIndex (centralizer ({t} : Set G)), hrel.symm⟩
    have hodd : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G)) := hctx.sylow.2.2
    obtain ⟨n, hn⟩ := hP2.index (S.subgroupOf P)
    have hdiv' : 2 ^ n ∣ S.relIndex (centralizer ({t} : Set G)) := hn ▸ hdiv
    have hn0 : n = 0 := by
      by_contra hn0
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      exact hodd (Dvd.dvd.trans ⟨2 ^ k, by rw [pow_succ']⟩ hdiv')
    have hrelidx : S.relIndex P = 1 := by
      show (S.subgroupOf P).index = 1
      rw [hn, hn0]
      norm_num
    exact Subgroup.relIndex_eq_one.mp hrelidx
  have hcP : c ∈ P := Subgroup.mem_inf.mpr ⟨hcct, hcR⟩
  have hg_eq : g = d * c := by
    rw [hc]
    group
  rw [hg_eq]
  have hmem : d * c ∈ secD K1 K2 R ⊔ T := Subgroup.mul_mem_sup hdD (hctx.S_le (hPS hcP))
  rwa [sup_comm] at hmem

theorem sec11c_bar [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∀ g ∈ R, (∀ q ∈ secQ K1 K2, g * q * g⁻¹ * q⁻¹ ∈ zpowers z) →
      g ∈ secD K1 K2 R ⊔ secQ K1 K2 := by
  intro g hgR hgtriv
  have hQ8_1 := sec11_Q8_K1 hp hctx.toSec10Ctx
  have hQ8_2 := sec11_Q8_K2 hp hctx.toSec10Ctx
  have htriv1 : ∀ q ∈ twoCoreIn K1, g * q * g⁻¹ * q⁻¹ ∈ zpowers z := fun q hq =>
    hgtriv q (by rw [sec11_Q_eq_sup hp hctx.toSec10Ctx]; exact Subgroup.mem_sup_left hq)
  have htriv2 : ∀ q ∈ twoCoreIn K2, g * q * g⁻¹ * q⁻¹ ∈ zpowers z := fun q hq =>
    hgtriv q (by rw [sec11_Q_eq_sup hp hctx.toSec10Ctx]; exact Subgroup.mem_sup_right hq)
  have hnorm1 : ∀ q ∈ twoCoreIn K1, g * q * g⁻¹ ∈ twoCoreIn K1 := by
    intro q hq
    have hz1 : z ∈ twoCoreIn K1 := hQ8_1.z_mem
    have hcomm : g * q * g⁻¹ * q⁻¹ ∈ twoCoreIn K1 := (Subgroup.zpowers_le.mpr hz1) (htriv1 q hq)
    have hdecomp : g * q * g⁻¹ = (g * q * g⁻¹ * q⁻¹) * q := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _ hcomm hq
  have hnorm2 : ∀ q ∈ twoCoreIn K2, g * q * g⁻¹ ∈ twoCoreIn K2 := by
    intro q hq
    have hz2 : z ∈ twoCoreIn K2 := hQ8_2.z_mem
    have hcomm : g * q * g⁻¹ * q⁻¹ ∈ twoCoreIn K2 := (Subgroup.zpowers_le.mpr hz2) (htriv2 q hq)
    have hdecomp : g * q * g⁻¹ = (g * q * g⁻¹ * q⁻¹) * q := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _ hcomm hq
  obtain ⟨k1, hk1Q, hk1⟩ := Sec11Q8.inner_of_trivial hQ8_1 hnorm1 htriv1
  obtain ⟨k2, hk2Q, hk2⟩ := Sec11Q8.inner_of_trivial hQ8_2 hnorm2 htriv2
  have hcom12 := sec11_Q12_comm hp hctx.toSec10Ctx
  set w : G := (k1 * k2)⁻¹ * g with hw
  have hwC1 : w ∈ centralizer (twoCoreIn K1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hwq : w * q * w⁻¹ = q := by
      rw [hw]
      calc (k1 * k2)⁻¹ * g * q * ((k1 * k2)⁻¹ * g)⁻¹
          = (k1 * k2)⁻¹ * (g * q * g⁻¹) * (k1 * k2) := by group
        _ = (k1 * k2)⁻¹ * (k1 * q * k1⁻¹) * (k1 * k2) := by rw [hk1 q hq]
        _ = k2⁻¹ * q * k2 := by group
        _ = q := by
              calc k2⁻¹ * q * k2 = k2⁻¹ * (q * k2) := by group
                _ = k2⁻¹ * (k2 * q) := by rw [hcom12 q hq k2 hk2Q]
                _ = q := by group
    have hcomm : w * q = q * w := by
      calc w * q = w * q * w⁻¹ * w := by group
        _ = q * w := by rw [hwq]
    exact hcomm.symm
  have hwC2 : w ∈ centralizer (twoCoreIn K2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hwq : w * q * w⁻¹ = q := by
      rw [hw]
      calc (k1 * k2)⁻¹ * g * q * ((k1 * k2)⁻¹ * g)⁻¹
          = (k1 * k2)⁻¹ * (g * q * g⁻¹) * (k1 * k2) := by group
        _ = (k1 * k2)⁻¹ * (k2 * q * k2⁻¹) * (k1 * k2) := by rw [hk2 q hq]
        _ = k1⁻¹ * q * k1 := by
              rw [hcom12 k1 hk1Q k2 hk2Q]
              group
        _ = q := by
              calc k1⁻¹ * q * k1 = k1⁻¹ * (q * k1) := by group
                _ = k1⁻¹ * (k1 * q) := by rw [hcom12 k1 hk1Q q hq]
                _ = q := by group
    have hcomm : w * q = q * w := by
      calc w * q = w * q * w⁻¹ * w := by group
        _ = q * w := by rw [hwq]
    exact hcomm.symm
  have hwC : w ∈ centralizer (secQ K1 K2 : Set G) := by
    rw [sec11_Q_eq_sup hp hctx.toSec10Ctx, Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with hh | hh
    · exact Subgroup.mem_centralizer_iff.mp hwC1 h hh
    · exact Subgroup.mem_centralizer_iff.mp hwC2 h hh
  have hk1T : k1 ∈ T := sec11_Q1_le_T hp hctx hk1Q
  have hk2T : k2 ∈ T := sec11_Q2_le_T hp hctx hk2Q
  have hwR : w ∈ R := by
    rw [hw]
    exact R.mul_mem (R.inv_mem (R.mul_mem (hctx.T_le hk1T) (hctx.T_le hk2T))) hgR
  have hwD : w ∈ secD K1 K2 R := Subgroup.mem_inf.mpr ⟨hwC, hwR⟩
  have hk12Q : k1 * k2 ∈ secQ K1 K2 := by
    rw [sec11_Q_eq_sup hp hctx.toSec10Ctx]
    exact Subgroup.mul_mem_sup hk1Q hk2Q
  have hg_prod : g = (k1 * k2) * w := by
    rw [hw]
    group
  have hmem : (k1 * k2) * w ∈ secQ K1 K2 ⊔ secD K1 K2 R :=
    Subgroup.mul_mem_sup hk12Q hwD
  rw [hg_prod]
  rwa [sup_comm] at hmem

end CFSG.OddStandard.SmallF3.Omega
