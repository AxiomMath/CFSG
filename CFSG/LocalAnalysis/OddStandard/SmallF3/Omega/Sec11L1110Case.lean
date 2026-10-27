module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Comm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Single
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110QCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Perm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110QCrit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110QInner
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Th

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11L1110_crit {E : Type} [Group E] {s z q : E} (hs2 : s * s = 1)
    (hsz : s * z * s⁻¹ = z)
    (hcomm : (q * s * q⁻¹) * s = s * (q * s * q⁻¹) → q * s * q⁻¹ = s ∨ q * s * q⁻¹ = s * z)
    (hc : q * (s * q⁻¹ * s⁻¹) * (q * (s * q⁻¹ * s⁻¹)) = 1) :
    q * (s * q⁻¹ * s⁻¹) ∈ zpowers z := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  obtain ⟨s', hs'⟩ : ∃ s', s' = q * s * q⁻¹ := ⟨_, rfl⟩
  have hs'2 : s' * s' = 1 := by
    rw [hs']
    calc q * s * q⁻¹ * (q * s * q⁻¹) = q * (s * s) * q⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'2
  have hcdef : q * (s * q⁻¹ * s⁻¹) = s' * s := by rw [hs', hsinv]; group
  rw [hcdef] at hc ⊢
  have h1 : s' * s = s * s' := by
    have e : s' * s = (s' * s)⁻¹ := eq_inv_of_mul_eq_one_left hc
    rw [e, mul_inv_rev, hsinv, hs'inv]
  have hsz2 : s * z * s = z := by
    calc s * z * s = s * z * s⁻¹ := by rw [hsinv]
      _ = z := hsz
  rcases hcomm (by rw [← hs']; exact h1) with h | h
  · rw [← hs'] at h
    rw [h, hs2]
    exact one_mem _
  · rw [← hs'] at h
    rw [h, hsz2]
    exact Subgroup.mem_zpowers z

theorem sec11L1110_sub_D [Finite G] (hp : Asc82Pre11) (hT : Asc82Step1110Type)
    (hS : Asc82Step1110Single) (h118 : Asc82Lemma118) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) (hR : h⁻¹ * t * h ∈ R) :
    h⁻¹ * t * h ∈ secD K1 K2 R := by
  by_contra hsD
  have hctx' : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx'.toSec10Z).1
  obtain ⟨ht2, -, -, -, -⟩ := sec11_invols hctx'
  obtain ⟨-, hQS, -, hQz, -⟩ := sec11_Q_facts hp hctx'
  have hQR : secQ K1 K2 ≤ R := hQS.trans (hctx.S_le.trans hctx.T_le)
  have hs2 : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
    calc h⁻¹ * t * h * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [ht2]; group
  have hsz : (h⁻¹ * t * h) * z = z * (h⁻¹ * t * h) :=
    Subgroup.mem_centralizer_singleton_iff.mp (sec11_R_le_H hp hctx hR)
  have hsz' : (h⁻¹ * t * h) * z * (h⁻¹ * t * h)⁻¹ = z := by rw [hsz]; group
  set s : G := h⁻¹ * t * h with hsdef
  have hcrit : ∀ q ∈ secQ K1 K2, q * (s * q⁻¹ * s⁻¹) * (q * (s * q⁻¹ * s⁻¹)) = 1 →
      q * (s * q⁻¹ * s⁻¹) ∈ zpowers z := by
    intro q hq hc
    refine sec11L1110_crit hs2 hsz' (fun hcomm => ?_) hc
    have hqC : q ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hQz q hq)
    have hh' : h * q⁻¹ ∈ centralizer ({z} : Set G) :=
      (centralizer ({z} : Set G)).mul_mem hh ((centralizer ({z} : Set G)).inv_mem hqC)
    have e : (h * q⁻¹)⁻¹ * t * (h * q⁻¹) = q * s * q⁻¹ := by rw [hsdef]; group
    have hcm : ((h * q⁻¹)⁻¹ * t * (h * q⁻¹)) * (h⁻¹ * t * h) =
        (h⁻¹ * t * h) * ((h * q⁻¹)⁻¹ * t * (h * q⁻¹)) := by
      rw [e]
      exact hcomm
    rcases sec11L1110_comm hp hT hctx hh hh' hcm with h1 | h1
    · left
      rw [← e]
      exact h1
    · right
      rw [← e]
      exact h1
  have P : Sec11Q8Pair z (twoCoreIn K1) (twoCoreIn K2) := sec11L1110_q8pair hp hctx'
  have hQsup : secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 :=
    sec10KS_twoCore_sup hp.facts.pockets5 hp.facts.centZ5 hpsp hctx'
  have hsN : s ∈ normalizer (secQ K1 K2 : Set G) := hctx.sylowR.1 hR
  have hmap : ∀ x ∈ twoCoreIn K1 ⊔ twoCoreIn K2, s * x * s⁻¹ ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := by
    intro x hx
    rw [← hQsup] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
  have hcrit' : ∀ q ∈ twoCoreIn K1 ⊔ twoCoreIn K2,
      q * (s * q⁻¹ * s⁻¹) * (q * (s * q⁻¹ * s⁻¹)) = 1 → q * (s * q⁻¹ * s⁻¹) ∈ zpowers z := by
    intro q hq
    exact hcrit q (by rw [hQsup]; exact hq)
  rcases P.perm hsz' hmap with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · have hiff := hS G t L S z K1 K2 T R hctx h hh hR hsD hp1 hp2
    by_cases t1 : ActsTrivModZ z s (twoCoreIn K1)
    · have t2 : ActsTrivModZ z s (twoCoreIn K2) := hiff.mp t1
      obtain ⟨b, hb, hbx⟩ := P.triv_inner t1 t2
      have hbQ : b ∈ secQ K1 K2 := by rw [hQsup]; exact hb
      have hd : b⁻¹ * s ∈ secD K1 K2 R := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr (fun x hx => ?_),
          R.mul_mem (R.inv_mem (hQR hbQ)) hR⟩
        have hxQ : x ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := by rw [← hQsup]; exact hx
        have hx' := hbx x hxQ
        calc x * (b⁻¹ * s) = b⁻¹ * (b * x * b⁻¹) * s := by group
          _ = b⁻¹ * (s * x * s⁻¹) * s := by rw [hx']
          _ = b⁻¹ * s * x := by group
      have hsmem : s ∈ secD K1 K2 R ⊔ secQ K1 K2 := by
        have e : s = b * (b⁻¹ * s) := by group
        rw [e]
        exact (secD K1 K2 R ⊔ secQ K1 K2).mul_mem (Subgroup.mem_sup_right hbQ)
          (Subgroup.mem_sup_left hd)
      exact hsD (h118 G t L S z K1 K2 T R hctx h hh hsmem)
    · have t2 : ¬ ActsTrivModZ z s (twoCoreIn K2) := fun h2 => t1 (hiff.mpr h2)
      obtain ⟨q, hq, hq2, hqz⟩ := P.double_crit hsz' hp1 hp2 t1 t2
      exact hqz (hcrit' q hq hq2)
  ·
    obtain ⟨q, hq, hq2, hqz⟩ := P.swap_crit hsz' hp1
    exact hqz (hcrit' q hq hq2)

end CFSG.OddStandard.SmallF3.Omega
