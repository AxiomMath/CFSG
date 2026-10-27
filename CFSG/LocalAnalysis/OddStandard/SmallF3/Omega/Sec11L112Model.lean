module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Mb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Amb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_model_of [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    ∃ (Alt : Subgroup (Equiv.Perm (Fin 6))) (φ : (Fin 6 → ZMod 2) → G),
      Sec11Model t L S z K1 K2 T Alt φ := by
  classical
  obtain ⟨Alt, φ, hAlt, hm, ht, htz⟩ := sec11_perm_normalized hp hctx
  refine ⟨Alt, φ, ?_⟩
  obtain ⟨ht2, hz2, htzc, ht1, hz1, -, htS, hzS, hQS⟩ := sec11L114_data hp hctx
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hmB := sec11_mem_B hp hctx.toSec10Ctx hm hAlt ht
  have hTM : T ≤ secM t S L := hctx.sylowT.1
  have hQM : secQ K1 K2 ≤ secM t S L := hQS.trans (hctx.S_le.trans hTM)
  have hQL : secQ K1 K2 ≤ S ⊓ L := sec10J_Q_le hp.facts.pockets5 hp.basic hctx.toSec10Ctx
  have hQcent := sec11L114_cent_Q hp hctx
  have hzφ : φ (Pi.single 0 1 + Pi.single 1 1) = z := by
    rw [hm.mul, ← ht, ← htz]
    calc t * (t * z) = (t * t) * z := by group
      _ = z := by rw [ht2, one_mul]
  have hQel := sec10KS_Q_elem hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx
  have hQD := sec11_Q_structure hm hQM
    (sec10B_card_Q hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx)
    (fun q hq => by rw [← ht]; exact Subgroup.mem_centralizer_iff.mp hQcent.1 q hq)
    (fun q hq => by
      rw [← htz]
      have h1 := Subgroup.mem_centralizer_iff.mp hQcent.1 q hq
      have h2 := Subgroup.mem_centralizer_iff.mp hQcent.2 q hq
      calc q * (t * z) = (q * t) * z := by group
        _ = t * (q * z) := by rw [h1]; group
        _ = t * (z * q) := by rw [h2]
        _ = (t * z) * q := by group)
    (fun a ha b hb => by rw [hzφ]; exact (hQel.2 a ha b hb).1)
    (by rw [hzφ]; exact hQel.1)
    (fun v hv => by
      have hvL : φ v ∈ L := (hQL hv).2
      exact (hmB v).mp (sec11_A_inf_L hp hctx.toSec10Ctx (hm.mem v) hvL))
    (fun q hq hq1 => by
      have hqM : q ∈ secM t S L := hQM hq
      have hcomm := (hm.rho_eq_one_iff hqM).mp hq1
      have hqA : q ∈ secA t S L := sec11_cenSA hp hctx.toSec10Ctx (hQS hq) fun a ha =>
        mul_inv_eq_iff_eq_mul.mp (hcomm a ha)
      exact hm.surj q hqA)
    (fun v w hv hw hvQ hwQ => by
      have hvB : φ v ∈ secB S L := (hmB v).mpr hv
      have hwB : φ w ∈ secB S L := (hmB w).mpr hw
      rw [hm.mul]
      exact sec11_Q_mul_mem hp hctx.toSec10Ctx (secB_le_inf S L hvB) (secB_le_inf S L hwB)
        hvQ hwQ)
  obtain ⟨hmemQ, hQact, hQsurj⟩ := hQD
  have hAT : secA t S L ≤ T := by
    refine sup_le ((secB_le_S S L).trans hctx.S_le) ?_
    exact zpowers_le.mpr (hctx.S_le htS)
  have hcenTA : ∀ c ∈ T, (∀ a ∈ secA t S L, c * a = a * c) → c ∈ secA t S L :=
    fun c hc h => sec11_cenTA hp hctx hc h
  obtain ⟨-, hcl, -, -⟩ := asc82Step111T_of hp G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp
    hctx.sylowT hctx.S_le
  exact ⟨hm, hAlt, ht, htz, hmB, hmemQ, hQact, hQsurj,
    sec11_T_set hm hTM ht htz hcl, hcenTA, sec11_card_T hm hAlt hctx.sylowT hAT hcenTA⟩

theorem Sec11Model.cent_T_Q [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}
    (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    (Alt = alternatingGroup (Fin 6) ∧ secCTQ K1 K2 T = zpowers t ⊔ zpowers z) ∨
      (Alt = ⊤ ∧ ∃ r : G, orderOf r = 2 ∧ secCTQ K1 K2 T = zpowers t ⊔ zpowers r ∧
        IsD8 (secCTQ K1 K2 T) ∧ ∀ v, r * φ v * r⁻¹ = φ (permVec (Equiv.swap 0 1) v)) :=
  sec11_cent_T_Q hp hctx hm

end CFSG.OddStandard.SmallF3.Omega
