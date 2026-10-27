module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11L115_alt6_not_perm6 {X : Type} [Group X]
    (h1 : Nonempty (X ≃* ↥(alternatingGroup (Fin 6))))
    (h2 : Nonempty (X ≃* Equiv.Perm (Fin 6))) : False := by
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := h2
  have h : Nat.card ↥(alternatingGroup (Fin 6)) = Nat.card (Equiv.Perm (Fin 6)) :=
    (Nat.card_congr e1.symm.toEquiv).trans (Nat.card_congr e2.toEquiv)
  rw [nat_card_alternatingGroup, Nat.card_perm] at h
  simp [Nat.factorial] at h

theorem sec11L115_conj_cent {Q T : Subgroup G} {y : G} (hyQ : y ∈ normalizer (Q : Set G))
    (hyT : y ∈ normalizer (T : Set G)) {c : G} (hc : c ∈ centralizer (Q : Set G) ⊓ T) :
    y * c * y⁻¹ ∈ centralizer (Q : Set G) ⊓ T := by
  refine ⟨fun q hq => ?_, (Subgroup.mem_normalizer_iff.mp hyT c).mp hc.2⟩
  have hq' : y⁻¹ * q * y ∈ Q := by
    refine (Subgroup.mem_normalizer_iff.mp hyQ (y⁻¹ * q * y)).mpr ?_
    have h : y * (y⁻¹ * q * y) * y⁻¹ = q := by group
    rw [h]
    exact hq
  have hcq : (y⁻¹ * q * y) * c = c * (y⁻¹ * q * y) := hc.1 _ hq'
  calc q * (y * c * y⁻¹) = y * ((y⁻¹ * q * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * q * y)) * y⁻¹ := by rw [hcq]
    _ = (y * c * y⁻¹) * q := by group

theorem asc82Lemma115b_of (hp : Asc82Pre11) (h112 : Asc82Lemma112) : Asc82Lemma115b := by
  intro G _ _ t L S z K1 K2 T R hctx hA6
  obtain ⟨ht2, hz2, htz, ht1, hz1, hne, htS, hzS, hQS⟩ := sec11L114_data hp hctx
  have hA : secCTQ K1 K2 T = zpowers t ⊔ zpowers z := by
    rcases h112 G t L S z K1 K2 T R hctx with ⟨-, hA⟩ | ⟨h6, -⟩
    · exact hA
    · exact (sec11L115_alt6_not_perm6 hA6 h6).elim
  obtain ⟨-, hcl, -, -⟩ := asc82Step111T_of hp G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp
    hctx.sylowT hctx.S_le
  obtain ⟨m, hmT, hm⟩ : t * z ∈ conjClassIn T t := by
    rw [hcl]
    simp
  have hSR : S ≤ R := hctx.S_le.trans hctx.T_le
  by_contra hRT
  obtain ⟨y, hyR, hyN, hyT⟩ := CFSG.OddStandard.SmallF3.HarrisU33.S4A.exists_mem_normalizer_not_mem
    hctx.sylowR.2.1 (lt_of_le_of_ne hctx.T_le (fun h => hRT h.symm))
  have hyQ : y ∈ normalizer (secQ K1 K2 : Set G) := hctx.sylowR.1 hyR
  have htC : t ∈ secCTQ K1 K2 T := ⟨(sec11L114_cent_Q hp hctx).1, hctx.S_le htS⟩
  have hyt : y * t * y⁻¹ ∈ zpowers t ⊔ zpowers z := by
    rw [← hA]
    exact sec11L115_conj_cent hyQ hyN htC
  rcases (sec11L114_pair_mem ht2 hz2 htz).1 hyt with h1 | h1 | h1 | h1
  · exact ht1 (calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group)
  · have hcomm : y * t = t * y := calc y * t = (y * t * y⁻¹) * y := by group
      _ = t * y := by rw [h1]
    exact hyT (hctx.S_le (sec11L114_cent_le hctx.sylow hctx.sylowR.2.1 hSR hyR hcomm))
  · exact sec10_not_conj_z hp.s3.l37 hctx.toSec10Ctx y (by rw [← h1]; group)
  · have hmR : m ∈ R := hctx.T_le hmT
    have hcomm : (m⁻¹ * y) * t = t * (m⁻¹ * y) := by
      calc (m⁻¹ * y) * t = (m⁻¹ * (y * t * y⁻¹) * m) * (m⁻¹ * y) := by group
        _ = (m⁻¹ * (m * t * m⁻¹) * m) * (m⁻¹ * y) := by rw [h1, hm]
        _ = t * (m⁻¹ * y) := by group
    have hS' : m⁻¹ * y ∈ S :=
      sec11L114_cent_le hctx.sylow hctx.sylowR.2.1 hSR (R.mul_mem (R.inv_mem hmR) hyR) hcomm
    apply hyT
    have h : y = m * (m⁻¹ * y) := by group
    rw [h]
    exact T.mul_mem hmT (hctx.S_le hS')

end CFSG.OddStandard.SmallF3.Omega
