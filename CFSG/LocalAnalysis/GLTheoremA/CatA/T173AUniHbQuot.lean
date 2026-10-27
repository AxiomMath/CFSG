module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem hb_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S B : Subgroup Ω} {x : Ω} (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    (hB : IsElemAbelian p B) (hBS : B ≤ Subgroup.normalizer (S : Set Ω))
    (hxC : x ∈ Subgroup.centralizer (S : Set Ω)) (hBx : B = Subgroup.zpowers x ⊔ B ⊓ S)
    (hb : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set Ω) ∧
      (⁅T, B⁆ : Subgroup Ω) ≠ ⊥) :
    ∃ T' : Subgroup (↥S ⧸ Subgroup.center ↥S), IsPGroup 2 T' ∧
      modCentreImage S B ≤ Subgroup.normalizer (T' : Set (↥S ⧸ Subgroup.center ↥S)) ∧
      (⁅T', modCentreImage S B⁆ : Subgroup (↥S ⧸ Subgroup.center ↥S)) ≠ ⊥ := by
  obtain ⟨T, hTS, hT2, hBnorm, hTB_ne⟩ := hb
  let q : ↥S →* (↥S ⧸ Subgroup.center ↥S) :=
    QuotientGroup.mk' (Subgroup.center ↥S)
  let D : Subgroup Ω := B ⊓ S
  let T' : Subgroup (↥S ⧸ Subgroup.center ↥S) := (T.subgroupOf S).map q
  refine ⟨T', ?_, ?_, ?_⟩
  · have hTsub : IsPGroup 2 (T.subgroupOf S) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTS).symm
    simpa [T'] using hTsub.map q
  ·
    have hDnormT : D ≤ Subgroup.normalizer (T : Set Ω) := inf_le_left.trans hBnorm
    have hDsub : D.subgroupOf S ≤
        Subgroup.normalizer (T.subgroupOf S : Set ↥S) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTS]
      intro d hd
      exact hDnormT hd
    have hC : modCentreImage S B = (D.subgroupOf S).map q := by
      simp [modCentreImage, D, q]
    rw [hC]
    exact (Subgroup.map_mono hDsub).trans
      (Subgroup.le_normalizer_map (H := T.subgroupOf S) q)
  · intro hcomm
    have hmap : ((⁅T.subgroupOf S, D.subgroupOf S⁆ : Subgroup ↥S).map q) =
        ⁅T', modCentreImage S B⁆ := by
      have hC : modCentreImage S B = (D.subgroupOf S).map q := by
        simp [modCentreImage, D, q]
      rw [hC, Subgroup.map_commutator]
    have hcenter : (⁅T, D⁆ : Subgroup Ω) ≤ (Subgroup.center ↥S).map S.subtype := by
      rw [Subgroup.commutator_le]
      intro t ht d hd
      have htS : t ∈ S := hTS ht
      have hdS : d ∈ S := hd.2
      have hmemS : ⁅t, d⁆ ∈ S := by
        rw [commutatorElement_def]
        exact S.mul_mem (S.mul_mem (S.mul_mem htS hdS) (S.inv_mem htS)) (S.inv_mem hdS)
      have hmemComm : (⟨⁅t, d⁆, hmemS⟩ : ↥S) ∈
          (⁅T.subgroupOf S, D.subgroupOf S⁆ : Subgroup ↥S) := by
        have heq : (⟨⁅t, d⁆, hmemS⟩ : ↥S) =
            ⁅(⟨t, htS⟩ : ↥S), (⟨d, hdS⟩ : ↥S)⁆ := by
          apply Subtype.ext
          simp [commutatorElement_def, mul_assoc]
        rw [heq]
        exact Subgroup.commutator_mem_commutator
          (show (⟨t, htS⟩ : ↥S) ∈ T.subgroupOf S from ht)
          (show (⟨d, hdS⟩ : ↥S) ∈ D.subgroupOf S from hd)
      have hqmem : q ⟨⁅t, d⁆, hmemS⟩ ∈ ⁅T', modCentreImage S B⁆ := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem q hmemComm
      have hq1 : q ⟨⁅t, d⁆, hmemS⟩ = 1 := by
        have := hqmem
        rw [hcomm] at this
        simpa using this
      have hcenterS : (⟨⁅t, d⁆, hmemS⟩ : ↥S) ∈ Subgroup.center ↥S := by
        have hker : (⟨⁅t, d⁆, hmemS⟩ : ↥S) ∈ MonoidHom.ker q :=
          MonoidHom.mem_ker.mpr hq1
        rwa [QuotientGroup.ker_mk' (Subgroup.center ↥S)] at hker
      exact Subgroup.mem_map.mpr ⟨_, hcenterS, rfl⟩
    have hDcent : D ≤ Subgroup.centralizer ((⁅T, D⁆ : Subgroup Ω) : Set Ω) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨zS, hzS, hz_eq⟩ := Subgroup.mem_map.mp (hcenter hz)
      have hdS : d ∈ S := hd.2
      have hcommS : (⟨d, hdS⟩ : ↥S) * zS = zS * ⟨d, hdS⟩ :=
        Subgroup.mem_center_iff.mp hzS ⟨d, hdS⟩
      rw [← hz_eq]
      simpa using (congrArg Subtype.val hcommS).symm
    have hdouble_bot : (⁅⁅T, D⁆, D⁆ : Subgroup Ω) = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mpr hDcent)
    have hDexp : Monoid.exponent ↥D ∣ p := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => ?_)
      exact Subtype.ext (by simpa using hB.2 (g : Ω) g.2.1)
    have hDp : IsPGroup p D :=
      IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hDexp)
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hcop : Nat.Coprime p (Nat.card T) := by
      rw [hk]
      simpa using Nat.coprime_pow_primes 1 k hp Nat.prime_two hp2
    have hDnormT : D ≤ Subgroup.normalizer (T : Set Ω) := inf_le_left.trans hBnorm
    have hidem : (⁅⁅T, D⁆, D⁆ : Subgroup Ω) = ⁅T, D⁆ :=
      CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
        hp D T hDp (hp.coprime_iff_not_dvd.mp hcop) hDnormT
    have hTD_bot : (⁅T, D⁆ : Subgroup Ω) = ⊥ := by
      rw [← hidem]
      exact hdouble_bot
    have hDcentT : D ≤ Subgroup.centralizer (T : Set Ω) :=
      Subgroup.le_centralizer_iff.mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTD_bot)
    have hx_cent : x ∈ Subgroup.centralizer (T : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subgroup.mem_centralizer_iff.mp hxC t (hTS ht)
    have hBD : B ≤ Subgroup.centralizer (T : Set Ω) := by
      rw [hBx]
      exact sup_le (Subgroup.zpowers_le.mpr hx_cent) hDcentT
    exact hTB_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hBD))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
