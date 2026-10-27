module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem kFactCenterFive_of_coverRankFive (hCov : KFactCoverRankFive) : KFactCenterFive := by
  intro K _ _ hK hcat h5
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Z := Subgroup.center K with hZdef
  obtain ⟨S⟩ : Nonempty (Sylow 5 Z) := inferInstance
  have hSn : (S : Subgroup Z).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime S.card_coprime_index
  have hcardZ : Nat.card (S : Subgroup Z) * Nat.card H = Nat.card Z := hH.card_mul_card
  have hSidx : Nat.card H = (S : Subgroup Z).index := by
    have := (S : Subgroup Z).card_mul_index
    have hpos : 0 < Nat.card (S : Subgroup Z) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (hcardZ.trans this.symm)
  have hH5 : ¬ 5 ∣ Nat.card H := hSidx ▸ S.not_dvd_index
  have hSne : (S : Subgroup Z) ≠ ⊥ := S.ne_bot_of_dvd_card h5
  set A : Subgroup K := H.map Z.subtype with hAdef
  have hAZ : A ≤ Z := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hAn : A.Normal :=
    ⟨fun a ha g => by
      rw [Subgroup.mem_center_iff.1 (hAZ ha) g, mul_inv_cancel_right]
      exact ha⟩
  have hAcard : Nat.card A = Nat.card H :=
    Nat.card_congr (H.equivMapOfInjective _ Z.subtype_injective).toEquiv.symm
  have hA5 : ¬ 5 ∣ Nat.card A := hAcard ▸ hH5
  let mk := QuotientGroup.mk' A
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective A
  have hker : mk.ker ≤ Subgroup.center K := by rw [QuotientGroup.ker_mk']; exact hAZ
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperf mk hsurj hker
  have hcenter : Subgroup.center (K ⧸ A) = Z.map mk := by
    rw [hZdef, ← hcomap, Subgroup.map_comap_eq_self_of_surjective hsurj]
  let e : (K ⧸ A) ⧸ Subgroup.center (K ⧸ A) ≃* K ⧸ Z :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientQuotientEquivQuotient A Z hAZ)
  have hqs : Open.IsQuasisimple (K ⧸ A) := by
    refine ⟨?_, ?_⟩
    · have h1 : (commutator K).map mk = ⊤ := by
        rw [hK.1, Subgroup.map_top_of_surjective mk hsurj]
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective mk hsurj]
        at h1
      rw [commutator_def]
      exact h1
    · have : IsSimpleGroup (K ⧸ Z) := hK.2
      exact e.isSimpleGroup
  have hcat' : IsCatalogGroup ((K ⧸ A) ⧸ Subgroup.center (K ⧸ A)) := by
    obtain ⟨i, ⟨φ⟩⟩ := hcat
    exact ⟨i, ⟨e.trans φ⟩⟩
  have hSA : Z.map mk ≤ ((S : Subgroup Z).map Z.subtype).map mk := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨⟨s, h⟩, hsh⟩ := hH.existsUnique ⟨z, hz⟩ |>.exists
    have hzsh : z = (s : Z) * (h : Z) := by
      have := congrArg Subtype.val hsh
      simpa using this.symm
    refine ⟨s, ⟨s, s.2, rfl⟩, ?_⟩
    have hhA : ((h : Z) : K) ∈ A := ⟨h, h.2, rfl⟩
    have hmk : mk ((h : Z) : K) = 1 := (QuotientGroup.eq_one_iff _).2 hhA
    rw [hzsh, map_mul, hmk, mul_one]
  have hp5 : IsPGroup 5 (Subgroup.center (K ⧸ A)) := by
    rw [hcenter]
    exact ((S.isPGroup'.map Z.subtype).map mk).to_le hSA
  have hne : Subgroup.center (K ⧸ A) ≠ ⊥ := by
    rw [hcenter]
    intro hbot
    have hle : Z ≤ A := by
      intro z hz
      have : mk z = 1 := by
        have hmem : mk z ∈ Z.map mk := ⟨z, hz, rfl⟩
        rw [hbot] at hmem
        exact hmem
      exact (QuotientGroup.eq_one_iff z).1 this
    have h1 := Subgroup.card_le_of_le hle
    rw [hAcard, ← hcardZ] at h1
    have h2 : 1 < Nat.card (S : Subgroup Z) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hSne
    have h3 : 0 < Nat.card H := Nat.card_pos
    nlinarith
  have h4 := hCov (K ⧸ A) hqs hcat' 5 Nat.prime_five le_rfl hne hp5
  rwa [CFSG.SectionRank.pRank_quotient_eq A hA5] at h4

end CFSG.AGLEmbedding
