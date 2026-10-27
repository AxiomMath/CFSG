module

public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.KCoreOpen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem i145s_centralizer_map {A : Type*} [Group A] [Finite A] (U : Subgroup A) [U.Normal]
    (hU : Nat.Coprime 3 (Nat.card U)) {Q : Subgroup A} (hQ : IsPGroup 3 Q) :
    (Subgroup.centralizer (Q : Set A)).map (QuotientGroup.mk' U) =
      Subgroup.centralizer ((Q.map (QuotientGroup.mk' U) : Subgroup (A ⧸ U)) :
        Set (A ⧸ U)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨q, hq, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hc q hq
    show QuotientGroup.mk q * QuotientGroup.mk c = QuotientGroup.mk c * QuotientGroup.mk q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  · intro ĉ hĉ
    have hN := Subgroup.centralizer_le_normalizer _ hĉ
    obtain ⟨c, hcN, rfl⟩ := normalizer_map_quotient_le U
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hU) hQ hN
    refine ⟨c, Subgroup.mem_centralizer_iff.2 fun q hq => ?_, rfl⟩
    have hk : c * q * c⁻¹ * q⁻¹ = 1 := by
      have hkQ : c * q * c⁻¹ * q⁻¹ ∈ Q :=
        Q.mul_mem ((Subgroup.mem_normalizer_iff.1 hcN q).1 hq) (Q.inv_mem hq)
      have hkU : c * q * c⁻¹ * q⁻¹ ∈ U := by
        rw [← QuotientGroup.eq_one_iff]
        have h1 : (QuotientGroup.mk q : A ⧸ U) * QuotientGroup.mk c =
            QuotientGroup.mk c * QuotientGroup.mk q :=
          Subgroup.mem_centralizer_iff.1 hĉ (QuotientGroup.mk q) ⟨q, hq, rfl⟩
        have h2 : (QuotientGroup.mk c : A ⧸ U) * QuotientGroup.mk q * (QuotientGroup.mk c)⁻¹ *
            (QuotientGroup.mk q)⁻¹ = 1 := by
          calc (QuotientGroup.mk c : A ⧸ U) * QuotientGroup.mk q * (QuotientGroup.mk c)⁻¹ *
              (QuotientGroup.mk q)⁻¹ = (QuotientGroup.mk q * QuotientGroup.mk c) *
              (QuotientGroup.mk c)⁻¹ * (QuotientGroup.mk q)⁻¹ := by rw [h1]
            _ = 1 := by group
        simpa using h2
      obtain ⟨a, ha⟩ := hQ.exists_card_eq
      have hcop : Nat.Coprime (Nat.card Q) (Nat.card U) := by
        rw [ha]
        exact Nat.Coprime.pow_left a hU
      have hd := Subgroup.disjoint_of_coprime_natCard (H := Q) (K := U) hcop
      have : c * q * c⁻¹ * q⁻¹ ∈ Q ⊓ U := ⟨hkQ, hkU⟩
      rwa [hd.eq_bot, Subgroup.mem_bot] at this
    have h2 : ⁅c, q⁆ = 1 := by
      rw [commutatorElement_def]
      exact hk
    exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm

theorem i145s_openKGroup_of_surjective {A B : Type*} [Group A] [Group B]
    (hA : CFSG.Open.IsKGroup A) (f : A →* B) (hf : Function.Surjective f) :
    CFSG.Open.IsKGroup B :=
  hA.of_surjective f hf

theorem i145s_primeCore_three_quotient (A : Type*) [Group A] [Finite A] :
    GLAPPrimeCore 3 (A ⧸ GLAPPrimeCore 3 A) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := GLAPPrimeCore 3 A with hY
  set Z := GLAPPrimeCore 3 (A ⧸ Y) with hZ
  have hcopZ : Nat.Coprime 3 (Nat.card Z) := CFSG.pPrimeCore_coprime_card
  have hcopY : Nat.Coprime 3 (Nat.card Y) := CFSG.pPrimeCore_coprime_card
  have hpre : Nat.Coprime 3 (Nat.card (Z.comap (QuotientGroup.mk' Y))) := by
    have h : Nat.card (Z.comap (QuotientGroup.mk' Y)) = Nat.card Y * Nat.card Z :=
      QuotientGroup.card_preimage_mk Y (Z : Set (A ⧸ Y))
    rw [h]
    exact hcopY.mul_right hcopZ
  have hnorm : (Z.comap (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.comap inferInstance _
  have hle : Z.comap (QuotientGroup.mk' Y) ≤ Y := le_sSup ⟨hnorm, hpre⟩
  have h2 : Z ≤ Y.map (QuotientGroup.mk' Y) := by
    calc Z = (Z.comap (QuotientGroup.mk' Y)).map (QuotientGroup.mk' Y) :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y) Z).symm
      _ ≤ _ := Subgroup.map_mono hle
  rw [(Subgroup.map_eq_bot_iff Y).2 (by rw [QuotientGroup.ker_mk'])] at h2
  exact le_bot_iff.1 h2

end CFSG.HardMathSupport.Solomon.Coordinator
