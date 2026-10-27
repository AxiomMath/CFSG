module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Quot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

@[expose] def S2019Full : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D J : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple q (PSimple p S) →
      IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
      S2019Omega p S B D J

theorem s2019Full_of_facts (hCl : S2019FactClassical) (hA1 : S2019FactA1)
    (hEx : S2019FactExceptional) (hAm : S2019FactAmbiguous) : S2019Full := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hChev hBel hSB hrank
  rcases hChev with hL | hA
  · obtain ⟨i, hi, e⟩ := hL
    cases i with
    | cyclic r hr => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie d =>
      have hchar : d.1.characteristic = q := hi
      by_cases hcl : S267ClassicalIdx d.1
      · by_cases ha : S2019IsA1 d.1
        · exact hA1 p q hp hp2 hq hq2 hqp Ω S B D J hSn hSq hSp
            ⟨TauCeti.CFSGIndex.lie d, ⟨hchar, ha⟩, e⟩ hBel hSB hrank
        · exact hCl p q hp hp2 hq hq2 hqp Ω S B D J hSn hSq hSp
            ⟨TauCeti.CFSGIndex.lie d, ⟨hchar, hcl, ha⟩, e⟩ hBel hSB hrank
      · exact hEx p q hp hp2 hq hq2 hqp Ω S B D J hSn hSq hSp
          ⟨TauCeti.CFSGIndex.lie d, ⟨hchar, hcl⟩, e⟩ hBel hSB hrank
  · exact hAm p q hp hp2 hq hq2 hqp Ω S B D J hSn hSq hSp hA hBel hSB hrank

section A

variable {A : Type} [Group A] [Finite A]

theorem s2019_A (hFull : S2019Full) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {B D K J : Subgroup A} (hBel : IsElemAbelian p B)
    (hKB : K ⊔ B = ⊤) (hrank : p ^ GLATwoLocalRank p A ≤ Nat.card B)
    (hBK : B ≤ Subgroup.normalizer (K : Set A)) (hQ : CFSG.Open.IsQuasisimple (PQuot p K))
    (hChev : IsChevSimple q (PSimple p K)) (hC : B ⊓ centModSubgroup p K ≠ ⊥) (hDB : D ≤ B)
    (hCD : B ⊓ centModSubgroup p K ≤ D) (hrel : (B ⊓ centModSubgroup p K).relIndex D ≤ p)
    (hD : p ^ 2 * Nat.card D ≤ Nat.card B)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set A)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set A)) (hcm : ∀ b ∈ B, CentMod p J b ↔ b ∈ D)
    {T : Subgroup A} (hTK : T ≤ K) (hT2 : IsPGroup 2 T)
    (hJT : J ≤ Subgroup.normalizer ((T ⊔ GLAPPrimeCoreOf p K : Subgroup A) : Set A)) :
    ⁅T, J⁆ ≤ GLAPPrimeCoreOf p K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hKn : K.Normal := by
    refine Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 ?_)
    rw [← hKB]
    exact sup_le Subgroup.le_normalizer hBK
  set N₀ : Subgroup A := GLAPPrimeCoreOf p K with hN₀def
  haveI hN₀n : N₀.Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p K
    rw [Subgroup.normalizer_eq_top_iff.2 hKn, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  have hN : ¬ p ∣ Nat.card N₀ := not_dvd_card_glaPPrimeCoreOf hp K
  have hNK : N₀ ≤ K := Subgroup.map_subtype_le _
  set π : A →* A ⧸ N₀ := QuotientGroup.mk' N₀ with hπ
  have hker : ¬ p ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hN
  set S : Subgroup (A ⧸ N₀) := K.map π with hS
  have hSn : S.Normal := hKn.map π (QuotientGroup.mk'_surjective N₀)
  obtain ⟨e₁⟩ : Nonempty (PQuot p K ≃* ↥S) :=
    nonempty_pQuot_equiv_map_self (p := p) (ψ := π) (K := K)
      (by rw [hπ, QuotientGroup.ker_mk', inf_eq_left.2 hNK])
  have hSq : CFSG.Open.IsQuasisimple ↥S := hQ.of_mulEquiv e₁.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 := map_glaPPrimeCoreOf hp π hker K
    have h2 : GLAPPrimeCoreOf p S = ⊥ := by
      rw [← h1]
      exact (Subgroup.map_eq_bot_iff _).2 (by rw [hπ, QuotientGroup.ker_mk'])
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h2
  let eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  let eK : PQuot p K ≃* PQuot p S := e₁.trans eS.symm
  let eKS : PSimple p K ≃* PSimple p S := QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  have hChevS : IsChevSimple q (PSimple p S) :=
    chev_isChevSimple_of_mulEquiv eKS.symm hChev
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hBel
  have hDp : IsPGroup p D := hBp.to_le hDB
  have hBbel : IsElemAbelian p (B.map π) := CFSG.SectionRank.isElemAbelian_map hBel π
  have hcB : Nat.card (B.map π) = Nat.card B := card_map_of_isPGroup hp π hker hBp
  have hcD : Nat.card (D.map π) = Nat.card D := card_map_of_isPGroup hp π hker hDp
  have hSB : S ⊔ B.map π = ⊤ := by
    rw [hS, ← Subgroup.map_sup, hKB,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N₀)]
  have hrank' : p ^ GLATwoLocalRank p (A ⧸ N₀) ≤ Nat.card (B.map π) := by
    rw [hcB]
    exact le_trans (pow_le_pow_right₀ hp.one_lt.le (glaTwoLocalRank_quotient_le hp hp2 N₀ hN)) hrank
  have hOmega := hFull p q hp hp2 hq hq2 hqp (A ⧸ N₀) S (B.map π) (D.map π) (J.map π) hSn hSq hSp
    hChevS hBbel hSB hrank'
  have hconc := s2019OmegaLE_of_omega hp hSq hSp hBbel hOmega
  have hmapC : (B ⊓ centModSubgroup p K).map π = B.map π ⊓ centModSubgroup p S :=
    map_inf_centModSubgroup hp π hker hBK
  have hcC : Nat.card ↥(B.map π ⊓ centModSubgroup p S) = Nat.card ↥(B ⊓ centModSubgroup p K) :=
    card_inf_centModSubgroup_map hp π hker hBp hBK
  have hC' : B.map π ⊓ centModSubgroup p S ≠ ⊥ := by
    intro h
    apply hC
    rw [h, Subgroup.card_bot] at hcC
    exact Subgroup.eq_bot_of_card_eq _ hcC.symm
  have hCD' : B.map π ⊓ centModSubgroup p S ≤ D.map π := by
    rw [← hmapC]
    exact Subgroup.map_mono hCD
  have hrel' : (B.map π ⊓ centModSubgroup p S).relIndex (D.map π) ≤ p := by
    rw [relIndex_eq_of_card hCD (hCD') hcC hcD]
    exact hrel
  have hD' : p ^ 2 * Nat.card (D.map π) ≤ Nat.card (B.map π) := by
    rw [hcD, hcB]; exact hD
  have hJ' : GLAPComponent p
      (S ⊓ Subgroup.centralizer ((D.map π : Subgroup (A ⧸ N₀)) : Set (A ⧸ N₀))) (J.map π) :=
    glaPComponent_map_inf_centralizer hp π hker hDp (hDB.trans hBK) hJ
  have hBJ' : B.map π ≤ Subgroup.normalizer ((J.map π : Subgroup (A ⧸ N₀)) : Set (A ⧸ N₀)) :=
    (Subgroup.map_mono hBJ).trans (Subgroup.le_normalizer_map π)
  have hcm' : ∀ b ∈ B.map π, CentMod p (J.map π) b ↔ b ∈ D.map π := by
    rintro _ ⟨b, hb, rfl⟩
    rw [centMod_iff, ← mem_centModSubgroup_map_iff hp π hker (hBJ hb), ← centMod_iff, hcm b hb]
    exact ⟨fun h => ⟨b, h, rfl⟩, fun h => mem_of_map_mem_of_isPGroup hp π hker hBp hDB hb h⟩
  have hNbot : N₀.map π = ⊥ :=
    (Subgroup.map_eq_bot_iff _).2 (by rw [hπ, QuotientGroup.ker_mk'])
  have hJT' : J.map π ≤ Subgroup.normalizer ((T.map π : Subgroup (A ⧸ N₀)) : Set (A ⧸ N₀)) := by
    have h1 : (T ⊔ N₀).map π = T.map π := by
      rw [Subgroup.map_sup, hNbot, sup_bot_eq]
    calc J.map π ≤ (Subgroup.normalizer ((T ⊔ N₀ : Subgroup A) : Set A)).map π :=
          Subgroup.map_mono hJT
      _ ≤ Subgroup.normalizer (((T ⊔ N₀).map π : Subgroup (A ⧸ N₀)) : Set (A ⧸ N₀)) :=
          Subgroup.le_normalizer_map π
      _ = Subgroup.normalizer ((T.map π : Subgroup (A ⧸ N₀)) : Set (A ⧸ N₀)) := by rw [h1]
  have hfin := hconc hC' (Subgroup.map_mono hDB) hCD' hrel' hD' hJ' hBJ' hcm' (T.map π)
    (Subgroup.map_mono hTK) (hT2.map π) hJT'
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hfin
  exact hfin

end A

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
