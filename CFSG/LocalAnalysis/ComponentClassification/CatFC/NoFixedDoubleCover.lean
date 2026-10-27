module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.NFDCReduce
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause1
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause2
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.TwoAltEightPowFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (not_oddLieOrder_L34 not_oddLieOrder_A11)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (alt_degree_unique)
open CFSG.OddStandard.AltStdSec (not_evenLieType_alt)


theorem card_quotient_of_alt11 {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 11))) : Nat.card X = 19958400 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem rows_alt11 (s : TauCeti.SporadicName) (hd : 19958400 ∣ AGLEmbedding.sporOrd s) :
    (SporadicInnerRow s 19958400 → s = .Ly) ∧ ¬ SporadicOuterRow s 19958400 := by
  cases s <;> first
    | exact absurd hd (by simp only [AGLEmbedding.sporOrd]; decide)
    | (simp only [SporadicInnerRow, SporadicOuterRow]; decide)

theorem center_eq_bot_of_mulEquiv_alt {Y : Type} [Group Y] {k : ℕ} (hk : 5 ≤ k)
    (e : Y ≃* alternatingGroup (Fin k)) : center Y = ⊥ := by
  have hZ : center (alternatingGroup (Fin k)) = ⊥ :=
    alternatingGroup.center_eq_bot (α := Fin k) (by rw [Nat.card_fin]; omega)
  have hmap := map_center_equiv e
  rw [hZ] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap

theorem card_eq_504_of_lieModel_psl28 (hO : LieOrderFormulasInput) {D : Type} [Group D]
    (hL8 : LieModel D .PSL 2 2 3) : Nat.card D = 504 := by
  have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
    ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
  obtain ⟨-, h1, -⟩ := hO _ .PSL 2 2 3 hadmL hL8
  simp only [lieOrderDivisor, lieOrderNumerator] at h1
  norm_num [Finset.Icc_self] at h1
  omega

theorem catalogNoFixedDoubleCover_of_inputs (I : ArmInputs) (hT : EvenOuterTypedInput)
    (hHSO : HeSuzONNoAltEight)
    (hMcL : ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      (S ≃* Carrier .McL) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      σ ∈ (MulAut.conj : S →* MulAut S).range → ∀ {D : Subgroup ↥(fixedSubgroup σ)},
      IsComponent D → Nat.card (center ↥D) = 2)
    (hLy : ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      (S ≃* Carrier .Ly) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      σ ∈ (MulAut.conj : S →* MulAut S).range → ∀ {D : Subgroup ↥(fixedSubgroup σ)},
      IsComponent D → Nat.card (center ↥D) = 2)
    (hHSZ : ∀ {Q : Type} [Group Q], Group.IsPerfect Q → (Q ⧸ center Q ≃* NativeSporadic.HS) →
      Nat.card (center Q) ≤ 2)
    (hHS4 : ∀ {E : Type} [Group E] [Finite E], Group.IsPerfect E → Nat.card (center E) = 2 →
      IsSporadic (E ⧸ center E) .HS → ∀ {z : E}, z ∈ center E → z ≠ 1 → ∀ w : E, w ^ 4 ≠ z)
    (hL44 : ∀ {Y : Type} [Group Y] [Finite Y], CFSG.IsQuasisimple Y →
      LieModel (Y ⧸ center Y) .PSL 4 2 2 → center Y = ⊥) :
    EvenSporadicStandard.Induction.Balance.CatalogNoFixedDoubleCover := by
  intro k hk X _ _ K B t hKq _ hcat hnalt ht htK hBK hBt hB hZ hBn
  have hk5 : 5 ≤ k := by omega
  have : Nontrivial ↥(center ↥B) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hB.2.1]
    norm_num
  obtain ⟨⟨zB, hzBc⟩, hzB1⟩ := exists_ne (1 : ↥(center ↥B))
  have hzB1' : zB ≠ 1 := fun h => hzB1 (Subtype.ext h)
  let zK : ↥K := ⟨zB.1, hBK zB.2⟩
  have hzKc : zK ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hcomm := hZ zB.1 zB.2 (fun b hb =>
      (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hzBc) ⟨b, hb⟩)).symm) y.1 y.2
    exact Subtype.ext hcomm.symm
  have hzK1 : zK ≠ 1 := by
    intro h
    apply hzB1'
    have h' : (zK : X) = 1 := by rw [h]; rfl
    exact Subtype.ext h'
  rcases nfdc_reduce hk5 hKq ht htK hBK hBt hB hZ hBn with hKA | ⟨σ, hσ, D, hD, ⟨eD⟩⟩
  · exact hnalt ⟨k, hk5, hKA⟩
  · have : IsSimpleGroup (↥K ⧸ center ↥K) := hKq.2.1
    have hna : ∃ a b : ↥K ⧸ center ↥K, a * b ≠ b * a := hKq.2.2
    have hZD : center ↥D = ⊥ := center_eq_bot_of_mulEquiv_alt hk5 eD
    have hDq : Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin k)) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hZD).trans (QuotientGroup.quotientBot.trans eD)⟩
    have hDle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
      ⟨n, k', -, hk'5, hk'n, -, ⟨θ⟩, -⟩ | ⟨-, hodd⟩ | ⟨heven, -, hE⟩ | ⟨s', ⟨es⟩⟩
    · exact hnalt ⟨n, by omega, ⟨θ⟩⟩
    · rcases hodd with ⟨τ', n', p, f', hp, hp2, hadm', hY⟩ | hL8
      · obtain ⟨-, h1, h2⟩ := I.order _ τ' n' p f' hadm' hY
        rcases hk with rfl | rfl
        · rw [card_quotient_of_alt8 hDq] at h1 h2
          exact not_oddLieOrder_L34 ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩
        · rw [card_quotient_of_alt11 hDq] at h1 h2
          exact not_oddLieOrder_A11 ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩
      · have h504 := card_eq_504_of_lieModel_psl28 I.order hL8
        rcases hk with rfl | rfl
        · rw [card_quotient_of_alt8 hDq] at hDle
          omega
        · rw [card_quotient_of_alt11 hDq] at hDle
          omega
    · rcases hk with rfl | rfl
      · have hL := lieModel_psl44_of_even_alt8 I.order I.evenInner hT hna heven hσ hD hDq
        have hKZ := hL44 hKq hL
        rw [hKZ] at hzKc
        exact hzK1 ((Subgroup.mem_bot).1 hzKc)
      · obtain ⟨e11⟩ := hDq
        rcases hE with hEv | hA6 | hU
        · exact not_evenLieType_alt I.order (m := 11) (by norm_num)
            (evenLieType_transport e11 hEv)
        · exact absurd (alt_degree_unique (by norm_num) (by norm_num) hA6 ⟨e11⟩) (by norm_num)
        · have hadm3 : StatedLieAdmissible .PSU 3 3 1 :=
            ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
          obtain ⟨-, h1, h2⟩ := I.order _ .PSU 3 3 1 hadm3 hU
          rw [card_quotient_of_alt11 ⟨e11⟩] at h1 h2
          exact not_oddLieOrder_A11 ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num, hadm3, h1, h2⟩
    · obtain ⟨hdvd, hin, hout⟩ := I.table ‹IsSimpleGroup (↥K ⧸ center ↥K)› hna es hσ hD
      rcases hk with rfl | rfl
      · rw [card_quotient_of_alt8 hDq] at hdvd hin hout
        obtain ⟨hr1, hr2⟩ := rows_alt8 s' hdvd
        by_cases hinn : σ ∈ (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K)).range
        · rcases hr1 (hin hinn) with rfl | rfl | rfl | rfl
          · have h2 := hMcL ‹IsSimpleGroup (↥K ⧸ center ↥K)› hna es hσ hinn hD
            rw [hZD] at h2
            simp at h2
          · exact hHSO _ ‹IsSimpleGroup (↥K ⧸ center ↥K)› hna (Or.inr (Or.inl ⟨es⟩)) σ hσ D hD hDq
          · exact hHSO _ ‹IsSimpleGroup (↥K ⧸ center ↥K)› hna (Or.inr (Or.inr ⟨es⟩)) σ hσ D hD hDq
          · exact hHSO _ ‹IsSimpleGroup (↥K ⧸ center ↥K)› hna (Or.inl ⟨es⟩) σ hσ D hD hDq
        · have h := hr2 (hout hinn)
          subst h
          have hKp : Group.IsPerfect ↥K := hKq.1
          have hle := hHSZ hKp es
          have hlt : 1 < Nat.card (center ↥K) := by
            rw [Finite.one_lt_card_iff_nontrivial]
            exact ⟨⟨⟨zK, hzKc⟩, 1, fun h => hzK1 (congrArg Subtype.val h)⟩⟩
          have hc2 : Nat.card (center ↥K) = 2 := by omega
          obtain ⟨w, hw⟩ := exists_pow_four_eq_of_doubleCover_alt8 hB hzBc hzB1'
          refine hHS4 hKp hc2 ⟨es⟩ hzKc hzK1 ⟨w.1, hBK w.2⟩ ?_
          apply Subtype.ext
          simp only [SubmonoidClass.coe_pow]
          exact congrArg Subtype.val hw
      · rw [card_quotient_of_alt11 hDq] at hdvd hin hout
        obtain ⟨hr1, hr2⟩ := rows_alt11 s' hdvd
        by_cases hinn : σ ∈ (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K)).range
        · have h := hr1 (hin hinn)
          subst h
          have h2 := hLy ‹IsSimpleGroup (↥K ⧸ center ↥K)› hna es hσ hinn hD
          rw [hZD] at h2
          simp at h2
        · exact hr2 (hout hinn)

end CFSG.ComponentClassification.CatFC
