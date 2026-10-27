module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Class
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdStep2

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.exists_sylow_cent
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K) {r : G} (hrR : r ∈ baum S)
    (hrC : r ∈ Subgroup.centralizer (K : Set G)) (hr2 : r * r = 1) (hr1 : r ≠ 1)
    {J : Subgroup G} (hJ : IsComponentIn J (centralizerElem r)) :
    ∃ Tr : Subgroup G, IsSylowTwoOf Tr (centralizerElem r) ∧ z₂ ∈ Tr ∧
      ∀ P : Subgroup G, P ≤ Tr → (centralizerElem z₂).relIndex P ≤ 4 := by
  have hcs := hK.cs
  have hrz₂ : r * z₂ = z₂ * r := Subgroup.mem_centralizer_iff.mp hK.toA3A3x.z₂_mem.2 r hrR
  set CR : Subgroup G := centralizerElem r ⊓ baum S with hCR
  have hCR2 : IsPGroup 2 ↥CR := (isPGroup_baum hcs).to_le inf_le_right
  obtain ⟨Tr, hCRTr, hTrS⟩ := exists_isSylowTwoOf_of_le (inf_le_left : CR ≤ centralizerElem r) hCR2
  have hz₂CR : z₂ ∈ CR :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hrz₂.symm, hK.z₂_mem_baum⟩
  have hTr2 : IsPGroup 2 ↥Tr := hTrS.isPGroup
  have hTrle : Tr ≤ centralizerElem r := hTrS.le
  have hTcard : Nat.card T = twoPart ⊤ := hcs.setting.sylow.card_eq
  have hdvd : Nat.card Tr ∣ twoPart ⊤ := card_dvd_twoPart le_top hTr2
  have hTr_lt : 2 * Nat.card Tr ≤ Nat.card T := by
    obtain ⟨k, hk⟩ := hdvd
    have hpos := twoPart_pos (⊤ : Subgroup G)
    have hTrpos : 0 < Nat.card Tr := Nat.card_pos
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · exfalso
      interval_cases k
      · omega
      · have hsyl : IsSylowTwoOf Tr ⊤ := isSylowTwoOf_of_card_eq le_top hTr2 (by omega)
        have hpc : pCoreOf 2 (centralizerElem r) ≠ ⊥ :=
          Id2519.pCoreOf_centralizer_ne_bot hr1 hr2
        have hchar : CharTwo (centralizerElem r) :=
          charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hcs.setting.qtke.2.1 hsyl hTrle hpc
        exact not_isComponentIn_of_charTwo hchar J hJ
    · have : Nat.card Tr * 2 ≤ Nat.card Tr * k := Nat.mul_le_mul_left _ hk2
      omega
  obtain ⟨-, -, -, -, ⟨-, -, hT4⟩⟩ := lemma2_4_30 hD h27_1 G T M H S L s hK.toA3A3
  have hidxR := hK.relIndex_centralizerElem_baum_le_two hD h27_1 h34 hrR hrC
  have hRcard : (centralizerElem r).relIndex (baum S) * Nat.card ↥CR = Nat.card (baum S) :=
    Subgroup.relIndex_mul_card _ _
  have hCRpos : 0 < Nat.card ↥CR := Nat.card_pos
  have hTr4 : Nat.card Tr ≤ 4 * Nat.card ↥CR := by
    have h1 : (centralizerElem r).relIndex (baum S) * Nat.card ↥CR ≤ 2 * Nat.card ↥CR :=
      Nat.mul_le_mul_right _ hidxR
    omega
  refine ⟨Tr, hTrS, hCRTr hz₂CR, fun P hP => ?_⟩
  have hne : ∀ Q U : Subgroup G, Q.relIndex U ≠ 0 := by
    intro Q U h0
    have := Subgroup.relIndex_mul_card Q U
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  have h1 : (centralizerElem z₂).relIndex P ≤ (centralizerElem z₂).relIndex Tr :=
    Subgroup.relIndex_le_of_le_right hP (hne _ _)
  have hCRz : CR ≤ centralizerElem z₂ := fun y hy => hK.toA3A3x.baum_le_cent₂ hy.2
  have h2 : (centralizerElem z₂).relIndex Tr ≤ CR.relIndex Tr :=
    Subgroup.relIndex_le_of_le_left hCRz (hne _ _)
  have h3 : CR.relIndex Tr * Nat.card ↥CR = Nat.card Tr := by
    have := Subgroup.relIndex_mul_card CR Tr
    rwa [inf_of_le_left hCRTr] at this
  have h4 : CR.relIndex Tr ≤ 4 := by
    by_contra hcon
    have : 5 * Nat.card ↥CR ≤ CR.relIndex Tr * Nat.card ↥CR := Nat.mul_le_mul_right _ (by omega)
    omega
  omega

end CFSG.QuasithinUnique.DoubleA3
