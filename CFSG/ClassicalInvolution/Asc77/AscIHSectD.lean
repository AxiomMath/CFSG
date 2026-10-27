module

public import CFSG.ClassicalInvolution.Asc77.AscT7AMain
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectA
public import CFSG.ClassicalInvolution.Asc77.AscIHSectB

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Datum

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem exists_datum_of_omegaLie (D : OmegaLie p f Φ) (hΦ : HypOmegaMod p f Φ)
    (hgen : omegaGen Φ = ⊤) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hne : Φ.Nonempty) :
    ∃ (t : StatedLieTag) (k e : ℕ) (_ : Ih8Model p f Φ t k e), HasLieType p f Φ t k := by
  have hcard := D.card_eq_one_of_transitive hΦ hgen htrans hne
  let i : Fin D.card := ⟨0, by omega⟩
  have hsurj := D.hom_surjective_of_gen hcard hgen i
  exact ⟨D.tag i, D.rank i, D.exp i,
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := hsurj
      cls := D.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => D.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g },
    D, hcard, i, rfl, rfl⟩

end Datum

section Neighbours

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}
  (M : Ih8Model p f Ω t k e)

include M

theorem Ih8Model.commutes_of_omegaNbr_sect (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R S : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hJ : S.map M.ψ ∈ omegaNbr Ω (R.map M.ψ)) : Commutes R S := by
  obtain ⟨A, hA2, hAJ, hAN, hAnc⟩ := ih8_nbr_sylow hp2 hΩ hJ
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eS⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hS
  have hodd := M.natCard_galoisField_odd hp2
  have hpR := M.cls_perfect hp2 hD4 hq hR
  have hpS := M.cls_perfect hp2 hD4 hq hS
  have hRS : R ≠ S := fun h => hJ.2.1 (by rw [h])
  obtain ⟨-, -, -, -, -, -, hzcomm⟩ := ih8_nbr_model M.ψ M.ker_le_center hodd hodd hpR eR eS hA2
    hAJ hAnc hAN
  have hdich := ih8_stdDichotomy M.isFundTag hG2 hD4 M.admissible
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hR)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  rcases hdich.map_of_commute hp2 hq' M.ψ M.ker_le_center hRl hSl (sl2Inv_mem eR)
    (sl2Inv_mem eS) (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hzcomm.symm
    with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact absurd (ih8_eq_of_map_eq M.ψ M.ker_le_center hpR hpS h) hRS
  · exact ih8_commutes_of_commutes_map M.ψ M.ker_le_center hpR h
  · obtain ⟨x, hx, y, hy, hxy⟩ := hAnc
    exact absurd (LinearBlockStandardPair.comm_of_normalizes
      (M.four_le_natCard_galoisField hD4 hq) hW (hAJ hx) (hAJ hy) (hAN hx) (hAN hy)) hxy
  · obtain ⟨x, hx, y, hy, hxy⟩ := hAnc
    have hf : 1 ≤ e := M.admissible.2.1
    exact absurd (UnitaryBlockStandardPair.comm_of_normalizes
      (CFSG.LieType.Universal.card_galoisField_two_mul p e hf) hq' hW (hAJ hx) (hAJ hy)
      (hAN hx) (hAN hy)) hxy

theorem Ih8Model.exists_clique (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {K K' J : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hJK : J ∈ omegaNbr Ω K) (hJK' : J ∈ omegaNbr Ω K') :
    ∃ A ∈ M.cls, ∃ B ∈ M.cls, ∃ S ∈ M.cls, A ≠ B ∧ A ≠ S ∧ B ≠ S ∧ Commutes A B ∧
      Commutes A S ∧ Commutes B S := by
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨B, hB, rfl⟩ := (M.mem_iff K').mp hK'Ω
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff J).mp hJK.1
  have hexA := M.oddCore_eq_bot hΩ hp2 hq hG2 hD4 hA
  have hpA := M.cls_perfect hp2 hD4 hq hA
  have hAB : A ≠ B := fun h => hne (by rw [h])
  have hAS : A ≠ S := fun h => hJK.2.1 (by rw [h])
  have hBS : B ≠ S := fun h => hJK'.2.1 (by rw [h])
  have hne' : A.map M.ψ ≠ B.map M.ψ := fun h => hne h.symm
  obtain ⟨hcomm, -⟩ := ih8_twin_data hΩ M.ker_le_center hpA (M.map_mem hA) (M.map_mem hB) hne'
    hzK hzK' hexA
  exact ⟨A, hA, B, hB, S, hS, hAB, hAS, hBS, hcomm,
    M.commutes_of_omegaNbr_sect hΩ hp2 hq hG2 hD4 hA hS hJK,
    M.commutes_of_omegaNbr_sect hΩ hp2 hq hG2 hD4 hB hS hJK'⟩

end Neighbours

section Facts

variable (p f)

@[expose] def SmallNoThree : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k p e → p ≠ 2 → 5 ≤ p ^ e →
    ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨ (t = .POmegaOdd ∧ k = 3) ∨
      (t = .POmegaMinus ∧ k = 4)) →
    ∀ A ∈ ModelFund p t k e, ∀ B ∈ ModelFund p t k e, ∀ S ∈ ModelFund p t k e,
      A ≠ B → A ≠ S → B ≠ S → Commutes A B → Commutes A S → Commutes B S → False

@[expose] def Ih8D4Star : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (e : ℕ),
    HypOmegaMod p f Ω → Nonempty (Ih8Model p f Ω .POmegaPlus 4 e) → T3.DStarConnected Ω

@[expose] def DStarConnectedTwinGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TransSection p f Φ →
    OmegaLie p f Φ → TwinTriple Φ → T3.DStarConnected Φ

end Facts

theorem dstarConnectedTwinGen_of (hNT : SmallNoThree p) (hP4 : Ih8G2D4 p f) (hD4 : Ih8D4Star p f)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : DStarConnectedTwinGen p f := by
  intro X _ _ Φ hS D htt
  obtain ⟨K, hK, K', hK'tw, hne', J, hJK, hJK'⟩ := htt
  have hΦ := hS.hyp
  have hne : Φ.Nonempty := ⟨K, hK⟩
  obtain ⟨t, k, e, M, -⟩ := exists_datum_of_omegaLie D hΦ hS.gen hS.trans hne
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · exfalso
    have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
    exact hne' ((hP4 hp2 hq X Φ hΦ hS.aEmpty hS.trans t k e ⟨M⟩ hG2d4).1 K hK K' hK'tw)
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4' : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have htop := top_notMem_of_transitive hS.trans hK hK'tw.1 hne'
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4']; exact hq
  obtain ⟨A, hA, B, hB, S, hS', hAB, hAS, hBS, cAB, cAS, cBS⟩ :=
    M.exists_clique hΦ hp2 hq hG2 hD4' hK hK'tw hne' hJK hJK'
  have hAf := M.cls_sub hA
  have hBf := M.cls_sub hB
  have hSf := M.cls_sub hS'
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4' with hconn | hsmall
  · intro K₁ hK₁ L hL
    exact T7A.mem_dstarComp_of_mem_dComp hp2 hΦ
      (M.dConnected_of_connected hp2 hq hne hG2 hD4' hconn K₁ hK₁ L hL)
  · rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·
      have hk2 : 2 ≤ k := M.admissible.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact (hnpsl ⟨rfl, rfl⟩).elim
      · have := four_le_of_commutes_psl hp2 (le_refl 3) hAf hBf hAB cAB
        omega
      · exact (hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inl ⟨rfl, rfl⟩)) A hAf B hBf S hSf
          hAB hAS hBS cAB cAS cBS).elim
    ·
      have hk3 : 3 ≤ k := M.admissible.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · have := four_le_of_commutes_psu hp2 M.admissible hAf hBf hAB cAB
        omega
      · exact (hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) A hAf B hBf
          S hSf hAB hAS hBS cAB cAS cBS).elim
    · exact (hNT _ _ _ M.admissible hp2 hq' (Or.inl ⟨rfl, rfl⟩) A hAf B hBf S hSf hAB hAS hBS
        cAB cAS cBS).elim
    · exact (hNT _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) A hAf B hBf S hSf hAB hAS hBS cAB cAS
        cBS).elim
    · exact hD4 hp2 hq X Φ e hΦ ⟨M⟩
    · exact (hNT _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) A hAf B hBf S hSf hAB hAS hBS cAB cAS
        cBS).elim

end CFSG.ClassicalInvolution.Asc77
