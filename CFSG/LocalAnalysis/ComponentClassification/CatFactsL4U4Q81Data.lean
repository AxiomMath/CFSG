module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Inner
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem Lemma47.ofType_of_isLemma46d {p f k : ℕ} (hp2 : p ≠ 2) {β : X} {tb : MBar β}
    (hd : IsLemma46d p f L β tb) (hE : IsQuasisimple ↥(layer (MBar β)))
    (hm : Blueprint.LieModel (↥(layer (MBar β)) ⧸ center ↥(layer (MBar β))) .PSL 4 p k ∨
      Blueprint.LieModel (↥(layer (MBar β)) ⧸ center ↥(layer (MBar β))) .PSU 4 p k) :
    IsOfType (HarrisF p) ↥(layer (MBar β)) := by
  have hEn : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  rcases hd with ⟨-, hT⟩ | ⟨K₁, K₂, h12, -, hc12, -, ⟨e₁⟩, -, hmK, -, -⟩
  · exact hT
  · exfalso
    have hc21 : K₂ ≤ centralizer (K₁ : Set (MBar β)) := le_centralizer_iff.mp hc12
    have hK₁c : IsComponent K₁ :=
      Lemma47.isComponent_of_sup (GSThmB.OddQuot.lieModel_of_equiv e₁.symm hmK) hc21
        (h12 ▸ hEn.isSubnormal)
    have hEc : IsComponent (layer (MBar β)) := ⟨hE, hEn.isSubnormal⟩
    have hK₁E : K₁ ≤ layer (MBar β) := h12 ▸ le_sup_left
    rcases LocalCores.distinct_components_commute hK₁c hEc with h1 | h1
    · subst h1
      exact Lemma47.not_four_of_mulEquiv_psl_two hp2 e₁ hmK hm
    · have hc : K₁ ≤ centralizer (K₁ : Set (MBar β)) :=
        (commutator_eq_bot_iff_le_centralizer.mp h1).trans (centralizer_le hK₁E)
      exact Lemma47.ne_bot_of_isQuasisimple hK₁c.1
        (Lemma47.eq_bot_of_le_centralizer_self hK₁c.1.1 hc)

namespace Standing.Setup42

variable {h : Standing t L 3 4} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem tBar_mem_normalizer_layer (hσ : Setup42 h hS w z) (i j : ℕ) :
    hσ.tBar i j ∈ normalizer
      ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) : Subgroup _) : Set _) := by
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  rw [normalizer_eq_top_iff.mpr hEn]
  exact mem_top _

structure Q81Data (hσ : Setup42 h hS w z) (i j : ℕ) : Prop where
  quasisimple : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  center_cases :
    (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∧
      (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 1 ∨
        (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 ∧
          4 ∣ 3 ^ 1 - 1))) ∨
    (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1 ∧
      (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 1 ∨
        (Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 ∧
          4 ∣ 3 ^ 1 + 1)))
  isPGroup_centralizer : IsPGroup 2 ↥(centralizer
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
  tBar_not_mem : hσ.tBar i j ∉ centralizer
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  layerIn_eq : GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
    centralizer {hσ.tBar i j}) = KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  lieModel : Blueprint.LieModel ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) .PSL 2 3 2
  graph : ∀ I : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
    Q81.IsInnDiag (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) I → hσ.tBar i j ∉ I
  sl2 : ∀ w' ∈ KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j), orderOf w' = 2 →
    ∃ X₁ X₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), X₁ ≠ X₂ ∧
      X₁ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
      X₂ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
      (X₁.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {w'})).IsSubnormal ∧
      (X₂.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {w'})).IsSubnormal ∧
      X₁ ≤ centralizer (X₂ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      X₁ ⊓ X₂ = zpowers w' ∧ IsSLTwoOver 3 ↥X₁ ∧ IsSLTwoOver 3 ↥X₂
  ofType : IsOfType (HarrisF 3) ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

theorem q81Data_of [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKG : AutPSL2SylowInput) (hGA : TBLit.GriessMultipliersOdd)
    (hT1 : Harris82Theorem1KProper) (hC3 : L4U4InvolutionCentralizerFact)
    (hσ : Setup42 h hS w z) (i j : ℕ)
    (hc : IsLemma46c L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hd : IsLemma46d 3 4 L (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hσ.tBar i j))
    (he : IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hg : IsLemma46g (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hE : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hm : Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1) :
    Q81Data hσ i j := by
  have hZc := hσ.center_layer_cases hnonab hK hcat hGA hT1 i j hc hE hm
  have htc := hσ.tBar_not_mem_centralizer_layer hnonab hK hSch hFC hKC i j he hE hm
  have hKm : Blueprint.LieModel ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) .PSL 2 3 2 :=
    hσ.lieModel_KBar hFC hKC i j he
  have hlay := hσ.layerIn_layer_centralizer_tBar hnonab hK hSch hFC hKC i j
  have hlie : Blueprint.LieModel ↥(GSThmB.layerIn
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hσ.tBar i j}))
      .PSL 2 3 2 := by
    rw [hlay]
    exact hKm
  have ht2 : hσ.tBar i j * hσ.tBar i j = 1 := by
    have h1 := pow_orderOf_eq_one (hσ.tBar i j)
    rw [hσ.orderOf_tBar i j, sq] at h1
    exact h1
  have hC : centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) =
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [← hg.2.1, hg.1]
  obtain ⟨-, hcase⟩ := hC3 _ _ (hσ.tBar i j) 3 1 2 Nat.prime_three (by norm_num) le_rfl
    hE hZc (hσ.tBar_mem_normalizer_layer i j) ht2 htc hlie
  refine ⟨hE, hZc, ?_, htc, hlay, hKm, ?_, ?_, Lemma47.ofType_of_isLemma46d (by norm_num) hd hE hm⟩
  · rw [hC]
    exact pCore_isPGroup
  · intro I hI htI
    obtain ⟨B, hB, hZB, A, hAB, hA, hA8⟩ := hI.inner_b _ htI ht2 htc hlie
    exact hσ.not_inner_of_lemma47 hKG i j (hB.trans inf_le_right) hZB hAB hA hA8
  · intro w' hw' hw2
    rcases hcase with ⟨B, hB, hZB, A, hAB, hA, hA8⟩ | hgraph
    · exact (hσ.not_inner_of_lemma47 hKG i j (hB.trans inf_le_right) hZB hAB hA hA8).elim
    · exact hgraph w' (hlay ▸ hw') hw2

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
