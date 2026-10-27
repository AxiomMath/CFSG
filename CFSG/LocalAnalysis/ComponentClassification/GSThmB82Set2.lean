module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Sec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29C
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def CF82Prop29Corr : Prop := CF82Prop29A10 ∧ CF82Prop29L4Corr ∧ CF82Prop29U4Corr

namespace Eight2

variable {X : Type} [Group X] [Finite X]

structure Setting2 (X : Type) [Group X] [Finite X] extends Setting1 X where
  p : ℕ
  f : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  hf : 1 ≤ f
  simple : IsSimpleGroup ↥(generalizedFitting (h.subQuot y))
  centralizer_eq : centralizer (generalizedFitting (h.subQuot y) : Set (h.subQuot y)) = ⊥
  type : IsSec82LType ↥(generalizedFitting (h.subQuot y)) p f
  J_type : IsSec8JType (↥sec.J ⧸ pPrimeCore 2 ↥sec.J) p f
  a_mem : sec.a ∈ generalizedFitting (h.subQuot y)
  mod4_L : Blueprint.LieModel ↥(generalizedFitting (h.subQuot y)) .PSL 4 p f → p ^ f % 4 = 3
  mod4_U : Blueprint.LieModel ↥(generalizedFitting (h.subQuot y)) .PSU 4 p f → p ^ f % 4 = 1
  tb : h.subQuot y
  tb_mem : tb ∈ generalizedFitting (h.subQuot y)
  tb_norm : tb ∈ normalizer (sec.S : Set (h.subQuot y))
  tb_not : tb ∉ sec.S
  tb_sq : tb * tb ∈ sec.S
  D_inf : (sec.S ⊓ sec.J) ⊓ conjugate (sec.S ⊓ sec.J) tb = ⊥
  D_comm : ∀ d ∈ sec.S ⊓ sec.J, ∀ e ∈ conjugate (sec.S ⊓ sec.J) tb, d * e = e * d
  D_sup : (sec.S ⊓ sec.J) ⊔ conjugate (sec.S ⊓ sec.J) tb =
    sec.S ⊓ generalizedFitting (h.subQuot y)
  a_mem_Dt : sec.a ∈ conjugate (sec.S ⊓ sec.J) tb ⊓ coreActionKernel sec.J
  a_central : ∀ e ∈ conjugate (sec.S ⊓ sec.J) tb, sec.a * e = e * sec.a
  Dt_index_A10 : Nonempty (↥(generalizedFitting (h.subQuot y)) ≃* alternatingGroup (Fin 10)) →
    (conjugate (sec.S ⊓ sec.J) tb ⊓ coreActionKernel sec.J).relIndex
      (conjugate (sec.S ⊓ sec.J) tb) = 2
  Cp_cyclic : ¬ Nonempty (↥(generalizedFitting (h.subQuot y)) ≃* alternatingGroup (Fin 10)) →
    IsCyclic ↥((sec.S ⊓ generalizedFitting (h.subQuot y)) ⊓ coreActionKernel sec.J)
  Cp_card : ¬ Nonempty (↥(generalizedFitting (h.subQuot y)) ≃* alternatingGroup (Fin 10)) →
    2 * Nat.card ↥((sec.S ⊓ generalizedFitting (h.subQuot y)) ⊓ coreActionKernel sec.J) =
      Nat.card ↥(sec.S ⊓ sec.J)

namespace Setting1

variable (s : Setting1 X)

theorem exists_setting2 (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hInn : CF82Inner)
    (h29 : CF82Prop29Corr) : ∃ s2 : Setting2 X, s2.toSetting1 = s := by
  obtain ⟨hFeq, hsimple, hcent, -, -⟩ := Hyp59.generalizedFitting_simple s.sec
  have hcent' : centralizer (generalizedFitting (s.h.subQuot s.y) : Set (s.h.subQuot s.y)) =
      ⊥ := by rw [hFeq]; exact hcent
  obtain ⟨p, f, hp, hp2, hf, htype, hJt⟩ := s.exists_params s.sec s.sec_J_equiv s.lemma81
  obtain ⟨haF, hmL, hmU⟩ := s.inner_of_sec hInn s.sec (s.sec_a s.secCond.a_mem_secSub)
    s.map_P_le_secP hp hp2 hf htype hJt
  have hSyl := s.sec.toHyp52.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
  obtain ⟨h29A, h29L, h29U⟩ := h29
  obtain ⟨tb, htF, htN, htS, ht2, hDi, hDc, hDs, haD, hac, hDix, hCc, hCn⟩ :
      ∃ tb ∈ generalizedFitting (s.h.subQuot s.y), tb ∈ normalizer (s.sec.S : Set _) ∧
        tb ∉ s.sec.S ∧ tb * tb ∈ s.sec.S ∧
        (s.sec.S ⊓ s.sec.J) ⊓ conjugate (s.sec.S ⊓ s.sec.J) tb = ⊥ ∧
        (∀ d ∈ s.sec.S ⊓ s.sec.J, ∀ e ∈ conjugate (s.sec.S ⊓ s.sec.J) tb, d * e = e * d) ∧
        (s.sec.S ⊓ s.sec.J) ⊔ conjugate (s.sec.S ⊓ s.sec.J) tb =
          s.sec.S ⊓ generalizedFitting (s.h.subQuot s.y) ∧
        s.sec.a ∈ conjugate (s.sec.S ⊓ s.sec.J) tb ⊓ coreActionKernel s.sec.J ∧
        (∀ e ∈ conjugate (s.sec.S ⊓ s.sec.J) tb, s.sec.a * e = e * s.sec.a) ∧
        (Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) →
          (conjugate (s.sec.S ⊓ s.sec.J) tb ⊓ coreActionKernel s.sec.J).relIndex
            (conjugate (s.sec.S ⊓ s.sec.J) tb) = 2) ∧
        (¬ Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) →
          IsCyclic ↥((s.sec.S ⊓ generalizedFitting (s.h.subQuot s.y)) ⊓
            coreActionKernel s.sec.J)) ∧
        (¬ Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) →
          2 * Nat.card ↥((s.sec.S ⊓ generalizedFitting (s.h.subQuot s.y)) ⊓
            coreActionKernel s.sec.J) = Nat.card ↥(s.sec.S ⊓ s.sec.J)) := by
    by_cases hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))
    · obtain ⟨tb, htF, htN, htS, ht2, hDi, hDc, hDs, hDix, haD, hac, -, -⟩ :=
        h29A (s.h.subQuot s.y) p f hp hp2 hf hcent' hA s.sec.a s.sec.orderOf_a s.sec.J s.sec.J_le
          s.sec.isPComponent_J hJt s.sec.S hSyl
      exact ⟨tb, htF, htN, htS, ht2, hDi, hDc, hDs, haD, hac, fun _ => hDix,
        fun h => absurd hA h, fun h => absurd hA h⟩
    · have hC : Prop29ConclCorr (s.h.subQuot s.y) s.sec.a s.sec.J s.sec.S := by
        rcases htype with hL | hU | hA'
        · exact h29L (s.h.subQuot s.y) p f hp hp2 hf hsimple hcent' hL (hmL hL) s.sec.a haF
            s.sec.orderOf_a s.sec.J s.sec.J_le s.sec.isPComponent_J hJt s.sec.S hSyl
        · exact h29U (s.h.subQuot s.y) p f hp hp2 hf hsimple hcent' hU (hmU hU) s.sec.a haF
            s.sec.orderOf_a s.sec.J s.sec.J_le s.sec.isPComponent_J hJt s.sec.S hSyl
        · exact absurd hA' hA
      obtain ⟨tb, htF, htN, htS, ht2, hDi, hDc, hDs, -, haD, hac, -, hCc, hCn, -⟩ := hC
      exact ⟨tb, htF, htN, htS, ht2, hDi, hDc, hDs, haD, hac, fun h => absurd h hA,
        fun _ => hCc, fun _ => hCn⟩
  exact ⟨
    { toSetting1 := s
      p := p
      f := f
      hp := hp
      hp2 := hp2
      hf := hf
      simple := hsimple
      centralizer_eq := hcent'
      type := htype
      J_type := hJt
      a_mem := haF
      mod4_L := hmL
      mod4_U := hmU
      tb := tb
      tb_mem := htF
      tb_norm := htN
      tb_not := htS
      tb_sq := ht2
      D_inf := hDi
      D_comm := hDc
      D_sup := hDs
      a_mem_Dt := haD
      a_central := hac
      Dt_index_A10 := hDix
      Cp_cyclic := hCc
      Cp_card := hCn }, rfl⟩

end Setting1

end Eight2

end CFSG.ComponentClassification.GSThmB
