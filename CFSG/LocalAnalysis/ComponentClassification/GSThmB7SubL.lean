module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SecL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubQComp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubQData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma513

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

namespace Sub71Aux

variable {h : Hyp52 X} {y : X}

theorem card_B_sub {k : Hyp59 (h.subQuot y)}
    (hcard : Nat.card k.B * Nat.card (h.secB0 y) = Nat.card h.B)
    (hidx : Nat.card h.B = 2 * Nat.card (B0 h y)) : Nat.card k.B = 2 := by
  have hpos : 0 < Nat.card (h.secB0 y) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (hcard.trans hidx)

theorem card_T_quot_sub (k : Hyp59 (h.subQuot y))
    (eT : Nonempty (↥k.toHyp52.T ⧸ k.B.subgroupOf k.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T))
    (hT : h.T = h.B ⊔ zpowers h.a) :
    Nat.card (↥k.toHyp52.T ⧸ k.B.subgroupOf k.toHyp52.T) = 2 := by
  obtain ⟨e⟩ := eT
  rw [Nat.card_congr e.toEquiv]
  exact h.card_T_quot_eq_two (hT.le.trans (le_of_eq (sup_comm _ _)))

theorem eight_le_card_P_sub (hB7 : EmbedsTQuotStatement) (hc : h.SecCond y)
    (k : Hyp59 (h.subQuot y))
    (hkP : ((h.P ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ≤ k.toHyp52.P)
    (hkT : k.toHyp52.T = (h.T.subgroupOf (h.secSub y)).map (h.subQ y))
    (hkT2 : Nat.card (↥k.toHyp52.T ⧸ k.B.subgroupOf k.toHyp52.T) = 2) :
    8 ≤ Nat.card k.toHyp52.P := by
  have hB0T : h.secB0 y ≤ h.T := (h.secB0_le_B y).trans (B5a.B_le_T h)
  by_contra hlt
  push Not at hlt
  have hPT := k.P_eq_T_of_card_lt hB7 hkT2 hlt
  have h1 : h.subQ y ⟨y, hc.y_mem_secSub⟩ ∈ k.toHyp52.P :=
    hkP (mem_map_of_mem _ (mem_subgroupOf.mpr (mem_inf.mpr ⟨hc.mem_P, hc.y_mem_G0⟩)))
  rw [hPT, hkT, Hyp52.subQ_mem_map_iff hB0T inf_le_right hc.mem_P] at h1
  exact hc.not_mem_T h1

end Sub71Aux

section Section

variable {h : Hyp52 X} {y : X}

theorem lieModel_psp_of_section_sub_ne (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCI : GSLit.ClassicalInvolutionInput) (hDC : CFDoubleCover) (hRec : CFSp4RecognitionCI)
    (k : Hyp59 (h.subQuot y))
    (hOJ : center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
      Nonempty (↥k.J ⧸ pPrimeCore 2 ↥k.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J))
    (hconj : conjugate k.K k.a = k.K ↔ conjugate h.K h.a = h.K)
    (hcard : Nat.card k.B * Nat.card (h.secB0 y) = Nat.card h.B)
    (hidx : Nat.card h.B = 2 * Nat.card (B0 h y)) (hKa : conjugate h.K h.a ≠ h.K)
    (hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel ↥(generalizedFitting (h.subQuot y)) .PSp 2 p f ∧
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f := by
  have hkB := Sub71Aux.card_B_sub hcard hidx
  have hkKa : conjugate k.K k.a ≠ k.K := fun h1 => hKa (hconj.mp h1)
  obtain ⟨p, f, hp, hp2, hf, hLie, hJLie'⟩ := k.lieModel_psp hB1 hCF23 hCI hDC hRec hkB hkKa
  obtain ⟨eJ⟩ := hOJ hZJ
  have hJLie := LieType.CurtisTits.lieModel_of_mulEquiv eJ hJLie'
  exact ⟨p, f, hp, hp2, hf, five_le_of_lieModel_psl_two hp2 hJLie, hLie, hJLie⟩

theorem lieModel_psp_of_section_sub
    (hRS : RestrictedStandardInput) (hRec : CFSp4RecognitionStd) (hB7 : EmbedsTQuotStatement)
    (hc : h.SecCond y) (hKG : SectionRank.IsKGroupCat (h.subQuot y))
    (hLB : Assembly.ComponentType.LocalBProperty (h.subQuot y)) (k : Hyp59 (h.subQuot y))
    (hkP : ((h.P ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ≤ k.toHyp52.P)
    (hkT : k.toHyp52.T = (h.T.subgroupOf (h.secSub y)).map (h.subQ y))
    (hOJ : center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
      Nonempty (↥k.J ⧸ pPrimeCore 2 ↥k.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J))
    (hOK : center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥ →
      Nonempty (↥k.K ⧸ pPrimeCore 2 ↥k.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K))
    (hconj : conjugate k.K k.a = k.K ↔ conjugate h.K h.a = h.K)
    (eT : Nonempty (↥k.toHyp52.T ⧸ k.B.subgroupOf k.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T))
    (hcard : Nat.card k.B * Nat.card (h.secB0 y) = Nat.card h.B)
    (hT : h.T = h.B ⊔ zpowers h.a) (hidx : Nat.card h.B = 2 * Nat.card (B0 h y))
    (hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥) (hKa : conjugate h.K h.a = h.K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hJL : Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hKL : Blueprint.LieModel (OddBar h.K) .PSL 2 p (2 * f)) :
    Blueprint.LieModel ↥(generalizedFitting (h.subQuot y)) .PSp 2 p f := by
  have hkB := Sub71Aux.card_B_sub hcard hidx
  have hkKa : conjugate k.K k.a = k.K := hconj.mpr hKa
  have hZK : center (OddBar h.K) = ⊥ := by
    have : IsSimpleGroup (OddBar h.K) := isSimpleGroup_of_lieModel_psl_two hKL
    exact center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_K
  have hkJL : Blueprint.LieModel (↥k.J ⧸ pPrimeCore 2 ↥k.J) .PSL 2 p f := by
    obtain ⟨eJ⟩ := hOJ hZJ
    exact LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm hJL
  have hkKL : Blueprint.LieModel (↥k.K ⧸ pPrimeCore 2 ↥k.K) .PSL 2 p (2 * f) := by
    obtain ⟨eK⟩ := hOK hZK
    exact LieType.CurtisTits.lieModel_of_mulEquiv eK.symm hKL
  have hP8 := Sub71Aux.eight_le_card_P_sub hB7 hc k hkP hkT (Sub71Aux.card_T_quot_sub k eT hT)
  exact k.lieModel_psp_of_eq hRS hRec hKG hLB hkB hkKa hP8 hp hp2 hf h5 hkJL hkKL

theorem lieModel_Lay_of_section_sub (hCov : CFSp4CoverInv) (hc : h.SecCond y)
    (k : Hyp59 (h.subQuot y)) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hLie : Blueprint.LieModel ↥(generalizedFitting (h.subQuot y)) .PSp 2 p f)
    (hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥) :
    Blueprint.LieModel (Lay h y ⧸ pPrimeCore 2 (Lay h y)) .PSp 2 p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hMC, hM, ⟨eM⟩⟩ := hc.exists_isPComponent_centralizer_of_sub k (MulEquiv.refl _)
  have hLM : Lay h y = M := Hyp52.layerIn_centralizer_eq_sub k hMC hM
  have hq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMC).mp hM).2.2
  have hLieZ : Blueprint.LieModel ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M))
      .PSp 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv ((oddBarCenterEquiv M).trans eM).symm hLie
  have ha : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have haB0 : h.a ∈ centralizer (B0 h y : Set X) := mem_centralizer_iff.mpr fun _ hb =>
    h.comm_a (((inf_le_left : B0 h y ≤ h.B).trans h.B_le_S) hb)
  have haM : h.a ∈ normalizer (M : Set X) := by
    rw [← hLM]
    exact normalizer_le_normalizer_layerIn_centralizer _ (centralizer_le_normalizer _ haB0)
  have hJ0M : J0 h y ≤ M ⊓ centralizer ({h.a} : Set X) :=
    le_inf (hLM ▸ J0_le_Lay h y)
      (((GSLit.fixedLayer_le_inf _ _).trans inf_le_left).trans h.J_le)
  have hJ0pc : IsPComponent 2 ((J0 h y).subgroupOf (M ⊓ centralizer ({h.a} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0M
      (fun w hw => mem_inf.mpr ⟨(mem_inf.mp hw).2, hMC (mem_inf.mp hw).1⟩)
      (Hyp52.isPComponent_secJ0 (h := h) (y := y))
  have hZJ0 : center (↥(J0 h y) ⧸ pPrimeCore 2 ↥(J0 h y)) = ⊥ := by
    obtain ⟨e0⟩ := Hyp52.nonempty_secJ0_equiv (h := h) (y := y)
    have e0' : ↥(J0 h y) ⧸ pPrimeCore 2 ↥(J0 h y) ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J := e0
    rw [← Subgroup.card_eq_one] at hZJ ⊢
    rw [Nat.card_congr (Subgroup.centerCongr e0').toEquiv, hZJ]
  have hZ := center_oddBar_eq_bot hCov hp hp2 hf hq hLieZ ha haM hJ0M hJ0pc hZJ0
  have e1 : (↥M ⧸ pPrimeCore 2 ↥M) ≃* (↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  rw [hLM]
  exact LieType.CurtisTits.lieModel_of_mulEquiv e1.symm hLieZ

end Section

theorem lieModel_Lay_sub (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCI : GSLit.ClassicalInvolutionInput) (hDC : CFDoubleCover) (hRec : CFSp4RecognitionCI)
    (hCov : CFSp4CoverInv) {h : Hyp52 X} {y : X} (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hT : h.T = h.B ⊔ zpowers h.a) (hW : h.NoFusionW)
    (hidx : Nat.card h.B = 2 * Nat.card (B0 h y)) (hKa : conjugate h.K h.a ≠ h.K)
    (hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Lay h y ⧸ pPrimeCore 2 (Lay h y)) .PSp 2 p f) ∧
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f := by
  obtain ⟨k, -, -, -, -, -, -, -, -, -, -, -, hOJ, -, hconj, -, -, hcard⟩ :=
    hc.exists_hyp59_subQuot_of_T_eq hCN hSa hT hW
  obtain ⟨p, f, hp, hp2, hf, h5, hLie, hJLie⟩ :=
    lieModel_psp_of_section_sub_ne hB1 hCF23 hCI hDC hRec k hOJ hconj hcard hidx hKa hZJ
  exact ⟨⟨p, f, hp, hp2, hf, lieModel_Lay_of_section_sub hCov hc k hp hp2 hf hLie hZJ⟩,
    p, f, hp, hp2, hf, h5, hJLie⟩

theorem B0_inf_Lay_of_lieModel {h : Hyp52 X} {y : X} {p f : ℕ}
    (hLLie : Blueprint.LieModel (Lay h y ⧸ pPrimeCore 2 (Lay h y)) .PSp 2 p f) :
    Lay h y ⊓ B0 h y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC : Lay h y ≤ centralizer (B0 h y : Set X) := map_subtype_le _
  have hZ : center (↥(Lay h y) ⧸ pPrimeCore 2 ↥(Lay h y)) = ⊥ := by
    have := isSimpleGroup_of_lieModel_psp hLLie
    have : Group.IsPerfect ↥(Lay h y) := by
      have h1 := LBalance.pLayer_perfect 2 (centralizer (B0 h y : Set X))
      rw [LBalance.Asm.lBalancePLayer_eq_map] at h1
      exact h1
    have : Group.IsPerfect (↥(Lay h y) ⧸ pPrimeCore 2 ↥(Lay h y)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact center_eq_bot_of_isPerfect
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgL, hgB⟩ := mem_inf.mp hg
  have hgc : QuotientGroup.mk' (pPrimeCore 2 ↥(Lay h y)) ⟨g, hgL⟩ ∈
      center (↥(Lay h y) ⧸ pPrimeCore 2 ↥(Lay h y)) := by
    rw [mem_center_iff]
    intro u
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ u
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (hLC l.2) g hgB).symm
  rw [hZ, mem_bot] at hgc
  have hE2 : IsPGroup 2 ((Lay h y ⊓ B0 h y).subgroupOf (Lay h y)) :=
    ((h.isPGroup_B.to_le (inf_le_left : B0 h y ≤ h.B)).to_inf_right).comap_subtype
  have h1 := OddQuot.injOn_of_isPGroup hE2 (show (⟨g, hgL⟩ : ↥(Lay h y)) ∈ _ from
    mem_subgroupOf.mpr hg) (one_mem _) (by rw [map_one]; exact hgc)
  exact congrArg Subtype.val h1

theorem kappa_of_lieModel_Lay {h : Hyp52 X} {y : X} (hc : h.SecCond y) {p f : ℕ}
    (hLLie : Blueprint.LieModel (Lay h y ⧸ pPrimeCore 2 (Lay h y)) .PSp 2 p f) :
    ∀ l ∈ layerIn (centralizer (h.secB0 y : Set X)),
      l ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
      l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secB0 y → l * h.a = h.a * l :=
  hc.kappa_of_secL0_inf_eq_bot (B0_inf_Lay_of_lieModel hLLie)

end Seven

end CFSG.ComponentClassification.GSThmB
