module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9List
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

@[expose] def Case1295Amalgam_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ H₁ : Subgroup G, IsTSub T V V₁ 1 → IsMulCommutative ↥(u128 V V₁) →
      IsHStar T (Subgroup.normalizer (L : Set G)) H₁ →
      H₁ ≤ Subgroup.normalizer (V₁ : Set G) → H₁ ≤ Subgroup.normalizer (lOne L V₁ : Set G) →
      ⁅lOne L V₁, oTwoUpper H₁⁆ ≤ pCoreOf 2 (lOne L V₁) → False

@[expose] def Case1295Two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ K₁ : Subgroup G, IsTSub T V V₁ 1 → IsMulCommutative ↥(u128 V V₁) → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) → IsHzOne T L V₁ (K₁ ⊔ T) →
      (IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨ IsList1293Three (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) →
      ¬ (Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
        Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) →
      False

@[expose] def Case1295Three_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1291 G T L V 4 →
    ∀ V₁ K₁ : Subgroup G, IsTSub T V V₁ 1 → IsMulCommutative ↥(u128 V V₁) → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) → IsHzOne T L V₁ (K₁ ⊔ T) →
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      (¬ ∃ φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
          (((lOne L V₁).subgroupOf K₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))).map
            φ.toMonoidHom = Subgroup.centralizer ({transvection15} : Set _)) →
      ∃ H₁ : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H₁ ∧ H₁ ≤ K₁ ⊔ T ∧
        H₁ ≤ Subgroup.normalizer (lOne L V₁ : Set G) ∧
        ⁅lOne L V₁, oTwoUpper H₁⁆ ≤ pCoreOf 2 (lOne L V₁)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open L1295 in

theorem lemma12_9_5_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1293 : Lemma12_9_3K1_F4) (h1294 : Lemma12_9_4_F4)
    (hOut : OutFact1295) (hAm : Case1295Amalgam_F4) (hTwo : Case1295Two_F4)
    (hThree : Case1295Three_F4) : Lemma12_9_5_F4 := by
  classical
  intro G _ _ T L V n hcx V₁ K₁ hV₁ hLK hK
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  obtain ⟨hVT, hTV⟩ := hyp.le_and_normalizes_F4 h1222
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hab := h1294 G T L V n hcx V₁ hV₁
  set L₁ := lOne L V₁ with hL₁
  set G₁ := Subgroup.normalizer (V₁ : Set G) with hG₁
  set Q := pCoreOf 2 K₁ with hQ
  set C := centralizerMod Q G₁ K₁ with hC
  have hK₁G₁ : K₁ ≤ G₁ := le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hK₁n : G₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    normalizer_le_of_lOne_le_F4 h1222 h37 h38 h hn hV₁ hLK hK
  have hL₁G₁ : L₁ ≤ G₁ := (oTwoUpper_le _).trans inf_le_right
  have hTG₁ : T ≤ G₁ := hV₁.2.2
  have hTL₁ : T ≤ Subgroup.normalizer (L₁ : Set G) := le_normalizer_lOne hyp.normalizes hV₁.2.2
  have hL₁M : L₁ ≤ Subgroup.normalizer (L : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hG₁M : ¬ G₁ ≤ Subgroup.normalizer (L : Set G) := lemma12_8_3_four_F4 h12213 h hV₁
  have hL₁c : L₁ ∈ cComp (L₁ ⊔ T) := lOne_mem_cComp_F4 h1222 h hn hV₁
  have hL₁perf : ⁅L₁, L₁⁆ = L₁ := perfect_of_mem_cComp hL₁c
  have hL₁ne : L₁ ≠ ⊥ := hL₁c.1

  have hQG₁ : Q ≤ pCoreOf 2 G₁ :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁G₁)
      (hK₁n.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hO₂G₁T : pCoreOf 2 G₁ ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTG₁)
  have hO₂L₁T : pCoreOf 2 G₁ ≤ pCoreOf 2 (L₁ ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hO₂G₁T.trans le_sup_right)
      ((sup_le hL₁G₁ hTG₁).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 G₁))
      (LieType.BorelTits.pCoreOf_isPGroup 2 G₁)
  have hL₁L₁T : L₁ ⊔ T ≤ Subgroup.normalizer (L₁ : Set G) := sup_le Subgroup.le_normalizer hTL₁
  have hQL₁ : Q ≤ Subgroup.normalizer (L₁ : Set G) :=
    (hQG₁.trans hO₂L₁T).trans ((LieType.BorelTits.pCoreOf_le 2 _).trans hL₁L₁T)

  have hL₁Q : L₁ ⊔ Q ≤ Subgroup.normalizer (L₁ : Set G) := sup_le Subgroup.le_normalizer hQL₁
  have hQ2 : IsPGroup 2 Q := LieType.BorelTits.pCoreOf_isPGroup 2 K₁
  have hidem : oTwoUpper L₁ = L₁ := by
    refine le_antisymm (oTwoUpper_le _) ?_
    show oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
      oTwoUpper (oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G)))
    exact Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩
  have hO2L₁Q : oTwoUpper (L₁ ⊔ Q) = L₁ := by
    refine le_antisymm (oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hL₁Q) hQ2 le_sup_right
      le_rfl) ?_
    calc L₁ = oTwoUpper L₁ := hidem.symm
      _ ≤ oTwoUpper (L₁ ⊔ Q) := oTwoUpper_mono le_sup_left

  have hQK₁ : K₁ ≤ Subgroup.normalizer (Q : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 K₁
  have hCG₁ : C ≤ G₁ := centralizerMod_le_left _ _ _
  have hCn : G₁ ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod
      (hK₁n.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
      Subgroup.le_normalizer hK₁n
  have hCL₁Q : C ≤ Subgroup.normalizer ((L₁ ⊔ Q : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun c hc w hw => ?_
    obtain ⟨-, hcQ, hck⟩ := hc
    have hle : L₁ ⊔ Q ≤ (L₁ ⊔ Q).comap (MulAut.conj c).toMonoidHom := by
      refine sup_le (fun l hl => ?_) (fun q hq => ?_)
      · rw [Subgroup.mem_comap]
        show c * l * c⁻¹ ∈ L₁ ⊔ Q
        have h1 := hck l (hLK hl)
        rw [show c * l * c⁻¹ = (c * l * c⁻¹ * l⁻¹) * l by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hl)
      · rw [Subgroup.mem_comap]
        show c * q * c⁻¹ ∈ L₁ ⊔ Q
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hcQ q).1 hq)
    exact hle hw
  have hCL₁ : C ≤ Subgroup.normalizer (L₁ : Set G) := by
    intro c hc
    have := normalizer_le_normalizer_oTwoUpper (L₁ ⊔ Q) (hCL₁Q hc)
    rwa [hO2L₁Q] at this
  have hcomm : ∀ l ∈ L₁, ∀ c ∈ C, l * c * l⁻¹ * c⁻¹ ∈ pCoreOf 2 L₁ := by
    intro l hl c hc
    have hcL₁ := hCL₁ hc
    obtain ⟨-, -, hck⟩ := hc
    have hmemL : l * c * l⁻¹ * c⁻¹ ∈ L₁ := by
      have := L₁.mul_mem hl ((Subgroup.mem_normalizer_iff.1 hcL₁ l⁻¹).1 (L₁.inv_mem hl))
      rwa [show l * (c * l⁻¹ * c⁻¹) = l * c * l⁻¹ * c⁻¹ by group] at this
    have hmemQ : l * c * l⁻¹ * c⁻¹ ∈ Q := by
      have h1 := hck l⁻¹ (hLK (L₁.inv_mem hl))
      have h2 := (Subgroup.mem_normalizer_iff.1 (hQK₁ (hLK hl)) _).1 h1
      rwa [show l * (c * l⁻¹ * c⁻¹ * l⁻¹⁻¹) * l⁻¹ = l * c * l⁻¹ * c⁻¹ by group] at h2
    have hLQ : L₁ ⊓ Q ≤ pCoreOf 2 L₁ :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        ((le_inf Subgroup.le_normalizer (hLK.trans hQK₁)).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
        (hQ2.to_le inf_le_right)
    exact hLQ ⟨hmemL, hmemQ⟩
  have hV₁p : IsPGroup 2 V₁ := hT2.to_le (hV₁.1.trans hVT)
  have hV₁ne : V₁ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2

  have h1a : C ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hCM
    have hV₁CT : V₁ ≤ pCoreOf 2 (C ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((hV₁.1.trans hVT).trans le_sup_right)
        (sup_le hCG₁ hTG₁) hV₁p
    have hCT : InH T (C ⊔ T) := ⟨le_sup_right, fun hb => hV₁ne (le_bot_iff.1 (hb ▸ hV₁CT))⟩
    obtain ⟨H₁, hH₁, hH₁le⟩ := exists_isHStar_le hCT fun h1 => hCM (le_sup_left.trans h1)
    have hO2C : oTwoUpper H₁ ≤ C := (oTwoUpper_mono hH₁le).trans
      (oTwoUpper_le_of_normal_sup le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
          (sup_le Subgroup.le_normalizer (hTG₁.trans hCn))) hT2 le_sup_right le_rfl)
    refine hAm G T L V n hcx V₁ H₁ hV₁ hab hH₁ (hH₁le.trans (sup_le hCG₁ hTG₁))
      (hH₁le.trans (sup_le hCL₁ hTL₁)) (Subgroup.commutator_le.2 fun l hl x hx => ?_)
    rw [commutatorElement_def]
    exact hcomm l hl x (hO2C hx)

  have hK₁TG₁ : K₁ ⊔ T ≤ G₁ := sup_le hK₁G₁ hTG₁
  have hK₁TM : ¬ K₁ ⊔ T ≤ Subgroup.normalizer (L : Set G) := by
    intro hle
    have hK₁L₁ : K₁ ≤ Subgroup.normalizer (L₁ : Set G) :=
      le_normalizer_lOne (le_sup_left.trans hle) hK₁G₁
    have hL₁sub : IsSubnormal L₁ G₁ := A3.subnormal_trans (A3.subnormal_of_normal hLK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLK).2 hK₁L₁)) hK.2.2.1
    have hL₁K₁ : L₁ = K₁ := by
      by_contra hne
      exact hK.2.2.2 L₁ (lt_of_le_of_ne hLK hne) hL₁ne hL₁perf hL₁sub

    apply hG₁M
    intro x hx
    have hiso : Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
      obtain ⟨e⟩ := lOne_quotient_mulEquiv_F4 h1222 h hn hV₁
      rcases hcx.n45 with h4 | h5
      · subst h4
        exact Or.inl ⟨e⟩
      · subst h5
        exact Or.inr ⟨e⟩
    have hG₁L₁ : G₁ ≤ Subgroup.normalizer (L₁ : Set G) := hL₁K₁ ▸ hK₁n
    obtain ⟨d, hd, hdx⟩ := hOut G G₁ L₁ T hL₁G₁ hG₁L₁
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTG₁) hiso x hx
    have hdC : d ∈ C := by
      show d ∈ centralizerMod (pCoreOf 2 K₁) G₁ K₁
      rw [← hL₁K₁]
      exact hd
    rw [show x = d * (d⁻¹ * x) by group]
    exact Subgroup.mul_mem _ (h1a hdC) ((sup_le hL₁M hyp.normalizes) hdx)
  have hV₁K₁T : V₁ ≤ pCoreOf 2 (K₁ ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((hV₁.1.trans hVT).trans le_sup_right)
      hK₁TG₁ hV₁p
  have hHz : IsHzOne T L V₁ (K₁ ⊔ T) :=
    ⟨⟨sup_le_sup_right hLK T, fun hb => hV₁ne (le_bot_iff.1 (hb ▸ hV₁K₁T))⟩, hK₁TG₁, hK₁TM⟩
  have hL₁K₁ : L₁ ≠ K₁ := fun e => hK₁TM (by rw [← e]; exact sup_le hL₁M hyp.normalizes)

  have hlist : IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      IsList1293Three (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    obtain ⟨K', hLK', hK', -, hcases⟩ := h1293 G T L V n hcx V₁ hV₁
    obtain ⟨hS, hH, hBH, hB⟩ := lOne_lemma_1_2_4_data_F4 h1222 h hn hV₁
    obtain ⟨K'', -, huniq⟩ := lemma_1_2_4_existsUnique hyp.qtke hyp.simple hyp.nonabelian h37 h39
      hH hS hBH hB
    have hKK : K' = K₁ := (huniq K' ⟨hK', hLK'⟩).trans (huniq K₁ ⟨hK, hLK⟩).symm
    subst hKK
    rcases hcases with heq | h2 | ⟨-, h3⟩
    · exact absurd heq hL₁K₁
    · exact Or.inl h2
    · exact Or.inr h3

  have h2 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
    by_contra hnot
    exact hTwo G T L V n hcx V₁ K₁ hV₁ hab hLK hK hHz hlist hnot

  refine ⟨⟨h1a, hHz⟩, h2, fun hn4 hK5 => ?_⟩
  by_contra hnot
  subst hn4
  obtain ⟨H₁, hH₁, hH₁le, hH₁L₁, hcomm'⟩ := hThree G T L V hcx V₁ K₁ hV₁ hab hLK hK hHz hK5 hnot
  exact hAm G T L V 4 hcx V₁ H₁ hV₁ hab hH₁ (hH₁le.trans hK₁TG₁) hH₁L₁ hcomm'

end CFSG.Quasithin.H13
