module

public import CFSG.Goldschmidt75.CorollaryB1
public import CFSG.ClassicalInvolution.AschTight.Thm6TightB3
public import CFSG.ClassicalInvolution.Q3.TL3Induct
public import CFSG.ClassicalInvolution.Q3.TL3S8BCore
public import CFSG.ClassicalInvolution.Q3.TL3S8BCount

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def TightC19_11bS (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)], IH (Nat.card G) →
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G) (W L : Subgroup G) (t' : G)
      (V : Subgroup G), TightFStarOK G t → TightSylowStd R S t T →
    TightSylowDataT (tightCore R) t T W L t' V →
      (T : Subgroup G) ⊓
          Subgroup.centralizer (((T : Subgroup G) ⊓ tightCore R : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L = ⊥

@[expose] def TightF1S (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)], IH (Nat.card G) →
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G) (W L : Subgroup G) (t' : G)
      (V : Subgroup G), TightFStarOK G t → TightSylowStd R S t T →
    TightSylowDataT (tightCore R) t T W L t' V →
      ∀ x ∈ S19B.sec19BPrime (tightCore R) T W L, x ≠ 1 → ∀ g : G,
        g * t * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) →
          ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * t * c⁻¹ = g * t * g⁻¹

@[expose] def TightEndGameS (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)], IH (Nat.card G) →
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G), TightFStarOK G t →
    TightSylowStd R S t T →
    ∀ B : Subgroup G, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      fusionStronglyClosed (B : Set G) (T : Subgroup G) → B ≤ centralizerModOdd ⊤ (tightCore R) →
      t ∈ Subgroup.centralizer (B : Set G) →
      (∃ g ∈ Subgroup.centralizer (B : Set G),
        g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹)) → False

theorem tightC19_11bS_of_F1_endgame {IH : ℕ → Prop} (hF1 : TightF1S IH)
    (hEnd : TightEndGameS IH) : TightC19_11bS IH := by
  intro G _ _ _ hIH hnab R S t T W L t' V hF h hd
  by_contra hne
  exact hd.false_of_F1_endgame (hF1 G hIH hnab R S t T W L t' V hF h hd)
    (hEnd G hIH hnab R S t T hF h) hne

section E2

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}

theorem TightSylowStd.tightE2Prime_of_coreS {IH : ℕ → Prop} [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hF : TightFStarOK G t)
    (h11b : TightC19_11bS IH) (hbelow : IH (Nat.card G)) (h : TightSylowStd R S t T)
    (hmu : ¬ AllTypeTwo (tightCore R) t) : TightE2Prime (tightCore R) T := by
  obtain ⟨W₀, hW₀, hW₀S, -⟩ := h.tightMemStd.exists_wSet_le_normal T
  exact (h.sylowData hmu hW₀ hW₀S).tightE2Prime fun W₁ L t' V hdT =>
    h11b G hbelow hnab R S t T W₁ L t' V hF h hdT

end E2

@[expose] def TightThm6SylowBelowS (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)], IH (Nat.card G) →
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → TightFStarOK G t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) → ∀ T : Subgroup G,
      IsSylow2Of T
        (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)) →
      IsSylow2Of T ⊤ → Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) →
        TwoSubgroupsFourGenerated (genFittingFStar G)

theorem tightThm6SylowS_of_core {IH : ℕ → Prop} (hB3 : GoldschmidtB3Tmp)
    (h11b : TightC19_11bS IH) : TightThm6SylowBelowS IH := by
  intro G _ _ _ hbelow hnab R S t hd hF hq T hT hTG he
  by_contra hn
  obtain ⟨T', -, h⟩ := TightSylowStd.exists_of_sylowCase hd hq he hn hT hTG
  obtain ⟨W, hW, -⟩ := h.exists_w69
  have hS3 := h.muIsoS3' hF hB3 hW
  have hmu := h.not_allTypeTwo_of_muIsoS3 hW hS3
  exact hn (h.twoSubgroupsFourGenerated_of_e2Prime
    (h.tightE2Prime_of_coreS hnab hF h11b hbelow hmu))

section Edge


@[expose] def TightLargeEdgeS (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y]
    [IsSimpleGroup (genFittingFStar Y)], Nat.card Y = n →
    (∃ a b : genFittingFStar Y, a * b ≠ b * a) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R

theorem tightLargeEdgeS_of_thm6SylowBelowS {IH : ℕ → Prop} (hI : TightThm6SylowBelowS IH)
    (n : ℕ) (hIH : CIT3Below n → TightBelow n → IH n) : TightLargeEdgeS n := by
  intro hA hb Y _ _ _ hn hnab R S t hd hc _ hlarge he
  have ht1 : t ≠ 1 := by
    intro h
    have := hd.order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hF : TightFStarOK Y t := TightFStarOK.of_simple hnab ht1
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  obtain ⟨T, hT, -⟩ := exists_isSylow2Of_ge d.S_two
    (Subgroup.le_normalizer : ((S : Subgroup R).map R.subtype : Subgroup Y) ≤ _)
  by_cases hsyl : IsSylow2Of T ⊤
  · refine hlarge (hI Y ?_ hnab R S t hd hF hc.1 T hT hsyl he)
    rw [hn]
    exact hIH hA hb
  · exact hd.not_dEdgeless_of_not_sylow hT hsyl he

end Edge

section Gold


theorem tightThm6SylowS_proved {IH : ℕ → Prop} (h11b : TightC19_11bS IH) :
    TightThm6SylowBelowS IH :=
  tightThm6SylowS_of_core goldschmidtB3Tmp_holds h11b

theorem tightLargeEdgeS_of_core (h11b : TightC19_11bS fun m => CIT3Below m ∧ TightBelow m)
    (n : ℕ) : TightLargeEdgeS n :=
  tightLargeEdgeS_of_thm6SylowBelowS (tightThm6SylowS_proved h11b) n fun a b => ⟨a, b⟩

theorem isSolvable_centralizer_of_stronglyClosed_fstar {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (hO : classicalInvolutionOddCore G = ⊥) (T : Sylow 2 G) {B : Subgroup G}
    (hBT : B ≤ (T : Subgroup G)) (hB : B ≠ ⊥)
    (hsc : fusionStronglyClosed (B : Set G) (T : Subgroup G)) :
    Group.IsSolvable ↥(Subgroup.centralizer (B : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer (B : Set G) with hC
  set M : Subgroup G := (CFSG.perfectResidual ↥C).map C.subtype with hM
  have hO' : CFSG.Open.goldschmidtOddCore G = ⊥ := hO
  have hMn : M.Normal := by
    have h := CFSG.Goldschmidt75.corollaryB1 T hBT hsc
    rw [hO', sup_bot_eq] at h
    exact h
  set F : Subgroup G := genFittingFStar G with hF
  have hFn : F.Normal := genFittingFStar_normal G
  have hMF : M ⊓ F ≠ ⊥ → F ≤ M := by
    intro hne
    have hMFn : ((M ⊓ F).subgroupOf F).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hMn.conj_mem _ hn.1 g, hFn.conj_mem _ hn.2 g⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ F).subgroupOf F) with h0 | h0
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have hxF : (⟨x, hx.2⟩ : ↥F) ∈ (M ⊓ F).subgroupOf F := Subgroup.mem_subgroupOf.mpr hx
      rw [h0, Subgroup.mem_bot] at hxF
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxF)
    · intro f hf
      have : (⟨f, hf⟩ : ↥F) ∈ (M ⊓ F).subgroupOf F := by
        rw [h0]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
  have hMbot : M = ⊥ := by
    by_contra hMne
    by_cases hI : M ⊓ F = ⊥
    ·
      apply hMne
      have hcomm : ⁅M, F⁆ = ⊥ := by
        rw [eq_bot_iff, ← hI]
        exact Subgroup.commutator_le_inf M F
      have hMc : M ≤ Subgroup.centralizer (F : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hMF' : M ≤ F := hMc.trans (CFSG.Adapters.generalized_fitting_self_centralizing G)
      rw [eq_bot_iff, ← hI]
      exact le_inf le_rfl hMF'
    ·
      have hFM := hMF hI
      have hFC : F ≤ C := hFM.trans (Subgroup.map_subtype_le _)
      apply hB
      have hBc : B ≤ Subgroup.centralizer (F : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        exact (Subgroup.mem_centralizer_iff.mp (hFC hf) b hb).symm
      have hBF : B ≤ F := hBc.trans (CFSG.Adapters.generalized_fitting_self_centralizing G)
      rw [eq_bot_iff]
      intro b hb
      have hbZ : (⟨b, hBF hb⟩ : ↥F) ∈ Subgroup.center ↥F := by
        rw [Subgroup.mem_center_iff]
        intro f
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hBc hb)) f f.2)
      have hZ : Subgroup.center ↥F = ⊥ := by
        obtain ⟨a₀, b₀, hab⟩ := hnab
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥F) with h | h
        · exact h
        · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b₀) a₀) hab
      rw [hZ, Subgroup.mem_bot] at hbZ
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hbZ)
  have hP : CFSG.perfectResidual ↥C = ⊥ := by
    rw [hM, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hMbot
    exact hMbot
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mp hP

end Gold

@[expose] def TightEndGameSolv (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)], IH (Nat.card G) →
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G), TightFStarOK G t →
    TightSylowStd R S t T →
    ∀ B : Subgroup G, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      fusionStronglyClosed (B : Set G) (T : Subgroup G) → B ≤ centralizerModOdd ⊤ (tightCore R) →
      t ∈ Subgroup.centralizer (B : Set G) →
      Group.IsSolvable ↥(Subgroup.centralizer (B : Set G)) →
      (∃ g ∈ Subgroup.centralizer (B : Set G),
        g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹)) → False

section GoldEnd


theorem tightEndGameS_of_solv {IH : ℕ → Prop} (h : TightEndGameSolv IH) : TightEndGameS IH := by
  intro G _ _ _ hIH hnab R S t T hF hstd B hBT hB hsc hBK htB hg
  exact h G hIH hnab R S t T hF hstd B hBT hB hsc hBK htB
    (isSolvable_centralizer_of_stronglyClosed_fstar hnab hF.oddCore T hBT hB hsc) hg

end GoldEnd

end CFSG.ClassicalInvolution.Q3
