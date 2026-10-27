module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.Background.FLcSL
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SpSmall
public import CFSG.LargeExtraspecial.A2ModSLModel
public import CFSG.LargeExtraspecial.D73GL
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightS3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.Open Subgroup

theorem IsSpTwoLeviProduct.of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : IsSpTwoLeviProduct R) : IsSpTwoLeviProduct R' := by
  obtain ⟨k, X, hG, hF, ⟨e₀⟩, hX⟩ := h
  exact ⟨k, X, hG, hF,
    ⟨(QuotientGroup.congr (CFSG.pCore 2 R) (CFSG.pCore 2 R') e (CFSG.pCore_map_iso 2 e)).symm.trans
      e₀⟩, hX⟩

theorem forall_sylow_normalizer_eq_of_mulEquiv {X X' : Type} [Group X] [Group X'] [Finite X]
    (e : X ≃* X')
    (h : ∀ T : Sylow 2 X, normalizer ((T : Subgroup X) : Set X) = (T : Subgroup X)) :
    ∀ T : Sylow 2 X', normalizer ((T : Subgroup X') : Set X') = (T : Subgroup X') := by
  haveI : Finite X' := Finite.of_equiv X e.toEquiv
  intro T
  let T₀ : Sylow 2 X := Sylow.mapSurjective (p := 2) (f := e.symm.toMonoidHom)
    e.symm.surjective T
  have hcoe : (T₀ : Subgroup X) = (T : Subgroup X').map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T
  have hT : (T₀ : Subgroup X).map e.toMonoidHom = (T : Subgroup X') := by
    rw [hcoe, Subgroup.map_map]
    have hcomp : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id X' := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hmap := Subgroup.map_equiv_normalizer_eq (T₀ : Subgroup X) e
  rw [h T₀, hT] at hmap
  exact hmap.symm

theorem IsSpTwoFactor.of_mulEquiv {X X' : Type} [Group X] [Group X'] [Finite X] (e : X ≃* X')
    (h : IsSpTwoFactor X) : IsSpTwoFactor X' := by
  rcases h with hsub | ⟨hW, hz, hn⟩ | h₆
  · refine Or.inl ⟨fun a b => e.symm.injective ?_⟩
    exact hsub.elim (e.symm a) (e.symm b)
  · refine Or.inr (Or.inl ⟨IsWBlock.of_mulEquiv e hW, ?_, ?_⟩)
    · have hcard : Nat.card (center X') = 1 := by
        rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hz, Subgroup.card_bot]
      exact Subgroup.eq_bot_of_card_eq _ hcard
    · exact forall_sylow_normalizer_eq_of_mulEquiv e hn
  · exact Or.inr (Or.inr ⟨e.symm.trans h₆.some⟩)

theorem isSpTwoFactor_of_subsingleton {X : Type} [Group X] (h : Subsingleton X) :
    IsSpTwoFactor X :=
  Or.inl h

theorem isSpTwoFactor_of_perm_six {X : Type} [Group X] (e : X ≃* Equiv.Perm (Fin 6)) :
    IsSpTwoFactor X :=
  Or.inr (Or.inr ⟨e⟩)

theorem isSpTwoFactor_of_wBlock {X : Type} [Group X] (hW : IsWBlock X) (hz : center X = ⊥)
    (hn : ∀ T : Sylow 2 X, normalizer ((T : Subgroup X) : Set X) = (T : Subgroup X)) :
    IsSpTwoFactor X :=
  Or.inr (Or.inl ⟨hW, hz, hn⟩)


theorem pCore_two_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.pCore 2 H = ⊥) : CFSG.pCore 2 G = ⊥ := by
  have hmap := CFSG.pCore_map_iso (G := G) (G' := H) 2 e
  rw [h] at hmap
  rw [Subgroup.map_eq_bot_iff] at hmap
  rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective] at hmap
  exact le_bot_iff.mp hmap

theorem pCore_two_gl_zmod_two_eq_bot (n : ℕ) :
    CFSG.pCore 2 (GL (Fin n) (ZMod 2)) = ⊥ :=
  CFSG.LargeExtraspecial.DW.D73.eq_bot_of_normal_of_isPGroup n _
    inferInstance CFSG.pCore_isPGroup

theorem pCore_two_slt_eq_bot (n : ℕ) :
    CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ :=
  pCore_two_eq_bot_of_mulEquiv (CFSG.Quasithin.FLc.slEquivGLt n) (pCore_two_gl_zmod_two_eq_bot n)

theorem borelSubgroup_eq_unipotent_of_card_two {r : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup r K =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent r K := by
  refine (Subgroup.eq_of_le_of_card_ge
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent_le_borelSubgroup ?_).symm
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_borelSubgroup,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_unipotent, hK]
  simp

theorem normalizer_sylow_statedSp_eq_self {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hm : 1 ≤ m) (T : Sylow 2 (StatedSp m K)) :
    normalizer ((T : Subgroup (StatedSp m K)) : Set (StatedSp m K)) =
      (T : Subgroup (StatedSp m K)) := by
  obtain ⟨U, hU⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent
    (K := K) 2 m
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedSp m K) U T
  have hUcoe : (U : Subgroup (StatedSp m K)) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent m K := hU
  have hN : normalizer ((U : Subgroup (StatedSp m K)) : Set (StatedSp m K)) =
      (U : Subgroup (StatedSp m K)) := by
    rw [hUcoe, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent,
      borelSubgroup_eq_unipotent_of_card_two hK]
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  have hmap := Subgroup.map_equiv_normalizer_eq (U : Subgroup (StatedSp m K)) (MulAut.conj x)
  rw [hN] at hmap
  exact hmap.symm


theorem slt_isSpTwoFactor (n : ℕ) :
    IsSpTwoFactor (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
      CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  refine ⟨?_, pCore_two_slt_eq_bot n⟩
  rcases n with _ | m
  · exact isSpTwoFactor_of_subsingleton
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) (ZMod 2)) _ _)⟩
  rcases m with _ | k
  ·
    have h1 : ∀ A : Matrix.SpecialLinearGroup (Fin 1) (ZMod 2),
        (A : Matrix (Fin 1) (Fin 1) (ZMod 2)) = 1 := by
      intro A
      have hd := A.2
      rw [Matrix.det_fin_one] at hd
      ext i j
      fin_cases i
      fin_cases j
      simpa using hd
    exact isSpTwoFactor_of_subsingleton
      ⟨fun a b => Subtype.ext ((h1 a).trans (h1 b).symm)⟩
  ·
    have hn : 1 ≤ k + 2 := by omega
    have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin (k + 2)) (ZMod 2)) = ⊥ :=
      CFSG.LargeExtraspecial.A2Mod.sl_center_eq_bot_of_card_two (n := k + 2) (Nat.card_zmod 2)
    refine isSpTwoFactor_of_wBlock ?_ hZ fun T =>
      CFSG.Quasithin.FLc.normalizer_eq_of_sylow_equiv hn (MulEquiv.refl _) T
    rcases Nat.eq_or_lt_of_le (show 2 ≤ k + 2 by omega) with h2 | h3
    · have hk : k = 0 := by omega
      subst hk
      exact Or.inr (Or.inl ⟨(CFSG.CGT.PushingUpLit.BHS6.s3Equiv).symm⟩)
    · exact Or.inl ⟨spFlag_isQuasisimple_SL (K := ZMod 2) (k := k + 2) (by omega)
        (Or.inl h3), by rw [hZ, Subgroup.card_bot]; exact odd_one⟩

theorem statedSp_isSpTwoFactor {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) :
    IsSpTwoFactor (StatedSp m K) ∧ CFSG.pCore 2 (StatedSp m K) = ⊥ := by
  rcases m with _ | m
  ·
    have hsub : Subsingleton (StatedSp 0 K) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := GL (Fin 0 ⊕ Fin 0) K) _ _)⟩
    exact ⟨isSpTwoFactor_of_subsingleton hsub, by
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      exact hsub.elim x 1⟩
  rcases m with _ | m
  ·
    have hsym : IsSymThreeOrSUThreeTwo (StatedSp 1 K) := by
      obtain ⟨e₃⟩ :=
        CFSG.HardMathSupport.RichardWeiss.Proving.PLType.nonempty_statedSp_one_mulEquiv_perm_three
      exact Or.inl ⟨(CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr
        (CFSG.LargeExtraspecial.A2Mod.ringEquivZModTwo K hK) 1).trans e₃⟩
    have hZ : Subgroup.center (StatedSp 1 K) = ⊥ :=
      CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := K) (n := 1) (by norm_num)
    refine ⟨isSpTwoFactor_of_wBlock (Or.inr hsym) hZ fun T =>
      normalizer_sylow_statedSp_eq_self hK (by norm_num) T, ?_⟩
    obtain ⟨e₃⟩ :=
      CFSG.HardMathSupport.RichardWeiss.Proving.PLType.nonempty_statedSp_one_mulEquiv_perm_three
    exact pCore_two_eq_bot_of_mulEquiv
      ((CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr
        (CFSG.LargeExtraspecial.A2Mod.ringEquivZModTwo K hK) 1).trans e₃)
      CFSG.AGLEmbedding.pCore_perm_three_eq_bot
  rcases m with _ | m
  ·
    have htheta : StatedSp 2 K ≃* Equiv.Perm (Fin 6) :=
      (CFSG.Quasithin.B5FinSp.theta
        (CFSG.LargeExtraspecial.A2Mod.ringEquivZModTwo K hK).symm).symm
    refine ⟨isSpTwoFactor_of_perm_six htheta, ?_⟩
    exact pCore_two_eq_bot_of_mulEquiv htheta CFSG.AGLEmbedding.pCore_perm_six_eq_bot
  ·
    have hm : 1 ≤ m + 3 := by omega
    have hZ : Subgroup.center (StatedSp (m + 3) K) = ⊥ :=
      CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (K := K) (n := m + 3) hm
    refine ⟨isSpTwoFactor_of_wBlock
      (Or.inl ⟨spFlag_isQuasisimple_Sp (K := K) (m := m + 3) hm (Or.inr (by omega)),
        by rw [hZ, Subgroup.card_bot]; exact odd_one⟩) hZ (fun T =>
          normalizer_sylow_statedSp_eq_self hK hm T), ?_⟩
    exact CFSG.SeitzReduction.SymplecticPilot.eq_bot_of_normal_of_isPGroup_of_mulEquiv_two hK
      (m := m + 3) (by omega) (MulEquiv.refl _) _ inferInstance CFSG.pCore_isPGroup


variable {r : ℕ} {K : Type} [Field K] {I : Set ℕ}

@[expose] noncomputable def spFlagLeviCoordBlock (hI : ∀ i ∈ I, i ≤ r) (t : ℕ)
    (j : Fin (r + 1)) : Subgroup (StatedSp r K) := by
  classical
  exact if (j : ℕ) = 0 then (spFlagResEmb t).range
    else if hj : (j : ℕ) ∈ I then
      (spFlagCutEmb (spFlagPrev I j) j (hI j hj)).range
    else ⊥

theorem spFlagLeviCoordBlock_of_eq_zero (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)}
    (hj : (j : ℕ) = 0) :
    spFlagLeviCoordBlock (K := K) hI t j = (spFlagResEmb t).range := by
  classical
  simp only [spFlagLeviCoordBlock, hj, ↓reduceIte]

theorem spFlagLeviCoordBlock_of_mem (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)}
    (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I) :
    spFlagLeviCoordBlock (K := K) hI t j =
      (spFlagCutEmb (spFlagPrev I j) j (hI j hj)).range := by
  classical
  simp only [spFlagLeviCoordBlock, hj0, hj, ↓reduceIte, ↓reduceDIte]

theorem spFlagLeviCoordBlock_of_not_mem (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)}
    (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∉ I) :
    spFlagLeviCoordBlock (K := K) hI t j = ⊥ := by
  classical
  simp only [spFlagLeviCoordBlock, hj0, hj, ↓reduceIte, ↓reduceDIte]

theorem range_spFlagLeviHom (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)
    (hmax : ∀ c ∈ I, c ≤ t) :
    (spFlagLeviHom (K := K) hI htI).range =
      Subgroup.pi Set.univ (spFlagLeviCoordBlock (K := K) hI t) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Subgroup.le_pi_iff]
    intro j _
    rintro _ ⟨q, rfl⟩
    by_cases hj0 : (j : ℕ) = 0
    · rw [spFlagLeviCoordBlock_of_eq_zero hI t hj0, Subgroup.mem_comap]
      change (spFlagLeviCoord hI htI j) q ∈ (spFlagResEmb t).range
      rw [spFlagLeviCoord_of_eq_zero hI htI hj0]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    by_cases hj : (j : ℕ) ∈ I
    · rw [spFlagLeviCoordBlock_of_mem hI t hj0 hj, Subgroup.mem_comap]
      change (spFlagLeviCoord hI htI j) q ∈
        (spFlagCutEmb (spFlagPrev I j) j (hI j hj)).range
      rw [spFlagLeviCoord_of_mem hI htI hj0 hj]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · rw [spFlagLeviCoordBlock_of_not_mem hI t hj0 hj, Subgroup.mem_comap]
      change (spFlagLeviCoord hI htI j) q = 1
      rw [spFlagLeviCoord_of_not_mem hI htI hj0 hj, MonoidHom.one_apply]
  · rw [Subgroup.pi_le_iff]
    intro j
    rintro _ ⟨a, ha, rfl⟩
    by_cases hj0 : (j : ℕ) = 0
    · rw [spFlagLeviCoordBlock_of_eq_zero hI t hj0] at ha
      obtain ⟨c, rfl⟩ := ha
      refine MonoidHom.mem_range.mpr ⟨⟨spFlagResEmb t c, spFlagResEmb_mem hI hmax c⟩, ?_⟩
      have hj : j = 0 := Fin.ext hj0
      subst hj
      funext i
      rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_resEmb hI htI hmax,
        MonoidHom.mulSingle_apply]
      by_cases hi : (i : ℕ) = 0
      · rw [ite_eq_left hi, show i = (0 : Fin (r + 1)) from Fin.ext hi, Pi.mulSingle_eq_same]
      · rw [ite_eq_right hi,
          Pi.mulSingle_eq_of_ne (fun h => hi (by simpa using congrArg Fin.val h))]
    by_cases hj : (j : ℕ) ∈ I
    · rw [spFlagLeviCoordBlock_of_mem hI t hj0 hj] at ha
      obtain ⟨A, rfl⟩ := ha
      have hjr : (j : ℕ) ≤ r := hI _ hj
      refine MonoidHom.mem_range.mpr ⟨⟨spFlagCutEmb (spFlagPrev I j) j (hI j hj) A,
        spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) A⟩, ?_⟩
      funext i
      rw [spFlagLeviHom, MonoidHom.pi_apply, spFlagLeviCoord_cutEmb hI htI hmax hj (by omega),
        MonoidHom.mulSingle_apply]
      by_cases hi : (i : ℕ) = (j : ℕ)
      · rw [ite_eq_left hi, show i = j from Fin.ext hi, Pi.mulSingle_eq_same]
      · rw [ite_eq_right hi,
          Pi.mulSingle_eq_of_ne (fun h => hi (by simpa using congrArg Fin.val h))]
    · rw [spFlagLeviCoordBlock_of_not_mem hI t hj0 hj] at ha
      have ha1 : a = 1 := by simpa using ha
      rw [ha1, map_one]
      exact one_mem _


noncomputable def piSubgroupEquiv {ι : Type} {G : ι → Type} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) : ↥(Subgroup.pi Set.univ H) ≃* ∀ i, ↥(H i) where
  toFun x := fun i => ⟨x.1 i, (Subgroup.mem_pi Set.univ).mp x.2 i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => (x i : G i), (Subgroup.mem_pi Set.univ).mpr fun i _ => (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem pCore_spFlagResEmb_range_eq_bot [Finite K] [CharP K 2] {t : ℕ}
    (hK : Nat.card K = 2) :
    CFSG.pCore 2 ↥(spFlagResEmb (r := r) (K := K) t).range = ⊥ :=
  pCore_two_eq_bot_of_mulEquiv
    (MonoidHom.ofInjective (f := spFlagResEmb (r := r) (K := K) t)
      (spFlagResEmb_injective t)).symm (statedSp_isSpTwoFactor hK).2

theorem pCore_spFlagCutEmb_range_eq_bot [Finite K] [CharP K 2] {a b : ℕ} (hb : b ≤ r)
    (hK : Nat.card K = 2) :
    CFSG.pCore 2 ↥(spFlagCutEmb (K := K) a b hb).range = ⊥ := by
  refine pCore_two_eq_bot_of_mulEquiv ?_ (slt_isSpTwoFactor (b - a)).2
  exact (MonoidHom.ofInjective (f := spFlagCutEmb (K := K) a b hb)
    (spFlagCutEmb_injective a b hb)).symm.trans
    ((CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK (b - a)).trans
      (CFSG.Quasithin.FLc.slEquivGLt (b - a)).symm)

theorem pCore_spFlagLeviCoordBlock_eq_bot [Finite K] [CharP K 2] (hI : ∀ i ∈ I, i ≤ r)
    (t : ℕ) (hK : Nat.card K = 2) (j : Fin (r + 1)) :
    CFSG.pCore 2 ↥(spFlagLeviCoordBlock (K := K) hI t j) = ⊥ := by
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviCoordBlock_of_eq_zero hI t hj0]
    exact pCore_spFlagResEmb_range_eq_bot hK
  by_cases hj : (j : ℕ) ∈ I
  · rw [spFlagLeviCoordBlock_of_mem hI t hj0 hj]
    exact pCore_spFlagCutEmb_range_eq_bot (hI j hj) hK
  · rw [spFlagLeviCoordBlock_of_not_mem hI t hj0 hj]
    rw [Subgroup.eq_bot_iff_forall]
    intro x _
    exact Subsingleton.elim x 1


theorem pCore_flagStabilizer_eq_ker_spFlagLeviHom [Finite K] [CharP K 2]
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hK : Nat.card K = 2) :
    CFSG.pCore 2 ↥(CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer r K I) =
      (spFlagLeviHom (fun i hi => (hI i hi).2) htI).ker := by
  let hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  set Q := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer r K I
  set β := spFlagLeviHom (K := K) hI' htI
  have hβ2 : IsPGroup 2 β.ker :=
    isPGroup_ker_spFlagLeviHom hI' htI fun i hi => (hI i hi).1
  refine le_antisymm ?_ ?_
  ·
    intro z hzQ
    have hrange : β.range = Subgroup.pi Set.univ (spFlagLeviCoordBlock (K := K) hI' t) :=
      range_spFlagLeviHom hI' htI hmax
    funext j
    let ψ : ↥Q →* StatedSp r K :=
      (Pi.evalMonoidHom (fun _ : Fin (r + 1) => StatedSp r K) j).comp β
    have hψrange : ψ.range ≤ spFlagLeviCoordBlock (K := K) hI' t j := by
      rintro _ ⟨q, rfl⟩
      have hmem : β q ∈ Subgroup.pi Set.univ (spFlagLeviCoordBlock (K := K) hI' t) := by
        rw [← hrange]
        exact ⟨q, rfl⟩
      exact (Subgroup.mem_pi Set.univ).mp hmem j (Set.mem_univ j)
    let φ : ↥Q →* ↥(spFlagLeviCoordBlock (K := K) hI' t j) :=
      ψ.codRestrict _ fun x => hψrange ⟨x, rfl⟩
    have hφsurj : Function.Surjective φ := by
      intro y
      have hy : Pi.mulSingle j (y : StatedSp r K) ∈ β.range := by
        rw [hrange, Subgroup.mem_pi]
        intro i _
        by_cases hi : i = j
        · subst hi
          rw [Pi.mulSingle_eq_same]
          exact y.2
        · rw [Pi.mulSingle_eq_of_ne hi]
          exact (spFlagLeviCoordBlock (K := K) hI' t i).one_mem
      obtain ⟨q, hq⟩ := hy
      refine ⟨q, Subtype.ext ?_⟩
      change (β q) j = (y : StatedSp r K)
      rw [hq, Pi.mulSingle_eq_same]
    have hMnorm : ((CFSG.pCore 2 ↥Q).map φ).Normal :=
      (inferInstance : (CFSG.pCore 2 ↥Q).Normal).map φ hφsurj
    have hM2 : IsPGroup 2 ((CFSG.pCore 2 ↥Q).map φ) :=
      IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥Q)) φ
    have hMle : (CFSG.pCore 2 ↥Q).map φ ≤
        CFSG.pCore 2 ↥(spFlagLeviCoordBlock (K := K) hI' t j) :=
      le_sSup ⟨hMnorm, hM2⟩
    rw [pCore_spFlagLeviCoordBlock_eq_bot hI' t hK j] at hMle
    have hMbot : (CFSG.pCore 2 ↥Q).map φ = ⊥ := le_bot_iff.mp hMle
    have hz : φ z ∈ (CFSG.pCore 2 ↥Q).map φ := ⟨z, hzQ, rfl⟩
    rw [hMbot] at hz
    have h1 : φ z = 1 := Subgroup.mem_bot.mp hz
    simpa [φ, ψ] using congrArg Subtype.val h1
  ·
    exact le_sSup ⟨inferInstance, hβ2⟩

theorem nonempty_quotient_pCore_flagStabilizer [Finite K] [CharP K 2]
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hK : Nat.card K = 2) :
    Nonempty (↥(CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer r K I) ⧸
        CFSG.pCore 2 ↥(CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer r K I) ≃*
      ∀ j : Fin (r + 1),
        ↥(spFlagLeviCoordBlock (K := K) (fun i hi => (hI i hi).2) t j)) := by
  let hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hpc := pCore_flagStabilizer_eq_ker_spFlagLeviHom (K := K) hI htI hmax hK
  have hrange := range_spFlagLeviHom (K := K) hI' htI hmax
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans ?_⟩
  refine (QuotientGroup.quotientKerEquivRange (spFlagLeviHom (K := K) hI' htI)).trans ?_
  exact (MulEquiv.subgroupCongr hrange).trans
    (piSubgroupEquiv (fun j => spFlagLeviCoordBlock (K := K) hI' t j))

theorem isSpTwoFactor_spFlagLeviCoordBlock [Finite K] [CharP K 2] (hI : ∀ i ∈ I, i ≤ r)
    (t : ℕ) (hK : Nat.card K = 2) (j : Fin (r + 1)) :
    IsSpTwoFactor ↥(spFlagLeviCoordBlock (K := K) hI t j) := by
  by_cases hj0 : (j : ℕ) = 0
  · rw [spFlagLeviCoordBlock_of_eq_zero hI t hj0]
    exact IsSpTwoFactor.of_mulEquiv
      (MonoidHom.ofInjective (f := spFlagResEmb (r := r) (K := K) t)
        (spFlagResEmb_injective t)) (statedSp_isSpTwoFactor hK).1
  by_cases hj : (j : ℕ) ∈ I
  · rw [spFlagLeviCoordBlock_of_mem hI t hj0 hj]
    have hb : j ≤ r := hI j hj
    refine IsSpTwoFactor.of_mulEquiv ?_ (slt_isSpTwoFactor (j - spFlagPrev I j)).1
    exact (CFSG.Quasithin.FLc.slEquivGLt (j - spFlagPrev I j)).trans
      ((CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK (j - spFlagPrev I j)).symm.trans
        (MonoidHom.ofInjective (f := spFlagCutEmb (K := K) (spFlagPrev I j) j hb)
          (spFlagCutEmb_injective _ _ hb)))
  · rw [spFlagLeviCoordBlock_of_not_mem hI t hj0 hj]
    exact isSpTwoFactor_of_subsingleton (by infer_instance)


theorem isSpTwoLeviProduct_flagStabilizer [Finite K] [CharP K 2]
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {t : ℕ} (htI : t ∈ I) (hmax : ∀ c ∈ I, c ≤ t)
    (hK : Nat.card K = 2) :
    IsSpTwoLeviProduct
      ↥(CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer r K I) := by
  let hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  obtain ⟨e⟩ := nonempty_quotient_pCore_flagStabilizer (K := K) hI htI hmax hK
  exact ⟨r + 1, fun j => ↥(spFlagLeviCoordBlock (K := K) hI' t j),
    fun _ => inferInstance, fun _ => inferInstance, ⟨e⟩,
    fun j => isSpTwoFactor_spFlagLeviCoordBlock hI' t hK j⟩

theorem isSpTwoLeviProduct_idxBTwo (hZ : OddCenterRest) {X : Type} [Group X] [Finite X]
    {L J : Subgroup X} (hCP : CompParab L J) (h : IsLieOf IdxBTwo (↥L ⧸ center ↥L)) :
    IsSpTwoLeviProduct ↥J := by
  obtain ⟨r, K, hKf, hKfin, hKchar, -, hK2, ⟨φ⟩⟩ :=
    exists_mulEquiv_statedSp_of_idxBTwo hZ hCP.comp hCP.odd h
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hQI := isSpTwoLeviProduct_flagStabilizer (K := K) hI htI hmax hK2
  have hmapQ :
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer r K I).map
        ρ.toMonoidHom = J.subgroupOf L := by
    rw [← hρ, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr ρ.surjective, top_inf_eq]
  let e : ↥(CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer r K I) ≃* ↥J :=
    (MulEquiv.subgroupMap ρ _).trans
      ((MulEquiv.subgroupCongr hmapQ).trans (Subgroup.subgroupOfEquivOfLe hCP.parab.1))
  exact IsSpTwoLeviProduct.of_mulEquiv e hQI

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
