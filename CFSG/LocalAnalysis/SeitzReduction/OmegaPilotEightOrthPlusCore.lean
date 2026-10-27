module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommPlus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviOTwo

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.EvenSmallLie
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Factor

variable {M : Type*} [Group M]

theorem normal_of_centralizer_of_sup_eq_top {A B₁ B₂ : Subgroup M}
    (h1 : B₁ ≤ centralizer (A : Set M)) (h2 : B₂ ≤ centralizer (A : Set M))
    (htop : A ⊔ B₁ ⊔ B₂ = ⊤) : A.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← htop]
  exact sup_le (sup_le le_normalizer (h1.trans (centralizer_le_normalizer _)))
    (h2.trans (centralizer_le_normalizer _))

theorem map_le_of_simple_of_commute {A B₁ B₂ : Subgroup M}
    (hA : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤) (hAp : ⁅A, A⁆ = A) (hA1 : A ≠ ⊥)
    (h1 : A ≤ centralizer (B₁ : Set M)) (h2 : A ≤ centralizer (B₂ : Set M))
    (h3 : B₁ ≤ centralizer (B₂ : Set M)) (htop : A ⊔ B₁ ⊔ B₂ = ⊤) (ι : M ≃* M) :
    A.map ι.toMonoidHom ≤ A ∨ A.map ι.toMonoidHom ≤ B₁ ∨ A.map ι.toMonoidHom ≤ B₂ := by
  have hAn : A.Normal := normal_of_centralizer_of_sup_eq_top (le_centralizer_iff.mp h1)
    (le_centralizer_iff.mp h2) htop
  have hB₁n : B₁.Normal := normal_of_centralizer_of_sup_eq_top (A := B₁) (B₁ := A) (B₂ := B₂) h1
    (le_centralizer_iff.mp h3) (by
      rw [eq_top_iff, ← htop]
      exact sup_le (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left))
        le_sup_right)
  have hB₂n : B₂.Normal := normal_of_centralizer_of_sup_eq_top (A := B₂) (B₁ := A) (B₂ := B₁) h2 h3
    (by
      rw [eq_top_iff, ← htop]
      exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
        (le_sup_left.trans le_sup_left))
  set N := A.map ι.toMonoidHom with hN
  have hNn : N.Normal := hAn.map ι.toMonoidHom ι.surjective
  set ε : A ≃* N := ι.subgroupMap A with hε
  have hdich : ∀ X : Subgroup M, X.Normal → N ≤ X ∨ N ⊓ X = ⊥ := by
    intro X hX
    have hT : ((X.subgroupOf N).comap ε.toMonoidHom).Normal :=
      (hX.subgroupOf N).comap ε.toMonoidHom
    rcases hA _ hT with hbot | htop'
    · right
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxX⟩
      have hmem : ε.symm ⟨x, hxN⟩ ∈ (X.subgroupOf N).comap ε.toMonoidHom := by
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, mem_subgroupOf]
        exact hxX
      rw [hbot, mem_bot] at hmem
      have : (⟨x, hxN⟩ : N) = 1 := by
        rw [← ε.apply_symm_apply ⟨x, hxN⟩, hmem, map_one]
      exact (mem_bot).mpr (congrArg Subtype.val this)
    · left
      intro x hxN
      have hmem : ε.symm ⟨x, hxN⟩ ∈ (X.subgroupOf N).comap ε.toMonoidHom := htop' ▸ mem_top _
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, mem_subgroupOf] at hmem
      exact hmem
  have hcen : ∀ X : Subgroup M, X.Normal → N ⊓ X = ⊥ → N ≤ centralizer (X : Set M) := by
    intro X hX hbot
    rw [← commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← hbot]
    exact commutator_le_inf N X
  rcases hdich A hAn with hA' | hA'
  · exact Or.inl hA'
  rcases hdich B₁ hB₁n with hB₁' | hB₁'
  · exact Or.inr (Or.inl hB₁')
  rcases hdich B₂ hB₂n with hB₂' | hB₂'
  · exact Or.inr (Or.inr hB₂')
  exfalso
  have hc1 := le_centralizer_iff.mp (hcen A hAn hA')
  have hc2 := le_centralizer_iff.mp (hcen B₁ hB₁n hB₁')
  have hc3 := le_centralizer_iff.mp (hcen B₂ hB₂n hB₂')
  have htopc : (⊤ : Subgroup M) ≤ centralizer (N : Set M) := by
    rw [← htop]; exact sup_le (sup_le hc1 hc2) hc3
  have hNab : ⁅N, N⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact fun x _ => htopc (mem_top x)
  have hNp : ⁅N, N⁆ = N := by rw [hN, ← map_commutator, hAp]
  apply hA1
  rw [eq_bot_iff]
  intro a ha
  have hia : ι a ∈ N := ⟨a, ha, rfl⟩
  rw [← hNp, hNab, mem_bot] at hia
  rw [mem_bot]
  exact (MulEquiv.map_eq_one_iff ι).mp hia

end Factor

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem leviFixBar_le_rootLeviBar {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {P₁ P₂ : HypPair Q} :
    leviFixBar P₁ P₂ ≤ rootLeviBar Q P₁ P₂ := by
  rintro _ ⟨X, hX, rfl⟩
  exact ⟨X, mem_subgroupOf.mpr (mem_leviFix.mp (mem_subgroupOf.mp hX)).2.1, rfl⟩

omit [Finite K] [CharP K 2] in
theorem stabTwoBar_le_rootLeviBar_plusZ :
    stabTwoBar K 0 1 ≤ rootLeviBar (coordinateQuadPlus 4 K) (plusPair K 0)
      (flipPair (plusPair K 1)) := by
  have h := stabPairsBar_le_rootLeviBar (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0)
    (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm
  rw [stabPairsBar_swap_right] at h
  exact h

theorem exists_mul_mul_of_mem_rootLeviBar_plusZ (hq : 4 ≤ Nat.card K)
    {m : matrixProjectiveDerived (coordinateQuadPlus 4 K)}
    (hm : m ∈ rootLeviBar (coordinateQuadPlus 4 K) (plusPair K 0) (flipPair (plusPair K 1))) :
    ∃ a ∈ leviFixBar (plusPair K 0) (flipPair (plusPair K 1)),
      ∃ b₁ ∈ leviFixBar (plusPair K 2) (plusPair K 3),
        ∃ b₂ ∈ leviFixBar (plusPair K 2) (flipPair (plusPair K 3)), m = a * (b₁ * b₂) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_rootLeviBar
    (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0)
    (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm
    (pairDisjoint_plus (show (0 : Fin 4) ≠ 1 by decide)).swap_right hQ hT hm
  rw [stabPairsBar_swap_right] at hb
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mul_of_mem_stabTwoBar hq (show (0 : Fin 4) ≠ 1 by decide)
    (show (2 : Fin 4) ≠ 3 by decide) (by decide) (by decide) (by decide) (by decide) hb
  exact ⟨a, ha, b₁, hb₁, b₂, hb₂, rfl⟩

variable (K) in
noncomputable abbrev plusMz : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
  rootLeviBar (coordinateQuadPlus 4 K) (plusPair K 0) (flipPair (plusPair K 1))

variable (K) in
noncomputable abbrev plusA : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
  leviFixBar (plusPair K 0) (flipPair (plusPair K 1))

omit [Finite K] in
theorem stabTwoBar_le_centralizer_plusA :
    stabTwoBar K 0 1 ≤ centralizer (plusA K : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
  fun _ hb => mem_centralizer_iff.mpr fun _ ha =>
    leviFixBar_commute_stabTwoBar_zero_one (Or.inr rfl) ha hb

theorem hmodel_plusZ (hq : 4 ≤ Nat.card K) (ι : plusMz K ≃* plusMz K)
    {y : matrixProjectiveDerived (coordinateQuadPlus 4 K)}
    (hy : y ∈ (((plusA K).subgroupOf (plusMz K)).map ι.toMonoidHom).map (plusMz K).subtype)
    (hy1 : y ≠ 1) (hyo : Odd (orderOf y))
    {S R : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hSy : S ≤ centralizer {y})
    (hSgen : ∀ N : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)), plusZ K ∈ N →
      (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → S ≤ N)
    (hRz : R ≤ centralizer {plusZ K}) (hRy : R ≤ centralizer {y}) (hRperf : ⁅R, R⁆ = R) :
    S ≤ centralizer (R : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
  classical
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  set B₁ := leviFixBar (plusPair K 2) (plusPair K 3) with hB₁
  set B₂ := leviFixBar (plusPair K 2) (flipPair (plusPair K 3)) with hB₂
  have h₁₂ : (plusPair K 0).Orth (flipPair (plusPair K 1)) := plusPair_orth_flip (by decide)
  have h23 : (plusPair K 2).Orth (plusPair K 3) := plusPair_orth (by decide)
  have hAM : plusA K ≤ plusMz K := leviFixBar_le_rootLeviBar
  have hB₁M : B₁ ≤ plusMz K := (leviFixBar_le_stabTwoBar_of_orth (plusPair_orth (by decide))
    (plusPair_orth (by decide)) (plusPair_orth (by decide)) (plusPair_orth (by decide))).trans
    stabTwoBar_le_rootLeviBar_plusZ
  have hB₂M : B₂ ≤ plusMz K := (leviFixBar_le_stabTwoBar_of_orth (plusPair_orth (by decide))
    (plusPair_orth_flip (by decide)) (plusPair_orth (by decide))
    (plusPair_orth_flip (by decide))).trans stabTwoBar_le_rootLeviBar_plusZ
  have hAB₁ : plusA K ≤ centralizer (B₁ : Set _) := leviFixBar_le_centralizer_of_orth h₁₂
    (plusPair_orth (by decide)) (plusPair_orth (by decide))
    (orth_flipPair_left (plusPair_orth (by decide))) (orth_flipPair_left (plusPair_orth (by decide)))
  have hAB₂ : plusA K ≤ centralizer (B₂ : Set _) := leviFixBar_le_centralizer_of_orth h₁₂
    (plusPair_orth (by decide)) (plusPair_orth_flip (by decide))
    (orth_flipPair_left (plusPair_orth (by decide)))
    (orth_flipPair_left (plusPair_orth_flip (by decide)))
  have hB₁B₂ : B₁ ≤ centralizer (B₂ : Set _) := leviFixBar_le_centralizer_flip h23 hQ hT
  have hsub : ∀ {X Y : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))},
      X ≤ centralizer (Y : Set _) →
        X.subgroupOf (plusMz K) ≤ centralizer (Y.subgroupOf (plusMz K) : Set (plusMz K)) := by
    intro X Y hXY x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp (hXY (mem_subgroupOf.mp hx)) _ (mem_subgroupOf.mp hy))
  have : IsSimpleGroup SL(2, K) := LinearPilot.isSimpleGroup_specialLinearGroup_two hq
  have : Group.IsPerfect SL(2, K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hq
  set εA : (plusA K).subgroupOf (plusMz K) ≃* SL(2, K) :=
    (Subgroup.subgroupOfEquivOfLe hAM).trans (leviFixBarEquiv h₁₂ hQ hT hQ') with hεA
  have : IsSimpleGroup ((plusA K).subgroupOf (plusMz K)) := εA.isSimpleGroup
  have hAp : ⁅(plusA K).subgroupOf (plusMz K), (plusA K).subgroupOf (plusMz K)⁆ =
      (plusA K).subgroupOf (plusMz K) :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective (f := εA.symm.toMonoidHom)
      εA.symm.surjective)
  have hA1 : (plusA K).subgroupOf (plusMz K) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have htop : (plusA K).subgroupOf (plusMz K) ⊔ B₁.subgroupOf (plusMz K) ⊔
      B₂.subgroupOf (plusMz K) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨m, hm⟩ -
    obtain ⟨a, ha, b₁, hb₁, b₂, hb₂, hab⟩ := exists_mul_mul_of_mem_rootLeviBar_plusZ hq hm
    have he : (⟨m, hm⟩ : plusMz K) = ⟨a, hAM ha⟩ * (⟨b₁, hB₁M hb₁⟩ * ⟨b₂, hB₂M hb₂⟩) :=
      Subtype.ext hab
    rw [he]
    exact mul_mem (mem_sup_left (mem_sup_left (mem_subgroupOf.mpr ha)))
      (mul_mem (mem_sup_left (mem_sup_right (mem_subgroupOf.mpr hb₁)))
        (mem_sup_right (mem_subgroupOf.mpr hb₂)))
  have hcases := map_le_of_simple_of_commute
    (fun N hN => by have := hN; exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N)
    hAp hA1 (hsub hAB₁) (hsub hAB₂) (hsub hB₁B₂) htop ι
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  rcases hcases with h | h | h
  · have hyA : ((ι x : plusMz K) : matrixProjectiveDerived (coordinateQuadPlus 4 K)) ∈ plusA K :=
      mem_subgroupOf.mp (h ⟨x, hx, rfl⟩)
    exact le_centralizer_of_model_leviFix (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0)
      (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm
      (pairDisjoint_plus (show (0 : Fin 4) ≠ 1 by decide)).swap_right hQ
      (plusPair_orth (show (0 : Fin 4) ≠ 2 by decide))
      (orth_flipPair_left (plusPair_orth (show (1 : Fin 4) ≠ 2 by decide))) hyA hy1 hyo hSy hSgen
      hRz hRy hRperf
  · have hyB : ((ι x : plusMz K) : matrixProjectiveDerived (coordinateQuadPlus 4 K)) ∈ B₁ :=
      mem_subgroupOf.mp (h ⟨x, hx, rfl⟩)
    exact le_centralizer_of_model_plusB hq (Or.inl rfl) hyB hy1 hyo hSy hSgen hRz hRy hRperf
  · have hyB : ((ι x : plusMz K) : matrixProjectiveDerived (coordinateQuadPlus 4 K)) ∈ B₂ :=
      mem_subgroupOf.mp (h ⟨x, hx, rfl⟩)
    exact le_centralizer_of_model_plusB hq (Or.inr rfl) hyB hy1 hyo hSy hSgen hRz hRy hRperf

end Model

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_centralizer_stabTwoBar_of_conj_eq_mul_plus (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) {g : G} (hg : g⁻¹ * t * g = t * (e.symm (plusZ K) : G))
    (hzg : ∃ hz : g * (e.symm (plusZ K) : G) * g⁻¹ ∈ L,
      IsLongRoot (coordinateQuadPlus 4 K) (e ⟨_, hz⟩))
    {y₀ : matrixProjectiveDerived (coordinateQuadPlus 4 K)} (hy₀A : y₀ ∈ plusA K) (hy₀1 : y₀ ≠ 1)
    (hy₀o : Odd (orderOf y₀)) {S : Subgroup G} (hSperf : ⁅S, S⁆ = S)
    (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hSy : S ≤ centralizer ({(e.symm y₀ : G)} : Set G)) (hzS : (e.symm (plusZ K) : G) ∈ S) :
    S ≤ centralizer (modelToG e (stabTwoBar K 0 1) : Set G) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have ha := isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0
  have hb := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm
  have hd := (pairDisjoint_plus (n := 4) (show (0 : Fin 4) ≠ 1 by decide)).swap_right
  have h₁₂ : (plusPair K 0).Orth (flipPair (plusPair K 1)) := plusPair_orth_flip (by decide)
  have h₁₃ : (plusPair K 0).Orth (plusPair K 2) := plusPair_orth (by decide)
  have h₂₃ : (flipPair (plusPair K 1)).Orth (plusPair K 2) :=
    orth_flipPair_left (plusPair_orth (by decide))
  have hz₀ : plusZ K = rootPairElt hQ h₁₂ h₁₃ h₂₃ := rfl
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hBperf : ⁅stabTwoBar K 0 1, stabTwoBar K 0 1⁆ = stabTwoBar K 0 1 :=
    commutator_stabTwoBar_four hq (by decide)
  have hBperf' := hBperf
  rw [show stabTwoBar K 0 1 = stabPairsBar (coordinateQuadPlus 4 K) (plusIndexEquiv 4 (.inl 0))
      (plusIndexEquiv 4 (.inr 0)) (plusIndexEquiv 4 (.inr 1)) (plusIndexEquiv 4 (.inl 1)) from
    (stabPairsBar_swap_right _ _ _ _).symm] at hBperf'
  have hCperf : ⁅centralizer ({plusZ K} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      centralizer ({plusZ K} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))⁆ =
      centralizer ({plusZ K} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
    commutator_centralizer_rootPairElt_of ha hb hd hQ h₁₃ h₂₃ hl0 hl1 hBperf'
  have hC : centralizer ({plusZ K} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      rootRadicalBar (coordinateQuadPlus 4 K) (plusPair K 0) (flipPair (plusPair K 1)) ⊔
        plusMz K := centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  have hF3 : perfectCore (centralizer ({plusZ K} :
      Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) =
      rootRadicalBar (coordinateQuadPlus 4 K) (plusPair K 0) (flipPair (plusPair K 1)) ⊔
        plusMz K := by
    rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect hCperf]
    exact hC
  obtain ⟨hzL, hzl⟩ := hzg
  have hc : ∃ c, c * e ⟨_, hzL⟩ * c⁻¹ = plusZ K := isConj_iff.mp (isConj_of_isLongRoot hQ h₁₂ h₁₃
    h₂₃ hzl (isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃))
  obtain ⟨c'', hc''⟩ := hc
  obtain ⟨φ', hφ', hφ'r, hφ'z⟩ := EPilot.exists_coords_conjugate e g hc''
  have hφ'z' : φ' (plusZ K) = (e.symm (plusZ K) : G) := by
    rw [hφ'z, MulEquiv.symm_apply_apply]
    group
  have hM : ∀ N : Subgroup (plusMz K), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN h2
    refine rootLeviBar_normal_isPGroup_eq_bot_of_frame ha hb hd hQ hT
      (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 2)
      (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 3)
      (pairDisjoint_plus (show (2 : Fin 4) ≠ 3 by decide))
      (pairDisjoint_plus (show (0 : Fin 4) ≠ 2 by decide))
      (pairDisjoint_plus (show (0 : Fin 4) ≠ 3 by decide))
      (pairDisjoint_plus (show (1 : Fin 4) ≠ 2 by decide)).swap_left
      (pairDisjoint_plus (show (1 : Fin 4) ≠ 3 by decide)).swap_left (fun s => ?_) N hN h2
    obtain ⟨u, rfl⟩ := (plusIndexEquiv 4).surjective s
    rcases u with u | u <;> fin_cases u <;> simp
  have hAM : plusA K ≤ plusMz K := leviFixBar_le_rootLeviBar
  have hBM := stabTwoBar_le_rootLeviBar_plusZ (K := K)
  have hMz : plusMz K ≤ centralizer {plusZ K} := by
    rw [hC]; exact le_sup_right
  refine le_centralizer_of_coords_orth_aut hset hOut e ht htC (z₀ := plusZ K)
    (rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃ : plusZ K ≠ 1) hg hφ' hφ'r hφ'z' _ (plusMz K) hF3
    (isPGroup_rootRadicalBar _ _) (rootLeviBar_le_normalizer h₁₂)
    (disjoint_rootRadicalBar_rootLeviBar h₁₂) hM (J := plusA K) hAM ?_ hy₀A hy₀1 hy₀o hSperf
    hSsimple hSt hSy hzS
    (fun x hx => by obtain ⟨_, ⟨y, -, rfl⟩, rfl⟩ := hx; exact (e.symm y).2)
    (map_le_centralizer_singleton e (hBM.trans hMz))
    (map_le_centralizer_singleton e fun x hx => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (stabTwoBar_le_centralizer_plusA hx) y₀ hy₀A).symm)
    (by rw [UnitaryPilot.modelToG, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hBperf])
  intro ι y hy hy1 hyo S' R' hS'y hS'gen hR'z hR'y hR'perf
  exact hmodel_plusZ hq ι hy hy1 hyo hS'y hS'gen hR'z hR'y hR'perf

end Core

section TwoSided

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orthTorusElt_mem_plusA {l : Kˣ} (hl : l ≠ 1) :
    orthTorusElt (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0)
        (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm l ∈ plusA K ∧
      orthTorusElt (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0)
        (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm l ≠ 1 ∧
      Odd (orderOf (orthTorusElt (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0)
        (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm l)) := by
  have ha := isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0
  have hb := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm
  have hd := (pairDisjoint_plus (n := 4) (show (0 : Fin 4) ≠ 1 by decide)).swap_right
  have hQ' := ha.exists_ne_zero
  obtain ⟨hM, -, h1, ho⟩ := orthTorusElt_spec ha hb hd hl
  refine ⟨?_, h1, ho⟩
  have hL : orthTorusLin (plusIndexEquiv 4 (.inl 0)) (plusIndexEquiv 4 (.inr 0))
      (plusIndexEquiv 4 (.inr 1)) (plusIndexEquiv 4 (.inl 1)) l ∈
      rootLevi (coordinateQuadPlus 4 K) ha.hypPair hb.hypPair := by
    have h := projLift_mem_of_mem_map hQ' hM
    rwa [orthTorusElt, projLift_projHom] at h
  exact projHom_mem_leviFixBar (g := ⟨orthTorusLin (plusIndexEquiv 4 (.inl 0))
    (plusIndexEquiv 4 (.inr 0)) (plusIndexEquiv 4 (.inr 1)) (plusIndexEquiv 4 (.inl 1)) l,
    orthTorusLin_mem_orthDerived ha hb l⟩) (mem_leviFix.mpr ⟨orthTorusLin_mem_orthDerived ha hb l,
      hL, fun x hx => orthTorusLin_apply_of_inW ha hb l hx⟩)

theorem orthTorusElt_mem_plusLevelTorus (l : Kˣ) :
    orthTorusElt (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0)
        (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).symm l ∈
      plusLevelTorus K ({0, 1} : Finset (Fin 4)) := by
  have hfr := isHypFrame_plus K 4
  set t : Fin 4 → Kˣ := Pi.mulSingle 0 l * Pi.mulSingle 1 l with htdef
  have hlin : orthTorusLin (plusIndexEquiv 4 (.inl 0)) (plusIndexEquiv 4 (.inr 0))
      (plusIndexEquiv 4 (.inr 1)) (plusIndexEquiv 4 (.inl 1)) l =
      frameLin (plusFrameLeft 4) (plusFrameRight 4) t := by
    rw [orthTorusLin, torusLin_inv_swap (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 1).ne,
      htdef, map_mul, frameLin_mulSingle, frameLin_mulSingle]
    rfl
  have ht : t ∈ levelParam (K := K) ({0, 1} : Finset (Fin 4)) := by
    have ht0 : t 0 = l := by simp [htdef]
    have ht1 : t 1 = l := by simp [htdef]
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [ht0, ht1]
  refine ⟨⟨frameLin (plusFrameLeft 4) (plusFrameRight 4) t, hfr.frameLin_mem_orthDerived t⟩,
    mem_subgroupOf.mpr ⟨t, ht, rfl⟩, ?_⟩
  rw [orthTorusElt]
  congr 1
  exact Subtype.ext hlin.symm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_forall_le_centralizer_plus_four (hset : SeitzSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot (coordinateQuadPlus 4 K) (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot (coordinateQuadPlus 4 K) (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩))) :
    ∃ g : G, g⁻¹ * t * g = t * (e.symm (plusZ K) : G) ∧
      ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
        S ≤ centralizer ({g⁻¹ * t * g} : Set G) →
        S ≤ centralizer (modelToG e (plusLevelTorus K ({0, 1} : Finset (Fin 4))) : Set G) →
        (e.symm (plusZ K) : G) ∈ S →
        S ≤ centralizer (modelToG e (stabTwoBar K 0 1) : Set G) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK; omega
    · exact h
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_plus (le_refl 4) hf hK e
  have htC := mem_centralizer_of_inf_eq hKt
  have h₁₂ : (plusPair K 0).Orth (flipPair (plusPair K 1)) := plusPair_orth_flip (by decide)
  have h₁₃ : (plusPair K 0).Orth (plusPair K 2) := plusPair_orth (by decide)
  have h₂₃ : (flipPair (plusPair K 1)).Orth (plusPair K 2) :=
    orth_flipPair_left (plusPair_orth (by decide))
  obtain ⟨l, hl⟩ := exists_units_ne_one (K := K) (by omega : 3 ≤ Nat.card K)
  obtain ⟨hyA, hy1, hyo⟩ := orthTorusElt_mem_plusA (K := K) hl
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩⟩ := hR5
  have hc : ∃ c, c * e ⟨z, hzL⟩ * c⁻¹ = plusZ K := isConj_iff.mp (isConj_of_isLongRoot hQ h₁₂
    h₁₃ h₂₃ hzl (isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃))
  obtain ⟨c', hc'⟩ := hc
  set c : L := e.symm c'⁻¹ with hcdef
  have htc : ∀ m ∈ L, t * m = m * t := fun m hm => (mem_centralizer_iff.mp htC m hm).symm
  have hcz : (c : G)⁻¹ * z * c = (e.symm (plusZ K) : G) := by
    have h1 : (c⁻¹ * ⟨z, hzL⟩ * c : L) = e.symm (plusZ K) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hcdef,
        MulEquiv.apply_symm_apply, inv_inv, ← hc']
    rw [← h1]
    rfl
  have hxzx : x * z * x⁻¹ ∈ L := by
    obtain ⟨m, hm, hmz⟩ := hzx
    rw [← hmz]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show x * (x⁻¹ * m * x) * x⁻¹ = m by group]
    exact hm
  have hsymm : (((conjugateMulEquiv L x).symm ⟨z, hzx⟩ : L) : G) = x * z * x⁻¹ := by
    set w : G := (((conjugateMulEquiv L x).symm ⟨z, hzx⟩ : L) : G) with hw
    have h1 := coe_conjugateMulEquiv L x ((conjugateMulEquiv L x).symm ⟨z, hzx⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    have h1' : z = x⁻¹ * w * x := h1
    calc w = x * (x⁻¹ * w * x) * x⁻¹ := by group
      _ = x * z * x⁻¹ := by rw [← h1']
  have hg : (x * (c : G))⁻¹ * t * (x * c) = t * (e.symm (plusZ K) : G) := by
    rw [← hcz, show (x * (c : G))⁻¹ * t * (x * c) = (c : G)⁻¹ * (x⁻¹ * t * x) * c by group, hxz,
      show (c : G)⁻¹ * (t * z) * c = (c : G)⁻¹ * t * (z * c) by group, ← htc _ (inv_mem c.2)]
    group
  refine ⟨x * c, hg, fun S hSperf hSsimple hSt hST hzS => ?_⟩
  refine le_centralizer_stabTwoBar_of_conj_eq_mul_plus hset.standardSetting hOut hq e ht htC hg ?_
    hyA hy1 hyo hSperf hSsimple hSt (hST.trans (centralizer_le ?_)) hzS
  · have he : x * (c : G) * (e.symm (plusZ K) : G) * (x * c)⁻¹ = x * z * x⁻¹ := by
      rw [← hcz]; group
    refine ⟨he ▸ hxzx, ?_⟩
    have hzz : (⟨x * (c : G) * (e.symm (plusZ K) : G) * (x * c)⁻¹, he ▸ hxzx⟩ : L) =
        (conjugateMulEquiv L x).symm ⟨z, hzx⟩ := Subtype.ext (he.trans hsymm.symm)
    rw [hzz]
    exact hzl'
  · rw [Set.singleton_subset_iff]
    exact UnitaryPilot.symm_mem_modelToG e (orthTorusElt_mem_plusLevelTorus l)

end TwoSided

end CFSG.SeitzReduction.OmegaPilot
