module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.SeitzReduction.E6Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e6CentralizerYRootsNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

abbrev yA1 : Fin Tag.E6.rank → ℤ := Pi.single (0 : Fin 6) 1

abbrev yA4 : Fin Tag.E6.rank → ℤ := Pi.single (3 : Fin 6) 1

@[expose] def yLam : Fin Tag.E6.rank → ℤ := ![1, 0, 0, 1, 0, 0]

@[expose] def yLamAS : Fin Tag.E6.rank → ℤ := ![2, 2, 3, 4, 3, 2]

@[expose] def yRadicalRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ 0 < iform γ yLam}

@[expose] def yLeviRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform γ yLam = 0}

@[expose] def yFixedRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform γ yA1 = 0 ∧ iform γ yA4 = 0}

@[expose] def yPairRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform γ yA1 = 1 ∧ iform γ yA4 = -1}

@[expose] def yPartner (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ := γ - yA1 + yA4

@[expose] def yPairList : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 0, 1, 0, 0, 0], ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1], ![0, 0, -1, -1, 0, 0],
    ![0, -1, -1, -2, -1, 0], ![0, -1, -1, -2, -1, -1]]

theorem yLam_eq : yLam = yA1 + yA4 ∧ iform yA1 yA1 = 2 ∧ iform yA4 yA4 = 2 ∧
    iform yA1 yA4 = 0 ∧ iform yA4 yA1 = 0 := by
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i <;> rfl
  · decide +kernel

theorem yRadical_check : (∀ γ ∈ rootFinset .E6, 0 < iform γ yLam →
    0 ≤ iform γ yA1 ∧ 0 ≤ iform γ yA4) ∧
    ((rootFinset .E6).filter fun γ => 0 < iform γ yLam).card = 24 := by
  decide +kernel

theorem yPair_check : (∀ γ ∈ rootFinset .E6, iform γ yA1 = 1 → iform γ yA4 = -1 → γ ∈ yPairList) ∧
    (∀ γ ∈ yPairList, γ ∈ rootFinset .E6 ∧ iform γ yA1 = 1 ∧ iform γ yA4 = -1 ∧
      γ + yA4 ∈ rootFinset .E6 ∧ γ - yA1 + yA4 ∈ rootFinset .E6) ∧ yPairList.Nodup := by
  decide +kernel

theorem yLamAS_check : (∀ γ ∈ rootFinset .E6, iform γ yLamAS = γ 0 + γ 5 ∧
    (0 < iform γ yLamAS ↔ 0 < height γ ∧ ¬(γ 0 = 0 ∧ γ 5 = 0)) ∧
    (iform γ yLamAS = 0 ↔ γ 0 = 0 ∧ γ 5 = 0)) ∧
    yLamAS = oddDerivE6YFrame.sum := by
  decide +kernel

theorem iform_nonneg_of_mem_yRadicalRoots {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ yRadicalRoots) :
    0 ≤ iform γ yA1 ∧ 0 ≤ iform γ yA4 :=
  yRadical_check.1 γ (mem_rootFinset.2 hγ.1) hγ.2

theorem iform_yLam (γ : Fin Tag.E6.rank → ℤ) : iform γ yLam = iform γ yA1 + iform γ yA4 := by
  rw [yLam_eq.1, iform_add_right]

theorem yFixedRoots_subset_yLeviRoots : yFixedRoots ⊆ yLeviRoots := fun γ hγ =>
  ⟨hγ.1, by rw [iform_yLam, hγ.2.1, hγ.2.2, add_zero]⟩

theorem yPairRoots_subset_yLeviRoots : yPairRoots ⊆ yLeviRoots := fun γ hγ =>
  ⟨hγ.1, by rw [iform_yLam, hγ.2.1, hγ.2.2]; norm_num⟩

theorem iform_yPartner (γ : Fin Tag.E6.rank → ℤ) :
    iform (yPartner γ) yA1 = iform γ yA1 - 2 ∧ iform (yPartner γ) yA4 = iform γ yA4 + 2 := by
  obtain ⟨-, h11, h44, h14, h41⟩ := yLam_eq
  simp only [yPartner, iform_add_left, iform_sub_left, h11, h44, h14, h41]
  constructor <;> ring

theorem yPartner_spec {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ yPairRoots) :
    IsRoot .E6 (yPartner γ) ∧ iform (yPartner γ) yA1 = -1 ∧ iform (yPartner γ) yA4 = 1 ∧
      IsRoot .E6 (γ + yA4) ∧ yPartner γ + yA1 = γ + yA4 := by
  have hL := yPair_check.1 γ (mem_rootFinset.2 hγ.1) hγ.2.1 hγ.2.2
  obtain ⟨-, -, -, h4, hp⟩ := yPair_check.2.1 γ hL
  obtain ⟨h1, h2⟩ := iform_yPartner γ
  refine ⟨mem_rootFinset.1 hp, by rw [h1, hγ.2.1]; norm_num, by rw [h2, hγ.2.2]; norm_num,
    mem_rootFinset.1 h4, ?_⟩
  simp only [yPartner]
  abel

theorem highRoot_mem_yFixedRoots : highRoot .E6 ∈ yFixedRoots ∧ -highRoot .E6 ∈ yFixedRoots := by
  obtain ⟨h1, -, -, -, h5, h6⟩ := EPilot.e6PairPerp_check
  obtain ⟨r1, a1, a4⟩ := h1 _ h5
  obtain ⟨r1', a1', a4'⟩ := h1 _ h6
  exact ⟨⟨mem_rootFinset.1 r1, a1, a4⟩, ⟨mem_rootFinset.1 r1', a1', a4'⟩⟩

@[expose] def nodes16 : Set (Fin Tag.E6.rank) := {j | j ≠ 0 ∧ j ≠ 5}

theorem parabolicRoots_nodes16 :
    parabolicRoots .E6 nodes16 = {γ | IsRoot .E6 γ ∧ iform γ yLamAS = 0} := by
  ext γ
  simp only [parabolicRoots, nodes16, Set.mem_ofPred_eq, ne_eq, not_and_or, not_not]
  constructor
  · rintro ⟨hγ, h⟩
    exact ⟨hγ, ((yLamAS_check.1 γ (mem_rootFinset.2 hγ)).2.2).2
      ⟨h 0 (Or.inl rfl), h 5 (Or.inr rfl)⟩⟩
  · rintro ⟨hγ, h⟩
    obtain ⟨h0, h5⟩ := ((yLamAS_check.1 γ (mem_rootFinset.2 hγ)).2.2).1 h
    refine ⟨hγ, fun i hi => ?_⟩
    rcases hi with rfl | rfl
    · exact h0
    · exact h5

theorem parabolicRadicalRoots_nodes16 :
    parabolicRadicalRoots .E6 nodes16 = {γ | IsRoot .E6 γ ∧ 0 < iform γ yLamAS} := by
  ext γ
  simp only [parabolicRadicalRoots, parabolicPosRoots, Set.mem_sdiff, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  rw [parabolicRoots_nodes16]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hγ, hpos⟩, hn⟩
    refine ⟨hγ, ((yLamAS_check.1 γ (mem_rootFinset.2 hγ)).2.1).2 ⟨hpos, fun h => hn ⟨⟨hγ, ?_⟩,
      hγ, hpos⟩⟩⟩
    exact ((yLamAS_check.1 γ (mem_rootFinset.2 hγ)).2.2).2 h
  · rintro ⟨hγ, h⟩
    obtain ⟨hpos, hn⟩ := ((yLamAS_check.1 γ (mem_rootFinset.2 hγ)).2.1).1 h
    exact ⟨⟨hγ, hpos⟩, fun h' => hn (((yLamAS_check.1 γ (mem_rootFinset.2 hγ)).2.2).1 h'.1.2)⟩

theorem image_smul_setOf_iform (w : WeylGroup .E6) (v : Fin Tag.E6.rank → ℤ) (P : ℤ → Prop) :
    (fun γ => w • γ) '' {γ | IsRoot .E6 γ ∧ P (iform γ v)} =
      {γ | IsRoot .E6 γ ∧ P (iform γ (w • v))} := by
  ext γ
  constructor
  · rintro ⟨β, ⟨hβ, hP⟩, rfl⟩
    exact ⟨IsRoot.smul hβ w, by rwa [iform_smul]⟩
  · rintro ⟨hγ, hP⟩
    refine ⟨w⁻¹ • γ, ⟨IsRoot.smul hγ w⁻¹, ?_⟩, smul_inv_smul w γ⟩
    have e : iform (w⁻¹ • γ) v = iform γ (w • v) := by
      rw [← iform_smul w, smul_inv_smul]
    rwa [e]

theorem e6RepWeyl_smul_yLamAS : e6RepWeyl 1 • yLamAS = yLam := by
  have h := e6RepWeyl_smul_e6ASFrame 1
  have hL : yLamAS = (e6ASFrame 1).sum := yLamAS_check.2
  rw [hL]
  have e : ∀ F : List (Fin Tag.E6.rank → ℤ), e6RepWeyl 1 • F.sum = (F.map (e6RepWeyl 1 • ·)).sum :=
    fun F => by
      induction F with
      | nil => simp
      | cons a F ih => rw [List.sum_cons, smul_add, ih, List.map_cons, List.sum_cons]
  rw [e, h]
  funext i
  fin_cases i <;> rfl

theorem image_e6RepWeyl_parabolicRadicalRoots_nodes16 :
    (fun γ => e6RepWeyl 1 • γ) '' parabolicRadicalRoots .E6 nodes16 = yRadicalRoots := by
  rw [parabolicRadicalRoots_nodes16, image_smul_setOf_iform (P := fun n => 0 < n),
    e6RepWeyl_smul_yLamAS]
  rfl

theorem image_e6RepWeyl_parabolicRoots_nodes16 :
    (fun γ => e6RepWeyl 1 • γ) '' parabolicRoots .E6 nodes16 = yLeviRoots := by
  rw [parabolicRoots_nodes16, image_smul_setOf_iform (P := fun n => n = 0),
    e6RepWeyl_smul_yLamAS]
  rfl

end CFSG.SeitzReduction.E6Pilot
