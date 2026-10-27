module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinTorus3

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Universal.Spin (quadPlus)

local instance f4PilotGraphSpinCommNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotGraphSpinCommNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Model

variable {K : Type} [Field K]

theorem lin6Weights_sp6ParamT3 (a b : Kˣ) :
    lin6Weights K (sp6ParamT3 K (a, b)) = ![a, a, b, a⁻¹, a⁻¹, b⁻¹] := by
  rw [sp6ParamT3_apply]
  rfl

theorem transvection_mem_centralizer_sp6Torus3 {i j : Fin 6} (hij : i ≠ j)
    (hw : ∀ a b : Kˣ, lin6Weights K (sp6ParamT3 K (a, b)) i =
      lin6Weights K (sp6ParamT3 K (a, b)) j) (c : K) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ centralizer
      (((sp6Torus3 (⊤ : Subgroup Kˣ)).map (sp6ToSL6 (F := K))) :
        Set (Matrix.SpecialLinearGroup (Fin 6) K)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨⟨a, b⟩, -, rfl⟩, rfl⟩
  refine Subtype.ext ?_
  change ((sp6ToSL6 (sp6Diag K (sp6ParamT3 K (a, b))) : Matrix.SpecialLinearGroup (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) *
        (Matrix.SpecialLinearGroup.transvection hij c : Matrix.SpecialLinearGroup (Fin 6) K) =
    (Matrix.SpecialLinearGroup.transvection hij c : Matrix.SpecialLinearGroup (Fin 6) K) *
      (sp6ToSL6 (sp6Diag K (sp6ParamT3 K (a, b))) : Matrix.SpecialLinearGroup (Fin 6) K)
  rw [sp6ToSL6_sp6Diag, lin6Torus, coe_diagTorusSL]
  refine (transvection_mul_diagonal_comm hij c ?_).symm
  rw [hw a b]

theorem e6ScLevi_end_le_map_centralizer
    [Finite K] [CharP K 2] {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5) :
    e6ScLevi K {j} ≤ (centralizer (((sp6Torus3 (⊤ : Subgroup Kˣ)).map (sp6ToSL6 (F := K))) :
      Set (Matrix.SpecialLinearGroup (Fin 6) K))).map (graphParamHom K (RingEquiv.refl K)) := by
  obtain ⟨k, hk, rfl⟩ : ∃ k : Fin 5, (k = 0 ∨ k = 4) ∧ E6Pilot.chainNode k = j := by
    rcases hj with rfl | rfl
    exacts [⟨0, Or.inl rfl, rfl⟩, ⟨4, Or.inr rfl, rfl⟩]
  have hne : graphSwapPerm k.castSucc ≠ graphSwapPerm k.succ :=
    graphSwapPerm.injective.ne (Fin.castSucc_lt_succ (i := k)).ne
  have hw : ∀ a b : Kˣ, lin6Weights K (sp6ParamT3 K (a, b)) (graphSwapPerm k.castSucc) =
      lin6Weights K (sp6ParamT3 K (a, b)) (graphSwapPerm k.succ) := by
    intro a b
    rw [lin6Weights_sp6ParamT3]
    rcases hk with rfl | rfl <;> rfl
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
  refine sup_le ?_ ?_
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    refine ⟨Matrix.SpecialLinearGroup.transvection hne c,
      transvection_mem_centralizer_sp6Torus3 hne hw c, ?_⟩
    rw [graphParamHom_transvection, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      E6Pilot.a5Root_castSucc_succ]
    rfl
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    refine ⟨Matrix.SpecialLinearGroup.transvection hne.symm c,
      transvection_mem_centralizer_sp6Torus3 hne.symm (fun a b => (hw a b).symm) c, ?_⟩
    rw [graphParamHom_transvection, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      E6Pilot.a5Root_succ_castSucc]
    rfl

end Model

section PieceA


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem scLeviRestrict_end_mem_centralizer {e₁ : L ≃* adjointGroup .F4 K}
    {ΦA : e6ScLevi K e6A5Nodes →* G} (hrA : ΦA.range = neighbourCore e₁ .X)
    (hnA : IsLeviNormalizedA e₁ ΦA) {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5)
    (x : e6ScLevi K {j}) :
    scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) x ∈
      centralizer (leviTorusG e₁ {3} : Set G) := by
  set g := scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) x with hg
  have hgE : g ∈ neighbourCore e₁ .X := by
    rw [← hrA]
    exact ⟨_, rfl⟩
  obtain ⟨m, hm, hmx⟩ := e6ScLevi_end_le_map_centralizer hj x.2
  have hgm : g = ΦA (graphParamEquiv K (RingEquiv.refl K) m) := by
    rw [hg, scLeviRestrict_apply]
    congr 1
    exact Subtype.ext hmx.symm
  have hT : leviTorusG e₁ {3} ⊓ neighbourLeviG e₁ .X ≤ centralizer ({g} : Set G) := by
    rw [← map_levi6Hom_sp6Torus3 e₁ (RingEquiv.refl K)]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hnA s, hgm, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul]
    congr 2
    exact mem_centralizer_iff.1 hm _ ⟨s, hs, rfl⟩
  have hC : centralizer (neighbourCore e₁ .X : Set G) ≤ centralizer ({g} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hz g hgE).symm
  have hle : leviTorusG e₁ {3} ≤ centralizer ({g} : Set G) := by
    refine (le_sup_left (b := centralizer (neighbourCore e₁ .X : Set G))).trans ?_
    rw [leviTorusG_sup_centralizer_eq e₁ three_subset_X]
    exact sup_le hT hC
  rw [mem_centralizer_iff]
  intro z hz
  exact mem_centralizer_singleton_iff.1 (hle hz)

theorem range_scLeviRestrict_end_le_pieceCore (hq : 4 ≤ Nat.card K)
    {e₁ : L ≃* adjointGroup .F4 K} {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hrA : ΦA.range = neighbourCore e₁ .X) (hnA : IsLeviNormalizedA e₁ ΦA)
    {j : Fin (Tag.rank .E6)} (hj : j = 0 ∨ j = 5) :
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj)).range ≤ pieceCore e₁ {3} := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one_of_four_le (K := K) hq
  have hperf : Group.IsPerfect (e6ScLevi K {j}) :=
    Subgroup.isPerfect_iff.2 (commutator_e6ScLevi_singleton j ht)
  have hperf' := Subgroup.isPerfect_iff.1 (Group.IsPerfect.range
    (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj)))
  refine le_centralizerPerfectCore hperf' ?_
  rintro _ ⟨x, rfl⟩
  exact scLeviRestrict_end_mem_centralizer hrA hnA hj x

end PieceA

section Comm


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem comm_of_pieceComm {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* adjointGroup .F4 K} {N₁ N₂ : AmalgamNeighbour}
    (hN : (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X)) {e₁ e₂ : L ≃* adjointGroup .F4 K}
    (he₁ : IsNeighbourFrame e e₁ N₁) (he₂ : IsNeighbourFrame e e₂ N₂)
    {ΦA : e6ScLevi K e6A5Nodes →* G} (hrA : ΦA.range = neighbourCore e N₁)
    (hnA : IsLeviNormalizedA e₁ ΦA) {ε : K ≃+* K} {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e N₂) (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s)
    (h03 : ∀ g ∈ pieceCore e {0}, ∀ g' ∈ pieceCore e {3}, Commute g g') :
    ∀ j, (hj : j = 0 ∨ j = 5) → ∀ a b, Commute
      (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) one_subset_e6D4Nodes a)
      (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of hj) b) := by
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  intro j hj a b
  have hD := range_scLeviRestrict_one_le_pieceCore_of_frame hK hf hq he₂ hrY hn
  have hA := range_scLeviRestrict_end_le_pieceCore hq (hrA.trans (neighbourFrame_eq he₁).1) hnA hj
  rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h' : e₁ = e := he₁
    subst h'
    exact h03 _ (hD.2 rfl ⟨a, rfl⟩) _ (hA ⟨b, rfl⟩)
  · obtain ⟨hc, rfl⟩ := he₁
    rw [pieceCore_three_trans_graphAutF4_symm] at hA
    exact (h03 _ (hA ⟨b, rfl⟩) _ (hD.1 rfl ⟨a, rfl⟩)).symm

end Comm

end CFSG.SeitzReduction.F4Pilot
