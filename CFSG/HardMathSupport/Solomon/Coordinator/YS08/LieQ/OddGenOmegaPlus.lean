module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusIndexPoints
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusIndex
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.ClassicalGroups.Orthogonal

section PlusFlag

variable {n : ℕ} {K : Type} [Field K]

@[expose] def splitVec (n : ℕ) (K : Type) [Field K] (j : Fin n) : Fin n ⊕ Fin n → K :=
  Pi.single (Sum.inl j) 1

theorem splitVec_ne_zero (j : Fin n) : (splitVec n K j) ≠ 0 := fun h => by
  have := congrFun h (Sum.inl j)
  simp [splitVec] at this

theorem flag_one (h : 0 < n) :
    flag n K 1 = Submodule.span K {splitVec n K ⟨0, h⟩} := by
  unfold flag
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have : j = ⟨0, h⟩ := Fin.ext (show (j : ℕ) = 0 by omega)
    rw [this]
    rfl
  · rintro rfl
    exact ⟨⟨0, h⟩, by simp, rfl⟩

theorem flag_two (h : 1 < n) :
    flag n K 2 = Submodule.span K {splitVec n K ⟨0, by omega⟩} ⊔
      Submodule.span K {splitVec n K ⟨1, h⟩} := by
  unfold flag
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases hj0 : (j : ℕ) = 0
    · left
      have : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [this]
      rfl
    · right
      have : j = ⟨1, h⟩ := Fin.ext (show (j : ℕ) = 1 by omega)
      rw [this]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by omega⟩, by simp, rfl⟩
    · exact ⟨⟨1, h⟩, by simp, rfl⟩

theorem splitVec_one_notMem (h : 1 < n) :
    splitVec n K ⟨1, h⟩ ∉ Submodule.span K {splitVec n K ⟨0, by omega⟩} := by
  intro hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have := congrFun ha (Sum.inl ⟨1, h⟩)
  simp [splitVec, Pi.single_apply] at this

end PlusFlag

section Plus

variable {q : ℕ} [Fact q.Prime]

theorem twoParabolics_POmegaPlus {n f : ℕ} {S : Type} [Group S] [Finite S]
    (hm : StatedClassicalModel S .POmegaPlus n q f) : TwoParabolics q S := by
  obtain ⟨hq, -, hn4⟩ := hm.1
  have hn4' : 4 ≤ n := hn4
  have hm' := hm
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := hm'
  haveI : CharP K q := charP_of_natCard_eq hcard
  have hn3 : 3 ≤ n := by omega
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hcmp := orthogonal_geometry_plus_model_geometric_index_comparison (K := K) hm hcard
  set Φ := quadPlusForm n K with hΦ
  have hι : 6 ≤ Fintype.card (Fin n ⊕ Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  set x₁ : Fin n ⊕ Fin n → K := splitVec n K ⟨0, h0⟩ with hx₁
  set x₂ : Fin n ⊕ Fin n → K := splitVec n K ⟨1, h1⟩ with hx₂
  have hsing : ∀ i, ∀ v ∈ flag n K i, Φ.Q v = 0 := fun i v hv => by
    have := flag_singular (r := n) (K := K) i v hv
    rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at this
  have hQ₁ : Φ.Q x₁ = 0 := hsing 1 x₁ (by
    rw [flag_one h0]; exact Submodule.mem_span_singleton_self x₁)
  have hQ₂ : Φ.Q x₂ = 0 := hsing 2 x₂ (by
    rw [flag_two h1]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₂))
  have hQ₁₂ : Φ.Q (x₁ + x₂) = 0 := hsing 2 _ (by
    rw [flag_two h1]
    exact add_mem (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x₁))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₂)))
  have h12 : Φ.polar.β x₁ x₂ = 0 := by
    have := Φ.Q_add x₁ x₂
    rw [hQ₁₂, hQ₁, hQ₂] at this
    linear_combination -this
  have hind : x₂ ∉ Submodule.span K {x₁} := splitVec_one_notMem h1
  have hx₁0 : x₁ ≠ 0 := splitVec_ne_zero _
  obtain ⟨U, hU⟩ := plusProjectiveUnipotent_isSylow n K q hn3
  have hN : Subgroup.normalizer (plusProjectiveUnipotent n K :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) = plusProjectiveBorel n K :=
    plusProjectiveUnipotent_normalizer n K hn3
  have hUB : (U : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) ≤
      plusProjectiveBorel n K := by
    rw [← hN, ← hU]
    exact Subgroup.le_normalizer
  have hflag : ∀ i : Fin (n - 1), plusProjectiveBorel n K ≤
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K (i + 1)) :=
    fun i => iInf_le (fun i => statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
      (stdFlag n K i)) i
  have hB₁ : plusProjectiveBorel n K ≤
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K 1) :=
    hflag ⟨0, by omega⟩
  have hB₂ : plusProjectiveBorel n K ≤
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K 2) :=
    hflag ⟨1, by omega⟩
  have hc : IsCoatom (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K 1)) := by
    refine isCoatom_of_overgroups hB₁ ?_ ?_
    · rw [flag_one h0]
      exact stabilizer_line_ne_top Φ hι hx₁0 hQ₂ h12 hind
    · intro M hM hBM hPM
      have hL1 : Module.finrank K (flag n K 1) = 1 := finrank_flag_of_le (by omega)
      have hLs : ∀ v ∈ flag n K 1, StatedQuadPlus n K v = 0 := fun v hv => by
        have := flag_singular (r := n) (K := K) 1 v hv
        rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at this
      rcases orthogonal_geometry_plus_model_maximal_Borel_overgroups hm M hM hBM with
        ⟨i, hi1, hi2, rfl⟩ | rfl | rfl
      · by_cases hi : i = 1
        · rw [hi]
        · exfalso
          have hWs : ∀ v ∈ flag n K i, StatedQuadPlus n K v = 0 := fun v hv => by
            have := flag_singular (r := n) (K := K) i v hv
            rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at this
          have hW2 : Module.finrank K (flag n K i) = i := finrank_flag_of_le (by omega)
          have hlt : (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K 1)).index <
              (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K i)).index := by
            by_cases h5 : 5 ≤ n
            · exact hcmp.2.1 h5 _ _ hL1 hLs hWs (by omega)
            · have h4 : n = 4 := by omega
              subst h4
              exact (hcmp.2.2 rfl _ _ hL1 hLs hWs).2 (by omega)
          have hle := index_le_of_le hPM
          omega
      · by_cases h5 : 5 ≤ n
        · exfalso
          obtain ⟨hdim, hsX⟩ := Xstar_mem_singularSubspaces (r := n) (K := K) h0
          have hlt := hcmp.2.1 h5 _ _ hL1 hLs (fun v hv => by
            have := hsX v hv
            rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at this) (by rw [hdim]; omega)
          have hle := index_le_of_le hPM
          omega
        · have h4 : n = 4 := by omega
          subst h4
          obtain ⟨hdim, hsX⟩ := Xstar_mem_singularSubspaces (r := 4) (K := K) h0
          have hidx := (hcmp.2.2 rfl _ _ hL1 hLs (fun v hv => by
            have := hsX v hv
            rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at this)).1 hdim
          exact (eq_of_le_of_index_eq hPM hidx).symm
      · by_cases h5 : 5 ≤ n
        · exfalso
          obtain ⟨hdim, hsX⟩ := flag_mem_singularSubspaces (r := n) (K := K) le_rfl
          have hlt := hcmp.2.1 h5 _ _ hL1 hLs (fun v hv => by
            have := hsX v hv
            rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at this) (by rw [hdim]; omega)
          have hle := index_le_of_le hPM
          omega
        · have h4 : n = 4 := by omega
          subst h4
          obtain ⟨hdim, hsX⟩ := flag_mem_singularSubspaces (r := 4) (K := K) le_rfl
          have hidx := (hcmp.2.2 rfl _ _ hL1 hLs (fun v hv => by
            have := hsX v hv
            rwa [CFSG.LieType.Universal.Spin.coe_quadPlus] at this)).1 hdim
          exact (eq_of_le_of_index_eq hPM hidx).symm
  have hU₁ := hUB.trans hB₁
  have hU₂ := hUB.trans hB₂
  rw [flag_one h0] at hc hU₁
  rw [flag_two h1] at hU₂
  have key := twoParabolics_Omega Φ hι hx₁0 hQ₁ hQ₂ h12 hind U hc hU₁ hU₂
  exact key.of_mulEquiv e.symm

end Plus

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
