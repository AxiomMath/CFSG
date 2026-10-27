module

public import CFSG.Quasithin.Vol2.Ch5Sec3Lemmas
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def Stmt5_3_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      (quasithinIsLocal T L ∧ quasithinIsLocal T (oTwoUpper H) ∧
        IsUniqueM (L ⊔ T) (sec53M1 L) ∧ IsUniqueM (oTwoUpper H ⊔ T) (sec53M2 H) ∧
        sec53M1 L ≠ sec53M2 H) ∧
      (CharTwo (sec53M1 L) ∧ pCoreOf 2 (sec53M1 L) = pCoreOf 2 L ∧
        CharTwo (sec53M2 H) ∧ pCoreOf 2 (sec53M2 H) = pCoreOf 2 (oTwoUpper H)) ∧
      (Subgroup.normalizer (sec53S T L : Set G) = sec53M12 L H ∧
        sec53M1 L ⊓ Subgroup.normalizer (sec53S T L : Set G) = sec53M12 L H ∧
        sec53M2 H ⊓ Subgroup.normalizer (sec53S T L : Set G) = sec53M12 L H) ∧
      (L ⊔ sec53M12 L H = sec53M1 L ∧ oTwoUpper H ⊔ sec53M12 L H = sec53M2 H)

@[expose] def Stmt5_3_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      ∃ (Y : Type) (_ : Group Y), LieModel Y t m 2 f ∧
        IsExtensionOfLieAmalgam Y (sec53M1 L) (sec53M2 H)

@[expose] def Stmt5_3_3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      F431Hyps (sec53M1 L) (sec53M2 H) t m f ∨
      (t = .PSL ∧ m = 3 ∧ ∀ z ∈ sec53ZS T L, orderOf z = 2 →
        ¬ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H)

@[expose] def Stmt5_3_3_facts_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      (perfectCore (sec53M1 L) = L ∧ perfectCore (sec53M2 H) = oTwoUpper H ∧
        pCoreOf 2 (sec53M12 L H) = sec53S T L) ∧
      (∀ z ∈ centerOf L, z ≠ 1 → ∀ z' ∈ centerOf L, z' ≠ 1 → ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') ∧
      (∀ z ∈ centerOf (oTwoUpper H), z ≠ 1 → ∀ z' ∈ centerOf (oTwoUpper H), z' ≠ 1 →
        ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') ∧
      (t = .PSp → ∀ u ∈ sec53ZS T L, orderOf u = 2 → ∃ g ∈ B ⊔ D, g * u * g⁻¹ ∈ centerOf T)

theorem stmt5_3_4_of_F4 (h533 : Stmt5_3_3_F4) (h431 : F431Rank2) : Stmt5_3_4_F4 := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  rcases h533 G T M L V H B D L₂ n t m f hyp hty hpar with h | h
  · exact Or.inl (h431 G hyp.simple hyp.nonabelian _ _ t m f hpar h)
  · exact Or.inr h

theorem stmt5_3_3_of_F4 (h531 : Stmt5_3_1_F4) (h532 : Stmt5_3_2_F4) (hfacts : Stmt5_3_3_facts_F4) :
    Stmt5_3_3_F4 := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  obtain ⟨⟨-, -, hU1, hU2, -⟩, -, -, -⟩ := h531 G T M L V H B D L₂ n t m f hyp hty hpar
  have hext := h532 G T M L V H B D L₂ n t m f hyp hty hpar
  obtain ⟨⟨hpc1, hpc2, hO12⟩, htr1, htr2, hfus⟩ :=
    hfacts G T M L V H B D L₂ n t m f hyp hty hpar

  have hT1 : T ≤ sec53M1 L := hyp.T_le.trans hyp.normal
  have hT2 : T ≤ sec53M2 H := hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hB1 : B ≤ sec53M1 L := hyp.notation59.1.1.trans (inf_le_left.trans hyp.normal)
  have hB2 : B ≤ sec53M2 H :=
    hyp.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hD1 : D ≤ sec53M1 L :=
    hyp.notation59.2.1.1.trans (inf_le_left.trans Subgroup.le_normalizer)
  have hBD1 : B ⊔ D ≤ sec53M1 L := sup_le hB1 hD1
  have hBD2 : B ⊔ D ≤ sec53M2 H := sup_le hB2 hyp.D_le
  have hZS : centerOf (pCoreOf 2 (sec53M1 L ⊓ sec53M2 H)) = sec53ZS T L := by
    rw [show sec53M1 L ⊓ sec53M2 H = sec53M12 L H from rfl, hO12]
  have ha : (t = .PSp ∨ t = .PSU) →
      Subgroup.normalizer (centerOf (pCoreOf 2 (sec53M1 L)) : Set G) = sec53M1 L ∧
        Subgroup.normalizer (centerOf (pCoreOf 2 (sec53M2 H)) : Set G) = sec53M2 H :=
    fun _ => ⟨normalizer_centerOf_pCoreOf_eq hU1, normalizer_centerOf_pCoreOf_eq hU2⟩
  have hb : ¬ (t = .PSL ∧ m = 3) →
      (∀ z ∈ centerOf (perfectCore (sec53M1 L)), orderOf z = 2 →
        Subgroup.centralizer ({z} : Set G) ≤ sec53M1 L) ∧
      ∀ z ∈ centerOf (perfectCore (sec53M2 H)), orderOf z = 2 →
        Subgroup.centralizer ({z} : Set G) ≤ sec53M2 H := by
    intro _
    refine ⟨fun z hz hz2 => ?_, fun z hz hz2 => ?_⟩
    · rw [hpc1] at hz
      exact centralizer_le_of_transitive hyp.sylow hU1 hT1 hBD1 htr1 hz hz2
    · rw [hpc2] at hz
      exact centralizer_le_of_transitive hyp.sylow hU2 hT2 hBD2 htr2 hz hz2
  have hcd : t = .PSp → (∀ u ∈ centerOf (pCoreOf 2 (sec53M1 L ⊓ sec53M2 H)), orderOf u = 2 →
      CharTwo (Subgroup.centralizer ({u} : Set G))) ∧ ¬ 2 ∣ (sec53M1 L ⊓ sec53M2 H).index := by
    intro htp
    refine ⟨fun u hu hu2 => ?_, fun h2 => hyp.sylow.2 (h2.trans
      (Subgroup.index_dvd_of_le (le_inf hT1 hT2)))⟩
    rw [hZS] at hu
    obtain ⟨g, -, hg⟩ := hfus htp u hu hu2
    exact charTwo_centralizer_of_conj_mem hyp.qtke hyp.sylow hu2 hg
  by_cases hL3 : t = .PSL ∧ m = 3
  · by_cases hz : ∃ z ∈ sec53ZS T L, orderOf z = 2 ∧
        Subgroup.centralizer ({z} : Set G) ≤ sec53M1 L
    · refine Or.inl ⟨hext, ha, fun _ => ?_, hb, hcd⟩
      rw [hZS]
      exact hz
    · exact Or.inr ⟨hL3.1, hL3.2, fun z hzS hz2 hle =>
        hz ⟨z, hzS, hz2, hle.trans inf_le_left⟩⟩
  · exact Or.inl ⟨hext, ha, fun h => absurd h hL3, hb, hcd⟩

end CFSG.Quasithin.H13
