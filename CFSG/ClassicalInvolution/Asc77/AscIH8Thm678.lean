module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Inv
public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph
public import CFSG.ClassicalInvolution.Asc77.WP2Interface

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic

variable {p f : ℕ} [Fact p.Prime]

theorem ih8_exists_datum {n : ℕ} (hn : CITBelowU p f n) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hlt : Nat.card G < n) {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω)
    (hne : Ω.Nonempty) :
    ∃ (t : StatedLieTag) (k e : ℕ) (_ : Ih8Model p f Ω t k e), HasLieType p f Ω t k := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  have hO := ih8_oddCore_eq_bot_of_simple hz.orderOf_eq_two
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΩ.conjInvariant hΩ.classical ⟨K, hK⟩ hO hlt
  have hcard := D.card_eq_one_of_simple hΩ.conjInvariant hΩ.classical ⟨K, hK⟩
  let i : Fin D.card := ⟨0, by omega⟩
  exact ⟨D.tag i, D.rank i, D.exp i,
    D.toIh8Model hcard i hΩ.conjInvariant hΩ.classical ⟨K, hK⟩, D, hcard, i, rfl, rfl⟩

@[expose] def Ih8SmallEdge (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k p e → p ≠ 2 → 5 ≤ p ^ e →
    ((t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨ (t = .PSp ∧ k = 2) ∨ (t = .POmegaOdd ∧ k = 3) ∨
      (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) →
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, R ≠ S ∧ Commutes R S

@[expose] def Ih8G2D4 (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
      HypOmegaMod p f Ω → (∀ J ∈ Ω, AEmpty Ω J) →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ (t : StatedLieTag) (k e : ℕ), Nonempty (Ih8Model p f Ω t k e) →
            (t = .G2 ∨ t = .trialityD4) →
              (∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) ∧
                (Disconnected.DEdgeless Ω ∨ Disconnected.DConnected Ω)

theorem thm6TypedBelow_of (hP1 : Ih8SmallEdge p) {n : ℕ} (hn : CITBelowU p f n) :
    Thm6TypedBelow p f n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ _ hne _ hDE
  obtain ⟨t, k, e, M, hLie⟩ := ih8_exists_datum hn hlt hΩ hne
  by_cases hG2 : t = .G2
  · subst hG2
    obtain ⟨hk, -⟩ := M.admissible.2.2
    subst hk
    exact Or.inr (Or.inr (Or.inl hLie))
  by_cases hD4 : t = .trialityD4
  · subst hD4
    have hk : k = 0 := M.admissible.2.2
    subst hk
    exact Or.inr (Or.inr (Or.inr hLie))
  have hnpsl := M.not_psl_two hp2 hΩ.classical hne
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  have hedge : (∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, R ≠ S ∧ Commutes R S) →
      False := by
    rintro ⟨R, hR, S, hS, hRS, hc⟩
    exact M.not_dEdgeless_of_commutes hp2 hD4 hq (M.fund_subset_cls hne hG2 hD4 hR)
      (M.fund_subset_cls hne hG2 hD4 hS) hRS hc hDE
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4 with hconn | hsmall
  · obtain ⟨R, hR⟩ := M.cls_nonempty hne
    obtain ⟨S, hS, hSR, hc⟩ := ih8_exists_edge_of_connected hp2 hq' M.isFundTag M.admissible hnpsl
      hconn (M.cls_sub hR)
    exact (hedge ⟨R, M.cls_sub hR, S, hS, hSR.symm, hc⟩).elim
  · rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hk2 : 2 ≤ k := M.admissible.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact (hnpsl ⟨rfl, rfl⟩).elim
      · exact Or.inl hLie
      · exact (hedge (hP1 _ _ _ M.admissible hp2 hq' (Or.inl ⟨rfl, rfl⟩))).elim
    · have hk3 : 3 ≤ k := M.admissible.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact Or.inr (Or.inl hLie)
      · exact (hedge (hP1 _ _ _ M.admissible hp2 hq' (Or.inr (Or.inl ⟨rfl, rfl⟩)))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))).elim

theorem ih8_isOrth_of_twinShape {t : StatedLieTag} {k : ℕ}
    (h : ShapeTable 2 t k ∨ (t = .POmegaPlus ∧ k = 4 ∧ 2 ≤ 4)) :
    ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ IsOrthTag d ε t k := by
  rcases h with h | ⟨rfl, rfl, -⟩
  · simp only [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2, ShapeTwinTD,
      ShapeTwinSU4] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, hk⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hk⟩ | ⟨-, rfl, rfl⟩ |
      ⟨-, rfl, hk⟩ | ⟨-, rfl, rfl⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact ⟨2 * k, true, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, rfl, rfl, rfl⟩))))⟩
    · exact ⟨6, true, by norm_num, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
    · exact ⟨2 * k + 1, true, by omega, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, rfl, rfl⟩)))⟩
    · exact ⟨5, true, by norm_num, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨2 * k, false, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by omega, by omega, rfl, rfl, rfl⟩))))⟩
    · exact ⟨6, false, by norm_num, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))⟩
  · exact ⟨8, true, by norm_num, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by norm_num, by norm_num, rfl, rfl, rfl⟩))))⟩

theorem thm7TypedBelow_of (hP4 : Ih8G2D4 p f) {n : ℕ} (hn : CITBelowU p f n) :
    Thm7TypedBelow p f n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ hA htrans K hK hK'
  obtain ⟨K', hK', hne'⟩ := hK'
  obtain ⟨t, k, e, M, hLie⟩ := ih8_exists_datum hn hlt hΩ ⟨K, hK⟩
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · exact absurd ((hP4 hp2 hq G Ω hΩ hA htrans t k e ⟨M⟩ hG2d4).1 K hK K' hK') hne'
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have hne : Ω.Nonempty := ⟨K, hK⟩
  have hnpsl := M.not_psl_two hp2 hΩ.classical hne
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  obtain ⟨R', hR', rfl⟩ := (M.mem_iff K').mp hK'Ω
  have hRR' : R ≠ R' := fun h => hne' (by rw [h])
  have hmtc := M.modelTwinClass_two hΩ hp2 hq hne hG2 hD4 hR hR' hRR' hzK hzK'
  have hef : e = f := M.exp_eq_f hD4
  have hmtc' : ModelTwinClass p t k f 2 := modelTwinClass_congr rfl rfl hef hmtc
  have hadm : StatedLieAdmissible t k p f := hef ▸ M.admissible
  obtain ⟨d, ε, hd, hdε⟩ := ih8_isOrth_of_twinShape
    (mfTwin hp2 hq t k 2 M.isFundTag hG2 hD4 hadm hnpsl le_rfl hmtc')
  exact ⟨d, ε, hd, t, k, hdε, hLie⟩

theorem thm8TypedBelow_of (hP4 : Ih8G2D4 p f) {n : ℕ} (hn : CITBelowU p f n) :
    Thm8TypedBelow p f n := by
  intro hp2 hq G _ _ _ hlt Ω hΩ hA hne htrans hNE hNC
  obtain ⟨t, k, e, M, hLie⟩ := ih8_exists_datum hn hlt hΩ hne
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · exfalso
    rcases (hP4 hp2 hq G Ω hΩ hA htrans t k e ⟨M⟩ hG2d4).2 with h | h
    · exact hNE h
    · exact hNC h
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have hnpsl := M.not_psl_two hp2 hΩ.classical hne
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  have hedgeless : ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → Disconnected.DEdgeless Ω := by
    intro h3 K hK J hJ hadj
    rcases hadj with h | h
    · exact M.not_omegaNbr_of_three hΩ hp2 hq h3 hK h
    · exact M.not_omegaNbr_of_three hΩ hp2 hq h3 hJ h
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4 with hconn | hsmall
  · exact (hNC (M.dConnected_of_connected hp2 hq hne hG2 hD4 hconn)).elim
  · rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hk2 : 2 ≤ k := M.admissible.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact (hnpsl ⟨rfl, rfl⟩).elim
      · exact (hNE (hedgeless (Or.inl ⟨rfl, rfl⟩))).elim
      · exact ⟨6, true, by norm_num, by norm_num, .PSL, 4,
          Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩), hLie⟩
    · have hk3 : 3 ≤ k := M.admissible.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact (hNE (hedgeless (Or.inr ⟨rfl, rfl⟩))).elim
      · exact ⟨6, false, by norm_num, by norm_num, .PSU, 4,
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)), hLie⟩
    · exact ⟨5, true, by norm_num, by norm_num, .PSp, 2, Or.inl ⟨rfl, rfl, rfl⟩, hLie⟩
    · exact ⟨7, true, by norm_num, by norm_num, .POmegaOdd, 3,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, rfl, rfl⟩))), hLie⟩
    · exact ⟨8, true, by norm_num, by norm_num, .POmegaPlus, 4,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, rfl, rfl, rfl⟩)))),
        hLie⟩
    · exact ⟨8, false, by norm_num, by norm_num, .POmegaMinus, 4,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by norm_num, by norm_num, rfl, rfl, rfl⟩)))),
        hLie⟩

end CFSG.ClassicalInvolution.Asc77
