module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectA
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactLie
public import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Disconnected

section Simple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {t : StatedLieTag}
  {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem Ih8Model.isSimpleGroup_of_g2d4 (hp2 : p ≠ 2) (ht : t = .G2 ∨ t = .trialityD4) :
    IsSimpleGroup G := by
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 ht k he M.ψ M.ker_le_center
  have : IsSimpleGroup (modelUniv t k p e Fact.out).K :=
    T3Typed.isSimpleGroup_model_of_g2d4 hp2 M.admissible ht
  exact MulEquiv.isSimpleGroup (MulEquiv.ofBijective M.ψ ⟨hinj, M.surj⟩).symm

end Simple

section Statements

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Thm6SectBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), TransSection p f Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ →
        DEdgeless Φ →
          HasLieType p f Φ .PSL 3 ∨ HasLieType p f Φ .PSU 3 ∨ HasLieType p f Φ .G2 0 ∨
            HasLieType p f Φ .trialityD4 0

@[expose] def Thm7SectBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), TransSection p f Φ →
        ∀ K ∈ Φ, (∃ K' ∈ twinSet Φ K, K' ≠ K) →
          ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ HasOrthType p f Φ d ε

@[expose] def Thm8SectBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), TransSection p f Φ → Φ.Nonempty → ¬ DEdgeless Φ →
        ¬ DConnected Φ → ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthType p f Φ d ε

end Statements

variable {p f : ℕ} [Fact p.Prime]

theorem top_notMem_of_transitive {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {K K' : Subgroup X} (hK : K ∈ Φ)
    (hK' : K' ∈ Φ) (hne : K' ≠ K) : (⊤ : Subgroup X) ∉ Φ := by
  intro htop
  have h1 : ∀ L ∈ Φ, L = ⊤ := by
    intro L hL
    obtain ⟨g, hg⟩ := htrans ⊤ htop L hL
    rw [← hg]
    exact conjSub_eq_self_of_mem (Subgroup.mem_top g)
  exact hne ((h1 K' hK').trans (h1 K hK).symm)

theorem thm6SectBelow_of (hP1 : Ih8SmallEdge p) {n : ℕ} (hn : CITBelowU p f n) :
    Thm6SectBelow p f n := by
  intro hp2 hq X _ _ hlt Φ hS hne htop hDE
  obtain ⟨t, k, e, M, hLie⟩ := hS.exists_datum hn hlt hne
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
  have hnpsl := M.not_psl_two_sect hp2 hne htop
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

theorem thm7SectBelow_of (hP4 : Ih8G2D4 p f) {n : ℕ} (hn : CITBelowU p f n) :
    Thm7SectBelow p f n := by
  intro hp2 hq X _ _ hlt Φ hS K hK hK'
  obtain ⟨K', hK', hne'⟩ := hK'
  have hΩ := hS.hyp
  obtain ⟨t, k, e, M, hLie⟩ := hS.exists_datum hn hlt ⟨K, hK⟩
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
    exact absurd ((hP4 hp2 hq X Φ hΩ hS.aEmpty hS.trans t k e ⟨M⟩ hG2d4).1 K hK K' hK') hne'
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have hne : Φ.Nonempty := ⟨K, hK⟩
  have htop := top_notMem_of_transitive hS.trans hK hK'.1 hne'
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  obtain ⟨R', hR', rfl⟩ := (M.mem_iff K').mp hK'Ω
  have hRR' : R ≠ R' := fun h => hne' (by rw [h])
  have hmtc := M.modelTwinClass_two_sect hΩ hp2 hq hne hnpsl hG2 hD4 hR hR' hRR' hzK hzK'
  have hef : e = f := M.exp_eq_f hD4
  have hmtc' : ModelTwinClass p t k f 2 := modelTwinClass_congr rfl rfl hef hmtc
  have hadm : StatedLieAdmissible t k p f := hef ▸ M.admissible
  obtain ⟨d, ε, hd, hdε⟩ := ih8_isOrth_of_twinShape
    (mfTwin hp2 hq t k 2 M.isFundTag hG2 hD4 hadm hnpsl le_rfl hmtc')
  exact ⟨d, ε, hd, t, k, hdε, hLie⟩

theorem thm8SectBelow_of (hP4 : Ih8G2D4 p f) {n : ℕ} (hn : CITBelowU p f n) :
    Thm8SectBelow p f n := by
  intro hp2 hq X _ _ hlt Φ hS hne hNE hNC
  have hΩ := hS.hyp
  obtain ⟨t, k, e, M, hLie⟩ := hS.exists_datum hn hlt hne
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · exfalso
    have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
    rcases (hP4 hp2 hq X Φ hΩ hS.aEmpty hS.trans t k e ⟨M⟩ hG2d4).2 with h | h
    · exact hNE h
    · exact hNC h
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have htop : (⊤ : Subgroup X) ∉ Φ := by
    by_contra htop
    apply hNE
    intro K hK J hJ hadj
    have h1 : ∀ L ∈ Φ, L = ⊤ := by
      intro L hL
      obtain ⟨g, hg⟩ := hS.trans ⊤ htop L hL
      rw [← hg]
      exact conjSub_eq_self_of_mem (Subgroup.mem_top g)
    exact ne_of_dAdj hadj ((h1 K hK).trans (h1 J hJ).symm)
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  have hedgeless : ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → DEdgeless Φ := by
    intro h3 K hK J hJ hadj
    rcases hadj with h | h
    · exact M.not_omegaNbr_of_three_sect hΩ hp2 hq h3 hK h
    · exact M.not_omegaNbr_of_three_sect hΩ hp2 hq h3 hJ h
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
