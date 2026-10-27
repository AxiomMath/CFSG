module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesCheck
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Two
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerTwo
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneAnnihilator

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] noncomputable def twistedE6OrbitClosure
    (σ : K →+* K) (D : List (Fin TwistTag.E6.tag.rank → ℤ)) :
    Subgroup (graphFixedRootGroup TwistTag.E6 K σ) :=
  Subgroup.closure {c | ∃ γ ∈ D, (c : ModGL TwistTag.E6.tag K) ∈
    rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit γ : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σ}

theorem twistedE6ClassCommB_sound {x y : Fin TwistTag.E6.tag.rank → ℤ}
    (h : twistedE6ClassCommB x y = true) :
    ¬IsRoot TwistTag.E6.tag (x + y) ∧ x + y ≠ 0 := by
  simp only [twistedE6ClassCommB, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun hr => ?_, fun e => ?_⟩
  · rw [isRoot_iff_twistedE6TwoRootB, h.1] at hr
    exact absurd hr (by decide)
  · have := h.2
    rw [e, show twistedE6TwoVecB (0 : Fin TwistTag.E6.tag.rank → ℤ) 0 = true from
      twistedE6TwoVecB_iff.2 rfl] at this
    exact absurd this (by decide)

theorem twistedE6ClassFixedB_iff {x : Fin TwistTag.E6.tag.rank → ℤ} :
    twistedE6ClassFixedB x = true ↔ permLattice TwistTag.E6.perm x = x :=
  twistedE6TwoVecB_iff

theorem not_isRoot_of_twistedE6TwoRootB
    {v : Fin TwistTag.E6.tag.rank → ℤ} (h : twistedE6TwoRootB v = false) :
    ¬IsRoot TwistTag.E6.tag v := by
  rw [isRoot_iff_twistedE6TwoRootB, h]
  decide

theorem ne_of_twistedE6TwoVecB {u v : Fin TwistTag.E6.tag.rank → ℤ}
    (h : twistedE6TwoVecB u v = false) : u ≠ v := fun e => by
  rw [e, twistedE6TwoVecB_iff.2 rfl] at h
  exact absurd h (by decide)

theorem twistedE6ClassTableOK_targets
    {R Dl : List (Fin TwistTag.E6.tag.rank → ℤ)} :
    ∀ (T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
        (Fin TwistTag.E6.tag.rank → ℤ))) (done : List (Fin TwistTag.E6.tag.rank → ℤ)),
      twistedE6ClassTableOK R Dl done T = true →
        ∀ e ∈ T, IsRoot TwistTag.E6.tag (e.2.1 + e.2.2) ∧ 0 < height (e.2.1 + e.2.2) := by
  intro T
  induction T with
  | nil => intro _ _ e he; exact absurd he List.not_mem_nil
  | cons e es ih =>
    intro done h e' he'
    simp only [twistedE6ClassTableOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · have h1 := h.1
      simp only [twistedE6ClassEntryOK, Bool.and_eq_true, decide_eq_true_eq] at h1
      exact ⟨isRoot_iff_twistedE6TwoRootB.2 h1.1.1.1.1.1.1.1.2, h1.1.1.1.1.1.1.2⟩
    · exact ih _ h.2 e' he'

theorem twistedE6ClassCheck_sound
    {R : List (Fin TwistTag.E6.tag.rank → ℤ)} {h : ℤ}
    {T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))} {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hchk : twistedE6ClassCheck R h T L = true) :
    (∀ ε ∈ R, IsRoot TwistTag.E6.tag ε) ∧
    twistedE6ClassTableOK R (twistedE6ClassTargets T) [] T = true ∧
    (∀ x ∈ twistedE6ClassTargets T, IsRoot TwistTag.E6.tag x ∧ 0 < height x) ∧
    (∀ x ∈ twistedE6ClassTargets T, twistedE6ClassCentralB x R = true ∧
      twistedE6ClassCentralB (permLattice TwistTag.E6.perm x) R = true ∧
      permLattice TwistTag.E6.perm x ∈ twistedE6ClassTargets T) ∧
    (∀ α, IsRoot TwistTag.E6.tag α → 0 < height α → h ≤ height α →
      α ∈ twistedE6ClassTargets T) ∧
    (∀ α, IsRoot TwistTag.E6.tag α → 0 < height α → α ∉ L →
      ∃ δ ∈ twistedE6ClassTargets T, IsRoot TwistTag.E6.tag (α + δ)) ∧
    (∀ γ ∈ L, IsRoot TwistTag.E6.tag γ ∧ 0 < height γ ∧
      ∀ δ ∈ twistedE6ClassTargets T, ¬IsRoot TwistTag.E6.tag (γ + δ)) ∧
    (∀ γ ∈ L, ∀ γ' ∈ L, ¬IsRoot TwistTag.E6.tag (γ + γ')) := by
  simp only [twistedE6ClassCheck, Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨hR, hT⟩, hD⟩, hcov⟩, hL⟩, hLL⟩ := hchk
  have hTt := twistedE6ClassTableOK_targets T [] hT
  refine ⟨fun ε hε => isRoot_iff_twistedE6TwoRootB.2 (hR ε hε), hT, fun x hx => ?_,
    fun x hx => ?_, fun α hα hαp hαh => ?_, fun α hα hαp hαL => ?_, fun γ hγ => ?_,
    fun γ hγ γ' hγ' => ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact hTt e he
  · have := hD x hx
    simp only [twistedE6ClassMemB_iff] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · obtain ⟨k, hk, rfl⟩ :=
      RootCertificate.exists_root_eq (Tag.rootCertificate_check TwistTag.E6.tag) hα
    have := hcov k (List.mem_range.2 hk)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      twistedE6ClassMemB_iff] at this
    rcases this with h1 | ⟨h1 | h1, -⟩
    · exact absurd h1 (not_le.2 hαp)
    · exact absurd h1 (not_lt.2 hαh)
    · exact h1
  · obtain ⟨k, hk, rfl⟩ :=
      RootCertificate.exists_root_eq (Tag.rootCertificate_check TwistTag.E6.tag) hα
    have := hcov k (List.mem_range.2 hk)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      twistedE6ClassMemB_iff, List.any_eq_true] at this
    rcases this with h1 | ⟨-, h1 | ⟨δ, hδ, h2⟩⟩
    · exact absurd h1 (not_le.2 hαp)
    · exact absurd h1 hαL
    · exact ⟨δ, hδ, isRoot_iff_twistedE6TwoRootB.2 h2⟩
  · have := hL γ hγ
    simp only [decide_eq_true_eq, Bool.not_eq_true'] at this
    exact ⟨isRoot_iff_twistedE6TwoRootB.2 this.1.1, this.1.2,
      fun δ hδ => not_isRoot_of_twistedE6TwoRootB (this.2 δ hδ)⟩
  · have := hLL γ hγ γ' hγ'
    simp only [Bool.not_eq_true'] at this
    exact not_isRoot_of_twistedE6TwoRootB this


theorem commute_pinnedX_list_prod_of_centralB {R : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : ∀ ε ∈ R, IsRoot TwistTag.E6.tag ε) {x : Fin TwistTag.E6.tag.rank → ℤ}
    (hx : IsRoot TwistTag.E6.tag x) (hc : twistedE6ClassCentralB x R = true) (d : K) :
    Commute (pinnedX TwistTag.E6.tag K x d)
      (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod := by
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨ε, hε, rfl⟩ := List.mem_map.1 hy
  simp only [twistedE6ClassCentralB, List.all_eq_true] at hc
  obtain ⟨h1, h2⟩ := twistedE6ClassCommB_sound (hc ε hε)
  exact commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hx (hR ε hε) h1 h2 d 1

theorem pinnedX_mem_orbitGroup_of_fixed [CharP K 2] (σ : K →+* K)
    {x : Fin TwistTag.E6.tag.rank → ℤ} (hx : IsRoot TwistTag.E6.tag x)
    (hρ : permLattice TwistTag.E6.perm x = x) {c : K} (hc : σ c = c) :
    pinnedX TwistTag.E6.tag K x c ∈
      rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit x : Set _) ⊓
        twistedFixedGroup TwistTag.E6 K σ :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_iSup_of_mem x (Subgroup.mem_iSup_of_mem
    (Finset.mem_coe.2 (TwistTag.E6.self_mem_diagramOrbit x)) (mem_rootSubgroup.2 ⟨c, rfl⟩)),
    graphFixedRootGroup_le _ _ _ (pinnedX_mem_graphFixedRootGroup_of_fixed σ hx hρ hc)⟩

theorem twistedE6PairX_mem_orbitGroup [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {x : Fin TwistTag.E6.tag.rank → ℤ} (hx : IsRoot TwistTag.E6.tag x) (s : K) :
    twistedE6PairX σ x s ∈ rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit x : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σ :=
  Subgroup.mem_inf.2 ⟨mul_mem (Subgroup.mem_iSup_of_mem x (Subgroup.mem_iSup_of_mem
    (Finset.mem_coe.2 (TwistTag.E6.self_mem_diagramOrbit x)) (mem_rootSubgroup.2 ⟨s, rfl⟩)))
    (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem (Finset.mem_coe.2
      (TwistTag.E6.permLattice_mem_diagramOrbit (TwistTag.E6.self_mem_diagramOrbit x)))
      (mem_rootSubgroup.2 ⟨σ s, rfl⟩))), twistedE6PairX_mem_twistedFixedGroup hσσ hx s⟩

theorem coe_commutatorElement_twistedE6Classes {σ : K →+* K}
    (a b : graphFixedRootGroup TwistTag.E6 K σ) :
    ((⁅a, b⁆ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
      ⁅(a : ModGL TwistTag.E6.tag K), (b : ModGL TwistTag.E6.tag K)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

theorem commutatorElement_mem_commutator_of_or {G : Type*} [Group G] {A P : Subgroup G}
    {a b : G} (h : (a ∈ A ∧ b ∈ P) ∨ (a ∈ P ∧ b ∈ A)) : ⁅a, b⁆ ∈ ⁅A, P⁆ := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Subgroup.commutator_mem_commutator ha hb
  · rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator ha hb

theorem twistedE6ClassEntry_sound [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {t₀ : K} (ht₀ : t₀ + σ t₀ = 1) {R Dl done : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : ∀ ε ∈ R, IsRoot TwistTag.E6.tag ε) {t : graphFixedRootGroup TwistTag.E6 K σ}
    (ht : (t : ModGL TwistTag.E6.tag K) = (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod)
    (hdone : ∀ γ ∈ done, ∀ c : graphFixedRootGroup TwistTag.E6 K σ,
      (c : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K
          (TwistTag.E6.diagramOrbit γ : Set _) ⊓ twistedFixedGroup TwistTag.E6 K σ →
        c ∈ ⁅twistedE6OrbitClosure σ Dl, Subgroup.centralizer {t}⁆)
    {e : TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) × (Fin TwistTag.E6.tag.rank → ℤ)}
    (he : twistedE6ClassEntryOK R Dl done e = true) :
    ∀ c : graphFixedRootGroup TwistTag.E6 K σ,
      (c : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K
          (TwistTag.E6.diagramOrbit (e.2.1 + e.2.2) : Set _) ⊓ twistedFixedGroup TwistTag.E6 K σ →
        c ∈ ⁅twistedE6OrbitClosure σ Dl, Subgroup.centralizer {t}⁆ := by
  obtain ⟨k, x, y⟩ := e
  simp only [twistedE6ClassEntryOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    twistedE6ClassMemB_iff] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hy⟩, hg⟩, hgp⟩, hD⟩, hcx⟩, hcρx⟩, hcy⟩, hcρy⟩, hk⟩ := he
  rw [← isRoot_iff_twistedE6TwoRootB] at hx hy hg
  set A := twistedE6OrbitClosure σ Dl
  set P := Subgroup.centralizer ({t} : Set (graphFixedRootGroup TwistTag.E6 K σ))
  have hPmem : ∀ c : graphFixedRootGroup TwistTag.E6 K σ,
      Commute (c : ModGL TwistTag.E6.tag K) (t : ModGL TwistTag.E6.tag K) → c ∈ P :=
    fun c hc => Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact Subtype.ext hc.eq.symm
  have hXt : ∀ {z : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag z →
      twistedE6ClassCentralB z R = true → ∀ d : K,
        Commute (pinnedX TwistTag.E6.tag K z d) (t : ModGL TwistTag.E6.tag K) := by
    intro z hz hcz d
    rw [ht]
    exact commute_pinnedX_list_prod_of_centralB hR hz hcz d
  have hYt : ∀ {z : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag z →
      twistedE6ClassCentralB z R = true →
        twistedE6ClassCentralB (permLattice TwistTag.E6.perm z) R = true → ∀ s : K,
          Commute (twistedE6PairX σ z s) (t : ModGL TwistTag.E6.tag K) := fun hz h1 h2 s =>
    (hXt hz h1 s).mul_left (hXt (hz.permLattice TwistTag.E6.cartan_perm) h2 (σ s))
  have hAmem : ∀ {z : Fin TwistTag.E6.tag.rank → ℤ} {c : graphFixedRootGroup TwistTag.E6 K σ},
      z ∈ Dl → (c : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K
        (TwistTag.E6.diagramOrbit z : Set _) ⊓ twistedFixedGroup TwistTag.E6 K σ → c ∈ A :=
    fun hz hc => Subgroup.subset_closure ⟨_, hz, hc⟩
  intro c hc
  cases k with
  | ff =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', twistedE6ClassFixedB_iff] at hk
    obtain ⟨⟨hxρ, hyρ⟩, hxy⟩ := hk
    have hgρ : permLattice TwistTag.E6.perm (x + y) = x + y := by
      rw [permLattice_add_twistedE6Classes, hxρ, hyρ]
    obtain ⟨a, ha, hca⟩ := exists_eq_pinnedX_of_mem_fixedOrbitGroup hg hgρ hc
    set f₁ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨pinnedX TwistTag.E6.tag K x 1, pinnedX_mem_graphFixedRootGroup_of_fixed σ hx hxρ (map_one σ)⟩
    set f₂ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨pinnedX TwistTag.E6.tag K y a, pinnedX_mem_graphFixedRootGroup_of_fixed σ hy hyρ ha⟩
    have hcf : c = ⁅f₁, f₂⁆ := Subtype.ext (by
      rw [coe_commutatorElement_twistedE6Classes, hca]
      simp only [f₁, f₂]
      rw [commutator_pinnedX_of_isRoot_add_E6 hx hy (ne_of_twistedE6TwoVecB hxy) hg, one_mul])
    rw [hcf]
    refine commutatorElement_mem_commutator_of_or ?_
    rcases hD with hxD | hyD
    · exact Or.inl ⟨hAmem hxD (pinnedX_mem_orbitGroup_of_fixed σ hx hxρ (map_one σ)),
        hPmem f₂ (hXt hy hcy a)⟩
    · exact Or.inr ⟨hPmem f₁ (hXt hx hcx 1),
        hAmem hyD (pinnedX_mem_orbitGroup_of_fixed σ hy hyρ ha)⟩
  | ppf =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', twistedE6ClassFixedB_iff] at hk
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hgρ⟩, hxy⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hk
    obtain ⟨a, ha, hca⟩ := exists_eq_pinnedX_of_mem_fixedOrbitGroup hg hgρ hc
    have hcomm := commutator_twistedE6PairX σ hx hy hg hgρ (ne_of_twistedE6TwoVecB hxy)
      (not_isRoot_of_twistedE6TwoRootB h1) (ne_of_twistedE6TwoVecB h2)
      (ne_of_twistedE6TwoVecB h3) (not_isRoot_of_twistedE6TwoRootB h4)
      (not_isRoot_of_twistedE6TwoRootB h5) (ne_of_twistedE6TwoVecB h6)
      (ne_of_twistedE6TwoVecB h7) 1 (a * t₀)
    have hval : 1 * (a * t₀) + σ (1 * (a * t₀)) = a := by
      rw [one_mul, map_mul, ha, ← mul_add, ht₀, mul_one]
    rw [hval] at hcomm
    set f₁ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨twistedE6PairX σ x 1, twistedE6PairX_mem_graphFixedRootGroup hσσ hx 1⟩
    set f₂ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨twistedE6PairX σ y (a * t₀), twistedE6PairX_mem_graphFixedRootGroup hσσ hy _⟩
    have hcf : c = ⁅f₁, f₂⁆ := Subtype.ext (by
      rw [coe_commutatorElement_twistedE6Classes, hca]
      exact hcomm.symm)
    rw [hcf]
    refine commutatorElement_mem_commutator_of_or ?_
    rcases hD with hxD | hyD
    · exact Or.inl ⟨hAmem hxD (twistedE6PairX_mem_orbitGroup hσσ hx 1),
        hPmem f₂ (hYt hy hcy hcρy _)⟩
    · exact Or.inr ⟨hPmem f₁ (hYt hx hcx hcρx _),
        hAmem hyD (twistedE6PairX_mem_orbitGroup hσσ hy _)⟩
  | ppp =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hgρ⟩, hxy⟩, h1⟩, h2⟩, h3⟩ := hk
    obtain ⟨s, hcs⟩ := exists_eq_twistedE6PairX_of_mem_orbitGroup hσσ hg hgp
      (ne_of_twistedE6TwoVecB hgρ) hc
    obtain ⟨h1a, h1b⟩ := twistedE6ClassCommB_sound h1
    obtain ⟨h2a, h2b⟩ := twistedE6ClassCommB_sound h2
    obtain ⟨h3a, h3b⟩ := twistedE6ClassCommB_sound h3
    have hcomm := commutator_twistedE6PairX_pairSum σ hx hy hg (ne_of_twistedE6TwoVecB hxy)
      h1a h1b h2a h2b h3a h3b 1 s
    rw [one_mul] at hcomm
    set f₁ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨twistedE6PairX σ x 1, twistedE6PairX_mem_graphFixedRootGroup hσσ hx 1⟩
    set f₂ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨twistedE6PairX σ y s, twistedE6PairX_mem_graphFixedRootGroup hσσ hy _⟩
    have hcf : c = ⁅f₁, f₂⁆ := Subtype.ext (by
      rw [coe_commutatorElement_twistedE6Classes, hcs]
      exact hcomm.symm)
    rw [hcf]
    refine commutatorElement_mem_commutator_of_or ?_
    rcases hD with hxD | hyD
    · exact Or.inl ⟨hAmem hxD (twistedE6PairX_mem_orbitGroup hσσ hx 1),
        hPmem f₂ (hYt hy hcy hcρy _)⟩
    · exact Or.inr ⟨hPmem f₁ (hYt hx hcx hcρx _),
        hAmem hyD (twistedE6PairX_mem_orbitGroup hσσ hy _)⟩
  | fp =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', twistedE6ClassFixedB_iff,
      twistedE6ClassMemB_iff] at hk
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxρ, -⟩, hgρ⟩, he⟩, heρ⟩, h1⟩, h2⟩, h3⟩, h4⟩, hedone⟩ := hk
    rw [← isRoot_iff_twistedE6TwoRootB] at he
    obtain ⟨s, hcs⟩ := exists_eq_twistedE6PairX_of_mem_orbitGroup hσσ hg hgp
      (ne_of_twistedE6TwoVecB hgρ) hc
    obtain ⟨h4a, h4b⟩ := twistedE6ClassCommB_sound h4
    have hcomm := commutator_pinnedX_twistedE6PairX_of_fixed σ hx hxρ hy hg he
      (ne_of_twistedE6TwoVecB h1) (ne_of_twistedE6TwoVecB h2) (ne_of_twistedE6TwoVecB h3) h4a h4b
      (map_one σ) s
    rw [one_mul] at hcomm
    have hσe : σ (s * (1 * σ s)) = s * (1 * σ s) := by
      rw [map_mul, map_mul, map_one, hσσ]
      ring
    set f₁ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨pinnedX TwistTag.E6.tag K x 1, pinnedX_mem_graphFixedRootGroup_of_fixed σ hx hxρ (map_one σ)⟩
    set f₂ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨twistedE6PairX σ y s, twistedE6PairX_mem_graphFixedRootGroup hσσ hy _⟩
    set f₃ : graphFixedRootGroup TwistTag.E6 K σ :=
      ⟨pinnedX TwistTag.E6.tag K (y + (x + permLattice TwistTag.E6.perm y)) (s * (1 * σ s)),
        pinnedX_mem_graphFixedRootGroup_of_fixed σ he heρ hσe⟩
    have hcf : c = ⁅f₁, f₂⁆ * f₃⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_commutatorElement_twistedE6Classes, hcs]
      simp only [f₁, f₂, f₃]
      rw [hcomm, mul_inv_cancel_right])
    rw [hcf]
    refine mul_mem (commutatorElement_mem_commutator_of_or ?_)
      (inv_mem (hdone _ hedone f₃ (pinnedX_mem_orbitGroup_of_fixed σ he heρ hσe)))
    rcases hD with hxD | hyD
    · exact Or.inl ⟨hAmem hxD (pinnedX_mem_orbitGroup_of_fixed σ hx hxρ (map_one σ)),
        hPmem f₂ (hYt hy hcy hcρy _)⟩
    · exact Or.inr ⟨hPmem f₁ (hXt hx hcx 1),
        hAmem hyD (twistedE6PairX_mem_orbitGroup hσσ hy _)⟩

theorem twistedE6ClassTable_sound [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {t₀ : K} (ht₀ : t₀ + σ t₀ = 1) {R Dl : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : ∀ ε ∈ R, IsRoot TwistTag.E6.tag ε) {t : graphFixedRootGroup TwistTag.E6 K σ}
    (ht : (t : ModGL TwistTag.E6.tag K) = (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod) :
    ∀ (T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
        (Fin TwistTag.E6.tag.rank → ℤ))) (done : List (Fin TwistTag.E6.tag.rank → ℤ)),
      (∀ γ ∈ done, ∀ c : graphFixedRootGroup TwistTag.E6 K σ,
        (c : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K
            (TwistTag.E6.diagramOrbit γ : Set _) ⊓ twistedFixedGroup TwistTag.E6 K σ →
          c ∈ ⁅twistedE6OrbitClosure σ Dl, Subgroup.centralizer {t}⁆) →
      twistedE6ClassTableOK R Dl done T = true → ∀ e ∈ T,
        ∀ c : graphFixedRootGroup TwistTag.E6 K σ,
          (c : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K
              (TwistTag.E6.diagramOrbit (e.2.1 + e.2.2) : Set _) ⊓
                twistedFixedGroup TwistTag.E6 K σ →
            c ∈ ⁅twistedE6OrbitClosure σ Dl, Subgroup.centralizer {t}⁆ := by
  intro T
  induction T with
  | nil => intro _ _ _ e he; exact absurd he List.not_mem_nil
  | cons e es ih =>
    intro done hdone h
    simp only [twistedE6ClassTableOK, Bool.and_eq_true] at h
    have he := twistedE6ClassEntry_sound hσσ ht₀ hR ht hdone h.1
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact he
    · exact ih ((e.2.1 + e.2.2) :: done) (fun γ hγ => by
        rcases List.mem_cons.1 hγ with rfl | hγ
        · exact he
        · exact hdone γ hγ) h.2 e' he'

theorem twistedE6OrbitClosure_le_closure_odd [Finite K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {t₀ : K} (ht₀ : t₀ + σ t₀ = 1)
    {R : List (Fin TwistTag.E6.tag.rank → ℤ)} {h : ℤ}
    {T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))} {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hchk : twistedE6ClassCheck R h T L = true) {t : graphFixedRootGroup TwistTag.E6 K σ}
    (ht : (t : ModGL TwistTag.E6.tag K) = (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod) :
    twistedE6OrbitClosure σ (twistedE6ClassTargets T) ≤
      closure {c : graphFixedRootGroup TwistTag.E6 K σ | c * t = t * c ∧ Odd (orderOf c)} := by
  obtain ⟨hR, hT, hTp, hDc, -, -, -, -⟩ := twistedE6ClassCheck_sound hchk
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hAP : twistedE6OrbitClosure σ (twistedE6ClassTargets T) ≤
      Subgroup.centralizer ({t} : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro c ⟨γ, hγ, hc⟩
    obtain ⟨hc1, hc2, -⟩ := hDc γ hγ
    have hγr := (hTp γ hγ).1
    have hcomm : Commute (c : ModGL TwistTag.E6.tag K) (t : ModGL TwistTag.E6.tag K) := by
      refine commute_of_mem_rootSpan_twistedE6Classes (fun β hβ d => ?_) (Subgroup.mem_inf.1 hc).1
      rw [ht]
      rw [Finset.mem_coe, diagramOrbit_eq_pair_twistedE6Classes, Finset.mem_insert,
        Finset.mem_singleton] at hβ
      rcases hβ with rfl | rfl
      · exact commute_pinnedX_list_prod_of_centralB hR hγr hc1 d
      · exact commute_pinnedX_list_prod_of_centralB hR
          (hγr.permLattice TwistTag.E6.cartan_perm) hc2 d
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    rw [Set.mem_singleton_iff.1 hg]
    exact Subtype.ext hcomm.eq.symm
  refine le_closure_odd_of_le_commutator hAP
    (fun x hx => (Subgroup.mem_centralizer_iff.1 hx t (Set.mem_singleton t)).symm) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro c ⟨γ, hγ, hc⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hγ
  exact twistedE6ClassTable_sound hσσ ht₀ hR ht T [] (fun γ hγ => absurd hγ List.not_mem_nil) hT
    e he c hc

theorem fixedHeightSeries_le_closure_odd_of_classCheck [Finite K] [CharP K 2] {σ : K →+* K}
    (hσ : Function.Surjective σ) (hσσ : ∀ x, σ (σ x) = x) {t₀ : K} (ht₀ : t₀ + σ t₀ = 1)
    {R : List (Fin TwistTag.E6.tag.rank → ℤ)} {h : ℤ}
    {T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))} {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hchk : twistedE6ClassCheck R h T L = true) {t : graphFixedRootGroup TwistTag.E6 K σ}
    (ht : (t : ModGL TwistTag.E6.tag K) = (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod)
    (x : graphFixedRootGroup TwistTag.E6 K σ)
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ heightSeries TwistTag.E6.tag K h) :
    x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ | c * t = t * c ∧ Odd (orderOf c)} := by
  obtain ⟨-, -, -, -, hcov, -, -, -⟩ := twistedE6ClassCheck_sound hchk
  have hA := twistedE6OrbitClosure_le_closure_odd hσσ ht₀ hchk ht
  set Sh : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
    {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ h ≤ height α} with hSh
  have hS : ∀ α ∈ Sh, IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα => ⟨hα.1, hα.2.1⟩
  have hSρ : ∀ α ∈ Sh, permLattice TwistTag.E6.perm α ∈ Sh := fun α hα =>
    ⟨hα.1.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hα.2.1,
      by rw [height_permLattice]; exact hα.2.2⟩
  have hcl : ∀ α ∈ Sh, ∀ β ∈ Sh, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ Sh := by
    intro α hα β hβ a b ha hb hr
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    refine ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul] <;> nlinarith [hα.2.1, hβ.2.1, hα.2.2]
  obtain ⟨k, O, hO, hrange⟩ : ∃ (k : ℕ) (O : Fin k → Finset (Fin TwistTag.E6.tag.rank → ℤ)),
      Function.Injective O ∧ Set.range O = {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
        (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ Sh} := by
    have hfin : {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
        (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ Sh}.Finite :=
      ((finite_setOf_isRoot TwistTag.E6.tag).image TwistTag.E6.diagramOrbit).subset
        fun O' ⟨⟨α, hα, hαO⟩, _⟩ => ⟨α, hα, hαO⟩
    obtain ⟨k, O, hO⟩ := hfin.fin_embedding
    exact ⟨k, O, O.injective, hO⟩
  have hbij := bijOn_prod_graphFixed (K := K) (σ := σ) hσ hS hSρ hcl O hO hrange
  have hxΓ : (x : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ :=
    graphFixedRootGroup_le _ _ _ x.2
  obtain ⟨w, -, hw⟩ := hbij.surjOn (Subgroup.mem_inf.2 ⟨hx, hxΓ⟩)
  suffices hmem : (x : ModGL TwistTag.E6.tag K) ∈
      (closure {c : graphFixedRootGroup TwistTag.E6 K σ | c * t = t * c ∧ Odd (orderOf c)}).map
        (graphFixedRootGroup TwistTag.E6 K σ).subtype by
    obtain ⟨y, hy, hyx⟩ := hmem
    rwa [show x = y from Subtype.ext hyx.symm]
  rw [← hw]
  refine Subgroup.list_prod_mem _ fun z hz => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
  have hOj : O j ∈ TwistTag.E6.diagramRootOrbits ∧
      (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ Sh := by
    have h := Set.mem_range_self (f := O) j
    rw [hrange] at h
    exact h
  obtain ⟨α, -, hαO⟩ := hOj.1
  have hαS : α ∈ Sh := hOj.2 (by rw [← hαO]; exact TwistTag.E6.self_mem_diagramOrbit α)
  obtain ⟨hwO, hwΓ⟩ := Subgroup.mem_inf.1 (w j).2
  have hwU : (w j : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ :=
    Subgroup.mem_inf.2 ⟨rootSpan_mono (fun β hβ => hS β (hOj.2 hβ)) hwO, hwΓ⟩
  refine ⟨⟨w j, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hwU⟩,
    hA (Subgroup.subset_closure ⟨α, hcov α hαS.1 hαS.2.1 hαS.2.2, ?_⟩), rfl⟩
  rw [hαO]
  exact (w j).2

theorem sq_eq_one_of_classCheck [Finite K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {t₀ : K} (ht₀ : t₀ + σ t₀ = 1) {d₀ : K} (hd₀ : σ d₀ ≠ d₀)
    {R : List (Fin TwistTag.E6.tag.rank → ℤ)} {h : ℤ}
    {T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))} {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hchk : twistedE6ClassCheck R h T L = true) {t : graphFixedRootGroup TwistTag.E6 K σ}
    (ht : (t : ModGL TwistTag.E6.tag K) = (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod)
    {z : ModGL TwistTag.E6.tag K} (hz : z ∈ graphFixedPosUnipotent TwistTag.E6 K σ)
    (hzC : z ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (hc : ∀ c : graphFixedRootGroup TwistTag.E6 K σ, c * t = t * c → Odd (orderOf c) →
      (⟨z, hzC⟩ : graphFixedRootGroup TwistTag.E6 K σ) * c = c * ⟨z, hzC⟩) :
    z ^ 2 = 1 := by
  obtain ⟨-, -, hTp, hDc, -, hdet, hL, hLL⟩ := twistedE6ClassCheck_sound hchk
  have hA := twistedE6OrbitClosure_le_closure_odd hσσ ht₀ hchk ht
  set z' : graphFixedRootGroup TwistTag.E6 K σ := ⟨z, hzC⟩
  have hcl : ∀ c ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ |
      c * t = t * c ∧ Odd (orderOf c)}, Commute z' c := by
    intro c hc'
    induction hc' using Subgroup.closure_induction with
    | mem c hc'' => exact hc c hc''.1 hc''.2
    | one => exact Commute.one_right z'
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hcomm : ∀ γ ∈ twistedE6ClassTargets T, ∀ c : graphFixedRootGroup TwistTag.E6 K σ,
      (c : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K
        (TwistTag.E6.diagramOrbit γ : Set _) ⊓ twistedFixedGroup TwistTag.E6 K σ →
        z * c = c * z := fun γ hγ c hc' =>
    congrArg Subtype.val (hcl c (hA (Subgroup.subset_closure ⟨γ, hγ, hc'⟩))).eq
  have hzL : z ∈ rootSpan TwistTag.E6.tag K {γ | γ ∈ L} :=
    mem_rootSpan_of_commute_twistedE6 hd₀ (S := {δ | δ ∈ twistedE6ClassTargets T})
      (A := {γ | γ ∈ L}) (fun δ hδ => hTp δ hδ) (fun δ hδ => (hDc δ hδ).2.2)
      (fun γ hγ δ hδ => (hL γ hγ).2.2 δ hδ) hdet (Subgroup.mem_inf.1 hz).1
      (fun δ hδ hρ => hcomm δ hδ
        ⟨_, pinnedX_mem_graphFixedRootGroup_of_fixed σ (hTp δ hδ).1 hρ (map_one σ)⟩
        (pinnedX_mem_orbitGroup_of_fixed σ (hTp δ hδ).1 hρ (map_one σ)))
      (fun δ hδ _ d => hcomm δ hδ
        ⟨_, twistedE6PairX_mem_graphFixedRootGroup hσσ (hTp δ hδ).1 d⟩
        (twistedE6PairX_mem_orbitGroup hσσ (hTp δ hδ).1 d))
  refine sq_eq_one_of_mem_rootSpan_annih (fun γ hγ γ' hγ' c d => ?_) hzL
  obtain ⟨hγr, hγp, -⟩ := hL γ hγ
  obtain ⟨hγ'r, hγ'p, -⟩ := hL γ' hγ'
  refine (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hγr hγ'r (hLL γ hγ γ' hγ') ?_ c d).eq
  intro h0
  have := congrArg height h0
  rw [height_add, show height (0 : Fin TwistTag.E6.tag.rank → ℤ) = 0 by simp [height]] at this
  omega

theorem innerCentralizerCriterion_twistedE6_of_classCheck [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {R : List (Fin TwistTag.E6.tag.rank → ℤ)} {h : ℤ}
    {T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))} {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hchk : twistedE6ClassCheck R h T L = true) (h1 : 1 ≤ h) (h7 : h ≤ 7)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = (R.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod) :
    InnerCentralizerCriterion t := by
  have hσ2 := twistedE6_sigma_pow_order hK hσ
  have hσσ : ∀ x, σ.toRingHom (σ.toRingHom x) = x := fun x => by
    have h := congrArg (fun g : K ≃+* K => g x) hσ2
    simpa [TwistTag.order, pow_two] using h
  obtain ⟨d₀, hd₀⟩ := exists_twistedE6_sigma_ne hf hK hσ
  have hd₀' : σ.toRingHom d₀ ≠ d₀ := hd₀
  have hτ : d₀ + σ.toRingHom d₀ ≠ 0 := by
    intro h
    apply hd₀'
    have e : σ.toRingHom d₀ = -d₀ := by linear_combination h
    rw [e, CharTwo.neg_eq]
  have hστ : σ.toRingHom (d₀ + σ.toRingHom d₀) = d₀ + σ.toRingHom d₀ := by
    rw [map_add, hσσ, add_comm]
  have ht₀ : d₀ * (d₀ + σ.toRingHom d₀)⁻¹ + σ.toRingHom (d₀ * (d₀ + σ.toRingHom d₀)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hστ, ← add_mul, mul_inv_cancel₀ hτ]
  refine innerCentralizerCriterion_of_fixedHeightSeries_twistedE6 hf hK hσ h1 h7
    (fixedHeightSeries_le_closure_odd_of_classCheck σ.surjective hσσ ht₀ hchk ht) ?_
  intro u hu _ huC hc
  exact sq_eq_one_of_classCheck hσσ ht₀ hd₀' hchk ht hu huC hc

theorem innerCentralizerCriterion_twistedE6_classU [CharP K 2] {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = twistedE6ClassU K) :
    InnerCentralizerCriterion t :=
  innerCentralizerCriterion_twistedE6_of_classCheck hf hK hσ twistedE6ClassCheck_U (by norm_num)
    (by norm_num) (by rw [ht]; simp [twistedE6ClassU, twistedE6ClassURoots])

theorem innerCentralizerCriterion_twistedE6_classV [CharP K 2] {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = twistedE6ClassV K) :
    InnerCentralizerCriterion t :=
  innerCentralizerCriterion_twistedE6_of_classCheck hf hK hσ twistedE6ClassCheck_V (by norm_num)
    (by norm_num) (by rw [ht]; simp [twistedE6ClassV, twistedE6ClassVRoots, mul_assoc])

theorem innerCentralizerCriterion_twistedE6ClassReps [CharP K 2] {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∀ s ∈ twistedE6ClassReps K σ.toRingHom, InnerCentralizerCriterion s := by
  rintro s (hs | hs | hs)
  · have e : s = ⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1,
        pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom 1 (map_one _)⟩ :=
      Subtype.ext hs
    rw [e]
    exact innerCentralizerCriterion_twistedE6_longRoot' hf hK hσ
  · exact innerCentralizerCriterion_twistedE6_classU hf hK hσ hs
  · exact innerCentralizerCriterion_twistedE6_classV hf hK hσ hs

theorem innerInvolutionInput_twistedE6_of_classes {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hrep : ∀ t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      orderOf (MulAut.conj t) = 2 →
        ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
          ∃ s ∈ twistedE6ClassReps K σ.toRingHom, ψ s = t) :
    InnerInvolutionInput (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK'
  exact innerInvolutionInput_of_representatives
    (innerCentralizerCriterion_twistedE6ClassReps hf hK hσ) hrep

end CFSG.SeitzReduction
