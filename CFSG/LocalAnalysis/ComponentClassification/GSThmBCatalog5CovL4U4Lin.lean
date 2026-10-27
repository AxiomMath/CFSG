module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Inner

variable {N : Type} [Group N] (G : Subgroup (MulAut N))

abbrev innIn : Subgroup G := (MulAut.conj : N →* MulAut N).range.subgroupOf G

instance innIn_normal : (innIn G).Normal := by
  have : (MulAut.conj : N →* MulAut N).range.Normal := OuterAutomorphisms.inner_normal N
  exact Subgroup.Normal.subgroupOf this G

theorem conj_injective_of_center_eq_bot (hZ : center N = ⊥) :
    Function.Injective (MulAut.conj : N →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hc : y ∈ center N := by
    rw [mem_center_iff]
    intro x
    have h1 := congrArg (fun φ : MulAut N => φ x) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * y = (y * x * y⁻¹) * y := by rw [h1]
      _ = y * x := by group
  rw [hZ, mem_bot] at hc
  exact hc

theorem conj_apply_mulAut (σ : MulAut N) (n : N) :
    MulAut.conj (σ n) = σ * MulAut.conj n * σ⁻¹ := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem centralizer_innIn (hZ : center N = ⊥)
    (hInn : (MulAut.conj : N →* MulAut N).range ≤ G) :
    centralizer (innIn G : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  apply Subtype.ext
  refine MulEquiv.ext fun n => ?_
  have hmem : (⟨MulAut.conj n, hInn ⟨n, rfl⟩⟩ : G) ∈ innIn G := mem_subgroupOf.mpr ⟨n, rfl⟩
  have h1 := congrArg (fun γ : G => (γ : MulAut N)) (mem_centralizer_iff.mp hg _ hmem)
  simp only [Subgroup.coe_mul] at h1
  have h2 : MulAut.conj ((g : MulAut N) n) = MulAut.conj n := by
    rw [conj_apply_mulAut, ← h1, mul_inv_cancel_right]
  rw [conj_injective_of_center_eq_bot hZ h2]
  rfl

@[expose] noncomputable def innInEquiv (hZ : center N = ⊥)
    (hInn : (MulAut.conj : N →* MulAut N).range ≤ G) : innIn G ≃* N :=
  (subgroupOfEquivOfLe hInn).trans
    (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)).symm

theorem innIn_simple_nonabelian (hZ : center N = ⊥)
    (hInn : (MulAut.conj : N →* MulAut N).range ≤ G) [IsSimpleGroup N] :
    IsSimpleGroup (innIn G) ∧ ∃ x y : innIn G, x * y ≠ y * x := by
  have hs : IsSimpleGroup (innIn G) := (innInEquiv G hZ hInn).isSimpleGroup
  refine ⟨hs, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨a, b, hab⟩ := exists_pair_ne N
  apply hab
  have hc : ∀ x : N, x ∈ center N := fun x => by
    rw [mem_center_iff]
    intro y
    have h1 := h ((innInEquiv G hZ hInn).symm y) ((innInEquiv G hZ hInn).symm x)
    have h2 := congrArg (innInEquiv G hZ hInn) h1
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
  have ha := hc a
  have hb := hc b
  rw [hZ, mem_bot] at ha hb
  rw [ha, hb]

end Inner

theorem cf23L4U4O8Comp_psl4 {N : Type} [Group N] [Finite N] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hN : Blueprint.LieModel N .PSL 4 p f)
    (G : Subgroup (MulAut N)) (hInn : (MulAut.conj : N →* MulAut N).range ≤ G) (α : G)
    (J : Subgroup G) (hα : orderOf α = 2)
    (hJN : J ≤ (MulAut.conj : N →* MulAut N).range.subgroupOf G)
    (hJc : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (hstd : IsStandardSubgroup J) (hodd : Odd (Nat.card (center J)))
    (hsmall : Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7)) ∨
      ∃ s t : ℕ, s.Prime ∧ s ≠ 2 ∧ 1 ≤ t ∧ 5 ≤ s ^ t ∧
        Blueprint.LieModel (J ⧸ center J) .PSL 2 s t) :
    Blueprint.LieModel (J ⧸ center J) .PSL 2 p (2 * f) := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hN
  have : IsSimpleGroup (projectiveSL 4 k) :=
    OutcomeLocal.isSimpleGroup_projectiveSL (k := k) (n := 4) (by norm_num)
  have : IsSimpleGroup N := e.isSimpleGroup
  have hZ : center N = ⊥ := by
    have hZk := OddSelector.center_projectiveSL_eq_bot (k := k) (n := 4) (by norm_num)
    rw [eq_bot_iff]
    intro z hz
    have h1 : e z ∈ center (projectiveSL 4 k) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
    rw [hZk, mem_bot] at h1
    rw [mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  obtain ⟨hWs, hWnab⟩ := innIn_simple_nonabelian G hZ hInn
  have hCW := centralizer_innIn G hZ hInn
  have hL : CFSG.Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJc).2 hJ
  have hclass : Assembly.LowTwoRank.StatedLieTag.PSL ∈ Blueprint.classicalTags := by
    decide
  rcases hsmall with ⟨⟨e7⟩⟩ | ⟨s, t, hs, hs2, ht, hst, hm⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hstated, -⟩ :=
      OddSelector.faithful_odd_higher_linear_socle_selector_core hWs hWnab hCW hα hJN hL hstd
        (p := p) (f := 2 * f) hp2 (Or.inr (Or.inl ⟨e7⟩)) (fun _ => Or.inr hodd) (le_refl 4)
        hp hp2 hf hk ((innInEquiv G hZ hInn).trans e)
    exact Or.inl ⟨hclass, hstated⟩
  · obtain ⟨-, -, -, -, -, hps, hts, -, -, -⟩ :=
      OddSelector.faithful_odd_higher_linear_socle_selector_core hWs hWnab hCW hα hJN hL hstd
        (p := s) (f := t) hs2 (Or.inl (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hm))
        (fun _ => Or.inr hodd) (le_refl 4) hp hp2 hf hk ((innInEquiv G hZ hInn).trans e)
    subst hps hts
    exact hm

end CFSG.ComponentClassification.GSThmB.Cov
