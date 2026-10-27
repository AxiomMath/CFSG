module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCInd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open
open scoped commutatorElement

section L1

variable {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

theorem exists_minusPair (Q : QuadraticForm (ZMod 2) X)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank (ZMod 2) X) :
    ∃ a b : X, MinusPair Q a b := by
  have hnd1 : ∀ x : X, (∀ y, polar Q x y = 0) → x = 0 := fun x hx =>
    hnd.1 x (fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact hx y)
  obtain ⟨a, haQ⟩ : ∃ a : X, Q a = 1 := by
    by_contra hno
    push Not at hno
    have hQ0 : ∀ x, Q x = 0 := fun x => (zmod_two_cases (Q x)).resolve_right (hno x)
    have : ∀ x : X, x = 0 := fun x => hnd1 x (fun y => by
      rw [polar_eq Q, hQ0, hQ0, hQ0]; simp)
    have h1 : finrank (ZMod 2) X = 0 := by
      haveI : Subsingleton X := ⟨fun x y => by rw [this x, this y]⟩
      exact finrank_zero_of_subsingleton
    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at haQ
    exact zero_ne_one haQ
  set A : Submodule (ZMod 2) X := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
    (Submodule.span (ZMod 2) {a}) with hA
  have hmemA : ∀ x, x ∈ A ↔ polar Q a x = 0 := by
    intro x
    rw [hA, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have := h a (Submodule.subset_span rfl)
      rwa [QuadraticMap.polarBilin_apply_apply] at this
    · intro h n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
      rw [QuadraticMap.polarBilin_apply_apply, polar_smul_left, h]
      simp
  have hdimA : finrank (ZMod 2) A = finrank (ZMod 2) X - 1 := by
    rw [hA, LinearMap.BilinForm.finrank_orthogonal hnd, finrank_span_singleton ha0]
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : X, polar Q a b₀ = 1 := by
    by_contra hno
    push Not at hno
    exact ha0 (hnd1 a (fun y => (zmod_two_cases _).resolve_right (hno y)))
  by_contra hcon
  push Not at hcon
  have hQb : ∀ b, polar Q a b = 1 → Q b = 0 := fun b hb =>
    (zmod_two_cases (Q b)).resolve_right (fun h1 => hcon a b ⟨haQ, h1, hb⟩)
  have hQb₀ := hQb b₀ hb₀
  have hQA : ∀ c ∈ A, Q c = polar Q b₀ c := by
    intro c hc
    have h1 : polar Q a (b₀ + c) = 1 := by
      rw [polar_add_right, hb₀, (hmemA c).1 hc, add_zero]
    have h2 := hQb _ h1
    rw [QuadraticMap.map_add Q, hQb₀, zero_add] at h2
    have := vec_add_self (polar Q b₀ c)
    generalize Q c = u at h2 ⊢
    generalize polar Q b₀ c = w at h2 ⊢
    revert u w
    decide
  have hAA : ∀ c ∈ A, ∀ c' ∈ A, polar Q c c' = 0 := by
    intro c hc c' hc'
    rw [polar_eq Q, hQA _ (A.add_mem hc hc'), hQA c hc, hQA c' hc', polar_add_right]
    generalize polar Q b₀ c = u
    generalize polar Q b₀ c' = w
    revert u w
    decide
  have hle : A ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) A := by
    intro c hc
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hAA n hn c hc
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hnd A
  omega

end L1

section PolarComp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem polar_comp_subtype (P : Submodule (ZMod 2) V) (a b : P) :
    polar (Q.comp P.subtype) a b = polar Q (a : V) (b : V) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, Submodule.subtype_apply, Submodule.coe_add]

end PolarComp

section MaxFrame

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem nondeg_polar (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∀ x : V, (∀ y, polar Q x y = 0) → x = 0 := fun x hx =>
  hQ.1 x (fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact hx y)

theorem exists_frame_top (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE : IsElemAbelian 3 E) : ∃ l : List (V × V), IsFrame Q l ∧ E ≤ torus Q l := by
  obtain ⟨l, hl, -, hg⟩ := exists_frame hEO hE _ ⊤ rfl (fun g _ x _ => trivial)
    (fun x _ hx => nondeg_polar hQ x (fun y => hx y trivial))
  refine ⟨l, hl, fun g hg' => ?_⟩
  obtain ⟨t, ht, hgt⟩ := hg g hg'
  have : g = t := LinearEquiv.ext (fun x => hgt x trivial)
  rw [this]
  exact ht

theorem IsFrame.perpL_nondeg (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : List (V × V)}
    (hl : IsFrame Q l) : ∀ x ∈ perpL Q l, (∀ y ∈ perpL Q l, polar Q x y = 0) → x = 0 := by
  intro x hx hxy
  refine nondeg_polar hQ x (fun z => ?_)
  obtain ⟨w, hw, hz⟩ := hl.exists_decomp z
  have hz' : z = w + (z - w) := by abel
  rw [hz', polar_add_right, hxy _ hz, add_zero, polar_comm]
  have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hx) w hw
  rwa [QuadraticMap.polarBilin_apply_apply] at this

theorem exists_frame_max (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEΩ : E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hE : IsElemAbelian 3 E)
    (hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V),
      E' ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      IsElemAbelian 3 E' → Nat.card E' ≤ Nat.card E) :
    ∃ l : List (V × V), IsFrame Q l ∧ E = torus Q l ∧
      ¬ ∃ a b : V, a ∈ perpL Q l ∧ b ∈ perpL Q l ∧ MinusPair Q a b := by
  have hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hEΩ.trans (Subgroup.commutator_le_self _)
  obtain ⟨l, hl, hEl⟩ := exists_frame_top hQ hEO hE
  have hcardle : Nat.card (torus Q l) ≤ Nat.card E :=
    hmax _ (torus_le_commutator hl) (torus_isElemAbelian hl)
  have hEq : E = torus Q l := Subgroup.eq_of_le_of_card_ge hEl hcardle
  refine ⟨l, hl, hEq, ?_⟩
  rintro ⟨a, b, ha, hb, hp⟩
  have hperp : ∀ q ∈ l, PairPerp Q (a, b) q := by
    intro q hq
    obtain ⟨h1, h2⟩ := (mem_perpL_iff l a).1 ha q hq
    obtain ⟨h3, h4⟩ := (mem_perpL_iff l b).1 hb q hq
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_comm]; exact h1
    · rw [polar_comm]; exact h2
    · rw [polar_comm]; exact h3
    · rw [polar_comm]; exact h4
  have hl' : IsFrame Q ((a, b) :: l) := IsFrame.cons hp hperp hl
  have hcard := hmax _ (torus_le_commutator hl') (torus_isElemAbelian hl')
  rw [card_torus hl', hEq, card_torus hl, List.length_cons, pow_succ] at hcard
  have hpos : 0 < 3 ^ l.length := by positivity
  omega

theorem IsFrame.finrank_perpL_le (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {l : List (V × V)} (hl : IsFrame Q l)
    (hno : ¬ ∃ a b : V, a ∈ perpL Q l ∧ b ∈ perpL Q l ∧ MinusPair Q a b) :
    finrank (ZMod 2) (perpL Q l) ≤ 2 := by
  by_contra h3
  push Not at h3
  let Q' : QuadraticForm (ZMod 2) (perpL Q l) := Q.comp (perpL Q l).subtype
  have hnd : (QuadraticMap.polarBilin Q').Nondegenerate := by
    have key : ∀ a b : perpL Q l, polarBilin Q' a b = polar Q (a : V) (b : V) := by
      intro a b
      rw [QuadraticMap.polarBilin_apply_apply]
      exact polar_comp_subtype _ a b
    constructor
    · intro x hx
      refine Subtype.ext (hl.perpL_nondeg hQ x x.2 (fun y hy => ?_))
      have := hx ⟨y, hy⟩
      rwa [key] at this
    · intro y hy
      refine Subtype.ext (hl.perpL_nondeg hQ y y.2 (fun x hx => ?_))
      have := hy ⟨x, hx⟩
      rw [key] at this
      rw [polar_comm]
      exact this
  obtain ⟨a, b, hab⟩ := exists_minusPair Q' hnd (by omega)
  refine hno ⟨a, b, a.2, b.2, ⟨hab.qa, hab.qb, ?_⟩⟩
  have := hab.ab
  rwa [polar_comp_subtype] at this

end MaxFrame

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
