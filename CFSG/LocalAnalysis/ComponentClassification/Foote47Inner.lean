module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSec4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Four
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Tools

public section

namespace CFSG.ComponentClassification.Foote47

open scoped MatrixGroups

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.GSThmB
  CFSG.ComponentClassification.UnbalancedLayer

theorem outAbelian_alternating_seven {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7))
    (φ ψ : MulAut X) : ∃ s : X, φ * ψ * φ⁻¹ * ψ⁻¹ = MulAut.conj s := by
  set φ' := MulAut.congr e φ with hφ'
  set ψ' := MulAut.congr e ψ with hψ'
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inr le_rfl) φ'
  obtain ⟨τ, hτ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inr le_rfl) ψ'
  have hc : σ * τ * σ⁻¹ * τ⁻¹ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp only [map_mul, map_inv]
    rw [mul_comm (Equiv.Perm.sign σ) (Equiv.Perm.sign τ)]
    group
  have hinv : ∀ (χ : MulAut (alternatingGroup (Fin 7))) (ρ : Equiv.Perm (Fin 7)),
      (∀ g : alternatingGroup (Fin 7), (χ g : Equiv.Perm (Fin 7)) = ρ * g * ρ⁻¹) →
      ∀ g : alternatingGroup (Fin 7), (χ⁻¹ g : Equiv.Perm (Fin 7)) = ρ⁻¹ * g * ρ := by
    intro χ ρ hχ g
    have h1 := hχ (χ⁻¹ g)
    rw [show χ (χ⁻¹ g) = g from χ.apply_symm_apply g] at h1
    rw [h1]
    group
  have key : φ' * ψ' * φ'⁻¹ * ψ'⁻¹ = MulAut.conj ⟨_, hc⟩ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    show ((φ' (ψ' (φ'⁻¹ (ψ'⁻¹ g))) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      ((⟨_, hc⟩ * g * (⟨_, hc⟩ : alternatingGroup (Fin 7))⁻¹ : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7))
    rw [hσ, hτ, hinv φ' σ hσ, hinv ψ' τ hτ, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group
  refine ⟨e.symm ⟨_, hc⟩, ?_⟩
  have h1 : MulAut.congr e (φ * ψ * φ⁻¹ * ψ⁻¹) = MulAut.congr e (MulAut.conj (e.symm ⟨_, hc⟩)) := by
    rw [FooteLit.MulAut.congr_conj, MulEquiv.apply_symm_apply, ← key]
    simp only [map_mul, map_inv, hφ', hψ']
  exact (MulAut.congr e).injective h1

theorem outAbelian_of_type (hOut : FooteL2OutAbelian) (S : Type) [Group S] [Finite S]
    (hS : Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f)
    (φ ψ : MulAut S) : ∃ s : S, φ * ψ * φ⁻¹ * ψ⁻¹ = MulAut.conj s := by
  rcases hS with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact outAbelian_alternating_seven e φ ψ
  · exact hOut S p f hp hp2 hf hL φ ψ

variable {G : Type} [Group G]

@[expose] noncomputable def innerAct (X : Subgroup G) : Subgroup G :=
  ((MulAut.conj : X ⧸ pPrimeCore 2 X →* MulAut (X ⧸ pPrimeCore 2 X)).range.comap
    (oddBarConj X)).map (normalizer (X : Set G)).subtype

theorem mem_innerAct_iff {X : Subgroup G} {x : G} :
    x ∈ innerAct X ↔ ∃ hx : x ∈ normalizer (X : Set G),
      oddBarConj X ⟨x, hx⟩ ∈ (MulAut.conj : X ⧸ pPrimeCore 2 X →* _).range := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyI, rfl⟩
    exact ⟨hy, hyI⟩
  · rintro ⟨hx, hxI⟩
    exact ⟨⟨x, hx⟩, hxI, rfl⟩

theorem le_innerAct (X : Subgroup G) : X ≤ innerAct X := by
  intro x hx
  refine mem_innerAct_iff.mpr ⟨le_normalizer hx, (⟨x, hx⟩ : X), ?_⟩
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  rfl

theorem coreActionKernel_le_innerAct (X : Subgroup G) : coreActionKernel X ≤ innerAct X := by
  intro x hx
  refine mem_innerAct_iff.mpr ⟨hx.1, 1, ?_⟩
  rw [map_one, oddBarConj_eq_one_of_mem_coreActionKernel (g := ⟨x, hx.1⟩) hx]

theorem commutator_mem_innerAct_of_mulEquiv {X : Subgroup G} {S : Type} [Group S]
    (ε : X ⧸ pPrimeCore 2 X ≃* S)
    (hOut : ∀ φ ψ : MulAut S, ∃ s : S, φ * ψ * φ⁻¹ * ψ⁻¹ = MulAut.conj s)
    {x y : G} (hx : x ∈ normalizer (X : Set G)) (hy : y ∈ normalizer (X : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ innerAct X := by
  obtain ⟨s, hs⟩ := hOut (MulAut.congr ε (oddBarConj X ⟨x, hx⟩))
    (MulAut.congr ε (oddBarConj X ⟨y, hy⟩))
  have hxy : x * y * x⁻¹ * y⁻¹ ∈ normalizer (X : Set G) :=
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  refine mem_innerAct_iff.mpr ⟨hxy, ε.symm s, ?_⟩
  apply (MulAut.congr ε).injective
  rw [FooteLit.MulAut.congr_conj, MulEquiv.apply_symm_apply, ← hs]
  have h1 : (⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : normalizer (X : Set G)) =
      ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ := rfl
  rw [h1]
  simp only [map_mul, map_inv]

theorem commutator_mem_innerAct (hOut : FooteL2OutAbelian) {X : Subgroup G} {S : Type} [Group S]
    [Finite S]
    (hS : Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f)
    (ε : X ⧸ pPrimeCore 2 X ≃* S) {x y : G} (hx : x ∈ normalizer (X : Set G))
    (hy : y ∈ normalizer (X : Set G)) : x * y * x⁻¹ * y⁻¹ ∈ innerAct X := by
  exact commutator_mem_innerAct_of_mulEquiv ε (outAbelian_of_type hOut S hS) hx hy

theorem exists_mem_innerAct_of_card_four (hFI : FooteFourgroupInner) {X : Subgroup G}
    {S : Type} [Group S] [Finite S]
    (hS : Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f)
    (ε : X ⧸ pPrimeCore 2 X ≃* S) {V : Subgroup G} (hVN : V ≤ normalizer (X : Set G))
    (hV2 : ∀ v ∈ V, v * v = 1) (hV4 : Nat.card V = 4) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ innerAct X := by
  set N := normalizer (X : Set G) with hN
  set Φ : ↥N →* MulAut S := (MulAut.congr ε).toMonoidHom.comp (oddBarConj X) with hΦ
  have hinner : ∀ (x : G) (hx : x ∈ N), Φ ⟨x, hx⟩ ∈ (MulAut.conj : S →* MulAut S).range →
      x ∈ innerAct X := by
    rintro x hx ⟨s, hs⟩
    refine mem_innerAct_iff.mpr ⟨hx, ε.symm s, ?_⟩
    apply (MulAut.congr ε).injective
    rw [FooteLit.MulAut.congr_conj, MulEquiv.apply_symm_apply, hs]
    rfl
  set ψ := Φ.comp (V.subgroupOf N).subtype with hψ
  by_cases hinj : Function.Injective ψ
  · set V' := (V.subgroupOf N).map Φ with hV'
    have hrange : ψ.range = V' := by rw [MonoidHom.range_comp, range_subtype]
    have hV'4 : Nat.card V' = 4 := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hV4]
      exact Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv
    have hV'2 : ∀ u ∈ V', u * u = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have hx2 : x * x = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, OneMemClass.coe_one]
        exact hV2 _ hx)
      rw [← map_mul, hx2, map_one]
    obtain ⟨u, ⟨x, hx, rfl⟩, hu1, hu⟩ := hFI S hS V' hV'2 hV'4
    refine ⟨x, hx, fun h1 => hu1 ?_, hinner x x.2 hu⟩
    have h2 : x = 1 := Subtype.ext h1
    rw [h2, map_one]
  ·
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff] at hinj
    obtain ⟨⟨⟨x, hxN⟩, hxV⟩, hxk, hx1⟩ := (IsConcreteLE.not_le_iff_exists).mp hinj
    refine ⟨x, hxV, fun h1 => hx1 ?_, hinner x hxN ⟨1, ?_⟩⟩
    · rw [mem_bot]
      exact Subtype.ext (Subtype.ext h1)
    · rw [map_one]
      exact hxk.symm

end CFSG.ComponentClassification.Foote47
