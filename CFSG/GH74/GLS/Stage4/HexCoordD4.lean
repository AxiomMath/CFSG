module

public import CFSG.GH74.GLS.Stage4.HexCoord
public import CFSG.GH74.GLS.Stage4.HexD4Comm
public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.GH74.GLS.Stage4.HexClass

public noncomputable section

open CFSG.GH74.BNPair CFSG.LieType.Universal CFSG.LieType.Steinberg
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section Words

open CFSG.Timmesfeld.GradedPresentation CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] def d4W02 (s t : K) : FreeGroup (Σ γ, d43Par σ γ) := .of ⟨1, d43Tr hσ (s * t)⟩

@[expose] def d4W24 (s t : K) : FreeGroup (Σ γ, d43Par σ γ) := .of ⟨3, -d43Tr hσ (s * t)⟩

variable (σ) in
@[expose] def d4W15 (s t : fixedField σ) : FreeGroup (Σ γ, d43Par σ γ) :=
  .of ⟨3, -(s * t : fixedField σ)⟩

@[expose] def d4W04 (s t : K) : FreeGroup (Σ γ, d43Par σ γ) :=
  .of ⟨1, -d43Tr hσ (d43Sharp σ s * t)⟩ * .of ⟨2, -(d43Cross σ s t : K)⟩ *
    .of ⟨3, -d43Tr hσ (s * d43Sharp σ t)⟩

@[expose] def d4W05 (s : K) (t : fixedField σ) : FreeGroup (Σ γ, d43Par σ γ) :=
  .of ⟨1, (t * d43Norm hσ s : fixedField σ)⟩ * .of ⟨2, ((t : K) * d43Sharp σ s : K)⟩ *
    .of ⟨3, -(t ^ 2 * d43Norm hσ s : fixedField σ)⟩ * .of ⟨4, -((t : K) * s : K)⟩

@[expose] def d4WordLt :
    ∀ (i : Fin 6) (_ : d43Par σ i) (j : Fin 6) (_ : d43Par σ j), FreeGroup (Σ γ, d43Par σ γ)
  | 0, s, 2, t => d4W02 hσ s t
  | 2, s, 4, t => d4W24 hσ s t
  | 1, s, 5, t => d4W15 σ s t
  | 0, s, 4, t => d4W04 hσ s t
  | 0, s, 5, t => d4W05 hσ s t
  | _, _, _, _ => 1

@[expose] def d4Cm :
    ∀ (i : Fin 6) (_ : d43Par σ i) (j : Fin 6) (_ : d43Par σ j), FreeGroup (Σ γ, d43Par σ γ) :=
  hexCm (d4WordLt hσ)

structure D4Rel {G : Type*} [Group G] (φ : (Σ γ, d43Par σ γ) → G) : Prop where
  add : ∀ i (c d : d43Par σ i), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩
  r02 : ∀ s t : K, ⁅φ ⟨0, s⟩, φ ⟨2, t⟩⁆ = φ ⟨1, d43Tr hσ (s * t)⟩
  r24 : ∀ s t : K, ⁅φ ⟨2, s⟩, φ ⟨4, t⟩⁆ = φ ⟨3, -d43Tr hσ (s * t)⟩
  r15 : ∀ s t : fixedField σ, ⁅φ ⟨1, s⟩, φ ⟨5, t⟩⁆ = φ ⟨3, -(s * t : fixedField σ)⟩
  r04 : ∀ s t : K, ⁅φ ⟨0, s⟩, φ ⟨4, t⟩⁆ = φ ⟨1, -d43Tr hσ (d43Sharp σ s * t)⟩ *
    φ ⟨2, -(d43Cross σ s t : K)⟩ * φ ⟨3, -d43Tr hσ (s * d43Sharp σ t)⟩
  r05 : ∀ (s : K) (t : fixedField σ), ⁅φ ⟨0, s⟩, φ ⟨5, t⟩⁆ =
    φ ⟨1, (t * d43Norm hσ s : fixedField σ)⟩ * φ ⟨2, ((t : K) * d43Sharp σ s : K)⟩ *
      φ ⟨3, -(t ^ 2 * d43Norm hσ s : fixedField σ)⟩ * φ ⟨4, -((t : K) * s : K)⟩
  c01 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩)
  c03 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨0, s⟩) (φ ⟨3, t⟩)
  c12 : ∀ (s : fixedField σ) (t : K), Commute (φ ⟨1, s⟩) (φ ⟨2, t⟩)
  c13 : ∀ s t : fixedField σ, Commute (φ ⟨1, s⟩) (φ ⟨3, t⟩)
  c14 : ∀ (s : fixedField σ) (t : K), Commute (φ ⟨1, s⟩) (φ ⟨4, t⟩)
  c23 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨2, s⟩) (φ ⟨3, t⟩)
  c25 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨2, s⟩) (φ ⟨5, t⟩)
  c34 : ∀ (s : fixedField σ) (t : K), Commute (φ ⟨3, s⟩) (φ ⟨4, t⟩)
  c35 : ∀ s t : fixedField σ, Commute (φ ⟨3, s⟩) (φ ⟨5, t⟩)
  c45 : ∀ (s : K) (t : fixedField σ), Commute (φ ⟨4, s⟩) (φ ⟨5, t⟩)

theorem D4Rel.rels {G : Type*} [Group G] {φ : (Σ γ, d43Par σ γ) → G} (h : D4Rel hσ φ) :
    ∀ r ∈ rels (d4Cm hσ), FreeGroup.lift φ r = 1 := by
  refine rels_hexCm_of h.add fun i j hij s t => ?_
  have hc : ∀ {a b : G}, Commute a b → ⁅a, b⁆ = FreeGroup.lift φ 1 := fun h => by
    rw [map_one, commutatorElement_eq_one_iff_commute]
    exact h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact hc (h.c01 s t) | exact hc (h.c03 s t) | exact hc (h.c12 s t) | exact hc (h.c13 s t)
    | exact hc (h.c14 s t) | exact hc (h.c23 s t) | exact hc (h.c25 s t) | exact hc (h.c34 s t)
    | exact hc (h.c35 s t) | exact hc (h.c45 s t)
    | exact (h.r02 s t).trans (by simp [d4WordLt, d4W02])
    | exact (h.r24 s t).trans (by simp [d4WordLt, d4W24])
    | exact (h.r15 s t).trans (by simp [d4WordLt, d4W15])
    | exact (h.r04 s t).trans (by simp [d4WordLt, d4W04])
    | exact (h.r05 s t).trans (by simp [d4WordLt, d4W05])

theorem d4Cm_mem_above (i : Fin 6) (s : d43Par σ i) (j : Fin 6) (t : d43Par σ j) :
    d4Cm hσ i s j t ∈ above hexHt (max (hexHt i) (hexHt j)) := by
  refine hexCm_mem_above (fun i j hij s t => ?_) i s j t
  have hg : ∀ (k : Fin 6) (c : d43Par σ k) (m : ℕ), m < hexHt k →
      (FreeGroup.of ⟨k, c⟩ : FreeGroup (Σ γ, d43Par σ γ)) ∈ above hexHt m :=
    fun k c m hm => Subgroup.subset_closure ⟨⟨k, c⟩, hm, rfl⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact one_mem _
    | exact hg _ _ _ (by decide)
    | exact mul_mem (mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide))) (hg _ _ _ (by decide))
    | exact mul_mem (mul_mem (mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide)))
        (hg _ _ _ (by decide))) (hg _ _ _ (by decide))

end Words


section Model

open CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] def d4Sgn (σ : K →+* K) : ∀ i : Fin 6, d43Par σ i → d43Par σ i
  | 0, c => c
  | 1, c => -c
  | 2, c => -c
  | 3, c => -c
  | 4, c => c
  | 5, c => c

theorem d4Sgn_add (i : Fin 6) (c d : d43Par σ i) : d4Sgn σ i (c + d) = d4Sgn σ i c + d4Sgn σ i d := by
  fin_cases i
  · rfl
  · exact neg_add c d
  · exact neg_add c d
  · exact neg_add c d
  · rfl
  · rfl

theorem d4Sgn_injective (i : Fin 6) : Function.Injective (d4Sgn σ i) := by
  fin_cases i
  · exact fun _ _ h => h
  · exact fun _ _ h => neg_injective h
  · exact fun _ _ h => neg_injective h
  · exact fun _ _ h => neg_injective h
  · exact fun _ _ h => h
  · exact fun _ _ h => h

theorem d43XE_add' :
    ∀ (i : Fin 6) (c d : d43Par σ i),
    d43XE σ i (c + d) = d43XE σ i c * d43XE σ i d
  | 0, c, d => d43XSh_add (K := K) (σ := σ) (isRoot_hexRoot 0) short_hexRoot_zero c d
  | 1, c, d => d43XLg_add _ c d
  | 2, c, d => d43XSh_add (K := K) (σ := σ) (isRoot_hexRoot 2) short_hexRoot_two c d
  | 3, c, d => d43XLg_add _ c d
  | 4, c, d => d43XSh_add (K := K) (σ := σ) (isRoot_hexRoot 4) short_hexRoot_four c d
  | 5, c, d => d43XLg_add _ c d

@[expose] noncomputable def d4X
    (hσ : ∀ c, σ (σ (σ c)) = c) (i : Fin 6) (c : d43Par σ i) :
    twistedGroup σ :=
  d43X hσ i (d4Sgn σ i c)

theorem coe_d4X
    (i : Fin 6) (c : d43Par σ i) :
    ((d4X hσ i c : twistedGroup σ) : adjointGroup d4 K) = d43XE σ i (d4Sgn σ i c) := rfl

theorem d4X_add
    (i : Fin 6) (c d : d43Par σ i) : d4X hσ i (c + d) = d4X hσ i c * d4X hσ i d := by
  apply Subtype.ext
  rw [coe_d4X, Subgroup.coe_mul, coe_d4X, coe_d4X, d4Sgn_add, d43XE_add']


theorem commute_of_val {H : Type*} [Group H] {S : Subgroup H} {a b : S}
    (h : Commute (a : H) (b : H)) : Commute a b :=
  Subtype.ext h.eq

theorem d4Rel_model :
    D4Rel hσ (fun g : Σ i, d43Par σ i => d4X hσ g.1 g.2) where
  add i c d := d4X_add hσ i c d
  r02 s t := by
    apply Subtype.ext
    show ⁅d43XE σ 0 s, d43XE σ 2 (-t)⁆ = d43XE σ 1 (-d43Tr hσ (s * t))
    rw [d43XE_zero, d43XE_two, d43XE_one, d4g_comm02 σ hσ s (-t)]
    congr 1
    simp only [coe_d43Tr, map_neg, mul_neg, NegMemClass.coe_neg]
    ring
  r24 s t := by
    apply Subtype.ext
    show ⁅d43XE σ 2 (-s), d43XE σ 4 t⁆ = d43XE σ 3 (-(-d43Tr hσ (s * t)))
    rw [d43XE_two, d43XE_four, d43XE_three, d4g_comm24 σ hσ (-s) t]
    congr 1
    simp only [coe_d43Tr, map_neg, neg_mul, neg_neg]
    ring
  r15 s t := by
    apply Subtype.ext
    show ⁅d43XE σ 1 (-s), d43XE σ 5 t⁆ = d43XE σ 3 (-(-(s * t : fixedField σ)))
    rw [d43XE_one, d43XE_five, d43XE_three, d4g_comm15 σ (-s) t]
    congr 1
    simp
  r04 s t := by
    apply Subtype.ext
    show ⁅d43XE σ 0 s, d43XE σ 4 t⁆ = d43XE σ 1 (-(-d43Tr hσ (d43Sharp σ s * t))) *
      d43XE σ 2 (-(-(d43Cross σ s t : K))) * d43XE σ 3 (-(-d43Tr hσ (s * d43Sharp σ t)))
    rw [d43XE_zero, d43XE_four, d43XE_one, d43XE_two, d43XE_three, d4g_comm04 σ hσ s t]
    simp only [neg_neg]
  r05 s t := by
    apply Subtype.ext
    show ⁅d43XE σ 0 s, d43XE σ 5 t⁆ = d43XE σ 1 (-(t * d43Norm hσ s : fixedField σ)) *
      d43XE σ 2 (-((t : K) * d43Sharp σ s : K)) *
        d43XE σ 3 (-(-(t ^ 2 * d43Norm hσ s : fixedField σ))) * d43XE σ 4 (-((t : K) * s : K))
    rw [d43XE_zero, d43XE_five, d43XE_one, d43XE_two, d43XE_three, d43XE_four,
      d4g_comm05 σ hσ s t t.2]
    simp only [NegMemClass.coe_neg, neg_neg, MulMemClass.coe_mul, coe_d43Norm, d43Sharp,
      SubmonoidClass.coe_pow]
  c01 s t := commute_of_val (by
    show Commute (d43XE σ 0 s) (d43XE σ 1 (-t))
    rw [d43XE_zero, d43XE_one]
    exact d4g_commute01 σ _ _)
  c03 s t := commute_of_val (by
    show Commute (d43XE σ 0 s) (d43XE σ 3 (-t))
    rw [d43XE_zero, d43XE_three]
    exact d4g_commute03 σ _ _)
  c12 s t := commute_of_val (by
    show Commute (d43XE σ 1 (-s)) (d43XE σ 2 (-t))
    rw [d43XE_one, d43XE_two]
    exact d4g_commute12 σ hσ _ _)
  c13 s t := commute_of_val (by
    show Commute (d43XE σ 1 (-s)) (d43XE σ 3 (-t))
    rw [d43XE_one, d43XE_three]
    exact d4g_commute13 _ _)
  c14 s t := commute_of_val (by
    show Commute (d43XE σ 1 (-s)) (d43XE σ 4 t)
    rw [d43XE_one, d43XE_four]
    exact d4g_commute14 σ _ _)
  c23 s t := commute_of_val (by
    show Commute (d43XE σ 2 (-s)) (d43XE σ 3 (-t))
    rw [d43XE_two, d43XE_three]
    exact d4g_commute23 σ hσ _ _)
  c25 s t := commute_of_val (by
    show Commute (d43XE σ 2 (-s)) (d43XE σ 5 t)
    rw [d43XE_two, d43XE_five]
    exact d4g_commute25 σ hσ _ _)
  c34 s t := commute_of_val (by
    show Commute (d43XE σ 3 (-s)) (d43XE σ 4 t)
    rw [d43XE_three, d43XE_four]
    exact d4g_commute34 σ _ _)
  c35 s t := commute_of_val (by
    show Commute (d43XE σ 3 (-s)) (d43XE σ 5 t)
    rw [d43XE_three, d43XE_five]
    exact d4g_commute35 _ _)
  c45 s t := commute_of_val (by
    show Commute (d43XE σ 4 s) (d43XE σ 5 t)
    rw [d43XE_four, d43XE_five]
    exact d4g_commute45 σ _ _)

end Model


section NormalForm

open CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4Sgn_d4Sgn (i : Fin 6) (c : d43Par σ i) : d4Sgn σ i (d4Sgn σ i c) = c := by
  fin_cases i
  · rfl
  · exact neg_neg c
  · exact neg_neg c
  · exact neg_neg c
  · rfl
  · rfl

theorem d4X_mem
    (i : Fin 6) (c : d43Par σ i) :
    d4X hσ i c ∈ hexGroup (twistedX σ) ((i : ℤ) + 1) := by
  show d4X hσ i c ∈ twistedRootGroup σ (hexPos ((i : ℤ) + 1))
  rw [hexPos_succ]
  exact d43X_mem hσ i _

theorem mem_hexGroup_d4_iff
    (i : Fin 6) (y : twistedGroup σ) :
    y ∈ hexGroup (twistedX σ) ((i : ℤ) + 1) ↔ ∃ c : d43Par σ i, d4X hσ i c = y := by
  constructor
  · intro hy
    have hy' : y ∈ twistedRootGroup σ (hexRoot i) := by
      have : y ∈ twistedRootGroup σ (hexPos ((i : ℤ) + 1)) := hy
      rwa [hexPos_succ] at this
    have hy'' := (mem_twistedRootGroup σ).1 hy'
    suffices h : ∃ c : d43Par σ i, d43X hσ i c = y by
      obtain ⟨c, hc⟩ := h
      exact ⟨d4Sgn σ i c, by rw [d4X, d4Sgn_d4Sgn]; exact hc⟩
    fin_cases i
    · obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ (isRoot_hexRoot 0) short_hexRoot_zero _).1 hy''
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ (isRoot_hexRoot 1) long_hexRoot_one _).1 hy''
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ (isRoot_hexRoot 2) short_hexRoot_two _).1 hy''
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ (isRoot_hexRoot 3) long_hexRoot_three _).1 hy''
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XSh hσ (isRoot_hexRoot 4) short_hexRoot_four _).1 hy''
      exact ⟨c, Subtype.ext hc⟩
    · obtain ⟨c, hc⟩ := (mem_iff_d43XLg hσ (isRoot_hexRoot 5) long_hexRoot_five _).1 hy''
      exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩
    exact d4X_mem hσ i c

theorem d4X_mem_posUnipotent
    (i : Fin 6) (c : d43Par σ i) :
    d4X hσ i c ∈ posUnipotent (g2Shape (twistedX σ)) :=
  hexGroup_le_posUnipotent (by omega) (by have := i.isLt; omega) (d4X_mem hσ i c)

theorem mem_posUnipotent_d4_iff
    (y : twistedGroup σ) :
    y ∈ posUnipotent (g2Shape (twistedX σ)) ↔
      ∃ c : ∀ i, d43Par σ i, y = prod6 (fun i => d4X hσ i (c i)) := by
  constructor
  · intro hy
    have hc := (d4RGD2 σ hσ).carrier_eq
    have hy' : y ∈ chainProd (hexGroup (twistedX σ)) (intList 1 6) := by
      have h2 : y ∈ (posUnipotent (g2Shape (twistedX σ)) : Set (twistedGroup σ)) := hy
      rw [hc] at h2
      exact h2
    obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩ := (mem_chainProd_six _ y).1 hy'
    obtain ⟨c₀, rfl⟩ := (mem_hexGroup_d4_iff hσ 0 a₁).1 (by simpa using h₁)
    obtain ⟨c₁, rfl⟩ := (mem_hexGroup_d4_iff hσ 1 a₂).1 (by simpa using h₂)
    obtain ⟨c₂, rfl⟩ := (mem_hexGroup_d4_iff hσ 2 a₃).1 (by simpa using h₃)
    obtain ⟨c₃, rfl⟩ := (mem_hexGroup_d4_iff hσ 3 a₄).1 (by simpa using h₄)
    obtain ⟨c₄, rfl⟩ := (mem_hexGroup_d4_iff hσ 4 a₅).1 (by simpa using h₅)
    obtain ⟨c₅, rfl⟩ := (mem_hexGroup_d4_iff hσ 5 a₆).1 (by simpa using h₆)
    exact ⟨fun i => match i with
      | 0 => c₀ | 1 => c₁ | 2 => c₂ | 3 => c₃ | 4 => c₄ | 5 => c₅, rfl⟩
  · rintro ⟨c, rfl⟩
    exact prod6_mem _ fun i => d4X_mem_posUnipotent hσ i _

end NormalForm


section Match

open CFSG.Timmesfeld.GradedPresentation CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] {K : Type} [Field K] {σ : K →+* K}

structure D4Coords (D : RankTwoSystem G 6) (hσ : ∀ c, σ (σ (σ c)) = c)
    (ψ : ∀ i : Fin 6, d43Par σ i → G) : Prop where
  rel : D4Rel hσ (fun g : Σ i, d43Par σ i => ψ g.1 g.2)
  mem : ∀ (i : Fin 6) (c : d43Par σ i), ψ i c ∈ D.root ((i : ℤ) + 1)
  inj : ∀ i : Fin 6, Function.Injective (ψ i)
  surj : ∀ (i : Fin 6) (y : G), y ∈ D.root ((i : ℤ) + 1) → ∃ c, ψ i c = y

@[expose] def d4Gen
    (hσ : ∀ c, σ (σ (σ c)) = c) : Subgroup (twistedGroup σ) :=
  Subgroup.closure (Set.range fun g : Σ i, d43Par σ i => d4X hσ g.1 g.2)

theorem uMatch_of_d4Coords
    [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) {D : RankTwoSystem G 6} {ψ : ∀ i : Fin 6, d43Par σ i → G}
    (h : D4Coords D (sigma_three_of_card hK hσq) ψ) : UMatch (d4ModelSystem σ hq hK hσq) D := by
  classical
  set hσ := sigma_three_of_card hK hσq with hσdef
  have hfin : ∀ i, Fintype (d43Par σ i) := fun i =>
    match i with
    | 0 => (Fintype.ofFinite K : Fintype K)
    | 1 => (Fintype.ofFinite (fixedField σ) : Fintype (fixedField σ))
    | 2 => (Fintype.ofFinite K : Fintype K)
    | 3 => (Fintype.ofFinite (fixedField σ) : Fintype (fixedField σ))
    | 4 => (Fintype.ofFinite K : Fintype K)
    | 5 => (Fintype.ofFinite (fixedField σ) : Fintype (fixedField σ))
  have hinj : Function.Injective fun c : (∀ i, d43Par σ i) =>
      ([0, 5, 4, 2, 1, 3].map fun i => d4X hσ i (c i)).prod := fun c d hcd =>
    funext fun i => d4Sgn_injective i (congrFun (d43X_prod_injective hσ
      (a₁ := fun j => d4Sgn σ j (c j)) (a₂ := fun j => d4Sgn σ j (d j)) hcd) i)
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥(d4Gen hσ) →* G,
      ∀ g : Σ i, d43Par σ i, θ ⟨d4X hσ g.1 g.2, Subgroup.subset_closure ⟨g, rfl⟩⟩ = ψ g.1 g.2 :=
    exists_hom (F := d43Par σ) (cm := d4Cm hσ) (ht := hexHt) (d4Cm_mem_above hσ)
      (fun g : Σ i, d43Par σ i => d4X hσ g.1 g.2) (fun g => ψ g.1 g.2)
      (d4Rel_model hσ).rels h.rel.rels [0, 5, 4, 2, 1, 3] hinj
  have hclos : d4Gen hσ = posUnipotent (g2Shape (twistedX σ)) := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun y hy => ?_
    · rintro _ ⟨⟨i, c⟩, rfl⟩
      exact d4X_mem_posUnipotent hσ i c
    · obtain ⟨c, rfl⟩ := (mem_posUnipotent_d4_iff hσ y).1 hy
      exact prod6_mem (d4Gen hσ) fun j => Subgroup.subset_closure ⟨⟨j, c j⟩, rfl⟩
  have hθg : ∀ (i : Fin 6) (c : d43Par σ i),
      θ ⟨d4X hσ i c, Subgroup.subset_closure ⟨⟨i, c⟩, rfl⟩⟩ = ψ i c := fun i c => hθ ⟨i, c⟩
  have hθprod : ∀ (c : ∀ i, d43Par σ i) (s : ↥(d4Gen hσ)),
      (s : twistedGroup σ) = prod6 (fun j => d4X hσ j (c j)) →
        θ s = prod6 (fun j => ψ j (c j)) := by
    intro c s hs
    have hs' : s = prod6 (fun j => (⟨d4X hσ j (c j),
        Subgroup.subset_closure ⟨⟨j, c j⟩, rfl⟩⟩ : ↥(d4Gen hσ))) := by
      apply Subtype.ext
      simpa [prod6] using hs
    rw [hs']
    simp only [prod6, map_mul, hθg]
  have hθinj : Function.Injective θ := by
    intro s s' hss
    have hs : (s : twistedGroup σ) ∈ posUnipotent (g2Shape (twistedX σ)) := hclos ▸ s.2
    have hs' : (s' : twistedGroup σ) ∈ posUnipotent (g2Shape (twistedX σ)) := hclos ▸ s'.2
    obtain ⟨c, hc⟩ := (mem_posUnipotent_d4_iff hσ _).1 hs
    obtain ⟨c', hc'⟩ := (mem_posUnipotent_d4_iff hσ _).1 hs'
    have e : prod6 (fun j => ψ j (c j)) = prod6 (fun j => ψ j (c' j)) := by
      rw [← hθprod c s hc, ← hθprod c' s' hc', hss]
    have hcc : c = c' := funext fun j =>
      h.inj j (congrFun (rank6_unique D (fun i => h.mem i (c i)) (fun i => h.mem i (c' i)) e) j)
    apply Subtype.ext
    rw [hc, hc', hcc]
  have hθU : ∀ s : ↥(d4Gen hσ), θ s ∈ D.U := by
    intro s
    have hs : (s : twistedGroup σ) ∈ posUnipotent (g2Shape (twistedX σ)) := hclos ▸ s.2
    obtain ⟨c, hc⟩ := (mem_posUnipotent_d4_iff hσ _).1 hs
    rw [hθprod c s hc]
    exact prod6_mem D.U fun j =>
      D.root_le_U (by omega) (by have := j.isLt; omega) (h.mem j (c j))
  have hθsurj : ∀ y ∈ D.U, ∃ s : ↥(d4Gen hσ), θ s = y := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := exists_prod6_of_mem_U D hy
    choose c hc using fun i => h.surj i (a i) (ha i)
    refine ⟨⟨prod6 (fun j => d4X hσ j (c j)),
      prod6_mem (d4Gen hσ) fun j => Subgroup.subset_closure ⟨⟨j, c j⟩, rfl⟩⟩, ?_⟩
    rw [hθprod c _ rfl]
    congr 1
    funext j
    exact hc j
  let θ' : ↥(d4Gen hσ) →* D.U := θ.codRestrict D.U hθU
  have hθ'bij : Function.Bijective θ' := by
    refine ⟨fun s s' hss => hθinj (congrArg Subtype.val hss), fun y => ?_⟩
    obtain ⟨s, hs⟩ := hθsurj y y.2
    exact ⟨s, Subtype.ext hs⟩
  let Θ : ↥(d4Gen hσ) ≃* D.U := MulEquiv.ofBijective θ' hθ'bij
  let U₀ := posUnipotent (g2Shape (twistedX σ))
  let π := hexProj ↥(twistedGroup σ)
  have hinjU : ∀ u v : twistedGroup σ, u ∈ U₀ → v ∈ U₀ → π u = π v → u = v :=
    fun u v hu hv huv => hexProj_injOn (twistedData σ hσ) hu hv huv
  have hπbij : Function.Bijective (π.subgroupMap U₀) :=
    ⟨fun u v huv => Subtype.ext (hinjU u v u.2 v.2 (congrArg Subtype.val huv)),
      π.subgroupMap_surjective U₀⟩
  let e₂ : U₀ ≃* U₀.map π := MulEquiv.ofBijective (π.subgroupMap U₀) hπbij
  let φ : D.U ≃* (d4ModelSystem σ hq hK hσq).U :=
    Θ.symm.trans ((MulEquiv.subgroupCongr hclos).trans
      (e₂.trans (MulEquiv.subgroupCongr (d4ModelSystem_U σ hq hK hσq).symm)))
  refine ⟨φ, fun i h1 h6 x => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, (k : ℤ) + 1 = i :=
    ⟨⟨(i - 1).toNat, by omega⟩, by simp; omega⟩
  set s := Θ.symm x with hs_def
  have hθs : θ s = (x : G) := by
    have := Θ.apply_symm_apply x
    exact congrArg Subtype.val this
  have hu : (s : twistedGroup σ) ∈ U₀ := by
    show (s : twistedGroup σ) ∈ posUnipotent (g2Shape (twistedX σ))
    rw [← hclos]
    exact s.2
  have hφ : (((φ x : (d4ModelSystem σ hq hK hσq).U)) : twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) =
      π (s : twistedGroup σ) := rfl
  have hA : (x : G) ∈ D.root ((k : ℤ) + 1) ↔
      (s : twistedGroup σ) ∈ hexGroup (twistedX σ) ((k : ℤ) + 1) := by
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := h.surj k x hx
      have hsd : s = ⟨d4X hσ k d, Subgroup.subset_closure ⟨⟨k, d⟩, rfl⟩⟩ := by
        apply hθinj
        rw [hθs, hθg k d, hd]
      rw [hsd]
      exact (mem_hexGroup_d4_iff hσ k _).2 ⟨d, rfl⟩
    · intro hx
      obtain ⟨d, hd⟩ := (mem_hexGroup_d4_iff hσ k _).1 hx
      have hsd : s = ⟨d4X hσ k d, Subgroup.subset_closure ⟨⟨k, d⟩, rfl⟩⟩ := Subtype.ext hd.symm
      rw [← hθs, hsd, hθg]
      exact h.mem k d
  have hB : π (s : twistedGroup σ) ∈ (d4ModelSystem σ hq hK hσq).root ((k : ℤ) + 1) ↔
      (s : twistedGroup σ) ∈ hexGroup (twistedX σ) ((k : ℤ) + 1) := by
    rw [d4ModelSystem_root, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, hvu⟩
      have hv' : v ∈ U₀ := hexGroup_le_posUnipotent (by omega) (by have := k.isLt; omega) hv
      have := hinjU v s hv' hu hvu
      rwa [← this]
    · intro hx
      exact ⟨_, hx, rfl⟩
  rw [hφ, hA, hB]

theorem D4Rel.map {G' : Type*} [Group G'] {φ : (Σ γ, d43Par σ γ) → G} {hσ : ∀ c, σ (σ (σ c)) = c}
    (h : D4Rel hσ φ) (f : G →* G') : D4Rel hσ (fun g => f (φ g)) where
  add _ _ _ := by simp only [h.add, map_mul]
  r02 s t := by simp only [← map_commutatorElement, h.r02]
  r24 s t := by simp only [← map_commutatorElement, h.r24]
  r15 s t := by simp only [← map_commutatorElement, h.r15]
  r04 s t := by simp only [← map_commutatorElement, h.r04, map_mul]
  r05 s t := by simp only [← map_commutatorElement, h.r05, map_mul]
  c01 s t := (h.c01 s t).map f
  c03 s t := (h.c03 s t).map f
  c12 s t := (h.c12 s t).map f
  c13 s t := (h.c13 s t).map f
  c14 s t := (h.c14 s t).map f
  c23 s t := (h.c23 s t).map f
  c25 s t := (h.c25 s t).map f
  c34 s t := (h.c34 s t).map f
  c35 s t := (h.c35 s t).map f
  c45 s t := (h.c45 s t).map f

theorem d4X_injective
    (hσ : ∀ c, σ (σ (σ c)) = c) (i : Fin 6) : Function.Injective (d4X hσ i) :=
  fun _ _ h => d4Sgn_injective i (d43XE_injective i (congrArg Subtype.val h))

theorem d4Coords_model
    [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) :
    D4Coords (d4ModelSystem σ hq hK hσq) (sigma_three_of_card hK hσq)
      (fun (i : Fin 6) (c : d43Par σ i) =>
        hexProj ↥(twistedGroup σ) (d4X (sigma_three_of_card hK hσq) i c)) where
  rel := (d4Rel_model (sigma_three_of_card hK hσq)).map (hexProj ↥(twistedGroup σ))
  mem i c := by
    rw [d4ModelSystem_root]
    exact ⟨d4X (sigma_three_of_card hK hσq) i c, d4X_mem _ i c, rfl⟩
  inj i c d h :=
    d4X_injective (sigma_three_of_card hK hσq) i
      (hexProj_injOn (twistedData σ (sigma_three_of_card hK hσq))
        (d4X_mem_posUnipotent _ i c) (d4X_mem_posUnipotent _ i d) h)
  surj i y hy := by
    rw [d4ModelSystem_root] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := (mem_hexGroup_d4_iff (sigma_three_of_card hK hσq) i v).1 hv
    exact ⟨c, rfl⟩

end Match

section Leaves

open CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4 CFSG.Timmesfeld.RankTwo
  CFSG.LieType.Steinberg.TwistedD4

@[expose] def HexCoordD4p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (D : RankTwoSystem G 6) (p q : ℕ),
    3 ≤ q → p.Prime → Odd q →
    (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card (D.root i) = if i % 2 = 1 then q ^ 3 else q) →
      PStruct p D.U D.root →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
        (hσq : ∀ c, σ c = c ^ q) (ψ : ∀ i : Fin 6, d43Par σ i → G),
        D4Coords D (sigma_three_of_card hK hσq) ψ

theorem hexMatchD4p_of_coord
    (h : HexCoordD4p) : HexMatchD4p := by
  intro G _ _ _ D p q hq hp hodd hD hP
  obtain ⟨K, _, _, σ, hK, hσq, ψ, hψ⟩ := h G D p q hq hp hodd hD hP
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσq, uMatch_of_d4Coords (by omega) hK hσq hψ⟩

@[expose] def HexCoordD4s : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (H : Subgroup G) (r₁ r₂ : G)
    (U : Subgroup G) (root : ℤ → Subgroup G) (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (p q : ℕ), 3 ≤ q → p.Prime → Odd q →
      RootOrdersD4 root q → PStruct p U root → SL2At H R.N root 1 → SL2At H R.N root 4 →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
        (hσq : ∀ c, σ c = c ^ q) (ψ : ∀ i : Fin 6, d43Par σ i → G),
        D4Coords (R.toPre hgen).toSystemOfSimple (sigma_three_of_card hK hσq) ψ ∨
          D4Coords (R.toPre hgen).toSystemOfSimple.rev (sigma_three_of_card hK hσq) ψ

theorem hexMatchD4s_of_coord
    (h : HexCoordD4s) : HexMatchD4s := by
  intro G _ _ _ H r₁ r₂ U root R hgen p q hq hp hodd hD hP h1 h4
  obtain ⟨K, _, _, σ, hK, hσq, ψ, hψ⟩ := h G H r₁ r₂ U root R hgen p q hq hp hodd hD hP h1 h4
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσq,
    hψ.imp (uMatch_of_d4Coords (by omega) hK hσq) (uMatch_of_d4Coords (by omega) hK hσq)⟩

end Leaves


end CFSG.GH74.GLS.Stage4.Hex