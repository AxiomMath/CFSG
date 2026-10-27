module

public import CFSG.GH74.GLS.Stage4.HexClass
public import CFSG.GH74.GLS.Stage4.HexModelG2
public import CFSG.Timmesfeld.RankTwo.ModelG2
public import CFSG.LieType.Steinberg.G2

public noncomputable section

open CFSG.GH74.BNPair CFSG.LieType.Universal CFSG.LieType.Steinberg
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section Words

open CFSG.Timmesfeld.GradedPresentation CFSG.Timmesfeld.RankTwo

variable {K : Type*} [CommRing K]

@[expose] def g2WordLtGen : Fin 6 → K → Fin 6 → K → FreeGroup (Σ _ : Fin 6, K)
  | 0, s, 2, t => .of ⟨1, 3 * (s * t)⟩
  | 2, s, 4, t => .of ⟨3, -(3 * (s * t))⟩
  | 1, s, 5, t => .of ⟨3, -(s * t)⟩
  | 0, s, 4, t =>
    .of ⟨1, -(3 * (s ^ 2 * t))⟩ * .of ⟨2, -(2 * (s * t))⟩ * .of ⟨3, -(3 * (s * t ^ 2))⟩
  | 0, s, 5, t =>
    .of ⟨1, t * s ^ 3⟩ * .of ⟨2, t * s ^ 2⟩ * .of ⟨3, -(t ^ 2 * s ^ 3)⟩ * .of ⟨4, -(t * s)⟩
  | _, _, _, _ => 1

@[expose] def g2CmGen : Fin 6 → K → Fin 6 → K → FreeGroup (Σ _ : Fin 6, K) :=
  hexCm (F := fun _ => K) g2WordLtGen

theorem rels_g2CmGen_of {H : Type*} [Group H] {φ : (Σ _ : Fin 6, K) → H}
    (hadd : ∀ i (c d : K), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩)
    (h02 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨2, t⟩⁆ = φ ⟨1, 3 * (s * t)⟩)
    (h24 : ∀ s t, ⁅φ ⟨2, s⟩, φ ⟨4, t⟩⁆ = φ ⟨3, -(3 * (s * t))⟩)
    (h15 : ∀ s t, ⁅φ ⟨1, s⟩, φ ⟨5, t⟩⁆ = φ ⟨3, -(s * t)⟩)
    (h04 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨4, t⟩⁆ =
      φ ⟨1, -(3 * (s ^ 2 * t))⟩ * φ ⟨2, -(2 * (s * t))⟩ * φ ⟨3, -(3 * (s * t ^ 2))⟩)
    (h05 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨5, t⟩⁆ =
      φ ⟨1, t * s ^ 3⟩ * φ ⟨2, t * s ^ 2⟩ * φ ⟨3, -(t ^ 2 * s ^ 3)⟩ * φ ⟨4, -(t * s)⟩)
    (h01 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩)) (h03 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨3, t⟩))
    (h12 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨2, t⟩)) (h13 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨3, t⟩))
    (h14 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨4, t⟩)) (h23 : ∀ s t, Commute (φ ⟨2, s⟩) (φ ⟨3, t⟩))
    (h25 : ∀ s t, Commute (φ ⟨2, s⟩) (φ ⟨5, t⟩)) (h34 : ∀ s t, Commute (φ ⟨3, s⟩) (φ ⟨4, t⟩))
    (h35 : ∀ s t, Commute (φ ⟨3, s⟩) (φ ⟨5, t⟩)) (h45 : ∀ s t, Commute (φ ⟨4, s⟩) (φ ⟨5, t⟩)) :
    ∀ r ∈ rels (g2CmGen (K := K)), FreeGroup.lift φ r = 1 := by
  refine rels_hexCm_of hadd fun i j hij s t => ?_
  have hc : ∀ {a b : H}, Commute a b → ⁅a, b⁆ = FreeGroup.lift φ 1 := fun h => by
    rw [map_one, commutatorElement_eq_one_iff_commute]
    exact h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact hc (h01 s t) | exact hc (h03 s t) | exact hc (h12 s t) | exact hc (h13 s t)
    | exact hc (h14 s t) | exact hc (h23 s t) | exact hc (h25 s t) | exact hc (h34 s t)
    | exact hc (h35 s t) | exact hc (h45 s t)
    | (rw [h02]; simp [g2WordLtGen]) | (rw [h24]; simp [g2WordLtGen])
    | (rw [h15]; simp [g2WordLtGen]) | (rw [h04]; simp [g2WordLtGen])
    | (rw [h05]; simp [g2WordLtGen])

theorem g2CmGen_mem_above (i : Fin 6) (s : K) (j : Fin 6) (t : K) :
    g2CmGen i s j t ∈ above hexHt (max (hexHt i) (hexHt j)) := by
  refine hexCm_mem_above (F := fun _ => K) (fun i j hij s t => ?_) i s j t
  have hg : ∀ (k : Fin 6) (c : K) (m : ℕ), m < hexHt k →
      (FreeGroup.of ⟨k, c⟩ : FreeGroup (Σ _ : Fin 6, K)) ∈ above hexHt m :=
    fun k c m hm => Subgroup.subset_closure ⟨⟨k, c⟩, hm, rfl⟩
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.isValue] at hij ⊢ <;>
    first
    | exact absurd hij (by decide)
    | exact one_mem _
    | exact hg _ _ _ (by decide)
    | exact mul_mem (mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide)))
        (hg _ _ _ (by decide))
    | exact mul_mem (mul_mem (mul_mem (hg _ _ _ (by decide)) (hg _ _ _ (by decide)))
        (hg _ _ _ (by decide))) (hg _ _ _ (by decide))

end Words

section Model

open CFSG.Timmesfeld.GradedPresentation CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem g2X_comm02_gen
    (s t : K) : ⁅g2X 0 s, g2X 2 t⁆ = g2X 1 (3 * (s * t)) := by
  rw [commutator_g2X (fs := [(1, 1, 3, 3)]) (by decide)]
  simp [g2X_eq, g2Pos, mul_assoc]

theorem g2X_comm24_gen
    (s t : K) : ⁅g2X 2 s, g2X 4 t⁆ = g2X 3 (-(3 * (s * t))) := by
  rw [commutator_g2X (fs := [(1, 1, 7, -3)]) (by decide)]
  simp [g2X_eq, g2Pos, mul_assoc]

theorem g2X_comm15_gen
    (s t : K) : ⁅g2X 1 s, g2X 5 t⁆ = g2X 3 (-(s * t)) := by
  rw [commutator_g2X (fs := [(1, 1, 7, -1)]) (by decide)]
  simp [g2X_eq, g2Pos, mul_assoc]

theorem g2X_comm04_gen
    (s t : K) : ⁅g2X 0 s, g2X 4 t⁆ =
    g2X 1 (-(3 * (s ^ 2 * t))) * g2X 2 (-(2 * (s * t))) * g2X 3 (-(3 * (s * t ^ 2))) := by
  rw [commutator_g2X (fs := [(2, 1, 3, -3), (1, 1, 8, -2), (1, 2, 7, -3)]) (by decide)]
  simp [g2X_eq, g2Pos, mul_assoc]

theorem g2X_comm05_gen
    (s t : K) : ⁅g2X 0 s, g2X 5 t⁆ =
    g2X 1 (t * s ^ 3) * g2X 2 (t * s ^ 2) * g2X 3 (-(t ^ 2 * s ^ 3)) * g2X 4 (-(t * s)) := by
  rw [commutator_g2X (fs := [(3, 1, 3, 1), (2, 1, 8, 1), (3, 2, 7, -1), (1, 1, 4, -1)]) (by decide)]
  simp [g2X_eq, g2Pos, mul_assoc, mul_comm]

end Model

section Coords

variable {G : Type*} [Group G] {F : Type*} [Field F]

structure G2Rel (φ : (Σ _ : Fin 6, F) → G) : Prop where
  add : ∀ i (c d : F), φ ⟨i, c + d⟩ = φ ⟨i, c⟩ * φ ⟨i, d⟩
  r02 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨2, t⟩⁆ = φ ⟨1, 3 * (s * t)⟩
  r24 : ∀ s t, ⁅φ ⟨2, s⟩, φ ⟨4, t⟩⁆ = φ ⟨3, -(3 * (s * t))⟩
  r15 : ∀ s t, ⁅φ ⟨1, s⟩, φ ⟨5, t⟩⁆ = φ ⟨3, -(s * t)⟩
  r04 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨4, t⟩⁆ =
    φ ⟨1, -(3 * (s ^ 2 * t))⟩ * φ ⟨2, -(2 * (s * t))⟩ * φ ⟨3, -(3 * (s * t ^ 2))⟩
  r05 : ∀ s t, ⁅φ ⟨0, s⟩, φ ⟨5, t⟩⁆ =
    φ ⟨1, t * s ^ 3⟩ * φ ⟨2, t * s ^ 2⟩ * φ ⟨3, -(t ^ 2 * s ^ 3)⟩ * φ ⟨4, -(t * s)⟩
  c01 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨1, t⟩)
  c03 : ∀ s t, Commute (φ ⟨0, s⟩) (φ ⟨3, t⟩)
  c12 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨2, t⟩)
  c13 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨3, t⟩)
  c14 : ∀ s t, Commute (φ ⟨1, s⟩) (φ ⟨4, t⟩)
  c23 : ∀ s t, Commute (φ ⟨2, s⟩) (φ ⟨3, t⟩)
  c25 : ∀ s t, Commute (φ ⟨2, s⟩) (φ ⟨5, t⟩)
  c34 : ∀ s t, Commute (φ ⟨3, s⟩) (φ ⟨4, t⟩)
  c35 : ∀ s t, Commute (φ ⟨3, s⟩) (φ ⟨5, t⟩)
  c45 : ∀ s t, Commute (φ ⟨4, s⟩) (φ ⟨5, t⟩)

theorem G2Rel.rels {φ : (Σ _ : Fin 6, F) → G} (h : G2Rel φ) :
    ∀ r ∈ CFSG.Timmesfeld.GradedPresentation.rels (g2CmGen (K := F)),
      FreeGroup.lift φ r = 1 :=
  rels_g2CmGen_of h.add h.r02 h.r24 h.r15 h.r04 h.r05 h.c01 h.c03 h.c12 h.c13 h.c14 h.c23 h.c25
    h.c34 h.c35 h.c45

end Coords

theorem g2Rel_model
    (F : Type) [Field F] :
    G2Rel (fun g : Σ _ : Fin 6, F => CFSG.Timmesfeld.RankTwo.g2X g.1 g.2) where
  add i c d := CFSG.Timmesfeld.RankTwo.g2X_add i c d
  r02 := g2X_comm02_gen
  r24 := g2X_comm24_gen
  r15 := g2X_comm15_gen
  r04 := g2X_comm04_gen
  r05 := g2X_comm05_gen
  c01 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 0) (j := 1) (by decide) s t
  c03 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 0) (j := 3) (by decide) s t
  c12 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 1) (j := 2) (by decide) s t
  c13 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 1) (j := 3) (by decide) s t
  c14 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 1) (j := 4) (by decide) s t
  c23 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 2) (j := 3) (by decide) s t
  c25 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 2) (j := 5) (by decide) s t
  c34 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 3) (j := 4) (by decide) s t
  c35 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 3) (j := 5) (by decide) s t
  c45 s t := CFSG.Timmesfeld.RankTwo.commute_g2X (i := 4) (j := 5) (by decide) s t

@[expose] def prod6 {M : Type*} [Monoid M] (f : Fin 6 → M) : M :=
  f 0 * (f 1 * (f 2 * (f 3 * (f 4 * f 5))))

theorem prod6_mem {M : Type*} [Group M] (S : Subgroup M) {f : Fin 6 → M} (h : ∀ i, f i ∈ S) :
    prod6 f ∈ S :=
  mul_mem (h 0) (mul_mem (h 1) (mul_mem (h 2) (mul_mem (h 3) (mul_mem (h 4) (h 5)))))

theorem mem_chainProd_six {X : Type*} [Group X] (A : ℤ → Subgroup X) (y : X) :
    y ∈ chainProd A (intList 1 6) ↔ ∃ a₁ ∈ A 1, ∃ a₂ ∈ A 2, ∃ a₃ ∈ A 3, ∃ a₄ ∈ A 4, ∃ a₅ ∈ A 5,
      ∃ a₆ ∈ A 6, y = a₁ * (a₂ * (a₃ * (a₄ * (a₅ * a₆)))) := by
  have hl : intList 1 6 = [1, 2, 3, 4, 5, 6] := by decide
  rw [hl]
  simp only [chainProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Set.mem_mul,
    Set.mem_one, SetLike.mem_coe]
  constructor
  · rintro ⟨a₁, h₁, _, ⟨a₂, h₂, _, ⟨a₃, h₃, _, ⟨a₄, h₄, _, ⟨a₅, h₅, _, ⟨a₆, h₆, _, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, by simp⟩
  · rintro ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩
    exact ⟨a₁, h₁, _, ⟨a₂, h₂, _, ⟨a₃, h₃, _, ⟨a₄, h₄, _, ⟨a₅, h₅, _, ⟨a₆, h₆, 1, rfl, by simp⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

section R1Model

open CFSG.Timmesfeld.GradedPresentation CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable (F : Type) [Field F]

theorem hexPos_succ (i : Fin 6) : hexPos ((i : ℤ) + 1) = hexRoot i := by
  fin_cases i <;> rfl

theorem mem_hexGroup_g2_iff
    (i : Fin 6) (y : ↥(adjointGroup .G2 F)) :
    y ∈ hexGroup (g2Roots F) ((i : ℤ) + 1) ↔ ∃ c : F, g2X i c = y := by
  have hγ : IsRoot .G2 (hexRoot i) := isRoot_hexRoot i
  show y ∈ rootGroup (rootOperatorFamily .G2) F (hexPos ((i : ℤ) + 1)) ↔ _
  rw [hexPos_succ]
  exact mem_rootGroup_iff hγ y

theorem g2X_mem_posUnipotent
    (i : Fin 6) (c : F) :
    g2X i c ∈ posUnipotent (g2Shape (g2Roots F)) := by
  have h := (mem_hexGroup_g2_iff F i (g2X i c)).2 ⟨c, rfl⟩
  exact hexGroup_le_posUnipotent (by omega) (by omega) h

theorem mem_posUnipotent_g2_iff
    (y : ↥(adjointGroup .G2 F)) :
    y ∈ posUnipotent (g2Shape (g2Roots F)) ↔ ∃ c : Fin 6 → F, y = prod6 (fun i => g2X i (c i)) := by
  constructor
  · intro hy
    have hc := (hexRGD2 (g2Data F)).carrier_eq
    have hy' : y ∈ chainProd (hexGroup (g2Roots F)) (intList 1 6) := by
      have h2 : y ∈ (posUnipotent (g2Shape (g2Roots F)) : Set ↥(adjointGroup .G2 F)) := hy
      rw [hc] at h2
      exact h2
    obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩ := (mem_chainProd_six _ y).1 hy'
    obtain ⟨c₀, rfl⟩ := (mem_hexGroup_g2_iff F 0 a₁).1 (by simpa using h₁)
    obtain ⟨c₁, rfl⟩ := (mem_hexGroup_g2_iff F 1 a₂).1 (by simpa using h₂)
    obtain ⟨c₂, rfl⟩ := (mem_hexGroup_g2_iff F 2 a₃).1 (by simpa using h₃)
    obtain ⟨c₃, rfl⟩ := (mem_hexGroup_g2_iff F 3 a₄).1 (by simpa using h₄)
    obtain ⟨c₄, rfl⟩ := (mem_hexGroup_g2_iff F 4 a₅).1 (by simpa using h₅)
    obtain ⟨c₅, rfl⟩ := (mem_hexGroup_g2_iff F 5 a₆).1 (by simpa using h₆)
    exact ⟨![c₀, c₁, c₂, c₃, c₄, c₅], by simp [prod6]⟩
  · rintro ⟨c, rfl⟩
    exact prod6_mem _ fun i => g2X_mem_posUnipotent F i _

@[expose] def g2Gen
    : Subgroup ↥(adjointGroup .G2 F) :=
  Subgroup.closure (Set.range fun g : Σ _ : Fin 6, F => g2X g.1 g.2)

end R1Model

theorem hexProj_injOn
    {K : Type} [Group K] {X : (Fin 2 → ℤ) → Subgroup K} {n : Fin 2 → K}
    {H : Fin 2 → Subgroup K} (hd : G2Data X n H) {u v : K}
    (hu : u ∈ posUnipotent (g2Shape X)) (hv : v ∈ posUnipotent (g2Shape X))
    (h : hexProj K u = hexProj K v) : u = v := by
  have h1 : u⁻¹ * v ∈ posUnipotent (g2Shape X) ⊓ (hexProj K).ker := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) hv, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [posUnipotent_inf_ker_hexProj hd] at h1
  have : u⁻¹ * v = 1 := h1
  exact inv_mul_eq_one.1 this

section Match

variable {G : Type} [Group G] {F : Type} [Field F]

structure G2Coords (D : RankTwoSystem G 6) (ψ : Fin 6 → F → G) : Prop where
  rel : G2Rel (fun g : Σ _ : Fin 6, F => ψ g.1 g.2)
  mem : ∀ (i : Fin 6) (c : F), ψ i c ∈ D.root ((i : ℤ) + 1)
  inj : ∀ i : Fin 6, Function.Injective (ψ i)
  surj : ∀ (i : Fin 6) (y : G), y ∈ D.root ((i : ℤ) + 1) → ∃ c, ψ i c = y

theorem rank6_unique (D : RankTwoSystem G 6) {a b : Fin 6 → G}
    (ha : ∀ i : Fin 6, a i ∈ D.root ((i : ℤ) + 1)) (hb : ∀ i : Fin 6, b i ∈ D.root ((i : ℤ) + 1))
    (e : prod6 a = prod6 b) : a = b := by
  have hl : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide
  let ext : (Fin 6 → G) → ℤ → G := fun a k =>
    if k = 1 then a 0 else if k = 2 then a 1 else if k = 3 then a 2 else if k = 4 then a 3
      else if k = 5 then a 4 else if k = 6 then a 5 else 1
  have hmem : ∀ (a : Fin 6 → G), (∀ i : Fin 6, a i ∈ D.root ((i : ℤ) + 1)) →
      ∀ k ∈ intList 1 ((6 : ℕ) : ℤ), ext a k ∈ D.root k := by
    intro a ha k hk
    rw [hl] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [ext] using ha 0
    · simpa [ext] using ha 1
    · simpa [ext] using ha 2
    · simpa [ext] using ha 3
    · simpa [ext] using ha 4
    · simpa [ext] using ha 5
  have key := D.roots.unique (ext a) (ext b) (hmem a ha) (hmem b hb) (by
    rw [hl]
    simpa [ext, prod6] using e)
  rw [hl] at key
  funext i
  fin_cases i
  · simpa [ext] using key 1 (by simp)
  · simpa [ext] using key 2 (by simp)
  · simpa [ext] using key 3 (by simp)
  · simpa [ext] using key 4 (by simp)
  · simpa [ext] using key 5 (by simp)
  · simpa [ext] using key 6 (by simp)

theorem exists_prod6_of_mem_U (D : RankTwoSystem G 6) {x : G} (hx : x ∈ D.U) :
    ∃ a : Fin 6 → G, (∀ i : Fin 6, a i ∈ D.root ((i : ℤ) + 1)) ∧ x = prod6 a := by
  have h : x ∈ chainProd D.root (intList 1 ((6 : ℕ) : ℤ)) := by
    rw [← D.roots.carrier_eq]
    exact hx
  have h' : x ∈ chainProd D.root (intList 1 6) := h
  obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, a₅, h₅, a₆, h₆, rfl⟩ := (mem_chainProd_six _ x).1 h'
  refine ⟨![a₁, a₂, a₃, a₄, a₅, a₆], fun i => ?_, by simp [prod6]⟩
  fin_cases i
  · simpa using h₁
  · simpa using h₂
  · simpa using h₃
  · simpa using h₄
  · simpa using h₅
  · simpa using h₆

open CFSG.Timmesfeld.GradedPresentation CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem uMatch_of_g2Coords
    [Finite F] (hF : 3 ≤ Nat.card F) {D : RankTwoSystem G 6}
    {ψ : Fin 6 → F → G} (h : G2Coords D ψ) : UMatch (g2ModelSystem F hF) D := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥(g2Gen F) →* G,
      ∀ g : Σ _ : Fin 6, F, θ ⟨g2X g.1 g.2, Subgroup.subset_closure ⟨g, rfl⟩⟩ = ψ g.1 g.2 :=
    exists_hom (F := fun _ : Fin 6 => F) (cm := g2CmGen (K := F)) (ht := hexHt)
      g2CmGen_mem_above (fun g : Σ _ : Fin 6, F => g2X g.1 g.2) (fun g => ψ g.1 g.2)
      (g2Rel_model F).rels h.rel.rels [0, 5, 4, 2, 1, 3] g2X_prod_injective
  have hclos : g2Gen F = posUnipotent (g2Shape (g2Roots F)) := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun y hy => ?_
    · rintro _ ⟨⟨i, c⟩, rfl⟩
      exact g2X_mem_posUnipotent F i c
    · obtain ⟨c, rfl⟩ := (mem_posUnipotent_g2_iff F y).1 hy
      exact prod6_mem (g2Gen F) fun j => Subgroup.subset_closure ⟨⟨j, c j⟩, rfl⟩
  have hθg : ∀ (i : Fin 6) (c : F),
      θ ⟨g2X i c, Subgroup.subset_closure ⟨⟨i, c⟩, rfl⟩⟩ = ψ i c := fun i c => hθ ⟨i, c⟩
  have hθprod : ∀ (c : Fin 6 → F) (s : ↥(g2Gen F)), (s : ↥(adjointGroup .G2 F)) = prod6 (fun j => g2X j (c j)) →
      θ s = prod6 (fun j => ψ j (c j)) := by
    intro c s hs
    have hs' : s = prod6 (fun j => (⟨g2X j (c j), Subgroup.subset_closure ⟨⟨j, c j⟩, rfl⟩⟩ : ↥(g2Gen F))) := by
      apply Subtype.ext
      simpa [prod6] using hs
    rw [hs']
    simp only [prod6, map_mul, hθg]
  have hθinj : Function.Injective θ := by
    intro s s' hss
    have hs : (s : ↥(adjointGroup .G2 F)) ∈ posUnipotent (g2Shape (g2Roots F)) := hclos ▸ s.2
    have hs' : (s' : ↥(adjointGroup .G2 F)) ∈ posUnipotent (g2Shape (g2Roots F)) := hclos ▸ s'.2
    obtain ⟨c, hc⟩ := (mem_posUnipotent_g2_iff F _).1 hs
    obtain ⟨c', hc'⟩ := (mem_posUnipotent_g2_iff F _).1 hs'
    have e : prod6 (fun j => ψ j (c j)) = prod6 (fun j => ψ j (c' j)) := by
      rw [← hθprod c s hc, ← hθprod c' s' hc', hss]
    have hcc : c = c' := funext fun j =>
      h.inj j (congrFun (rank6_unique D (fun i => h.mem i (c i)) (fun i => h.mem i (c' i)) e) j)
    apply Subtype.ext
    rw [hc, hc', hcc]
  have hθU : ∀ s : ↥(g2Gen F), θ s ∈ D.U := by
    intro s
    have hs : (s : ↥(adjointGroup .G2 F)) ∈ posUnipotent (g2Shape (g2Roots F)) := hclos ▸ s.2
    obtain ⟨c, hc⟩ := (mem_posUnipotent_g2_iff F _).1 hs
    rw [hθprod c s hc]
    exact prod6_mem D.U fun j =>
      D.root_le_U (by omega) (by have := j.isLt; omega) (h.mem j (c j))
  have hθsurj : ∀ y ∈ D.U, ∃ s : ↥(g2Gen F), θ s = y := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := exists_prod6_of_mem_U D hy
    choose c hc using fun i => h.surj i (a i) (ha i)
    refine ⟨⟨prod6 (fun j => g2X j (c j)),
      prod6_mem (g2Gen F) fun j => Subgroup.subset_closure ⟨⟨j, c j⟩, rfl⟩⟩, ?_⟩
    rw [hθprod c _ rfl]
    congr 1
    funext j
    exact hc j
  let θ' : ↥(g2Gen F) →* D.U := θ.codRestrict D.U hθU
  have hθ'bij : Function.Bijective θ' := by
    refine ⟨fun s s' hss => hθinj (congrArg Subtype.val hss), fun y => ?_⟩
    obtain ⟨s, hs⟩ := hθsurj y y.2
    exact ⟨s, Subtype.ext hs⟩
  let Θ : ↥(g2Gen F) ≃* D.U := MulEquiv.ofBijective θ' hθ'bij
  let U₀ := posUnipotent (g2Shape (g2Roots F))
  let π := hexProj ↥(adjointGroup .G2 F)
  have hinjU : ∀ u v : ↥(adjointGroup .G2 F), u ∈ U₀ → v ∈ U₀ → π u = π v → u = v :=
    fun u v hu hv huv => hexProj_injOn (g2Data F) hu hv huv
  have hπbij : Function.Bijective (π.subgroupMap U₀) := by
    refine ⟨fun u v huv => Subtype.ext (hinjU u v u.2 v.2 (congrArg Subtype.val huv)),
      π.subgroupMap_surjective U₀⟩
  let e₂ : U₀ ≃* U₀.map π := MulEquiv.ofBijective (π.subgroupMap U₀) hπbij
  let φ : D.U ≃* (g2ModelSystem F hF).U :=
    Θ.symm.trans ((MulEquiv.subgroupCongr hclos).trans
      (e₂.trans (MulEquiv.subgroupCongr (g2ModelSystem_U hF).symm)))
  refine ⟨φ, fun i h1 h6 x => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, (k : ℤ) + 1 = i :=
    ⟨⟨(i - 1).toNat, by omega⟩, by simp; omega⟩
  set s := Θ.symm x with hs_def
  have hθs : θ s = (x : G) := by
    have := Θ.apply_symm_apply x
    exact congrArg Subtype.val this
  have hu : (s : ↥(adjointGroup .G2 F)) ∈ U₀ := by
    show (s : ↥(adjointGroup .G2 F)) ∈ posUnipotent (g2Shape (g2Roots F))
    rw [← hclos]
    exact s.2
  have hφ : (((φ x : (g2ModelSystem F hF).U)) : AdjointQuotient .G2 F) = π (s : ↥(adjointGroup .G2 F)) :=
    rfl
  have hA : (x : G) ∈ D.root ((k : ℤ) + 1) ↔
      (s : ↥(adjointGroup .G2 F)) ∈ hexGroup (g2Roots F) ((k : ℤ) + 1) := by
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := h.surj k x hx
      have hsd : s = ⟨g2X k d, Subgroup.subset_closure ⟨⟨k, d⟩, rfl⟩⟩ := by
        apply hθinj
        rw [hθs, hθg k d, hd]
      rw [hsd]
      exact (mem_hexGroup_g2_iff F k _).2 ⟨d, rfl⟩
    · intro hx
      obtain ⟨d, hd⟩ := (mem_hexGroup_g2_iff F k _).1 hx
      have hsd : s = ⟨g2X k d, Subgroup.subset_closure ⟨⟨k, d⟩, rfl⟩⟩ := Subtype.ext hd.symm
      rw [← hθs, hsd, hθg]
      exact h.mem k d
  have hB : π (s : ↥(adjointGroup .G2 F)) ∈ (g2ModelSystem F hF).root ((k : ℤ) + 1) ↔
      (s : ↥(adjointGroup .G2 F)) ∈ hexGroup (g2Roots F) ((k : ℤ) + 1) := by
    rw [g2ModelSystem_root hF, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, hvu⟩
      have hv' : v ∈ U₀ := hexGroup_le_posUnipotent (by omega) (by have := k.isLt; omega) hv
      have := hinjU v s hv' hu hvu
      rwa [← this]
    · intro hx
      exact ⟨_, hx, rfl⟩
  rw [hφ, hA, hB]

end Match

end CFSG.GH74.GLS.Stage4.Hex
