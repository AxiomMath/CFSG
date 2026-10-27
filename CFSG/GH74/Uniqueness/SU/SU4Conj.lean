module

public import CFSG.GH74.Uniqueness.SU.SU4Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G]

theorem mem_conjSub {g : G} {E : Subgroup G} {y : G} : y ∈ conjSub g E ↔ g⁻¹ * y * g ∈ E := by
  unfold conjSub
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using he
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjSub_one (E : Subgroup G) : conjSub 1 E = E := by
  ext y
  simp [mem_conjSub]

theorem conjSub_mul (g h : G) (E : Subgroup G) : conjSub (g * h) E = conjSub g (conjSub h E) := by
  ext y
  simp only [mem_conjSub, mul_inv_rev]
  rw [show h⁻¹ * (g⁻¹ * y * g) * h = h⁻¹ * g⁻¹ * y * (g * h) by group]

theorem conjSub_inv_conjSub (g : G) (E : Subgroup G) : conjSub g⁻¹ (conjSub g E) = E := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (E : Subgroup G) : conjSub g (conjSub g⁻¹ E) = E := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_le_conjSub_iff {g : G} {E F : Subgroup G} : conjSub g E ≤ conjSub g F ↔ E ≤ F := by
  constructor
  · intro h x hx
    have := h (mem_conjSub.mpr (show g⁻¹ * (g * x * g⁻¹) * g ∈ E by simpa [mul_assoc] using hx))
    simpa [mem_conjSub, mul_assoc] using this
  · intro h y hy
    rw [mem_conjSub] at hy ⊢
    exact h hy

theorem conjSub_injective (g : G) : Function.Injective (conjSub g) := fun _ _ h =>
  le_antisymm (conjSub_le_conjSub_iff.mp h.le) (conjSub_le_conjSub_iff.mp h.ge)

theorem conjSub_mono {g : G} {E F : Subgroup G} (h : E ≤ F) : conjSub g E ≤ conjSub g F :=
  conjSub_le_conjSub_iff.mpr h

theorem mem_conjSub_of_mem {g : G} {E : Subgroup G} {y : G} (hy : y ∈ E) :
    g * y * g⁻¹ ∈ conjSub g E := by
  rw [mem_conjSub]
  simpa [mul_assoc] using hy

theorem conjSub_self_of_mem {g : G} {X : Subgroup G} (hg : g ∈ X) : conjSub g X = X := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro h
    have := X.mul_mem (X.mul_mem hg h) (X.inv_mem hg)
    simpa [mul_assoc] using this
  · intro h
    exact X.mul_mem (X.mul_mem (X.inv_mem hg) h) hg

theorem conjSub_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ := by
  ext y
  simp [mem_conjSub]

theorem conjSub_inf (g : G) (E F : Subgroup G) : conjSub g (E ⊓ F) = conjSub g E ⊓ conjSub g F := by
  ext y
  simp [mem_conjSub]

theorem card_conjSub (g : G) (E : Subgroup G) : Nat.card (conjSub g E) = Nat.card E := by
  unfold conjSub
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_conjSub {p : ℕ} {g : G} {E : Subgroup G} (h : IsPGroup p E) :
    IsPGroup p (conjSub g E) := by
  unfold conjSub
  exact h.map _

theorem isElemAbelian_conjSub {p : ℕ} {g : G} {E : Subgroup G} (h : Open.IsElemAbelian p E) :
    Open.IsElemAbelian p (conjSub g E) := by
  rw [SU1.isElemAbelian_iff] at h ⊢
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [mem_conjSub] at ha hb
    have := h.1 _ ha _ hb
    calc a * b = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group
  · rw [mem_conjSub] at ha
    have := h.2 _ ha
    have h1 : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    calc a ^ p = (g * (g⁻¹ * a * g) * g⁻¹) ^ p := by rw [← h1]
      _ = g * (g⁻¹ * a * g) ^ p * g⁻¹ := conj_pow
      _ = 1 := by rw [this]; group

variable {G : Type} [Group G]

theorem conj_comm_iff (g a b : G) :
    a * b = b * a ↔ (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
  constructor
  · intro h
    calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group
  · intro h
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
      _ = b * a := by group

theorem conj_comm_iff' (g e y : G) :
    e * (g⁻¹ * y * g) = (g⁻¹ * y * g) * e ↔ (g * e * g⁻¹) * y = y * (g * e * g⁻¹) := by
  rw [conj_comm_iff g e (g⁻¹ * y * g)]
  have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [h1]

theorem conjSub_centralizer (g : G) (E : Subgroup G) :
    conjSub g (centralizer (E : Set G)) = centralizer ((conjSub g E : Subgroup G) : Set G) := by
  ext y
  rw [mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h e' he'
    rw [SetLike.mem_coe, mem_conjSub] at he'
    have h1 := h _ he'
    have h2 := (conj_comm_iff' g (g⁻¹ * e' * g) y).mp h1
    simpa [mul_assoc] using h2
  · intro h e he
    have h1 := h (g * e * g⁻¹) (mem_conjSub_of_mem he)
    exact (conj_comm_iff' g e y).mpr h1

theorem conjSub_centralizer_singleton (g x : G) :
    conjSub g (centralizer ({x} : Set G)) = centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have := conj_comm_iff' g x y
  exact ⟨fun h => (this.mp h.symm).symm, fun h => (this.mpr h.symm).symm⟩

theorem conjSub_normalizer (g : G) (E : Subgroup G) :
    conjSub g (normalizer (E : Set G)) = normalizer ((conjSub g E : Subgroup G) : Set G) := by
  ext y
  rw [mem_conjSub, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h z
    have hz := h (g⁻¹ * z * g)
    rw [mem_conjSub, mem_conjSub]
    have e : g⁻¹ * (y * z * y⁻¹) * g = (g⁻¹ * y * g) * (g⁻¹ * z * g) * (g⁻¹ * y * g)⁻¹ := by group
    rw [e]
    exact hz
  · intro h z
    have hz := h (g * z * g⁻¹)
    rw [mem_conjSub, mem_conjSub] at hz
    have e1 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have e : g⁻¹ * (y * (g * z * g⁻¹) * y⁻¹) * g = (g⁻¹ * y * g) * z * (g⁻¹ * y * g)⁻¹ := by group
    rw [e1, e] at hz
    exact hz

variable {G : Type} [Group G]

theorem isFour_conjSub {g : G} {X Y V : Subgroup G} (h : conjSub g X ≤ Y) (hV : IsFour X V) :
    IsFour Y (conjSub g V) :=
  ⟨(conjSub_mono hV.1).trans h, isElemAbelian_conjSub hV.2.1, by rw [card_conjSub]; exact hV.2.2⟩

private def conjHom (g : G) {X Y : Subgroup G} (h : conjSub g X ≤ Y) :
    SU1.Ep2Graph 2 X →g SU1.Ep2Graph 2 Y where
  toFun A := ⟨conjSub g A.1, isFour_conjSub h A.2⟩
  map_rel' := by
    intro A B hAB
    refine ⟨?_, ?_⟩
    · intro hEq
      apply hAB.1
      exact Subtype.ext (conjSub_injective g (congrArg Subtype.val hEq))
    · intro a ha b hb
      have ha' : g⁻¹ * a * g ∈ A.1 := mem_conjSub.mp ha
      have hb' : g⁻¹ * b * g ∈ B.1 := mem_conjSub.mp hb
      have := hAB.2 _ ha' _ hb'
      exact (conj_comm_iff g⁻¹ a b).mpr (by simpa using this)

theorem mem_compSet_conj_of_le {g : G} {X Y U E : Subgroup G} (h : conjSub g X ≤ Y)
    (hE : E ∈ compSet X U) : conjSub g E ∈ compSet Y (conjSub g U) := by
  obtain ⟨hU, hE', hr⟩ := hE
  exact ⟨isFour_conjSub h hU, isFour_conjSub h hE', hr.map (conjHom g h)⟩

theorem mem_compSet_conj {g : G} {X Y U E : Subgroup G} (h : conjSub g X = Y) :
    E ∈ compSet X U ↔ conjSub g E ∈ compSet Y (conjSub g U) := by
  constructor
  · exact mem_compSet_conj_of_le h.le
  · intro hE
    have h' : conjSub g⁻¹ Y ≤ X := by rw [← h, conjSub_inv_conjSub]
    have := mem_compSet_conj_of_le h' hE
    simpa [conjSub_inv_conjSub] using this

theorem isFour_of_mem_compSet_left {X U E : Subgroup G} (h : E ∈ compSet X U) : IsFour X U := h.1

theorem isFour_of_mem_compSet {X U E : Subgroup G} (h : E ∈ compSet X U) : IsFour X E := h.2.1

theorem mem_compSet_self {X U : Subgroup G} (hU : IsFour X U) : U ∈ compSet X U :=
  ⟨hU, hU, SimpleGraph.Reachable.refl _⟩

theorem compSet_symm {X U E : Subgroup G} (h : E ∈ compSet X U) : U ∈ compSet X E :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem compSet_trans {X U E F : Subgroup G} (h1 : E ∈ compSet X U) (h2 : F ∈ compSet X E) :
    F ∈ compSet X U :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

theorem mem_compSet_of_commute {X U E : Subgroup G} (hU : IsFour X U) (hE : IsFour X E)
    (h : ∀ a ∈ U, ∀ b ∈ E, a * b = b * a) : E ∈ compSet X U :=
  ⟨hU, hE, SU1.reachable_of_commute (A := ⟨U, hU⟩) (B := ⟨E, hE⟩) h⟩

theorem isIsolatedVertex_iff {X V : Subgroup G} :
    IsIsolatedVertex X V ↔ IsFour X V ∧ ∀ B : Subgroup G, IsFour X B →
      (∀ a ∈ V, ∀ b ∈ B, a * b = b * a) → B = V := by
  constructor
  · rintro ⟨hV, hiso⟩
    refine ⟨hV, fun B hB hc => ?_⟩
    by_contra hne
    exact hiso ⟨B, hB⟩ ⟨fun h => hne (congrArg Subtype.val h).symm, hc⟩
  · rintro ⟨hV, h⟩
    refine ⟨hV, fun B hAB => ?_⟩
    exact hAB.1 (Subtype.ext (h B.1 B.2 hAB.2).symm)

theorem IsIsolatedVertex.isFour {X V : Subgroup G} (h : IsIsolatedVertex X V) : IsFour X V :=
  (isIsolatedVertex_iff.mp h).1

theorem IsIsolatedVertex.eq_of_commute {X V B : Subgroup G} (h : IsIsolatedVertex X V)
    (hB : IsFour X B) (hc : ∀ a ∈ V, ∀ b ∈ B, a * b = b * a) : B = V :=
  (isIsolatedVertex_iff.mp h).2 B hB hc

theorem IsIsolatedVertex.mono {X Y V : Subgroup G} (hYX : Y ≤ X) (hVY : V ≤ Y)
    (hV : IsIsolatedVertex X V) : IsIsolatedVertex Y V := by
  rw [isIsolatedVertex_iff] at hV ⊢
  obtain ⟨hV4, h⟩ := hV
  exact ⟨⟨hVY, hV4.2⟩, fun B hB hc => h B ⟨hB.1.trans hYX, hB.2⟩ hc⟩

theorem isIsolatedVertex_conjSub {g : G} {X Y V : Subgroup G} (h : conjSub g X = Y)
    (hV : IsIsolatedVertex X V) : IsIsolatedVertex Y (conjSub g V) := by
  rw [isIsolatedVertex_iff] at hV ⊢
  obtain ⟨hV4, hiso⟩ := hV
  refine ⟨isFour_conjSub h.le hV4, fun B hB hc => ?_⟩
  have h' : conjSub g⁻¹ Y ≤ X := by rw [← h, conjSub_inv_conjSub]
  have hB' : IsFour X (conjSub g⁻¹ B) := isFour_conjSub h' hB
  have hcomm : ∀ a ∈ V, ∀ b ∈ conjSub g⁻¹ B, a * b = b * a := by
    intro a ha b hb
    have h1 := hc (g * a * g⁻¹) (mem_conjSub_of_mem ha) (g * b * g⁻¹)
      (by simpa using mem_conjSub.mp hb)
    exact (conj_comm_iff g a b).mpr h1
  have := hiso _ hB' hcomm
  calc B = conjSub g (conjSub g⁻¹ B) := (conjSub_conjSub_inv g B).symm
    _ = conjSub g V := by rw [this]

section Finite

variable [Finite G]

theorem pRank_conjSub_le {p : ℕ} (hp : 1 < p) (g : G) (E : Subgroup G) :
    Open.pRank p (conjSub g E) ≤ Open.pRank p E := by
  obtain ⟨F, hFE, hF, hFc⟩ := SU1.exists_pRank hp (conjSub g E)
  have hF' : conjSub g⁻¹ F ≤ E := by
    have := conjSub_mono (g := g⁻¹) hFE
    rwa [conjSub_inv_conjSub] at this
  exact SU1.le_pRank hp hF' (isElemAbelian_conjSub hF) (by rw [card_conjSub]; exact hFc)

theorem pRank_conjSub {p : ℕ} (hp : 1 < p) (g : G) (E : Subgroup G) :
    Open.pRank p (conjSub g E) = Open.pRank p E := by
  refine le_antisymm (pRank_conjSub_le hp g E) ?_
  have := pRank_conjSub_le hp g⁻¹ (conjSub g E)
  rwa [conjSub_inv_conjSub] at this

omit [Finite G] in
theorem permutesComp_one (U : Subgroup G) : PermutesComp U 1 := by
  intro E hE
  rwa [conjSub_one]

omit [Finite G] in
theorem permutesComp_mul {U : Subgroup G} {g h : G} (hg : PermutesComp U g)
    (hh : PermutesComp U h) : PermutesComp U (g * h) := by
  intro E hE
  rw [conjSub_mul]
  exact hg _ (hh E hE)

omit [Finite G] in
theorem permutesComp_pow {U : Subgroup G} {g : G} (hg : PermutesComp U g) (n : ℕ) :
    PermutesComp U (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact permutesComp_one U
  | succ n ih => rw [pow_succ]; exact permutesComp_mul ih hg

theorem permutesComp_inv {U : Subgroup G} {g : G} (hg : PermutesComp U g) :
    PermutesComp U g⁻¹ := by
  have h1 : g⁻¹ = g ^ (orderOf g - 1) := by
    have hpos : 0 < orderOf g := orderOf_pos g
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [h1]
  exact permutesComp_pow hg _

noncomputable def stabComp (U : Subgroup G) : Subgroup G where
  carrier := {g | PermutesComp U g}
  one_mem' := permutesComp_one U
  mul_mem' := fun hg hh => permutesComp_mul hg hh
  inv_mem' := fun hg => permutesComp_inv hg

theorem mem_stabComp {U : Subgroup G} {g : G} : g ∈ stabComp U ↔ PermutesComp U g := Iff.rfl

omit [Finite G] in
theorem permutesComp_of_mem {U A : Subgroup G} {g : G} (hA : A ∈ compSet ⊤ U)
    (hgA : conjSub g A ∈ compSet ⊤ U) : PermutesComp U g := by
  intro E hE
  have hEA : E ∈ compSet ⊤ A := compSet_trans (compSet_symm hA) hE
  have := mem_compSet_conj_of_le (g := g) (X := ⊤) (Y := ⊤) le_top hEA
  exact compSet_trans hgA this

theorem mem_compSet_of_conj_mem {U E : Subgroup G} {g : G} (hg : PermutesComp U g)
    (hE : conjSub g E ∈ compSet ⊤ U) : E ∈ compSet ⊤ U := by
  have := permutesComp_inv hg _ hE
  simpa [conjSub_inv_conjSub] using this

end Finite

end CFSG.GH74.Uniqueness.SU.SU4
