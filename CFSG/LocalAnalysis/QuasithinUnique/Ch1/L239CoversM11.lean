module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversBasic
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Mathieu.M11
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Covers

open CFSG.Sporadic.Bridge TauCeti
open CFSG.Sporadic.Bridge.M11 (generatorCount_eq finite_card_le img img_val alpha relators_eval
  nonempty_mulEquiv)

@[expose] def m11R1 : List Letter :=
  [(1, true), (0, false), (0, false), (0, false), (1, true), (0, false), (1, true), (1, true),
    (1, true)]

@[expose] def m11R2 : List Letter :=
  [(1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, true), (0, true),
    (1, false), (0, true)]

@[expose] def natLetter (l : Letter) : ℕ × Bool := (l.1.val, l.2)

theorem m11_relatorLetters :
    Sporadic.m11Presentation.relatorLetters =
      [m11R1.map natLetter, m11R2.map natLetter] := by
  rw [Sporadic.m11Presentation_relatorLetters]
  rfl

theorem expsum_m11R1 : expsum 0 m11R1 = -4 ∧ expsum 1 m11R1 = 5 := by decide

theorem expsum_m11R2 : expsum 0 m11R2 = 1 ∧ expsum 1 m11R2 = -1 := by decide

section Presented

theorem wordProd_map_natLetter {X : Type*} [Group X] (img : ℕ → X) (y : Fin 2 → X)
    (himg : ∀ i : Fin 2, img i.val = y i) (w : List Letter) :
    wordProd img (w.map natLetter) = wordVal y w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have h : wordProd img (natLetter l :: w.map natLetter) =
        (if l.2 then img l.1.val else (img l.1.val)⁻¹) * wordProd img (w.map natLetter) := by
      simp [wordProd, natLetter]
    rw [List.map_cons, h, ih, wordVal_cons, himg]
    rfl

theorem p11_rel {X : Type*} [Group X] (y : Fin 2 → X) (h1 : wordVal y m11R1 = 1)
    (h2 : wordVal y m11R2 = 1) :
    ∀ v ∈ Sporadic.m11Presentation.relatorLetters,
      wordProd (fun i => if h : i < 2 then y ⟨i, h⟩ else 1) v = 1 := by
  intro v hv
  rw [m11_relatorLetters] at hv
  have himg : ∀ i : Fin 2, (fun i => if h : i < 2 then y ⟨i, h⟩ else 1) i.val = y i := by
    intro i
    have hl := i.isLt
    simp only [hl, ↓reduceDIte]
  rcases List.mem_pair.mp hv with rfl | rfl
  · rw [wordProd_map_natLetter _ y himg]; exact h1
  · rw [wordProd_map_natLetter _ y himg]; exact h2

noncomputable def p11Hom {X : Type*} [Group X] (y : Fin 2 → X) (h1 : wordVal y m11R1 = 1)
    (h2 : wordVal y m11R2 = 1) : Sporadic.m11Presentation.Group →* X :=
  PresentedGroup.toGroup
    (f := fun i : Fin Sporadic.m11Presentation.generatorCount =>
      (fun j : ℕ => if h : j < 2 then y ⟨j, h⟩ else 1) i.val)
    (lift_relator Sporadic.m11Presentation _ (p11_rel y h1 h2))

theorem p11Hom_of
    {X : Type*} [Group X] (y : Fin 2 → X) (h1 : wordVal y m11R1 = 1)
    (h2 : wordVal y m11R2 = 1) (i : Fin Sporadic.m11Presentation.generatorCount) :
    p11Hom y h1 h2 (PresentedGroup.of i) = y (Fin.cast generatorCount_eq i) := by
  have hi : i.val < 2 := by
    have := generatorCount_eq
    omega
  unfold p11Hom
  rw [PresentedGroup.toGroup.of]
  simp only [hi, ↓reduceDIte]
  rfl

theorem p11Hom_range
    {X : Type*} [Group X] (y : Fin 2 → X) (h1 : wordVal y m11R1 = 1)
    (h2 : wordVal y m11R2 = 1) : (p11Hom y h1 h2).range = Subgroup.closure (Set.range y) := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨Fin.cast generatorCount_eq i, (p11Hom_of y h1 h2 i).symm⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of (Fin.cast generatorCount_eq.symm i), by
      rw [p11Hom_of]; rfl⟩

theorem card_closure_le
    {X : Type*} [Group X] (y : Fin 2 → X) (h1 : wordVal y m11R1 = 1)
    (h2 : wordVal y m11R2 = 1) : Nat.card (Subgroup.closure (Set.range y)) ≤ 7920 := by
  rw [← p11Hom_range y h1 h2]
  obtain ⟨hfin, hcard⟩ := finite_card_le
  have := hfin
  exact (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)).trans hcard

theorem finite_closure
    {X : Type*} [Group X] (y : Fin 2 → X) (h1 : wordVal y m11R1 = 1)
    (h2 : wordVal y m11R2 = 1) : Finite (Subgroup.closure (Set.range y)) := by
  rw [← p11Hom_range y h1 h2]
  obtain ⟨hfin, -⟩ := finite_card_le
  exact Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem p11_simple_card :
    IsSimpleGroup Sporadic.m11Presentation.Group ∧
      Nat.card Sporadic.m11Presentation.Group = 7920 := by
  obtain ⟨e⟩ := nonempty_mulEquiv
  have hs : IsSimpleGroup ↥Blueprint.NativeSporadic.M11 :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  rw [← CFSG.Sporadic.Mathieu.card_M11]
  exact (Nat.card_congr e.toEquiv).symm

theorem card_closure_eq
    {X : Type*} [Group X] (y : Fin 2 → X) (h1 : wordVal y m11R1 = 1)
    (h2 : wordVal y m11R2 = 1) (hy : y 0 ≠ 1) :
    Nat.card (Subgroup.closure (Set.range y)) = 7920 := by
  obtain ⟨hs, hc⟩ := p11_simple_card
  have hinj : Function.Injective (p11Hom y h1 h2) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hs.eq_bot_or_eq_top_of_normal (p11Hom y h1 h2).ker with h | h
    · exact h
    · exfalso
      apply hy
      have hk : p11Hom y h1 h2 (PresentedGroup.of (Fin.cast generatorCount_eq.symm 0)) = 1 := by
        have hmem : PresentedGroup.of (Fin.cast generatorCount_eq.symm (0 : Fin 2)) ∈
            (p11Hom y h1 h2).ker := by
          rw [h]; trivial
        exact hmem
      rw [p11Hom_of] at hk
      simpa using hk
  rw [← p11Hom_range y h1 h2, ← hc]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Presented

section Lifts

variable {E H : Type*} [Group E] [Group H]

theorem m11_exists_lifts (π : E →* H) (hπ : Function.Surjective π)
    (hz : ∀ z, π z = 1 → z ∈ Subgroup.center E) (h2 : ∀ z, π z = 1 → z * z = 1)
    (y : Fin 2 → H) (hy1 : wordVal y m11R1 = 1) (hy2 : wordVal y m11R2 = 1) :
    ∃ x : Fin 2 → E, (∀ i, π (x i) = y i) ∧ wordVal x m11R1 = 1 ∧ wordVal x m11R2 = 1 := by
  choose x₀ hx₀ using fun i => hπ (y i)
  set u := wordVal x₀ m11R1 with hu
  set v := wordVal x₀ m11R2 with hv
  have hu1 : π u = 1 := by rw [hu, map_wordVal]; simpa [hx₀] using hy1
  have hv1 : π v = 1 := by rw [hv, map_wordVal]; simpa [hx₀] using hy2
  have huz := hz u hu1
  have hvz := hz v hv1
  have hu2 := h2 u hu1
  have hv2 := h2 v hv1
  set z : Fin 2 → E := ![v * u, u] with hzdef
  have hzc : ∀ i, z i ∈ Subgroup.center E := by
    intro i
    fin_cases i
    · exact Subgroup.mul_mem _ hvz huz
    · exact huz
  have hz2 : ∀ i, π (z i) = 1 := by
    intro i
    fin_cases i
    · simp [hzdef, hu1, hv1]
    · simp [hzdef, hu1]
  have hzsq : ∀ i, z i * z i = 1 := by
    intro i
    fin_cases i
    · show v * u * (v * u) = 1
      have hvu : v * u = u * v := (Subgroup.mem_center_iff.mp huz v)
      calc v * u * (v * u) = v * (u * v) * u := by simp only [mul_assoc]
        _ = v * (v * u) * u := by rw [← hvu]
        _ = (v * v) * (u * u) := by simp only [mul_assoc]
        _ = 1 := by rw [hv2, hu2, one_mul]
    · exact hu2
  refine ⟨fun i => x₀ i * z i, ?_, ?_, ?_⟩
  · intro i
    rw [map_mul, hx₀, hz2, mul_one]
  · rw [wordVal_mul_central x₀ z hzc, wordVal_central z hzc]
    have e := expsum_m11R1
    rw [e.1, e.2, zpow_eq_of_mul_self_eq_one (hzsq 0), zpow_eq_of_mul_self_eq_one (hzsq 1)]
    have h1 : Even (-4 : ℤ) := by decide
    have h2' : ¬ Even (5 : ℤ) := by decide
    simp only [h1, h2', ↓reduceIte, one_mul]
    show u * u = 1
    exact hu2
  · rw [wordVal_mul_central x₀ z hzc, wordVal_central z hzc]
    have e := expsum_m11R2
    rw [e.1, e.2, zpow_eq_of_mul_self_eq_one (hzsq 0), zpow_eq_of_mul_self_eq_one (hzsq 1)]
    have h1 : ¬ Even (1 : ℤ) := by decide
    have h2' : ¬ Even (-1 : ℤ) := by decide
    simp only [h1, h2', ↓reduceIte]
    show v * ((v * u) * u) = 1
    calc v * (v * u * u) = (v * v) * (u * u) := by simp only [mul_assoc]
      _ = 1 := by rw [hv2, hu2, one_mul]

end Lifts

section Cover

@[expose] noncomputable def m11Gen
    : Fin 2 → ↥Blueprint.NativeSporadic.M11 := fun i => img i.val

theorem m11Gen_rel1 : wordVal m11Gen m11R1 = 1 := by
  have h := relators_eval (m11R1.map natLetter) (by rw [m11_relatorLetters]; simp)
  rwa [wordProd_map_natLetter img m11Gen (fun i => rfl)] at h

theorem m11Gen_rel2 : wordVal m11Gen m11R2 = 1 := by
  have h := relators_eval (m11R2.map natLetter) (by rw [m11_relatorLetters]; simp)
  rwa [wordProd_map_natLetter img m11Gen (fun i => rfl)] at h

theorem m11Gen_ne_one : m11Gen 0 ≠ 1 := by
  intro h
  have h0 : ((img 0 : ↥Blueprint.NativeSporadic.M11) : Equiv.Perm (Fin 11)) = 1 := by
    have := congrArg Subtype.val h
    simpa [m11Gen] using this
  rw [img_val] at h0
  have h1 : (alpha : Equiv.Perm (Fin 11)) 0 = 10 := by decide
  have h2 := congrArg (fun g : Equiv.Perm (Fin 11) => g 0) h0
  simp only [↓reduceIte] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

theorem closure_m11Gen :
    Subgroup.closure (Set.range m11Gen) = ⊤ := by
  have hfin : Finite ↥Blueprint.NativeSporadic.M11 := CFSG.Sporadic.Mathieu.fam_m11_simplicity.1
  apply Subgroup.eq_top_of_card_eq
  rw [card_closure_eq m11Gen m11Gen_rel1 m11Gen_rel2 m11Gen_ne_one]
  exact CFSG.Sporadic.Mathieu.card_M11.symm

theorem m11_cover_exp2
    {E : Type*} [Group E] [Finite E]
    (π : E →* ↥Blueprint.NativeSporadic.M11) (hπ : Function.Surjective π)
    (hz : ∀ z, π z = 1 → z ∈ Subgroup.center E) (h2 : ∀ z, π z = 1 → z * z = 1)
    (hperf : commutator E = ⊤) : π.ker = ⊥ := by
  obtain ⟨x, hxπ, hx1, hx2⟩ := m11_exists_lifts π hπ hz h2 m11Gen m11Gen_rel1 m11Gen_rel2
  have hrange : π '' Set.range x = Set.range m11Gen := by
    ext g
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hxπ i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hxπ i⟩
  have hclos : Subgroup.closure (Set.range x) = ⊤ :=
    closure_eq_top_of_lifts π hz hperf _ (by rw [hrange]; exact closure_m11Gen)
  have hsurj : Function.Surjective (p11Hom x hx1 hx2) := by
    rw [← MonoidHom.range_eq_top, p11Hom_range, hclos]
  obtain ⟨hfin, hcard⟩ := finite_card_le
  have hE : Nat.card E ≤ 7920 := (Nat.card_le_card_of_surjective _ hsurj).trans hcard
  have hM : Nat.card ↥Blueprint.NativeSporadic.M11 = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have hprod := card_eq_card_mul_card_ker π hπ
  rw [hM] at hprod
  have hker : Nat.card π.ker = 1 := by
    have hpos : 0 < Nat.card π.ker := Nat.card_pos
    nlinarith
  exact (Subgroup.card_eq_one).mp hker

end Cover

end CFSG.QuasithinUnique.Vol2Native.L239.Covers
