module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOuter
public import CFSG.LieType.SeitzGeneration.ThreeIndep

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.SeitzGeneration (RankLE2 HasThreeIndep)
open CFSG.Open (IsElemAbelian)

@[expose] def FixesIndepPair (p : ℕ) {P : Type*} [Group P] (α : MulAut P) : Prop :=
  ∃ y₁ y₂ : P, Commute y₁ y₂ ∧ y₁ ^ p = 1 ∧ y₂ ^ p = 1 ∧
    (∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧ α y₁ = y₁ ∧ α y₂ = y₂

theorem FixesIndepPair.map {p : ℕ} {P : Type*} [Group P] {f : MulAut P} (h : MulAut P)
    (hf : FixesIndepPair p f) : FixesIndepPair p (h * f * h⁻¹) := by
  obtain ⟨y₁, y₂, hc, h1, h2, hi, hf1, hf2⟩ := hf
  refine ⟨h y₁, h y₂, hc.map h, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (h.injective (hij.trans (map_one h).symm))
  · simp [MulAut.mul_apply, hf1]
  · simp [MulAut.mul_apply, hf2]

theorem FixesIndepPair.of_mulEquiv {p : ℕ} {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    {α : MulAut P} (h : FixesIndepPair p (MulAut.congr e α)) : FixesIndepPair p α := by
  obtain ⟨y₁, y₂, hc, h1, h2, hi, hf1, hf2⟩ := h
  have hα : ∀ y : Q, MulAut.congr e α y = y → α (e.symm y) = e.symm y := by
    intro y hy
    rw [MulAut.congr_apply] at hy
    have := congrArg e.symm hy
    simpa using this
  refine ⟨e.symm y₁, e.symm y₂, hc.map e.symm, ?_, ?_, ?_, hα y₁ hf1, hα y₂ hf2⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (e.symm.injective (hij.trans (map_one e.symm).symm))

theorem congr_conj_eq {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (y : P) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_mem_inner_iff {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (α : MulAut P) :
    MulAut.congr e α ∈ inner Q ↔ α ∈ inner P := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    have h1 : MulAut.congr e α = MulAut.conj y := hy.symm
    have h2 : α = MulAut.congr e.symm (MulAut.conj y) := by
      rw [← h1]
      ext z
      simp [MulAut.congr_apply]
    rw [h2, congr_conj_eq]
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (congr_conj_eq e y).symm⟩

theorem exists_elemAbelian_sq_of_pRank_eq_two {P : Type*} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) (h : CFSG.Open.pRank p (⊤ : Subgroup P) = 2) :
    ∃ E : Subgroup P, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  set S : Set ℕ := {k | ∃ E : Subgroup P, E ≤ ⊤ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}
    with hS
  have hbot : IsElemAbelian p (⊥ : Subgroup P) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have hab : a = b := Subsingleton.elim a b
      rw [hab]
    · rw [Subgroup.mem_bot.1 hx, one_pow]
  have hne : S.Nonempty := ⟨0, ⊥, le_top, hbot, by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card P, fun k hk => ?_⟩
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : p ^ k ≤ Nat.card P := hE ▸ Subgroup.card_le_card_group E
    exact (Nat.lt_pow_self hp.one_lt).le.trans h1
  have hmem := Nat.sSup_mem hne hbdd
  have hsup : sSup S = 2 := h
  rw [hsup] at hmem
  obtain ⟨E, -, hE, hc⟩ := hmem
  exact ⟨E, hE, hc⟩

theorem isElementaryAbelian_of_isElemAbelian {p : ℕ} {G : Type*} [Group G] {E : Subgroup G}
    (h : IsElemAbelian p E) : CFSG.IsElementaryAbelian p ↥E :=
  { toIsMulCommutative := h.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (h.2 x x.2) }

theorem hasThreeIndep_false_of_rankLE2 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : HasThreeIndep G p) (hrk : RankLE2 p G) : False := by
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, h1, h2, h3, hi⟩ := h
  exact CFSG.LieType.SeitzGeneration.false_of_three_independent hp hrk h12 h13 h23 h1 h2 h3 hi

theorem false_of_outer_fixesPair {p : ℕ} (hp : p.Prime) {P : Type} [Group P]
    (hconj : Function.Injective (MulAut.conj : P →* MulAut P))
    {X : Type} [Group X] [Finite X] (hrk : RankLE2 p X) (ψ : X →* MulAut P)
    (hψ : Function.Injective ψ) (L : Subgroup X)
    (hL : ∀ y : P, ∃ l ∈ L, ψ l = MulAut.conj y) {x : X} (hx : x ^ p = 1)
    (hxout : ψ x ∉ inner P) (h : FixesIndepPair p (ψ x)) : False := by
  obtain ⟨y₁, y₂, hc, h1, h2, hi, hf1, hf2⟩ := h
  exact false_of_outer_fixing_pair hp hconj hrk ψ hψ L hL hx hxout hc h1 h2 hi hf1 hf2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
