module

public import CFSG.HardMathSupport.Timmesfeld.DFour.Tower

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open Subgroup

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem pRank_mulAut_le_of_card_bounds {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hcen : Subgroup.center S = ⊥) (E : Subgroup (MulAut S)) (k : ℕ)
    (hE : ∀ X : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p X → X ≤ E →
      Nat.card X ≤ p * Nat.card (X ⊓ Inn S : Subgroup (MulAut S)))
    (hnE : ∀ X : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p X → ¬ X ≤ E →
      Nat.card X ≤ p ^ (k + 1))
    (hk : k ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ CFSG.Open.pRank p (⊤ : Subgroup S) + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, -, hX, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MulAut S))
  set m := CFSG.Open.pRank p (⊤ : Subgroup (MulAut S))
  by_cases hXE : X ≤ E
  · have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hX.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hX₀ : CFSG.Open.IsElemAbelian p (X ⊓ Inn S) :=
      ⟨⟨⟨fun a b => Subtype.ext (hcommX _ (Subgroup.mem_inf.mp a.2).1 _
        (Subgroup.mem_inf.mp b.2).1)⟩⟩, fun x hx => hX.2 x (Subgroup.mem_inf.mp hx).1⟩
    have hp0 : IsPGroup p ↥(X ⊓ Inn S) := fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
      exact hX₀.2 g g.2)⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp0
    have hjI : j ≤ CFSG.Open.pRank p (Inn S) :=
      CFSG.SectionRank.le_pRank hp.one_lt inf_le_right hX₀ hj
    have hInn : CFSG.Open.pRank p (Inn S) = CFSG.Open.pRank p (⊤ : Subgroup S) := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
        (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.innerAutEquiv hcen)).symm
    have h1 := hE X hX hXE
    rw [hcard, hj, ← pow_succ'] at h1
    have : m ≤ j + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  · have h1 := hnE X hX hXE
    rw [hcard] at h1
    have : m ≤ k + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega

theorem fixed_of_commute_conj {S : Type} [Group S] (hcen : Subgroup.center S = ⊥)
    {t : MulAut S} {s : S} (h : t * MulAut.conj s = MulAut.conj s * t) : t s = s := by
  have hconj : MulAut.conj (t s) = t * MulAut.conj s * t⁻¹ := by
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have h2 : t * MulAut.conj s * t⁻¹ = MulAut.conj s := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot hcen
    (hconj.trans h2)

theorem exists_fixed_of_mem {S : Type} [Group S] [Finite S] {p : ℕ}
    (hcen : Subgroup.center S = ⊥) {X : Subgroup (MulAut S)} (hX : CFSG.Open.IsElemAbelian p X)
    {t : MulAut S} (ht : t ∈ X) :
    ∃ A : Subgroup S, CFSG.Open.IsElemAbelian p A ∧ (∀ a ∈ A, t a = a) ∧
      Nat.card A = Nat.card (X ⊓ Inn S : Subgroup (MulAut S)) := by
  have hinj := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot
    hcen
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hX.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨X.comap (MulAut.conj : S →* MulAut S), ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩,
    fun a ha => ?_, ?_⟩
  · apply Subtype.ext
    apply hinj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hcommX _ a.2 _ b.2
  · apply hinj
    rw [map_pow, map_one]
    exact hX.2 _ ha
  · exact fixed_of_commute_conj hcen (hcommX _ ht _ ha)
  · have hmap : (X.comap (MulAut.conj : S →* MulAut S)).map (MulAut.conj : S →* MulAut S) =
        X ⊓ Inn S := by
      rw [Subgroup.map_comap_eq, inf_comm]
      rfl
    rw [← hmap, Subgroup.card_map_of_injective hinj]

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

theorem pRank_mulAut_le_of_trialityBound {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (hidx : (matrixProjectiveImage Q).index ≤ 3)
    (hcen : Subgroup.center (matrixProjectiveDerived Q) = ⊥)
    (hKL : ∀ t : MulAut (matrixProjectiveDerived Q), t ^ 3 = 1 → t ∉ matrixProjectiveImage Q →
      ∀ A : Subgroup (matrixProjectiveDerived Q), CFSG.Open.IsElemAbelian 3 A →
        (∀ a ∈ A, t a = a) → Nat.card A ≤ 9)
    (h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (matrixProjectiveDerived Q))) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (matrixProjectiveDerived Q))) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (matrixProjectiveDerived Q)) + 1 := by
  have hQv :=
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value Q hQ
  obtain ⟨g, hgE, hg⟩ := exists_gen_image Q
  have hbound : ∀ X : Subgroup (MulAut (matrixProjectiveDerived Q)),
      CFSG.Open.IsElemAbelian 3 X →
      Nat.card (matrixProjectiveImage Q ⊓ X : Subgroup _) ≤
          3 * Nat.card (X ⊓ Inn (matrixProjectiveDerived Q) : Subgroup _) ∧
        Nat.card X ≤ 3 * 3 * Nat.card (X ⊓ Inn (matrixProjectiveDerived Q) : Subgroup _) :=
    fun X hX => card_le_of_tower Nat.prime_three le_rfl (linearRange_normal Q) hidx g hgE hg
      (fun δ hδ hδp => mem_inner_of_mem_linearRange Q hQv hab Nat.prime_three (by norm_num) hδ
        hδp) hX.2
  refine pRank_mulAut_le_of_card_bounds Nat.prime_three hcen (matrixProjectiveImage Q) 3
    (fun X hX hXE => ?_) (fun X hX hXE => ?_) h3
  · have h1 := (hbound X hX).1
    rwa [inf_of_le_right hXE] at h1
  · obtain ⟨t, htX, htE⟩ := Set.not_subset.mp hXE
    obtain ⟨A, hA, hfix, hcardA⟩ := exists_fixed_of_mem hcen hX htX
    have h9 := hKL t (hX.2 t htX) htE A hA hfix
    have h2 := (hbound X hX).2
    rw [← hcardA] at h2
    calc Nat.card X ≤ 3 * 3 * Nat.card A := h2
      _ ≤ 3 * 3 * 9 := Nat.mul_le_mul_left _ h9
      _ = 3 ^ (3 + 1) := by norm_num

end CFSG.HardMathSupport.Timmesfeld.DFour
