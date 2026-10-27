module

public import CFSG.FeitThompson.Representations.IntPolyMeanSquareOverPrimitiveRoots
public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

variable {G : Type*} [Group G]

def cyclicGenerators (D : Subgroup G) : Set G := {x | Subgroup.zpowers x = D}

theorem mem_cyclicGenerators {D : Subgroup G} {x : G} :
    x ∈ cyclicGenerators D ↔ Subgroup.zpowers x = D := Iff.rfl

theorem self_mem_cyclicGenerators (x : G) : x ∈ cyclicGenerators (Subgroup.zpowers x) :=
  mem_cyclicGenerators.2 rfl

theorem cyclicGenerators_subset_coe (D : Subgroup G) : cyclicGenerators D ⊆ (D : Set G) :=
  fun _ hx => mem_cyclicGenerators.1 hx ▸ Subgroup.mem_zpowers _

theorem isCyclic_of_mem_cyclicGenerators {D : Subgroup G} {x : G}
    (hx : x ∈ cyclicGenerators D) : IsCyclic D :=
  D.isCyclic_iff_exists_zpowers_eq_top.2 ⟨x, mem_cyclicGenerators.1 hx⟩

theorem zpowers_pow_eq_zpowers {x : G} {a : ℕ} (ha : a.Coprime (orderOf x)) :
    Subgroup.zpowers (x ^ a) = Subgroup.zpowers x := by
  refine le_antisymm (Subgroup.zpowers_le.2 (Subgroup.npow_mem_zpowers x a)) ?_
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime ha
  exact Subgroup.zpowers_le.2 (Subgroup.mem_zpowers_iff.2 ⟨m, by rw [zpow_natCast]; exact hm⟩)

theorem zpowers_eq_zpowers_iff_exists_coprimeIndices {x y : G} (hx : IsOfFinOrder x) :
    Subgroup.zpowers y = Subgroup.zpowers x ↔ ∃ a ∈ coprimeIndices (orderOf x), x ^ a = y := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  constructor
  · intro hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hy ▸ Subgroup.mem_zpowers y)
    have hord : orderOf y = orderOf x := by
      rw [← Nat.card_zpowers, ← Nat.card_zpowers, hy]
    have hnn : (0 : ℤ) ≤ m % (orderOf x : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn)
    set r := (m % (orderOf x : ℤ)).toNat with hr
    have hrlt : r < orderOf x := by
      have h1 : m % (orderOf x : ℤ) < (orderOf x : ℤ) :=
        Int.emod_lt_of_pos _ (by exact_mod_cast hx.orderOf_pos)
      omega
    have hyr : x ^ r = y := by
      rw [hr, ← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf, hm]
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    ·
      have hy1 : y = 1 := by rw [← hyr, hr0, pow_zero]
      have hx1 : orderOf x = 1 := by rw [← hord, hy1, orderOf_one]
      refine ⟨1, mem_coprimeIndices.2 ⟨le_refl 1, hx1.symm.le, by simp [hx1]⟩, ?_⟩
      rw [pow_one, orderOf_eq_one_iff.1 hx1, hy1]
    · refine ⟨r, mem_coprimeIndices.2 ⟨hr0, hrlt.le, ?_⟩, hyr⟩
      have h1 : orderOf (x ^ r) = orderOf x / (orderOf x).gcd r := orderOf_pow' x hr0.ne'
      rw [hyr, hord] at h1
      exact Nat.Coprime.symm ((Nat.div_eq_self.1 h1.symm).resolve_left hn)
  · rintro ⟨a, ha, rfl⟩
    exact zpowers_pow_eq_zpowers (mem_coprimeIndices.1 ha).2.2

theorem cyclicGenerators_eq_image {x : G} (hx : IsOfFinOrder x) :
    cyclicGenerators (Subgroup.zpowers x)
      = (fun a : ℕ => x ^ a) '' (coprimeIndices (orderOf x) : Set ℕ) := by
  ext y
  simpa [mem_cyclicGenerators, eq_comm] using zpowers_eq_zpowers_iff_exists_coprimeIndices hx

theorem one_mem_coprimeIndices_orderOf {x : G} (hx : IsOfFinOrder x) :
    1 ∈ coprimeIndices (orderOf x) :=
  mem_coprimeIndices.2 ⟨le_refl 1, hx.orderOf_pos, Nat.coprime_one_left _⟩

theorem pow_injOn_coprimeIndices (x : G) :
    Set.InjOn (fun a : ℕ => x ^ a) (coprimeIndices (orderOf x) : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, mem_coprimeIndices] at ha hb
  have h : a ≡ b [MOD orderOf x] := pow_eq_pow_iff_modEq.1 hab
  rcases le_total a b with hle | hle
  · have hd := (Nat.modEq_iff_dvd' hle).1 h
    have h2 : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd := (Nat.modEq_iff_dvd' hle).1 h.symm
    have h2 : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

theorem ncard_cyclicGenerators {x : G} (hx : IsOfFinOrder x) :
    (cyclicGenerators (Subgroup.zpowers x)).ncard = (orderOf x).totient := by
  rw [cyclicGenerators_eq_image hx, (pow_injOn_coprimeIndices x).ncard_image,
    Set.ncard_coe_finset, card_coprimeIndices]

private def cyclicPolyValues (x : G) (ζ : ℂ) : Submodule ℤ (G → ℂ) where
  carrier := {f | ∃ A : ℤ[X], ∀ a : ℕ, f (x ^ a) = aeval (ζ ^ a) A}
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    exact ⟨A + B, fun a => by simp [hA a, hB a]⟩
  zero_mem' := ⟨0, fun a => by simp⟩
  smul_mem' c f := by
    rintro ⟨A, hA⟩
    exact ⟨c • A, fun a => by simp [hA a]⟩

private theorem character_mem_cyclicPolyValues (V : FDRep ℂ G) {x : G} (hx : IsOfFinOrder x)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (orderOf x)) :
    FDRep.character V ∈ cyclicPolyValues x ζ := by
  classical
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  have : NeZero (orderOf x) := ⟨hn⟩
  obtain ⟨b, d, hd, hpow⟩ := Representation.exists_basis_eigenvector (V := V.V) V.ρ hx
  choose e he hee using fun i => hζ.eq_pow_of_pow_eq_one (hpow i)
  refine ⟨∑ i, X ^ (e i), fun a => ?_⟩
  have key : ∀ (a : ℕ) (i), (V.ρ (x ^ a)) (b i) = d i ^ a • b i := by
    intro a i
    induction a with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, map_mul, Module.End.mul_apply, hd i, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have h2 := Representation.character_eq_sum_of_eigenbasis (V := V.V) V.ρ b (fun i => d i ^ a)
    (key a)
  change Representation.character (V := V.V) V.ρ (x ^ a) = _
  rw [h2]
  simp only [map_sum, aeval_X_pow, ← hee]
  exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul, ← pow_mul, mul_comm]

theorem exists_intPoly_apply_pow {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    {x : G} (hx : IsOfFinOrder x) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (orderOf x)) :
    ∃ A : ℤ[X], ∀ a : ℕ, f (x ^ a) = aeval (ζ ^ a) A :=
  Submodule.span_le.2 (fun _ hχ => by
    obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
    exact character_mem_cyclicPolyValues V hx hζ) hf

theorem forall_apply_pow_eq_zero_or_totient_le {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    {x : G} (hx : IsOfFinOrder x) :
    (∀ a ∈ coprimeIndices (orderOf x), f (x ^ a) = 0) ∨
      ((∀ a ∈ coprimeIndices (orderOf x), f (x ^ a) ≠ 0) ∧
        ((orderOf x).totient : ℝ) ≤ ∑ a ∈ coprimeIndices (orderOf x), ‖f (x ^ a)‖ ^ 2) := by
  have hpos : 0 < orderOf x := hx.orderOf_pos
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (orderOf x) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ hpos.ne'⟩
  obtain ⟨A, hA⟩ := exists_intPoly_apply_pow hf hx hζ
  by_cases h0 : aeval ζ A = 0
  · exact Or.inl fun a ha => by
      rw [hA a]
      exact aeval_pow_eq_zero_of_aeval_eq_zero hpos hζ h0 (mem_coprimeIndices.1 ha).2.2
  · refine Or.inr ⟨fun a ha => ?_, ?_⟩
    · have h1 := sq_norm_aeval_pow_pos hpos hζ h0 ha
      rw [hA a]
      intro hz
      rw [hz] at h1
      simp at h1
    · calc ((orderOf x).totient : ℝ)
          ≤ ∑ a ∈ coprimeIndices (orderOf x), ‖aeval (ζ ^ a) A‖ ^ 2 :=
            totient_le_sum_sq_norm_aeval_pow hpos hζ h0
        _ = _ := Finset.sum_congr rfl fun a _ => by rw [hA a]

theorem apply_eq_zero_iff_of_zpowers_eq {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    {x y : G} (hx : IsOfFinOrder x) (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    f x = 0 ↔ f y = 0 := by
  have hy : IsOfFinOrder y := by
    have : orderOf y = orderOf x := by rw [← Nat.card_zpowers, ← Nat.card_zpowers, hxy]
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf y, by
      rw [this]; exact hx.orderOf_pos, pow_orderOf_eq_one y⟩
  obtain ⟨a, ha, hay⟩ := (zpowers_eq_zpowers_iff_exists_coprimeIndices hx).1 hxy.symm
  have h1 : x = x ^ 1 := (pow_one x).symm
  rcases forall_apply_pow_eq_zero_or_totient_le hf hx with h | ⟨h, -⟩
  · exact iff_of_true (by rw [h1]; exact h 1 (one_mem_coprimeIndices_orderOf hx))
      (by rw [← hay]; exact h a ha)
  · exact iff_of_false (by rw [h1]; exact h 1 (one_mem_coprimeIndices_orderOf hx))
      (by rw [← hay]; exact h a ha)

open scoped Classical in
theorem card_filter_le_sum_sq_norm_pow {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    {x : G} (hx : IsOfFinOrder x) :
    (({a ∈ coprimeIndices (orderOf x) | f (x ^ a) ≠ 0}).card : ℝ)
      ≤ ∑ a ∈ coprimeIndices (orderOf x), ‖f (x ^ a)‖ ^ 2 := by
  rcases forall_apply_pow_eq_zero_or_totient_le hf hx with h | ⟨h1, h2⟩
  · have he : {a ∈ coprimeIndices (orderOf x) | f (x ^ a) ≠ 0} = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      exact fun a ha => not_not.2 (h a ha)
    rw [he]
    simpa using Finset.sum_nonneg fun a _ => sq_nonneg ‖f (x ^ a)‖
  · have he : {a ∈ coprimeIndices (orderOf x) | f (x ^ a) ≠ 0} = coprimeIndices (orderOf x) :=
      Finset.filter_true_of_mem h1
    rw [he, card_coprimeIndices]
    exact h2

open scoped Classical in
theorem card_filter_le_sum_sq_norm {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    (A : Finset G) (hA : ∀ x ∈ A, ∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x → y ∈ A)
    (hfin : ∀ x ∈ A, IsOfFinOrder x) :
    (({x ∈ A | f x ≠ 0}).card : ℝ) ≤ ∑ x ∈ A, ‖f x‖ ^ 2 := by
  classical
  set g : G → Subgroup G := fun x => Subgroup.zpowers x with hg
  have hmaps : ∀ x ∈ A, g x ∈ A.image g := fun x hx => Finset.mem_image_of_mem g hx
  have hmaps2 : ∀ x ∈ {x ∈ A | f x ≠ 0}, g x ∈ A.image g := fun x hx =>
    hmaps x (Finset.mem_filter.1 hx).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps2,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun x => ‖f x‖ ^ 2), Nat.cast_sum]
  refine Finset.sum_le_sum fun D hD => ?_
  obtain ⟨x₀, hx₀A, hx₀⟩ := Finset.mem_image.1 hD
  have hx₀' : Subgroup.zpowers x₀ = D := hx₀
  have hfib : {x ∈ A | g x = D} = (coprimeIndices (orderOf x₀)).image (fun a : ℕ => x₀ ^ a) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hyD⟩
      refine (zpowers_eq_zpowers_iff_exists_coprimeIndices (hfin x₀ hx₀A)).1 ?_
      rw [show Subgroup.zpowers y = g y from rfl, hyD, ← hx₀']
    · rintro ⟨a, ha, rfl⟩
      have h1 : Subgroup.zpowers (x₀ ^ a) = Subgroup.zpowers x₀ :=
        zpowers_pow_eq_zpowers (mem_coprimeIndices.1 ha).2.2
      refine ⟨hA x₀ hx₀A _ h1, ?_⟩
      change Subgroup.zpowers (x₀ ^ a) = D
      rw [h1, hx₀']
  have hfib2 : {x ∈ {x ∈ A | f x ≠ 0} | g x = D} = {y ∈ {x ∈ A | g x = D} | f y ≠ 0} := by
    simp only [Finset.filter_filter]
    exact Finset.filter_congr fun x _ => by tauto
  have hsub : ({a ∈ coprimeIndices (orderOf x₀) | f (x₀ ^ a) ≠ 0} : Finset ℕ)
      ⊆ coprimeIndices (orderOf x₀) := Finset.filter_subset _ _
  rw [hfib2, hfib, Finset.sum_image (pow_injOn_coprimeIndices x₀), Finset.filter_image,
    Finset.card_image_of_injOn ((pow_injOn_coprimeIndices x₀).mono (Finset.coe_subset.2 hsub))]
  exact card_filter_le_sum_sq_norm_pow hf (hfin x₀ hx₀A)

theorem card_le_sum_sum_sq_norm {k : ℕ} (f : Fin k → G → ℂ)
    (hf : ∀ j, f j ∈ Submodule.span ℤ (Irr G)) (A : Finset G)
    (hA : ∀ x ∈ A, ∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x → y ∈ A)
    (hfin : ∀ x ∈ A, IsOfFinOrder x) (hcov : ∀ x ∈ A, ∃ j, f j x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ∑ j, ‖f j x‖ ^ 2 := by
  classical
  have hcard : A.card ≤ ∑ j : Fin k, ({x ∈ A | f j x ≠ 0}).card := by
    calc A.card ≤ (Finset.univ.biUnion fun j : Fin k => {x ∈ A | f j x ≠ 0}).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨j, hj⟩ := hcov x hx
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, Finset.mem_filter.2 ⟨hx, hj⟩⟩
      _ ≤ _ := Finset.card_biUnion_le
  calc (A.card : ℝ) ≤ ∑ j : Fin k, (({x ∈ A | f j x ≠ 0}).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_le.2 hcard
    _ ≤ ∑ j : Fin k, ∑ x ∈ A, ‖f j x‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => card_filter_le_sum_sq_norm (hf j) A hA hfin
    _ = ∑ x ∈ A, ∑ j, ‖f j x‖ ^ 2 := Finset.sum_comm

theorem span_Irr_le_virtualChars : Submodule.span ℤ (Irr G) ≤ virtualChars G :=
  Submodule.span_le.2 Irr_subset_virtualChars

end CFSG.FeitThompson
