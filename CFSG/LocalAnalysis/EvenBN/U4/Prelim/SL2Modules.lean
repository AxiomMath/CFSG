module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBJEvenLinearTwoModule
public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
  CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule

variable {K : Type*} [Field K]

theorem center_specialLinearGroup_eq_bot [CharP K 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h1 : (r - 1) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination hr2 - (r - 1) * h2 + h2 * 0
  have h3 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  apply Subtype.ext
  rw [← hrA, h3]
  simp

omit [Field K] in
theorem exists_finset_card_four [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    ∃ s : Finset K, s.card = 4 := by
  classical
  let := Fintype.ofFinite K
  have h4 : 4 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by simpa using h4)
  exact ⟨t, ht⟩

theorem isSimpleGroup_specialLinearGroup [CharP K 2] (h4 : ∃ s : Finset K, s.card = 4) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr h4)
  exact ((QuotientGroup.quotientBot (G := SpecialLinearGroup (Fin 2) K)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq center_specialLinearGroup_eq_bot.symm)).isSimpleGroup

theorem charP_two_of_card [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  let := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem two_mul_le_of_ne_one [Finite K] {n d : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hn3 : n ≠ 3) {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 2 ^ d)
    (ρ : SpecialLinearGroup (Fin 2) K →* MulAut V) (hρ : ρ ≠ 1) : 2 * n ≤ d := by
  have : CharP K 2 := charP_two_of_card hK
  have hsimple := isSimpleGroup_specialLinearGroup (exists_finset_card_four hK hn)
  have hinj : Function.Injective ρ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ρ).mp h
    · exact absurd (MonoidHom.ker_eq_top_iff.mp h) hρ
  refine SL2MinimalFaithful.two_mul_le_of_injective Nat.prime_two (by omega) ?_ ?_ ρ hinj hV
  · rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
  · intro _
    exact exists_primitive_prime_dvd_two_pow_sub_one (2 * n) (by omega) (by omega)

section Module

variable {V : Type*} [CommGroup V]

theorem eq_one_of_forall_inv_mul_apply_mem (h4 : ∃ s : Finset K, s.card = 4)
    (ρ : SpecialLinearGroup (Fin 2) K →* MulAut V)
    (hδ : ∀ g v, v⁻¹ * ρ g v ∈ actionFixed ρ ⊤) : ρ = 1 := by
  have hfix : ∀ g (w : V), w ∈ actionFixed ρ ⊤ → ρ g w = w := fun g w hw => hw g trivial
  have hcomm : ∀ g h, ρ g * ρ h = ρ h * ρ g := by
    intro g h
    ext v
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have ha : ρ h v = v * (v⁻¹ * ρ h v) := (mul_inv_cancel_left v _).symm
    have hb : ρ g v = v * (v⁻¹ * ρ g v) := (mul_inv_cancel_left v _).symm
    calc ρ g (ρ h v) = ρ g (v * (v⁻¹ * ρ h v)) := by rw [← ha]
      _ = ρ g v * ρ g (v⁻¹ * ρ h v) := map_mul _ _ _
      _ = v * (v⁻¹ * ρ g v) * (v⁻¹ * ρ h v) := by rw [← hb, hfix g _ (hδ h v)]
      _ = v * (v⁻¹ * ρ h v) * (v⁻¹ * ρ g v) := mul_right_comm _ _ _
      _ = ρ h v * ρ h (v⁻¹ * ρ g v) := by rw [← ha, hfix h _ (hδ g v)]
      _ = ρ h (v * (v⁻¹ * ρ g v)) := (map_mul _ _ _).symm
      _ = ρ h (ρ g v) := by rw [← hb]
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl (Or.inr h4)
  have hle : commutator (SpecialLinearGroup (Fin 2) K) ≤ ρ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hcomm g h]
    group
  rw [hperf.commutator_eq_top, top_le_iff] at hle
  exact MonoidHom.ker_eq_top_iff.mp hle

variable [Finite V]

theorem actionFixed_top_eq_bot [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hn3 : n ≠ 3) (hV : Nat.card V = (2 ^ n) ^ 2) (ρ : SpecialLinearGroup (Fin 2) K →* MulAut V)
    (hρ : ρ ≠ 1) : actionFixed ρ ⊤ = ⊥ := by
  by_contra hW
  set W := actionFixed ρ ⊤
  have hmap : ∀ j, W.map (ρ j : V →* V) = W := by
    intro j
    ext w
    constructor
    · rintro ⟨w', hw', rfl⟩
      change ρ j w' ∈ W
      rw [hw' j trivial]
      exact hw'
    · intro hw
      exact ⟨w, hw, hw j trivial⟩
  set ρbar := SL2MinimalFaithful.quotientAction ρ W hmap
  have hV' : Nat.card V = 2 ^ (2 * n) := by rw [hV, ← pow_mul, mul_comm]
  obtain ⟨e, he, hWe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hV' ▸ Subgroup.card_subgroup_dvd_card W)
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exact absurd (Subgroup.eq_bot_of_card_eq W (by rw [hWe, pow_zero])) hW
    · exact h
  have hQ : Nat.card (V ⧸ W) = 2 ^ (2 * n - e) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup W
    rw [hV', hWe] at h
    have h2 : 2 ^ (2 * n) = 2 ^ (2 * n - e) * 2 ^ e := by
      rw [← pow_add, Nat.sub_add_cancel he]
    rw [h2] at h
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos two_pos e) h).symm
  have hbar : ρbar = 1 := by
    by_contra hne
    have := two_mul_le_of_ne_one hK hn hn3 hQ ρbar hne
    omega
  apply hρ
  refine eq_one_of_forall_inv_mul_apply_mem (exists_finset_card_four hK hn) ρ fun g v => ?_
  have h1 : ρbar g (v : V ⧸ W) = (v : V ⧸ W) := by rw [hbar]; rfl
  rw [SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq] at h1
  have := W.inv_mem h1
  rwa [_root_.mul_inv_rev, inv_inv] at this

theorem card_actionFixed_upperUnipotent_le [CharP K 2] {n : ℕ} (hV : Nat.card V = (2 ^ n) ^ 2)
    (ρ : SpecialLinearGroup (Fin 2) K →* MulAut V) (hD : actionFixed ρ ⊤ = ⊥) :
    Nat.card (actionFixed ρ (upperUnipotent K)) ≤ 2 ^ n := by
  set U := actionFixed ρ (upperUnipotent K)
  set U' := U.map (ρ (weylElt K)).toMonoidHom
  have hdisj := disjoint_map_weylElt hD
  have hU' : Nat.card U' = Nat.card U :=
    Subgroup.card_map_of_injective (by exact (ρ (weylElt K)).injective)
  let μ : U × U' → V := fun p => (p.1 : V) * p.2
  have hμ : Function.Injective μ := by
    rintro ⟨x, x'⟩ ⟨y, y'⟩ hxy
    have h1 : (y : V)⁻¹ * x = y' * (x' : V)⁻¹ := by
      have : (x : V) * x' = y * y' := hxy
      calc (y : V)⁻¹ * x = (y : V)⁻¹ * (x * x') * (x' : V)⁻¹ := by group
        _ = y' * (x' : V)⁻¹ := by rw [this]; group
    have hU : (y : V)⁻¹ * x ∈ U := U.mul_mem (U.inv_mem y.2) x.2
    have hU'm : (y : V)⁻¹ * x ∈ U' := h1 ▸ U'.mul_mem y'.2 (U'.inv_mem x'.2)
    have h2 : (y : V)⁻¹ * x = 1 := (Subgroup.disjoint_def.mp hdisj) hU hU'm
    have hx : (x : V) = y := (inv_mul_eq_one.mp h2).symm
    have hx' : (x' : V) = y' := by
      rw [hx] at h1
      have := h1.symm
      rw [inv_mul_cancel, mul_inv_eq_one] at this
      exact this.symm
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hx')
  have hle := Nat.card_le_card_of_injective μ hμ
  rw [Nat.card_prod, hU', hV, ← sq] at hle
  exact (Nat.pow_le_pow_iff_left two_ne_zero).mp hle

theorem gomi_natural_module [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) (hn3 : n ≠ 3) (hV : Nat.card V = (2 ^ n) ^ 2)
    (ρ : SpecialLinearGroup (Fin 2) K →* MulAut V) (hρ : ρ ≠ 1)
    (hB : 2 ^ n ≤ Nat.card (actionFixed ρ (upperUnipotent K))) :
    actionFixed ρ ⊤ = ⊥ ∧ Nat.card (actionFixed ρ (upperUnipotent K)) = 2 ^ n ∧
      Function.Injective ρ ∧
      (actionFixed ρ (upperUnipotent K)).IsComplement'
        ((actionFixed ρ (upperUnipotent K)).map (ρ (weylElt K)⁻¹).toMonoidHom) ∧
      (∀ t ∈ diagTorus K, ∀ u ∈ actionFixed ρ (upperUnipotent K),
        ρ t u ∈ actionFixed ρ (upperUnipotent K)) ∧
      (∀ u ∈ actionFixed ρ (upperUnipotent K), u ≠ 1 →
        ∀ u' ∈ actionFixed ρ (upperUnipotent K), u' ≠ 1 → ∃! t : diagTorus K, ρ t u = u') ∧
      (∀ x y : V, x ≠ 1 → y ≠ 1 → ∃ d, ρ d x = y) ∧
      (∀ u ∈ actionFixed ρ (upperUnipotent K), u ≠ 1 →
        ∀ d, ρ d u = u ↔ d ∈ upperUnipotent K) ∧
      ∀ x : V, x ≠ 1 → ∃ P : Sylow 2 (SpecialLinearGroup (Fin 2) K), ∀ d, ρ d x = x ↔ d ∈ P := by
  have hD := actionFixed_top_eq_bot hK hn hn3 hV ρ hρ
  have hB' : Nat.card (actionFixed ρ (upperUnipotent K)) = 2 ^ n :=
    le_antisymm (card_actionFixed_upperUnipotent_le hV ρ hD) hB
  exact ⟨hD, hB', even_linear_two_half_fixed_module_transitivity hK hV ρ hD hB'⟩

end Module

end CFSG.LocalAnalysis.EvenBN.U4
