module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingAbstract
public import CFSG.GH74.GLS.Stage4.HexCoordD4
public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.LieType.Steinberg.TwistedD4.RankOne

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement

section Closing


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] def diagSL (l : Kˣ) : SL(2, K) :=
  ⟨!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

theorem diagSL_conj_sl2Upper (l : Kˣ) (c : K) :
    diagSL l * sl2Upper c * (diagSL l)⁻¹ = sl2Upper ((l : K) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show (!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)] * !![1, c; 0, 1]) =
    !![1, (l : K) ^ 2 * c; 0, 1] * !![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | (have hl := l.ne_zero; field_simp)

theorem d4X_zero_eq (c : K) : d4X hσ 0 c = slShort σ hσ (sl2Upper c) := by
  apply Subtype.ext
  refine (coe_d4X hσ 0 c).trans ?_
  show d43XE σ 0 c = _
  rw [d43XE_zero, slShort_upper, d4Root_zero_eq, xOrbit_single]

def shortCoords (H : Subgroup (twistedGroup σ)) : AddSubgroup K :=
  (Subgroup.toAddSubgroup H).comap
    (AddMonoidHom.mk' (fun c : K => Additive.ofMul (d4X hσ 0 c)) fun a b =>
      congrArg Additive.ofMul (d4X_add hσ 0 a b))

theorem mem_shortCoords {H : Subgroup (twistedGroup σ)} {c : K} :
    c ∈ shortCoords hσ H ↔ d4X hσ 0 c ∈ H := Iff.rfl

theorem shortCoords_eq_top (h2 : (2 : K) ≠ 0) (H : Subgroup (twistedGroup σ))
    (htor : ∀ l : Kˣ, slShort σ hσ (diagSL l) ∈ H) {c₀ : K} (hc₀ : c₀ ≠ 0)
    (hH : d4X hσ 0 c₀ ∈ H) : shortCoords hσ H = ⊤ := by
  have hsq : ∀ a : K, a ^ 2 * c₀ ∈ shortCoords hσ H := by
    intro a
    by_cases ha : a = 0
    · rw [ha]; simp
    · have e := diagSL_conj_sl2Upper (Units.mk0 a ha) c₀
      simp only [Units.val_mk0] at e
      rw [mem_shortCoords, d4X_zero_eq, ← e, map_mul, map_mul, map_inv]
      refine H.mul_mem (H.mul_mem (htor _) ?_) (H.inv_mem (htor _))
      rw [← d4X_zero_eq]
      exact hH
  rw [eq_top_iff]
  intro x _
  have hx : x = (((x / c₀) + 1) / 2) ^ 2 * c₀ - (((x / c₀) - 1) / 2) ^ 2 * c₀ := by
    field_simp
    ring
  rw [hx]
  exact (shortCoords hσ H).sub_mem (hsq _) (hsq _)

include hσ in
theorem exists_cross_eq [Finite K] (h2 : (2 : K) ≠ 0) (c : K) : ∃ t : K, d43Cross σ 1 t = c := by
  let f : K →+ K := AddMonoidHom.mk' (fun t => σ (σ t) + σ t) fun a b => by
    simp only [map_add]; ring
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    have h1 : σ (σ t) + σ t = 0 := ht
    have h2' : t + σ (σ t) = 0 := by
      have := congrArg σ h1
      rw [map_add, map_zero, hσ t] at this
      exact this
    have h3 : σ t = t := by linear_combination h1 - h2'
    have h4 : σ (σ t) = t := by rw [h3]; exact h3
    have h5 : (2 : K) * t = 0 := by linear_combination h2' - h4
    exact (mul_eq_zero.1 h5).resolve_left h2
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj c
  refine ⟨t, ?_⟩
  have h : σ (σ t) + σ t = c := ht
  simpa [d43Cross] using h

theorem mem_hexGroup_iff' (i : Fin 6) {k : ℤ} (hk : (i : ℤ) + 1 = k) {y : twistedGroup σ} :
    y ∈ hexGroup (twistedX σ) k ↔ ∃ c : d43Par σ i, d4X hσ i c = y := by
  subst hk
  exact mem_hexGroup_d4_iff hσ i y

theorem d4X_mem_hexGroup' (i : Fin 6) (c : d43Par σ i) {k : ℤ} (hk : (i : ℤ) + 1 = k) :
    d4X hσ i c ∈ hexGroup (twistedX σ) k := by
  subst hk
  exact d4X_mem hσ i c

theorem eq_top_of_long_short
    [Finite K] (h2 : (2 : K) ≠ 0) (H : Subgroup (twistedGroup σ))
    (hlong : longSub 6 (hexGroup (twistedX σ)) ≤ H)
    (htor : ∀ l : Kˣ, slShort σ hσ (diagSL l) ∈ H) {c₀ : K} (hc₀ : c₀ ≠ 0)
    (hH : d4X hσ 0 c₀ ∈ H) : H = ⊤ := by
  have R := d4RGD2 σ hσ
  have hA := shortCoords_eq_top hσ h2 H htor hc₀ hH
  have h0 : hexGroup (twistedX σ) 1 ≤ H := by
    intro y hy
    obtain ⟨c, rfl⟩ := (mem_hexGroup_iff' hσ 0 (by norm_num)).1 hy
    have : c ∈ shortCoords hσ H := by rw [hA]; trivial
    exact (mem_shortCoords hσ).1 this
  have h5 := root_five_le R H hlong h0
  have h2r : hexGroup (twistedX σ) 3 ≤ H := by
    intro y hy
    obtain ⟨c, rfl⟩ := (mem_hexGroup_iff' hσ 2 (by norm_num)).1 hy
    obtain ⟨t, ht⟩ := exists_cross_eq hσ h2 (-c)
    have hrel := (d4Rel_model hσ).r04 1 t
    have hx0 : d4X hσ 0 (1 : K) ∈ H := h0 (d4X_mem_hexGroup' hσ 0 (1 : K) (by norm_num))
    have hx4 : d4X hσ 4 t ∈ H := h5 ((d4X_mem_hexGroup' hσ 4 t (by norm_num)))
    have hlong' : ∀ (i : Fin 6) (c : d43Par σ i) (k : ℤ), (i : ℤ) + 1 = k → k % 2 = 0 →
        IsRoot 6 k → d4X hσ i c ∈ H := fun i c k hk hk2 hkr =>
      hlong (root_le_longSub hkr hk2 (d4X_mem_hexGroup' hσ i c hk))
    have hA1 := hlong' 1 (-d43Tr hσ (d43Sharp σ (1 : K) * t)) 2 (by norm_num) (by norm_num)
      ⟨by norm_num, by norm_num⟩
    have hA3 := hlong' 3 (-d43Tr hσ ((1 : K) * d43Sharp σ t)) 4 (by norm_num) (by norm_num)
      ⟨by norm_num, by norm_num⟩
    have hcomm : ⁅d4X hσ 0 (1 : K), d4X hσ 4 t⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hx0 hx4) (H.inv_mem hx0)) (H.inv_mem hx4)
    rw [hrel] at hcomm
    have hB : d4X hσ 2 (-(d43Cross σ (1 : K) t : K)) ∈ H := by
      have e : d4X hσ 2 (-(d43Cross σ (1 : K) t : K)) =
          (d4X hσ 1 (-d43Tr hσ (d43Sharp σ (1 : K) * t)))⁻¹ *
            (d4X hσ 1 (-d43Tr hσ (d43Sharp σ (1 : K) * t)) *
              d4X hσ 2 (-(d43Cross σ (1 : K) t : K)) *
                d4X hσ 3 (-d43Tr hσ ((1 : K) * d43Sharp σ t))) *
              (d4X hσ 3 (-d43Tr hσ ((1 : K) * d43Sharp σ t)))⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem hA1) hcomm) (H.inv_mem hA3)
    have hc : c = -(d43Cross σ (1 : K) t : K) := by rw [ht]; exact (neg_neg c).symm
    rw [hc]
    exact hB
  have hall := root_le_of_two R H hlong h0 h2r
  have htop : ⨆ β ∈ {β : Fin (Tag.rank .G2) → ℤ | CFSG.Blueprint.Chevalley.IsRoot .G2 β},
      twistedRootGroup σ β = ⊤ := by
    rw [iSup_twistedRootGroup_eq_subgroupOf σ
      (S := {β | CFSG.Blueprint.Chevalley.IsRoot .G2 β}) fun β hβ => hβ]
    exact Subgroup.subgroupOf_self _
  rw [eq_top_iff, ← htop]
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨k, hk, rfl⟩ := (isRoot_iff.1 hβ)
  have hk' := mem_hexIdx_iff.1 hk
  exact hall k ⟨hk'.1, hk'.2⟩

end Closing

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
