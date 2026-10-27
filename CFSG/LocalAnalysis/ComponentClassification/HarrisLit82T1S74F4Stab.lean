module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4Levi

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem VEnd_ext {m₁ m₂ : VEnd K}
    (hv : ∀ (i : Fin 3) (s : Bool), m₁ (oddVec 3 K i s) = m₂ (oddVec 3 K i s))
    (hz : m₁ (oddZ 3 K) = m₂ (oddZ 3 K)) : m₁ = m₂ := by
  refine LinearEquiv.toLinearMap_injective
    ((Pi.basisFun K (Fin 3 ⊕ Fin 3 ⊕ Unit)).ext fun σ => ?_)
  rw [Pi.basisFun_apply]
  rcases σ with i | i | ⟨⟩
  · exact hv i true
  · exact hv i false
  · exact hz

theorem eq_neg_one_of_mul_self {μ : K} (hμ : μ * μ = 1) (h1 : μ ≠ 1) : μ = -1 := by
  have h : (μ - 1) * (μ + 1) = 0 := by linear_combination hμ
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact eq_neg_of_add_eq_zero_left h

theorem smul_oddZ_eq_iff {μ : K} : μ • oddZ 3 K = oddZ 3 K ↔ μ = 1 := by
  constructor
  · intro h
    have := congrFun h (.inr (.inr ()))
    simpa [oddZ] using this
  · rintro rfl
    exact one_smul _ _

theorem finite_VEnd [Finite K] : Finite (VEnd K) :=
  Finite.of_injective (fun e : VEnd K => (e : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) → _))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

theorem card_leviSet_le [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (leviSet K) ≤ 2 * (Nat.card SL(2, K) * Nat.card K) := by
  have := finite_VEnd (K := K)
  let φ : leviSet K → Prop × SL(2, K) × K := fun ℓ =>
    (ℓ.1 (oddZ 3 K) = oddZ 3 K, slL ℓ.2,
      polar (quadOdd 3 K) (leviRest ℓ.2 (oddVec 3 K 1 false)) (oddVec 3 K 0 false))
  have hφ : Function.Injective φ := by
    rintro ⟨ℓ₁, h₁⟩ ⟨ℓ₂, h₂⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hz, hA, hs⟩ := h
    obtain ⟨μ₁, hμ₁, hf₁⟩ := h₁.2.2.1
    obtain ⟨μ₂, hμ₂, hf₂⟩ := h₂.2.2.1
    have hz₁ := hf₁ _ La_neg_one_apply_z
    have hz₂ := hf₂ _ La_neg_one_apply_z
    have hμ : μ₁ = μ₂ := by
      have hiff : μ₁ = 1 ↔ μ₂ = 1 := by
        rw [← smul_oddZ_eq_iff, ← smul_oddZ_eq_iff, ← hz₁, ← hz₂]
        exact Eq.to_iff hz
      by_cases h1 : μ₁ = 1
      · rw [h1, hiff.mp h1]
      · rw [eq_neg_one_of_mul_self hμ₁ h1, eq_neg_one_of_mul_self hμ₂ (fun h => h1 (hiff.mpr h))]
    subst hμ
    have hrest : leviRest h₁ = leviRest h₂ := by
      obtain ⟨a₀, a₁⟩ := leviRest_apply_f h₁ h2
      obtain ⟨b₀, b₁⟩ := leviRest_apply_f h₂ h2
      refine VEnd_ext (fun i s => ?_) ?_
      · fin_cases i <;> cases s
        · exact a₀.trans (hs ▸ b₀.symm)
        · exact (leviRest_apply_eZero h₁).trans (leviRest_apply_eZero h₂).symm
        · exact a₁.trans (hs ▸ b₁.symm)
        · exact (leviRest_apply_eOne h₁).trans (leviRest_apply_eOne h₂).symm
        · exact (leviRest_apply_of_fix h₁ h2 hf₁ La_neg_one_apply_f2).trans
            (leviRest_apply_of_fix h₂ h2 hf₂ La_neg_one_apply_f2).symm
        · exact (leviRest_apply_of_fix h₁ h2 hf₁ La_neg_one_apply_e2).trans
            (leviRest_apply_of_fix h₂ h2 hf₂ La_neg_one_apply_e2).symm
      · exact (leviRest_apply_of_fix h₁ h2 hf₁ La_neg_one_apply_z).trans
          (leviRest_apply_of_fix h₂ h2 hf₂ La_neg_one_apply_z).symm
    have e₁ : ℓ₁ = rhoJ (slL h₁) * leviRest h₁ := (mul_inv_cancel_left _ _).symm
    have e₂ : ℓ₂ = rhoJ (slL h₂) * leviRest h₂ := (mul_inv_cancel_left _ _).symm
    apply Subtype.ext
    show ℓ₁ = ℓ₂
    calc ℓ₁ = rhoJ (slL h₁) * leviRest h₁ := e₁
      _ = rhoJ (slL h₂) * leviRest h₂ := by rw [hrest, hA]
      _ = ℓ₂ := e₂.symm
  have hcard : Nat.card (Prop × SL(2, K) × K) = 2 * (Nat.card SL(2, K) * Nat.card K) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop]
  rw [← hcard]
  exact Nat.card_le_card_of_injective φ hφ

@[expose] noncomputable def cenOne (K : Type) [Field K] : Subgroup (VEnd K) :=
  TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓
    centralizer {eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K)} ⊓
    centralizer {eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true)}

@[expose] def ySet (K : Type) [Field K] : Set (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  {y | polar (quadOdd 3 K) y (oddVec 3 K 2 true) = 0 ∧
    polar (quadOdd 3 K) y (oddVec 3 K 2 false) = 0 ∧
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) y = y}

theorem eichOne_apply_vec_two (s : Bool) :
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) (oddVec 3 K 2 s) =
      oddVec 3 K 2 s := by
  refine eichler_apply_of_polar_eq_zero ?_ ?_ <;> rw [polar_quadOdd_oddVec] <;> simp

theorem eichler_eTwo_smul_fTwo {u : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hu : polar (quadOdd 3 K) (oddVec 3 K 2 true) u = 0)
    (hu' : polar (quadOdd 3 K) (oddVec 3 K 2 false) u = 0) (μ : K) :
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) u (μ • oddVec 3 K 2 false) =
      μ • (oddVec 3 K 2 false + u - quadOdd 3 K u • oddVec 3 K 2 true) := by
  rw [map_smul, eichler_apply quadOdd_eTwo hu, polar_fTwo_eTwo, hu', one_smul, zero_add, mul_one]

variable {h : VEnd K}

theorem decomp_commute_eichOne (hh : CommThree h)
    (hc1 : h * eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) =
      eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) * h) :
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) (yThree h) = yThree h ∧
      ellThree h * eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) =
        eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) * ellThree h := by
  set E₁ := eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) with hE₁
  have hO1 : E₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
    eichler_mem_orthogonalGroup _ _ _
  have hE2 : ∀ s, E₁ (oddVec 3 K 2 s) = oddVec 3 K 2 s := fun s => eichOne_apply_vec_two s
  have hhℓ : h = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) * ellThree h :=
    (mul_inv_cancel_left _ _).symm
  have hconj : E₁ * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (E₁ (yThree h)) * E₁ := by
    have := eichler_conj hO1 (oddVec 3 K 2 true) (yThree h)
    rw [hE2] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have key : eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) * (ellThree h * E₁) =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true) (E₁ (yThree h)) * (E₁ * ellThree h) := by
    calc eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) * (ellThree h * E₁) =
          eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) * ellThree h * E₁ :=
          (mul_assoc _ _ _).symm
      _ = E₁ * (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) * ellThree h) := by
          rw [← hhℓ, hc1]
      _ = E₁ * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h) * ellThree h :=
          (mul_assoc _ _ _).symm
      _ = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (E₁ (yThree h)) * (E₁ * ellThree h) := by
          rw [hconj, mul_assoc]
  have he2 : polar (quadOdd 3 K) (oddVec 3 K 2 true) (E₁ (yThree h)) = 0 := by
    rw [← hE2 true, polar_map_of_mem hO1, polar_eTwo_yThree]
  have hf2 : polar (quadOdd 3 K) (oddVec 3 K 2 false) (E₁ (yThree h)) = 0 := by
    rw [← hE2 false, polar_map_of_mem hO1, polar_fTwo_yThree]
  have hQ : quadOdd 3 K (E₁ (yThree h)) = quadOdd 3 K (yThree h) := map_of_mem hO1 _
  have hl := hh.ell_fTwo
  have hlam := hh.lam
  have hcalc : lamThree h • (oddVec 3 K 2 false + yThree h -
        quadOdd 3 K (yThree h) • oddVec 3 K 2 true) =
      lamThree h • (oddVec 3 K 2 false + E₁ (yThree h) -
        quadOdd 3 K (E₁ (yThree h)) • oddVec 3 K 2 true) := by
    calc lamThree h • (oddVec 3 K 2 false + yThree h -
          quadOdd 3 K (yThree h) • oddVec 3 K 2 true) =
          eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h)
            (lamThree h • oddVec 3 K 2 false) :=
          (eichler_eTwo_smul_fTwo polar_eTwo_yThree polar_fTwo_yThree _).symm
      _ = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree h)
            (ellThree h (E₁ (oddVec 3 K 2 false))) := by rw [hE2, hl]
      _ = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (E₁ (yThree h))
            (E₁ (ellThree h (oddVec 3 K 2 false))) := LinearEquiv.congr_fun key _
      _ = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (E₁ (yThree h))
            (lamThree h • oddVec 3 K 2 false) := by
          rw [hl, map_smul E₁ (lamThree h) (oddVec 3 K 2 false), hE2]
      _ = lamThree h • (oddVec 3 K 2 false + E₁ (yThree h) -
            quadOdd 3 K (E₁ (yThree h)) • oddVec 3 K 2 true) :=
          eichler_eTwo_smul_fTwo he2 hf2 _
  have hl0 : lamThree h ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hlam
    exact zero_ne_one hlam
  have hy := smul_right_injective _ hl0 hcalc
  rw [hQ, sub_left_inj, add_right_inj] at hy
  refine ⟨hy.symm, ?_⟩
  rw [← hy] at key
  exact mul_left_cancel key

theorem coords_of_mem_ySet {y : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hy : y ∈ ySet K) :
    y (.inr (.inl 0)) = 0 ∧ y (.inr (.inl 1)) = 0 ∧ y (.inr (.inl 2)) = 0 ∧ y (.inl 2) = 0 := by
  obtain ⟨h2, h2', h1⟩ := hy
  rw [polar_vecT] at h2
  rw [polar_vecF] at h2'
  rw [eichOne_apply, polar_vecT, polar_vecT] at h1
  have a := congrFun h1 (.inl 0)
  have b := congrFun h1 (.inl 1)
  simp at a b
  exact ⟨b, a, h2, h2'⟩

theorem card_ySet_le [Finite K] : Nat.card (ySet K) ≤ Nat.card K ^ 3 := by
  let φ : ySet K → K × K × K := fun y => (y.1 (.inl 0), y.1 (.inl 1), y.1 (.inr (.inr ())))
  have hφ : Function.Injective φ := by
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨a0, a1, az⟩ := h
    obtain ⟨b0, b1, b2, b3⟩ := coords_of_mem_ySet hy
    obtain ⟨c0, c1, c2, c3⟩ := coords_of_mem_ySet hy'
    apply Subtype.ext
    funext σ
    rcases σ with i | i | ⟨⟩
    · fin_cases i
      · exact a0
      · exact a1
      · exact b3.trans c3.symm
    · fin_cases i
      · exact b0.trans c0.symm
      · exact b1.trans c1.symm
      · exact b2.trans c2.symm
    · exact az
  have hcard : Nat.card (K × K × K) = Nat.card K ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod]
    ring
  rw [← hcard]
  exact Nat.card_le_card_of_injective φ hφ

theorem card_cenOne_le [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (cenOne K) ≤ Nat.card K ^ 3 * Nat.card (leviSet K) := by
  have := finite_VEnd (K := K)
  have hmem : ∀ g : cenOne K, CommThree (g : VEnd K) ∧
      (g : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) =
        eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) * g := by
    intro g
    obtain ⟨hg12, hc1⟩ := mem_inf.mp g.2
    obtain ⟨hO, hc2⟩ := mem_inf.mp hg12
    exact ⟨⟨h2, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO,
      mem_centralizer_singleton_iff.mp hc2⟩, mem_centralizer_singleton_iff.mp hc1⟩
  let φ : cenOne K → ySet K × leviSet K := fun g =>
    (⟨yThree (g : VEnd K), by
        obtain ⟨hh, hc1⟩ := hmem g
        refine ⟨by rw [polar_comm]; exact polar_eTwo_yThree,
          by rw [polar_comm]; exact polar_fTwo_yThree, (decomp_commute_eichOne hh hc1).1⟩⟩,
      ⟨ellThree (g : VEnd K), by
        obtain ⟨hh, hc1⟩ := hmem g
        exact ⟨hh.ell_map, hh.ell_commute_La,
          ⟨lamThree (g : VEnd K), hh.lam, fun v hv => hh.ell_apply_of_fix hv⟩,
          (decomp_commute_eichOne hh hc1).2⟩⟩)
  have hφ : Function.Injective φ := by
    intro g g' h
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨hy, hl⟩ := h
    apply Subtype.ext
    calc (g : VEnd K) = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree (g : VEnd K)) *
          ellThree (g : VEnd K) := (mul_inv_cancel_left _ _).symm
      _ = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (yThree (g' : VEnd K)) *
          ellThree (g' : VEnd K) := by rw [hy, hl]
      _ = g' := mul_inv_cancel_left _ _
  calc Nat.card (cenOne K) ≤ Nat.card (ySet K × leviSet K) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (ySet K) * Nat.card (leviSet K) := Nat.card_prod _ _
    _ ≤ Nat.card K ^ 3 * Nat.card (leviSet K) := Nat.mul_le_mul_right _ card_ySet_le

end CFSG.ComponentClassification.HarrisLit.T1.S74
