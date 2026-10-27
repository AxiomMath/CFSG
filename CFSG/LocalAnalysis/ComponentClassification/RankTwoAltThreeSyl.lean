module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThreeCover
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixAut

public section

namespace CFSG.ComponentClassification.RankTwoAlt.Three

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB
  CFSG.ComponentClassification.AschbacherTightEmbedding

section Perm

variable {n : ℕ}

noncomputable abbrev vA (h : 4 ≤ n) : Perm (Fin n) :=
  viaEmbeddingHom (fourEmb h) (swap 0 1 * swap 2 3)

noncomputable abbrev vB (h : 4 ≤ n) : Perm (Fin n) :=
  viaEmbeddingHom (fourEmb h) (swap 0 2 * swap 1 3)

theorem mem_range_fourEmb_iff (h : 4 ≤ n) (x : Fin n) :
    x ∈ Set.range (fourEmb h) ↔ (x : ℕ) < 4 := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [fourEmb_apply]
    exact i.2
  · intro hx
    exact ⟨⟨x, hx⟩, Fin.ext (by rw [fourEmb_apply])⟩

theorem commute_of_mem_rootVP (h : 4 ≤ n) {σ : Perm (Fin n)} (h1 : Commute σ (vA h))
    (h2 : Commute σ (vB h)) {v : Perm (Fin n)} (hv : v ∈ rootVP n) : Commute σ v := by
  rw [rootVP_eq h] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  | one => rw [map_one]; exact Commute.one_right σ
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
  | inv x _ hx => rw [map_inv]; exact hx.inv_right

theorem mul_self_of_mem_rootVP (h : 4 ≤ n) {v : Perm (Fin n)} (hv : v ∈ rootVP n) : v * v = 1 := by
  rw [rootVP_eq h] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  rw [← map_mul, mul_self_of_mem_kleinFour hk, map_one]

theorem exists_mem_rootVP_fix (h : 4 ≤ n) {σ : Perm (Fin n)} (h1 : Commute σ (vA h))
    (h2 : Commute σ (vB h)) :
    ∃ v ∈ rootVP n, ∀ x : Fin n, (x : ℕ) < 4 → (σ * v) x = x := by
  obtain ⟨k, hk, hσk⟩ := exists_kleinFour_of_commute (fourEmb h) h1 h2
  refine ⟨viaEmbeddingHom (fourEmb h) k⁻¹, ?_, fun x hx => ?_⟩
  · rw [rootVP_eq h]
    exact ⟨k⁻¹, inv_mem hk, rfl⟩
  · obtain ⟨i, rfl⟩ := (mem_range_fourEmb_iff h x).mpr hx
    rw [Perm.mul_apply, viaEmbeddingHom_apply_image, hσk, Perm.coe_inv, Equiv.apply_symm_apply]

theorem isSwap_of_fix (hn : n = 6 ∨ n = 7) {τ : Perm (Fin n)}
    (hfix : ∀ x : Fin n, (x : ℕ) < 4 → τ x = x) (h2 : τ * τ = 1) (h1 : τ ≠ 1) :
    ∃ x y : Fin n, 4 ≤ (x : ℕ) ∧ 4 ≤ (y : ℕ) ∧ x ≠ y ∧ τ = swap x y := by
  classical
  have hsupp : τ.support ⊆ Finset.univ.filter (fun x : Fin n => 4 ≤ (x : ℕ)) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hlt
    exact (Perm.mem_support.mp hx) (hfix x (by omega))
  have hle : τ.support.card ≤ 3 := by
    refine (Finset.card_le_card hsupp).trans ?_
    rcases hn with rfl | rfl <;> decide
  have hdvd := two_dvd_card_support (σ := τ) (by rw [sq]; exact h2)
  have hne : τ.support.card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, support_eq_empty_iff]
    exact h1
  have hcard : τ.support.card = 2 := by omega
  obtain ⟨x, y, hxy, rfl⟩ := card_support_eq_two.mp hcard
  refine ⟨x, y, ?_, ?_, hxy, rfl⟩
  · have hx : x ∈ (swap x y).support := by
      rw [Perm.mem_support, swap_apply_left]
      exact hxy.symm
    exact (Finset.mem_filter.mp (hsupp hx)).2
  · have hy : y ∈ (swap x y).support := by
      rw [Perm.mem_support, swap_apply_right]
      exact hxy
    exact (Finset.mem_filter.mp (hsupp hy)).2

theorem swap01_mul_s45 (hn : n = 6 ∨ n = 7) :
    swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ * s45 (six_le_of hn) =
      s45 (six_le_of hn) * swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ := by
  rcases hn with rfl | rfl <;> decide

theorem exists_conj_s45 (hn : n = 6 ∨ n = 7) {σ : Perm (Fin n)}
    (h1 : Commute σ (vA (by omega))) (h2 : Commute σ (vB (by omega))) (hσ2 : σ * σ = 1)
    (hσV : σ ∉ rootVP n) :
    ∃ v ∈ rootVP n, ∃ ρ ∈ alternatingGroup (Fin n), ρ * (σ * v) * ρ⁻¹ = s45 (six_le_of hn) := by
  have h4 : 4 ≤ n := by omega
  obtain ⟨v, hv, hfix⟩ := exists_mem_rootVP_fix h4 h1 h2
  have hσv := commute_of_mem_rootVP h4 h1 h2 hv
  have hv2 := mul_self_of_mem_rootVP h4 hv
  have hτ2 : σ * v * (σ * v) = 1 := by
    calc σ * v * (σ * v) = σ * (v * σ) * v := by group
      _ = σ * (σ * v) * v := by rw [hσv.eq]
      _ = σ * σ * (v * v) := by group
      _ = 1 := by rw [hσ2, hv2, one_mul]
  have hτ1 : σ * v ≠ 1 := by
    intro h
    apply hσV
    have : σ = v⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_mem hv
  obtain ⟨x, y, -, -, hxy, hτ⟩ := isSwap_of_fix hn hfix hτ2 hτ1
  have h45 : (⟨4, by omega⟩ : Fin n) ≠ ⟨5, by omega⟩ := by simp
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_swap hxy h45)
  rw [← hτ] at hc
  by_cases hs : sign c = 1
  · exact ⟨v, hv, c, mem_alternatingGroup.mpr hs, hc⟩
  · refine ⟨v, hv, swap ⟨0, by omega⟩ ⟨1, by omega⟩ * c, ?_, ?_⟩
    · rw [mem_alternatingGroup, map_mul, sign_swap (by simp), Int.units_ne_iff_eq_neg.mp hs]
      decide
    · calc swap ⟨0, by omega⟩ ⟨1, by omega⟩ * c * (σ * v) *
            (swap ⟨0, by omega⟩ ⟨1, by omega⟩ * c)⁻¹ =
          swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ * (c * (σ * v) * c⁻¹) *
            swap ⟨0, by omega⟩ ⟨1, by omega⟩ := by
            rw [_root_.mul_inv_rev, swap_inv]; group
        _ = s45 (six_le_of hn) := by
            rw [hc, s45, ← s45, swap01_mul_s45 hn, mul_assoc, swap_mul_self, mul_one]

theorem eq_one_of_commute_of_odd (hn : n = 6 ∨ n = 7) {σ σ' : Perm (Fin n)}
    (h1 : Commute σ (vA (by omega))) (h2 : Commute σ (vB (by omega))) (hσ2 : σ * σ = 1)
    (hσV : σ ∉ rootVP n) (h1' : Commute σ' (vA (by omega))) (h2' : Commute σ' (vB (by omega)))
    {m : ℕ} (hm : Odd m) (hσ'm : σ' ^ m = 1) (hcomm : Commute σ' σ) : σ' = 1 := by
  classical
  have h4 : 4 ≤ n := by omega
  obtain ⟨k, hk, hσk⟩ := exists_kleinFour_of_commute (fourEmb h4) h1' h2'
  have hk2 := mul_self_of_mem_kleinFour hk
  have hpow : ∀ j : ℕ, ∀ i : Fin 4, (σ' ^ j) (fourEmb h4 i) = fourEmb h4 ((k ^ j) i) := by
    intro j
    induction j with
    | zero => intro i; rfl
    | succ j ih =>
      intro i
      rw [pow_succ, Perm.mul_apply, hσk, ih, pow_succ, Perm.mul_apply]
  have hkm : k ^ m = k := by
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, hk2, one_pow, one_mul]
  have hfix0 : ∀ x : Fin n, (x : ℕ) < 4 → σ' x = x := by
    intro x hx
    obtain ⟨i, rfl⟩ := (mem_range_fourEmb_iff h4 x).mpr hx
    have h := hpow m i
    rw [hσ'm, hkm, Perm.one_apply] at h
    rw [hσk, ← h]
  obtain ⟨v, hv, hfix⟩ := exists_mem_rootVP_fix h4 h1 h2
  have hσv := commute_of_mem_rootVP h4 h1 h2 hv
  have hv2 := mul_self_of_mem_rootVP h4 hv
  have hτ2 : σ * v * (σ * v) = 1 := by
    calc σ * v * (σ * v) = σ * (v * σ) * v := by group
      _ = σ * (σ * v) * v := by rw [hσv.eq]
      _ = σ * σ * (v * v) := by group
      _ = 1 := by rw [hσ2, hv2, one_mul]
  have hτ1 : σ * v ≠ 1 := by
    intro h
    apply hσV
    have : σ = v⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_mem hv
  obtain ⟨x, y, hx4, hy4, hxy, hτ⟩ := isSwap_of_fix hn hfix hτ2 hτ1
  have hσ'v := commute_of_mem_rootVP h4 h1' h2' hv
  have hcτ : Commute σ' (swap x y) := by
    rw [← hτ]
    exact hcomm.mul_right hσ'v
  have hsw : swap (σ' x) (σ' y) = swap x y := by
    rw [swap_apply_apply, hcτ.eq, mul_inv_cancel_right]
  have hxy' : σ' x = x ∧ σ' y = y := by
    have hv1 := congrArg (fun f : Perm (Fin n) => f (σ' x)) hsw
    simp only [swap_apply_left] at hv1
    by_cases h1x : σ' x = x
    · rw [h1x, swap_apply_left] at hv1
      exact ⟨h1x, hv1⟩
    · by_cases h2x : σ' x = y
      · exfalso
        rw [h2x, swap_apply_right] at hv1
        obtain ⟨j, rfl⟩ := hm
        have hsq' : (σ' ^ 2) y = y := by rw [sq, Perm.mul_apply, hv1, h2x]
        have := congrArg (fun f : Perm (Fin n) => f x) hσ'm
        simp only [Perm.one_apply] at this
        rw [pow_succ, pow_mul, Perm.mul_apply, h2x,
          pow_apply_eq_self_of_apply_eq_self hsq' j] at this
        exact hxy this.symm
      · rw [swap_apply_of_ne_of_ne h1x h2x] at hv1
        exact absurd (σ'.injective hv1).symm hxy
  have hsupp :
      σ'.support ⊆ ((Finset.univ.filter (fun z : Fin n => 4 ≤ (z : ℕ))).erase x).erase y := by
    intro z hz
    have hz' := Perm.mem_support.mp hz
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => hz' (h ▸ hxy'.2), fun h => hz' (h ▸ hxy'.1), ?_⟩
    by_contra hlt
    exact hz' (hfix0 z (by omega))
  have hcard : σ'.support.card ≤ 1 := by
    refine (Finset.card_le_card hsupp).trans ?_
    have hx : x ∈ Finset.univ.filter (fun z : Fin n => 4 ≤ (z : ℕ)) := by simp [hx4]
    have hy : y ∈ (Finset.univ.filter (fun z : Fin n => 4 ≤ (z : ℕ))).erase x := by
      simp [hy4, hxy.symm]
    rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]
    rcases hn with rfl | rfl <;> decide
  have h0 : σ'.support.card = 0 := by
    have := card_support_ne_one σ'
    omega
  rwa [Finset.card_eq_zero, support_eq_empty_iff] at h0

theorem exists_conjPerm (hn : n = 6 ∨ n = 7)
    (α : MulAut (alternatingGroup (Fin n))) (hα : ∀ u ∈ rootV n, α u = u) :
    ∃ σ : Perm (Fin n), α = conjPerm n σ ∧ Commute σ (vA (by omega)) ∧
      Commute σ (vB (by omega)) := by
  have h4 : 4 ≤ n := by omega
  obtain ⟨σ, hσ⟩ : ∃ σ : Perm (Fin n), α = conjPerm n σ := by
    rcases hn with rfl | rfl
    · obtain ⟨σ, hσ⟩ := mem_range_conj_of_normalizes_rootFour α (fun u hu => by
        have hmem : u ∈ rootV 6 := by
          have : (u : Perm (Fin 6)) ∈ rootVP 6 := (mem_rootVP_six_iff).mpr (Or.inr hu)
          obtain ⟨u', hu', hu'u⟩ := this
          rwa [← Subtype.ext hu'u]
        rw [hα u hmem]
        exact hu)
      exact ⟨σ, MulEquiv.ext fun x => Subtype.ext (by rw [hσ, conjPerm_apply])⟩
    · obtain ⟨σ, hσ⟩ := conjPerm_surjective (Or.inr le_rfl) α
      exact ⟨σ, hσ.symm⟩
  refine ⟨σ, hσ, ?_, ?_⟩
  · have hmem : (⟨vA h4, mem_alternatingGroup.mpr (by
        rw [sign_viaEmbeddingHom]; decide)⟩ : alternatingGroup (Fin n)) ∈ rootV n :=
      (mem_rootV_iff h4 _).mpr ⟨_, swap_mem_kleinFour_one, rfl⟩
    have h := congrArg Subtype.val (hα _ hmem)
    rw [hσ, conjPerm_apply] at h
    calc σ * vA h4 = σ * vA h4 * σ⁻¹ * σ := by group
      _ = vA h4 * σ := by rw [h]
  · have hmem : (⟨vB h4, mem_alternatingGroup.mpr (by
        rw [sign_viaEmbeddingHom]; decide)⟩ : alternatingGroup (Fin n)) ∈ rootV n :=
      (mem_rootV_iff h4 _).mpr ⟨_, swap_mem_kleinFour_two, rfl⟩
    have h := congrArg Subtype.val (hα _ hmem)
    rw [hσ, conjPerm_apply] at h
    calc σ * vB h4 = σ * vB h4 * σ⁻¹ * σ := by group
      _ = vB h4 * σ := by rw [h]

end Perm

end CFSG.ComponentClassification.RankTwoAlt.Three
