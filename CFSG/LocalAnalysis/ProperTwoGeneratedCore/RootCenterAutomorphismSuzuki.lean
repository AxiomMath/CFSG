module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiOppositeRootCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismData

public section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.SuzukiModel
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_one_of_pow_eq_self (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : K}
    (hx : x ^ 2 ^ (a + 1) = x) : x = 0 ∨ x = 1 := by
  obtain ⟨-, -, hθ, -⟩ := suzuki_frobenius_exponents a K hK
  have h := hθ x
  rw [hx, hx] at h
  have h' : x * (x - 1) = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h').imp id sub_eq_zero.1

theorem suzukiSElt_commute_iff
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v c d : K) :
    suzukiSElt a K u v * suzukiSElt a K c d = suzukiSElt a K c d * suzukiSElt a K u v ↔
      u ^ 2 ^ (a + 1) * c = c ^ 2 ^ (a + 1) * u := by
  rw [suzukiSElt_mul hK, suzukiSElt_mul hK, suzukiSElt_inj]
  exact ⟨fun h => by linear_combination h.2, fun h => ⟨add_comm u c, by linear_combination h⟩⟩

theorem eq_zero_or_eq_of_commute
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {u v c d : K} (hu : u ≠ 0)
    (h : suzukiSElt a K u v * suzukiSElt a K c d = suzukiSElt a K c d * suzukiSElt a K u v) :
    c = 0 ∨ c = u := by
  rw [suzukiSElt_commute_iff hK] at h
  have hx : (c / u) ^ 2 ^ (a + 1) = c / u := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero _ hu) hu]
    linear_combination -h
  rcases eq_zero_or_eq_one_of_pow_eq_self hK hx with h0 | h1
  · exact Or.inl ((div_eq_zero_iff.1 h0).resolve_right hu)
  · exact Or.inr ((div_eq_one_iff_eq hu).1 h1)

theorem mem_suzukiZ0_iff_commute
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} :
    x ∈ suzukiZ0 a K ↔ x ∈ suzukiU a K ∧ ∀ y ∈ suzukiU a K, x * y = y * x := by
  refine ⟨fun hx => ⟨suzukiZ0_le_suzukiU hx,
    fun y hy => (suzuki_unipotent_structure hK).2.2.2.2.2.1 x hx y hy⟩, ?_⟩
  rintro ⟨hx, hc⟩
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  by_cases hu : u = 0
  · exact (mem_suzukiZ0_iff hK).2 ⟨v, by rw [hu]⟩
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  obtain ⟨h, hh⟩ := exists_add_pow_ne_zero hK ha
  rcases eq_zero_or_eq_of_commute hK hu (hc _ (suzukiSElt_mem_suzukiU a K (u * h) 0)) with
    h0 | h1
  · obtain rfl : h = 0 := (mul_eq_zero.1 h0).resolve_left hu
    exact absurd (by simp) hh
  · obtain rfl : h = 1 := mul_left_cancel₀ hu (h1.trans (mul_one u).symm)
    exact absurd (by rw [one_pow]; linear_combination h2) hh

theorem suzukiU_rootCenterAutomorphisms
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    RootCenterAutomorphisms (suzukiU a K) (suzukiZ0 a K) (2 ^ (2 * a + 1)) := by
  have hpt := suzukiPointAction_suzukiGroup hK
  have : FaithfulSMul (suzukiGroup a K) (suzukiOmegaSub hK) := faithfulSMul_suzukiOmegaSub ha hK
  have : MulAction.IsMultiplyPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) 2 :=
    hpt.isMultiplyPretransitive
  have : MulAction.IsPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hcent := (suzuki_unipotent_structure hK).2.2.2.2.2.1
  have hinner : ∀ r ∈ suzukiU a K, (suzukiU a K).map (MulAut.conj r).toMonoidHom =
      suzukiU a K ∧ ∀ z ∈ suzukiZ0 a K, MulAut.conj r z = z := fun r hr =>
    ⟨map_conj_of_mem hr, fun z hz => by
      rw [MulAut.conj_apply, ← hcent z hz r hr, mul_inv_cancel_right]⟩
  have hA : ∀ γ : MulAut (suzukiGroup a K), (suzukiU a K).map γ.toMonoidHom = suzukiU a K →
      (∀ z ∈ suzukiZ0 a K, γ z = z) → ∃ r ∈ suzukiU a K, MulAut.conj r = γ := by
    intro γ hγU hγZ
    obtain ⟨P, hPU, -, -, ⟨φ, hφ, hφξ, hφ0, -, -⟩, -, -⟩ :=
      Suzuki_model_opposite_root_interface ha hK
    have hγP : γ • P = P := Sylow.ext (by rw [coe_mulAut_smul_sylow', hPU, hγU])
    have hWP : suzukiWElt a K • P ≠ P := by
      intro h
      apply hpt.ne
      apply φ.injective
      rw [hφξ, hφ0, h]
    set S := γ • (suzukiWElt a K • P) with hS
    have hSξ : φ.symm S ≠ ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ := by
      intro h
      apply hWP
      have h' : S = P := by rw [← φ.apply_symm_apply S, h, hφξ]
      exact smul_left_cancel γ
        (show γ • (suzukiWElt a K • P) = γ • P from h'.trans hγP.symm)
    obtain ⟨r, hr, -⟩ := hpt.regular _ _ hpt.ne.symm hSξ
    have hrS : (r : suzukiGroup a K) • (suzukiWElt a K • P) = S := by
      rw [← hφ0, ← hφ, hr, Equiv.apply_symm_apply]
    refine ⟨r, r.2, ?_⟩
    set γ' := (MulAut.conj (r : suzukiGroup a K))⁻¹ * γ with hγ'
    have hγ'S : γ' • (suzukiWElt a K • P) = suzukiWElt a K • P := by
      rw [hγ', mul_smul, ← hS, ← hrS, Sylow.smul_def, inv_smul_smul]
    have hγ'U : (suzukiU a K).map γ'.toMonoidHom = suzukiU a K := by
      rw [hγ', map_mul_mulAut, hγU, ← map_inv]
      exact map_conj_of_mem (inv_mem r.2)
    have hγ'W : ((suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom).map
        γ'.toMonoidHom = (suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom := by
      have h := congrArg (fun S : Sylow 2 (suzukiGroup a K) => (S : Subgroup (suzukiGroup a K)))
        hγ'S
      simp only [coe_mulAut_smul_sylow', coe_smul_sylow', hPU] at h
      exact h
    have hγ'Q : ∀ b : K, γ' (suzukiSElt a K 0 b) = suzukiSElt a K 0 b := fun b => by
      have hz : suzukiSElt a K 0 b ∈ suzukiZ0 a K := (mem_suzukiZ0_iff hK).2 ⟨b, rfl⟩
      rw [hγ', MulAut.mul_apply, hγZ _ hz, MulAut.conj_inv_apply, mul_assoc,
        hcent _ hz _ r.2, inv_mul_cancel_left]
    exact inv_mul_eq_one.1 (suzuki_opposite_root_center_action_faithful ha hK γ' hγ'U hγ'W hγ'Q)
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  apply RootCenterAutomorphisms.of_core (fun x => mem_suzukiZ0_iff_commute ha hK)
    (isElementaryAbelian_of_isElemAbelian (isElemAbelian_suzukiZ0 hK)) (card_suzukiZ0 hK)
  · intro x hx
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
    rw [suzukiSElt_sq hK]
    exact (mem_suzukiZ0_iff hK).2 ⟨_, rfl⟩
  · exact injOn_conj_of_le_stabilizer hpt.le_stabilizer_left
  · ext γ
    refine ⟨fun ⟨hγU, hγZ⟩ => ?_, ?_⟩
    · obtain ⟨r, hr, hrγ⟩ := hA γ hγU hγZ
      exact ⟨r, hr, hrγ⟩
    · rintro ⟨r, hr, rfl⟩
      exact hinner r hr
  · intro R₀ hZR₀ hR₀U hidx
    ext γ
    refine ⟨fun ⟨⟨hγU, hγZ⟩, hfix⟩ => ?_, ?_⟩
    · obtain ⟨r, hr, rfl⟩ := hA γ hγU hγZ
      refine ⟨r, ?_, rfl⟩
      by_contra hrZ
      obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hr
      have hu : u ≠ 0 := fun hu => hrZ ((mem_suzukiZ0_iff hK).2 ⟨v, by rw [hu]⟩)
      have hsub : (R₀ : Set (suzukiGroup a K)) ⊆ (fun p : K × K => suzukiSElt a K p.1 p.2) ''
          (({0, u} : Set K) ×ˢ Set.univ) := by
        intro x hx
        obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 (hR₀U hx)
        have hcomm := hfix _ hx
        rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hcomm
        exact ⟨(c, d), ⟨eq_zero_or_eq_of_commute hK hu hcomm, trivial⟩, rfl⟩
      have hle : Nat.card R₀ ≤ 2 * 2 ^ (2 * a + 1) := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
        refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
          ((Set.ncard_image_le (Set.toFinite _)).trans ?_)
        rw [Set.ncard_prod, Set.ncard_pair hu.symm, Set.ncard_univ, hK]
      have hge : (2 ^ (2 * a + 1)) ^ 2 ≤ 2 * Nat.card R₀ := by
        have h := Subgroup.relIndex_mul_card (H := R₀) (K := suzukiU a K)
        rw [inf_of_le_left hR₀U, (suzuki_unipotent_structure hK).2.1] at h
        rw [← h]
        exact Nat.mul_le_mul_right _ hidx
      nlinarith
    · rintro ⟨r, hr, rfl⟩
      refine ⟨hinner r (suzukiZ0_le_suzukiU hr), fun x hx => ?_⟩
      rw [MulAut.conj_apply, hcent r hr x (hR₀U hx), mul_inv_cancel_right]

end CFSG.ProperTwoGeneratedCore.RootCenter
