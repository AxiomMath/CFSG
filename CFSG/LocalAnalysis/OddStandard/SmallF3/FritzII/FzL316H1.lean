module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H0

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

private theorem fzlV4_card : Nat.card fzlV4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem fzlV4_normal : fzlV4.Normal where
  conj_mem := by decide

private theorem not_three_dvd_orderOf_of_isPGroup {G : Type} [Group G] {H : Subgroup G}
    (hH : IsPGroup 2 H) {g : G} (hg : g ∈ H) : ¬ 3 ∣ orderOf g := by
  obtain ⟨n, hn⟩ := hH ⟨g, hg⟩
  have hn' : g ^ 2 ^ n = 1 := by
    have := congrArg (Subtype.val) hn
    simpa using this
  have hdvd : orderOf g ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn'
  intro h3
  have h32 : 3 ∣ 2 ^ n := h3.trans hdvd
  have h32' : 3 ∣ 2 := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow h32
  norm_num at h32'

private theorem FzZ2xSigma4_pow_twelve (z : FzZ2xSigma4) : z ^ 12 = 1 := by
  have h : ∀ z : FzZ2xSigma4, z ^ 12 = 1 := by decide +kernel
  exact h z

private theorem three_dvd_orderOf_of_pow_twelve (z : FzZ2xSigma4) (h12 : z ^ 12 = 1)
    (h4 : z ^ 4 ≠ 1) : 3 ∣ orderOf z := by
  have hdvd : orderOf z ∣ 12 := orderOf_dvd_iff_pow_eq_one.mpr h12
  by_contra h3
  have hcop : Nat.Coprime (orderOf z) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
  have hdvd4 : orderOf z ∣ 4 := hcop.dvd_of_dvd_mul_right (m := 4) hdvd
  exact h4 (orderOf_dvd_iff_pow_eq_one.mp hdvd4)

private theorem fzl_finite_check (g : FzZ2xSigma4) (hg : g ∉ fzlK8) :
    (∃ h : FzZ2xSigma4, (g * (h * g * h⁻¹)) ^ 4 ≠ 1) ∨ g ^ 4 ≠ 1 := by
  revert g
  decide +kernel

theorem fzl_card_K4 : Nat.card fzlK4 = 4 := by
  unfold fzlK4
  rw [Nat.card_congr (Subgroup.prodEquiv ⊥ fzlV4).toEquiv, Nat.card_prod, Subgroup.card_bot,
    fzlV4_card]

theorem fzl_card_K8 : Nat.card fzlK8 = 8 := by
  unfold fzlK8
  rw [Nat.card_congr (Subgroup.prodEquiv ⊤ fzlV4).toEquiv, Nat.card_prod, Subgroup.card_top,
    Nat.card_eq_fintype_card, fzlV4_card]
  norm_num [ZMod.card]

theorem fzl_K4_normal : fzlK4.Normal := by
  haveI : fzlV4.Normal := fzlV4_normal
  unfold fzlK4
  infer_instance

theorem fzl_K8_normal : fzlK8.Normal := by
  haveI : fzlV4.Normal := fzlV4_normal
  unfold fzlK8
  infer_instance

theorem fzl_K4_le_K8 : fzlK4 ≤ fzlK8 := by
  unfold fzlK4 fzlK8
  exact Subgroup.prod_mono bot_le le_rfl

theorem fzl_K8_sq : ∀ x ∈ fzlK8, x ^ 2 = 1 := by
  decide +kernel

theorem fzl_K8_comm : ∀ x ∈ fzlK8, ∀ y ∈ fzlK8, x * y = y * x := by
  decide +kernel

theorem fzl_K8_comm_mem_K4 :
    ∀ u ∈ fzlK8, ∀ y : FzZ2xSigma4, u * y * u⁻¹ * y⁻¹ ∈ fzlK4 := by
  decide +kernel

private theorem fzlK8_isPGroup : IsPGroup 2 fzlK8 := by
  apply IsPGroup.of_card (n := 3)
  rw [fzl_card_K8]
  norm_num

theorem fzl_pCore_eq : CFSG.pCore 2 FzZ2xSigma4 = fzlK8 := by
  apply le_antisymm
  · intro x hx
    by_contra hxV
    rcases fzl_finite_check x hxV with ⟨h, hh⟩ | hx4
    · have hmem : x * (h * x * h⁻¹) ∈ CFSG.pCore 2 FzZ2xSigma4 :=
        (CFSG.pCore 2 FzZ2xSigma4).mul_mem hx
          ((CFSG.pCore_normal (p := 2) (G := FzZ2xSigma4)).conj_mem x hx h)
      have h3 : 3 ∣ orderOf (x * (h * x * h⁻¹)) :=
        three_dvd_orderOf_of_pow_twelve _ (FzZ2xSigma4_pow_twelve _) hh
      exact (not_three_dvd_orderOf_of_isPGroup
        (CFSG.pCore_isPGroup (p := 2) (G := FzZ2xSigma4)) hmem) h3
    · have h3 : 3 ∣ orderOf x :=
        three_dvd_orderOf_of_pow_twelve x (FzZ2xSigma4_pow_twelve x) hx4
      exact (not_three_dvd_orderOf_of_isPGroup
        (CFSG.pCore_isPGroup (p := 2) (G := FzZ2xSigma4)) hx) h3
  · exact le_sSup (show fzlK8 ∈ {K : Subgroup FzZ2xSigma4 | K.Normal ∧ IsPGroup 2 K} from
      ⟨fzl_K8_normal, fzlK8_isPGroup⟩)

theorem fzl_K4_fpf : ∀ a : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 →
    ∀ v ∈ fzlK4, a * v * a⁻¹ = v → v = 1 := by
  decide +kernel

theorem fzl_K4_comm_surj : ∀ a : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 →
    ∀ v ∈ fzlK4, ∃ w ∈ fzlK4, w * a * w⁻¹ * a⁻¹ = v := by
  decide +kernel

private theorem fzl_orbit_ne_one : ∀ a : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 →
    ∀ v ∈ fzlK4, v ≠ 1 → a * v * a⁻¹ ≠ 1 := by
  intro a
  fin_cases a <;> decide +kernel

private theorem fzl_orbit_ne_self : ∀ a : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 →
    ∀ v ∈ fzlK4, v ≠ 1 → a * v * a⁻¹ ≠ v := by
  intro a
  fin_cases a <;> decide +kernel

private theorem fzl_orbit_mem : ∀ a : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 →
    ∀ v ∈ fzlK4, v ≠ 1 →
      ∀ x ∈ fzlK4,
        x ∈ ({1, v, a * v * a⁻¹, v * (a * v * a⁻¹)} : Finset FzZ2xSigma4) := by
  intro a
  fin_cases a <;> decide +kernel

theorem fzl_K4_orbit : ∀ a : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 → ∀ v ∈ fzlK4, v ≠ 1 →
    a * v * a⁻¹ ≠ 1 ∧ a * v * a⁻¹ ≠ v ∧
      ∀ x ∈ fzlK4, x = 1 ∨ x = v ∨ x = a * v * a⁻¹ ∨ x = v * (a * v * a⁻¹) := by
  intro a ha3 ha1 v hv hv1
  refine ⟨fzl_orbit_ne_one a ha3 ha1 v hv hv1, fzl_orbit_ne_self a ha3 ha1 v hv hv1, ?_⟩
  intro x hx
  have hmem := fzl_orbit_mem a ha3 ha1 v hv hv1 x hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem fzl_kappa_facts : fzlKappa ∈ fzlK8 ∧ fzlKappa ∉ fzlK4 ∧ fzlKappa ^ 2 = 1 ∧
    ∀ x : FzZ2xSigma4, x * fzlKappa = fzlKappa * x := by
  decide +kernel

theorem fzl_tau_image : ∀ a c : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 → c ^ 2 = 1 → c ≠ 1 →
    c * a = a * c → c = fzlKappa := by
  intro a
  fin_cases a <;> decide +kernel

theorem fzl_lam_image : ∀ a b : FzZ2xSigma4, a ^ 3 = 1 → a ≠ 1 → b ^ 2 = 1 →
    b * a * b⁻¹ = a⁻¹ → ∃ v ∈ fzlK4, b * v * b⁻¹ * v⁻¹ ≠ 1 := by
  intro a
  fin_cases a <;> decide +kernel

end CFSG.OddStandard.SmallF3.FritzII
