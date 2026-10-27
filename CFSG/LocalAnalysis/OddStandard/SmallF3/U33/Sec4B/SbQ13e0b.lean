module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def q13AN (t tau x₁ x₂ rho : G) : Subgroup G :=
  q13A t tau x₁ x₂ rho ⊔ zpowers tau

@[expose] def q13CLP (t tau x₁ x₂ rho om : G) : Subgroup G :=
  q13L t tau x₁ x₂ rho om ⊓ centralizer ((q13P t tau x₁ x₂ rho om : Subgroup G) : Set G)

variable [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_A_sq_mem_V (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, a * a ∈ fourGrp x₁ x₂ := by
  intro a ha
  have hmem : a ^ 2 ∈ q13A t tau x₁ x₂ rho := by
    simpa [pow_two] using (q13A t tau x₁ x₂ rho).mul_mem ha ha
  have hsq : a ^ 2 * a ^ 2 = 1 := by
    have ha4 : a ^ 4 = 1 := q13d_P_pow_four h hD.A_cent a (q13d_A_le_P h ha)
    rw [← pow_add]
    norm_num
    exact ha4
  have hV := q13b_omega1_A h (a ^ 2) hmem hsq
  simpa [pow_two] using hV

private lemma q13e_tau_zpow_odd (h : Q13Om t L S x₁ x₂ lam rho tau om) {k : ℤ}
    (hk : k % 2 = 1) : tau ^ k = tau := by
  have h2 : tau ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, q13a_tau_mul_self h]
  rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_one, zpow_mul, h2, one_zpow, mul_one]

private lemma q13e_gam_zpow_two_mul (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) (k : ℤ) :
    (t * om) ^ (2 * k) = tau ^ k := by
  rw [zpow_mul, zpow_ofNat, hD.gam_sq]

private lemma q13e_gam_zpow_of_even (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {k : ℤ} (hk : k % 2 = 0) :
    (t * om) ^ k ∈ zpowers tau := by
  have hk' : k = 2 * (k / 2) := by
    have := Int.emod_add_mul_ediv k 2
    rw [hk, zero_add] at this
    exact this.symm
  rw [hk', q13e_gam_zpow_two_mul h hD]
  exact Subgroup.zpow_mem_zpowers tau (k / 2)

private lemma q13e_gam_zpow_odd (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {k : ℤ} (hk : k % 2 = 1) :
    (t * om) ^ (2 * k) = tau := by
  rw [q13e_gam_zpow_two_mul h hD]
  exact q13e_tau_zpow_odd h hk

private lemma q13e_sq_mul_zpow {a g : G} (hc : Commute g a) (k : ℤ) :
    (a * g ^ k) * (a * g ^ k) = a * a * g ^ (2 * k) := by
  have hgk : g ^ k * a = a * g ^ k := hc.zpow_left k
  calc (a * g ^ k) * (a * g ^ k)
      = a * (g ^ k * a) * g ^ k := by group
    _ = a * (a * g ^ k) * g ^ k := by rw [hgk]
    _ = a * a * (g ^ k * g ^ k) := by group
    _ = a * a * g ^ (k + k) := by rw [← zpow_add]
    _ = a * a * g ^ (2 * k) := by rw [show k + k = 2 * k by ring]

private lemma q13e_z4pow_sq :
    ∀ x : Outside.Z4pow 3, x ^ 2 = 1 → ∃ y : Outside.Z4pow 3, y ^ 2 = x := by
  decide +kernel

private lemma q13e_x_mem_M' (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ∈ ctxM t tau x₁ x₂ ∧ x₂ ∈ ctxM t tau x₁ x₂ := by
  have hbase : baseGrp x₁ x₂ ≤ ctxM t tau x₁ x₂ :=
    h.c11.base_le_Q.trans
      ((l12_Q_le_R h.c11).trans (h.c11.R_le_O.trans (p0_O_le_M t tau x₁ x₂)))
  exact ⟨hbase (Subgroup.subset_closure (by simp)),
    hbase (Subgroup.subset_closure (by simp))⟩

theorem q13e_V_normal_L (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ v ∈ fourGrp x₁ x₂, g * v * g⁻¹ ∈ fourGrp x₁ x₂ := by
  have hBnorm : q13B t tau x₁ x₂ rho om ≤
      Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    intro b hb
    have hbC : b ∈ Subgroup.centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hb).2
    have hbV : b ∈ Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (q13b_V_le_N h) hbC
    exact Subgroup.centralizer_le_normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) hbV
  have hMnorm : ctxM t tau x₁ x₂ ≤
      Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    exact ⟨fun hv => h.c11.normal_V.2 g hg v hv, fun hv => by
      have hmem := h.c11.normal_V.2 g⁻¹ ((ctxM t tau x₁ x₂).inv_mem hg) (g * v * g⁻¹) hv
      rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at hmem⟩
  have hKnorm : closure ({x₁, x₂, rho, lam} : Set G) ≤
      Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hMnorm (q13e_x_mem_M' h).1
    · exact hMnorm (q13e_x_mem_M' h).2
    · exact hMnorm (q13a_mem_M h).2.2.1
    · exact hMnorm (q13a_mem_M h).2.2.2.1
  intro g hg v hv
  rw [hD.L_eq] at hg
  have hsup : q13B t tau x₁ x₂ rho om ⊔ closure ({x₁, x₂, rho, lam} : Set G) ≤
      Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := sup_le hBnorm hKnorm
  exact (Subgroup.mem_normalizer_iff.mp (hsup hg) v).mp hv

theorem q13e_E0_normal_L :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ e ∈ q13E0 t tau x₁ x₂ rho om,
      g * e * g⁻¹ ∈ q13E0 t tau x₁ x₂ rho om := by
  intro g hg e he
  exact (Subgroup.mem_normalizer_iff.mp hg e).mp he

theorem q13e_A_le_AN : q13A t tau x₁ x₂ rho ≤ q13AN t tau x₁ x₂ rho :=
  le_sup_left

theorem q13e_tau_mem_AN : tau ∈ q13AN t tau x₁ x₂ rho :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)

theorem q13e_AN_le_P (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13AN t tau x₁ x₂ rho ≤ q13P t tau x₁ x₂ rho om :=
  sup_le (q13d_A_le_P h) (Subgroup.zpowers_le.mpr (q13d_tau_mem_P h))

theorem q13e_N_le_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxN tau x₁ x₂ ≤ q13AN t tau x₁ x₂ rho := by
  rw [ctxN, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact q13e_tau_mem_AN
  · exact q13e_A_le_AN (q13a_V_le_A h (Subgroup.subset_closure (by simp)))
  · exact q13e_A_le_AN (q13a_V_le_A h (Subgroup.subset_closure (by simp)))

theorem q13e_mem_AN' (h : Q13Om t L S x₁ x₂ lam rho tau om) {p : G} :
    p ∈ q13AN t tau x₁ x₂ rho ↔ ∃ a ∈ q13A t tau x₁ x₂ rho, p = a ∨ p = a * tau := by
  have hτcent : tau ∈ Subgroup.centralizer
      ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (q13d_A_cent_tau h)
  constructor
  · intro hp
    have hnorm : ∀ k ∈ zpowers tau, ∀ a ∈ q13A t tau x₁ x₂ rho,
        k * a * k⁻¹ ∈ q13A t tau x₁ x₂ rho := by
      intro k hk a ha
      have hkcent : k ∈ Subgroup.centralizer
          ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
        Subgroup.zpowers_le.mpr hτcent hk
      have hcomm : a * k = k * a := Subgroup.mem_centralizer_iff.mp hkcent a ha
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact ha
    obtain ⟨a, ha, k, hk, rfl⟩ := (mem_sup_iff_of_normalizes hnorm).mp hp
    rcases q13b_mem_zpowers_sq (q13a_tau_mul_self h) hk with hk1 | hk1
    · exact ⟨a, ha, Or.inl (by rw [hk1, mul_one])⟩
    · exact ⟨a, ha, Or.inr (by rw [hk1])⟩
  · rintro ⟨a, ha, rfl | rfl⟩
    · exact q13e_A_le_AN ha
    · exact Subgroup.mul_mem _ (q13e_A_le_AN ha) q13e_tau_mem_AN

theorem q13e_mem_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om)
    {p : G} :
    p ∈ q13AN t tau x₁ x₂ rho ↔ p ∈ q13P t tau x₁ x₂ rho om ∧ p ^ 2 ∈ fourGrp x₁ x₂ := by
  constructor
  · intro hp
    refine ⟨q13e_AN_le_P h hp, ?_⟩
    rcases (q13e_mem_AN' h).mp hp with ⟨a, ha, hp' | hp'⟩
    · rw [hp', pow_two]
      exact q13e_A_sq_mem_V h hD a ha
    · rw [hp', pow_two]
      have hsq : (a * tau) * (a * tau) = a * a := by
        calc (a * tau) * (a * tau) = a * (tau * a) * tau := by group
          _ = a * (a * tau) * tau := by rw [← q13d_A_cent_tau h a ha]
          _ = a * a * (tau * tau) := by group
          _ = a * a := by rw [q13a_tau_mul_self h, mul_one]
      rw [hsq]
      exact q13e_A_sq_mem_V h hD a ha
  · rintro ⟨hpP, hp2V⟩
    obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hD.A_cent).mp hpP
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · have hmem : (t * om) ^ k ∈ zpowers tau := q13e_gam_zpow_of_even h hD hk
      exact Subgroup.mul_mem _ (q13e_A_le_AN ha) (Subgroup.mem_sup_right hmem)
    · exfalso
      have hcomm : Commute (t * om) a := q13d_gam_cent_A h hD.A_cent a ha
      have hsq : (a * (t * om) ^ k) * (a * (t * om) ^ k) = a * a * tau := by
        rw [q13e_sq_mul_zpow hcomm, q13e_gam_zpow_odd h hD hk]
      have hp2V' : (a * (t * om) ^ k) * (a * (t * om) ^ k) ∈ fourGrp x₁ x₂ := by
        simpa [pow_two] using hp2V
      have hmem2 : (a * (t * om) ^ k) * (a * (t * om) ^ k) ∈ q13A t tau x₁ x₂ rho :=
        q13a_V_le_A h hp2V'
      have hmem1 : (a * a)⁻¹ ∈ q13A t tau x₁ x₂ rho :=
        (q13A t tau x₁ x₂ rho).inv_mem (q13a_V_le_A h (q13e_A_sq_mem_V h hD a ha))
      have heq : tau = (a * a)⁻¹ * ((a * (t * om) ^ k) * (a * (t * om) ^ k)) := by
        rw [hsq]; group
      have hmem : (a * a)⁻¹ * ((a * (t * om) ^ k) * (a * (t * om) ^ k)) ∈
          q13A t tau x₁ x₂ rho :=
        (q13A t tau x₁ x₂ rho).mul_mem hmem1 hmem2
      exact q13d_tau_not_mem_A h (heq.symm ▸ hmem)

theorem q13e_sq_of_not_mem_AN (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {p : G} (hp : p ∈ q13P t tau x₁ x₂ rho om)
    (hpA : p ∉ q13AN t tau x₁ x₂ rho) :
    ∃ v ∈ fourGrp x₁ x₂, p ^ 2 = tau * v := by
  have hp2N : p ^ 2 ∈ ctxN tau x₁ x₂ := q13d_P_sq_mem_N h hD.A_cent p hp
  rcases (q13d_mem_N h).mp hp2N with hV | ⟨v, hv, hpx⟩
  · exact absurd ((q13e_mem_AN h hD).mpr ⟨hp, hV⟩) hpA
  · exact ⟨v, hv, hpx⟩

theorem q13e_card_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card (q13AN t tau x₁ x₂ rho) = 2 ^ 5 := by
  have hnorm : ∀ k ∈ zpowers tau, ∀ a ∈ q13A t tau x₁ x₂ rho,
      k * a * k⁻¹ ∈ q13A t tau x₁ x₂ rho := by
    intro k hk a ha
    have hτcent : tau ∈ Subgroup.centralizer
        ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (q13d_A_cent_tau h)
    have hkcent : k ∈ Subgroup.centralizer
        ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hτcent hk
    have hcomm : a * k = k * a := Subgroup.mem_centralizer_iff.mp hkcent a ha
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact ha
  have hinf : q13A t tau x₁ x₂ rho ⊓ zpowers tau = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨hxA, hxτ⟩ := Subgroup.mem_inf.mp hx
    rcases q13b_mem_zpowers_sq (q13a_tau_mul_self h) hxτ with h1 | h1
    · rw [h1]; exact Subgroup.mem_bot.mpr rfl
    · exact absurd (h1 ▸ hxA) (q13d_tau_not_mem_A h)
  have hcardτ : Nat.card ↥(zpowers tau) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact q13a_tau_mul_self h) (q13b_tau_ne_one h)
  rw [q13AN, card_sup_eq_mul hnorm hinf, q13a_card_A h, hcardτ]
  norm_num

theorem q13e_exists_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ n ∈ ctxN tau x₁ x₂, ∃ p ∈ q13P t tau x₁ x₂ rho om, p ^ 2 = n := by
  obtain ⟨e⟩ := hD.P_iso
  intro n hn
  have hnP : n ∈ q13P t tau x₁ x₂ rho om := q13d_N_le_P h hn
  have hn2 : n * n = 1 := by simpa [pow_two] using (q13b_N_elemAbelian h).2 n hn
  have hsub : (⟨n, hnP⟩ : ↥(q13P t tau x₁ x₂ rho om)) ^ 2 = 1 :=
    Subtype.ext (by simpa [Subgroup.coe_pow, pow_two] using hn2)
  have hx2 : (e ⟨n, hnP⟩) ^ 2 = 1 := by rw [← map_pow, hsub, map_one]
  obtain ⟨y, hy⟩ := q13e_z4pow_sq (e ⟨n, hnP⟩) hx2
  refine ⟨((e.symm y : ↥(q13P t tau x₁ x₂ rho om)) : G),
    (e.symm y : ↥(q13P t tau x₁ x₂ rho om)).2, ?_⟩
  have heq : (e.symm y : ↥(q13P t tau x₁ x₂ rho om)) ^ 2 = ⟨n, hnP⟩ := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, hy]
  simpa [Subgroup.coe_pow] using Subtype.ext_iff.mp heq

theorem q13e_A_inf_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, a ∈ ctxN tau x₁ x₂ → a ∈ fourGrp x₁ x₂ := by
  intro a haA haN
  rcases (q13d_mem_N h).mp haN with hV | ⟨v, hv, hτv⟩
  · exact hV
  · exfalso
    apply q13d_tau_not_mem_A h
    have hτ : tau = a * v⁻¹ := by rw [hτv]; group
    have hmem : a * v⁻¹ ∈ q13A t tau x₁ x₂ rho :=
      (q13A t tau x₁ x₂ rho).mul_mem haA
        ((q13A t tau x₁ x₂ rho).inv_mem (q13a_V_le_A h hv))
    exact hτ.symm ▸ hmem

theorem q13e_AN_normal_L (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ p ∈ q13AN t tau x₁ x₂ rho,
      g * p * g⁻¹ ∈ q13AN t tau x₁ x₂ rho := by
  intro g hg p hp
  have hp' := (q13e_mem_AN h hD).mp hp
  rw [q13e_mem_AN h hD]
  refine ⟨q13d_P_normal_L h hD.A_cent g hg p (q13e_AN_le_P h hp), ?_⟩
  have hconj := q13e_V_normal_L h hD g hg (p ^ 2) hp'.2
  have hsq : (g * p * g⁻¹) ^ 2 = g * p ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
  rwa [hsq]

theorem q13e_P_le_CLP (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    q13P t tau x₁ x₂ rho om ≤ q13CLP t tau x₁ x₂ rho om := by
  intro p hp
  rw [q13CLP, Subgroup.mem_inf]
  refine ⟨(q13d_P_le_E0 h).trans Subgroup.le_normalizer hp, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact (q13d_P_comm h hD.A_cent p hp q hq).symm

theorem q13e_CLP_le_B (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13CLP t tau x₁ x₂ rho om ≤ q13B t tau x₁ x₂ rho om := by
  intro k hk
  rw [q13CLP, Subgroup.mem_inf] at hk
  rw [q13B, Subgroup.mem_inf]
  exact ⟨hk.1, Subgroup.centralizer_le (q13d_N_le_P h) hk.2⟩

theorem q13e_CLP_normal_L (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ k ∈ q13CLP t tau x₁ x₂ rho om,
      g * k * g⁻¹ ∈ q13CLP t tau x₁ x₂ rho om := by
  intro g hg k hk
  rw [q13CLP, Subgroup.mem_inf] at hk ⊢
  obtain ⟨hkL, hkC⟩ := hk
  refine ⟨(q13L t tau x₁ x₂ rho om).mul_mem
    ((q13L t tau x₁ x₂ rho om).mul_mem hg hkL)
    ((q13L t tau x₁ x₂ rho om).inv_mem hg), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hkC ⊢
  intro p hp
  have hgp : g⁻¹ * p * g ∈ q13P t tau x₁ x₂ rho om := by
    have := q13d_P_normal_L h hD.A_cent g⁻¹ ((q13L t tau x₁ x₂ rho om).inv_mem hg) p hp
    simpa using this
  have hcomm := hkC (g⁻¹ * p * g) hgp
  calc p * (g * k * g⁻¹) = g * ((g⁻¹ * p * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * p * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * k * g⁻¹) * p := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
