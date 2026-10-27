module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
import CFSG.LocalAnalysis.EvenBN.TrialityD4.D4RootCentralizer
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bZsig
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.LocalAnalysis.EvenBN.TrialityD4 Subgroup

private theorem not_dvd_of_orderOf_two {ℓ o a : ℕ} (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = o) (ho : o ≠ 0) (h : ¬ o ∣ 2 * a) :
    ¬ ℓ ∣ 2 ^ a * (2 ^ a - 1) * (2 ^ (2 * a) - 1) := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := rfl
    rw [h0, orderOf_zero] at hord
    exact ho hord.symm
  intro hdvd
  rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hℓ).1 h1 with h2 | h2
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h2))
    · have := orderOf_dvd_of_pow_eq_one ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff a).1 h2)
      rw [hord] at this
      exact h (this.mul_left 2)
  · have := orderOf_dvd_of_pow_eq_one
      ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (2 * a)).1 h1)
    rw [hord] at this
    exact h this

private theorem exists_prime_dvd_card_SL_not_dvd {f a : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 * f ∣ a) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ (2 ^ f) ^ 3 * ((2 ^ f) ^ 6 - 1) ∧
      ¬ ℓ ∣ 2 ^ a * (2 ^ a - 1) * (2 ^ (2 * a) - 1) := by
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h7 : orderOf (2 : ZMod 7) = 3 := orderOf_eq_prime (by decide) (by decide)
    refine ⟨7, by norm_num, by norm_num,
      not_dvd_of_orderOf_two (by norm_num) h7 (by norm_num) fun h => h3 ?_⟩
    rw [mul_one]
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h
  · obtain ⟨ℓ, hℓ, -, hord⟩ :=
      CFSG.QuasithinUnique.Setup.X5.exists_prime_orderOf_two_eq_six_mul hf2
    refine ⟨ℓ, hℓ, Dvd.dvd.mul_left ?_ _,
      not_dvd_of_orderOf_two hℓ hord (by omega) fun h => h3 ?_⟩
    · rw [← pow_mul, mul_comm, CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff, ← hord]
      exact pow_orderOf_eq_one _
    · exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
        (by rw [show 2 * (3 * f) = 6 * f by ring]; exact h)

private theorem one_le_of_trialityD4Data {X : Type} [Group X] {f : ℕ}
    (d : TrialityD4Data X (2 ^ f)) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · have := d.two_le_q
    norm_num at this
  · exact hf

private theorem leviShort_le_of_isKLConfig {X : Type} [Group X] [Finite X] {f a : ℕ}
    (d : TrialityD4Data X (2 ^ f)) (hf : 1 ≤ f) {N A : Subgroup X}
    (h : IsKLConfig (d.x₆ 1) a N A) (h3 : ¬ 3 * f ∣ a) : d.leviShort ≤ N := by
  have := d.isSimpleGroup_leviShort
  obtain ⟨ℓ, hℓ, hℓL, hℓq⟩ := exists_prime_dvd_card_SL_not_dvd hf h3
  refine h.kernel.le_of_isSimpleGroup ?_ hℓ (by rw [d.card_leviShort]; exact hℓL) hℓq
  exact d.leviShort_le_centralizer_V.trans
    (centralizer_le (Set.singleton_subset_iff.2 (d.x₆_mem_V 1)))

private theorem le_D_of_isKLConfig {X : Type} [Group X] [Finite X] {f a : ℕ}
    (d : TrialityD4Data X (2 ^ f)) {N A : Subgroup X} (h : IsKLConfig (d.x₆ 1) a N A)
    (hL : d.leviShort ≤ N) : A ≤ d.D := by
  have hAC : A ≤ d.D ⊔ d.leviShort := by
    rw [← d.centralizer_x₆_one_eq]
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact h.comm x hx _ h.mem
  exact d.le_D_of_isPGroup_of_le_sup_leviShort h.isPGroup hAC fun s hs =>
    mem_normalizer_fintype fun x hx => h.conj_mem s (hL hs) x hx

private theorem conj_u_mem_Y_of_fixed {X : Type} [Group X] {q : ℕ} (d : TrialityD4Data X q)
    {x : X} (hx : x ∈ d.D)
    (hfix : ∀ w ∈ d.U₁.map (MulAut.conj d.u).toMonoidHom, w * x * w⁻¹ * x⁻¹ ∈ d.V) :
    d.u * x * d.u ∈ d.Y := by
  have hu : ∀ w, d.u * (d.u * w) = w := fun w => by rw [← mul_assoc, d.u_mul_self, one_mul]
  have hy : d.u * x * d.u ∈ d.D := by
    simpa only [d.u_inv] using (mem_normalizer_iff.1 d.u_mem_normalizer_D x).1 hx
  refine d.mem_Y_of_forall_conj_x₁_mem_V hy fun b => ?_
  have hw := hfix (d.u * d.x₁ b * d.u⁻¹) ⟨d.x₁ b, d.x₁_mem_U₁ b, rfl⟩
  have hV : d.u * (d.u * d.x₁ b * d.u⁻¹ * x * (d.u * d.x₁ b * d.u⁻¹)⁻¹ * x⁻¹) * d.u⁻¹ ∈ d.V :=
    (mem_normalizer_iff.1 (d.leviShort_le_normalizer_V d.u_mem_leviShort) _).1 hw
  have e : d.x₁ b * (d.u * x * d.u) * (d.x₁ b)⁻¹ * (d.u * x * d.u)⁻¹ =
      d.u * (d.u * d.x₁ b * d.u⁻¹ * x * (d.u * d.x₁ b * d.u⁻¹)⁻¹ * x⁻¹) * d.u⁻¹ := by
    simp only [mul_assoc, mul_inv_rev, d.u_inv, hu]
  rw [e]
  exact hV

private theorem le_V_of_isKLConfig {X : Type} [Group X] [Finite X] {f a : ℕ}
    (d : TrialityD4Data X (2 ^ f)) {N A : Subgroup X} (h : IsKLConfig (d.x₆ 1) a N A)
    (hL : d.leviShort ≤ N) (hAD : A ≤ d.D) : A ≤ d.V := by
  have hconj : ∀ s ∈ d.leviShort, ∀ x ∈ A, s * x * s⁻¹ ∈ A := fun s hs x hx =>
    h.conj_mem s (hL hs) x hx
  have hcV : ∀ s ∈ d.leviShort, ∀ z ∈ d.V, s * z * s⁻¹ ∈ d.V := fun s hs z hz =>
    (mem_normalizer_iff.1 (d.leviShort_le_normalizer_V hs) z).1 hz
  have hU'L : d.U₁.map (MulAut.conj d.u).toMonoidHom ≤ d.leviShort := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem d.u_mem_leviShort (d.U₁_le_leviShort hy)) (inv_mem d.u_mem_leviShort)
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hU₁ : IsPGroup 2 d.U₁ := (hP ▸ P.isPGroup').to_le d.U₁_le_S
  refine le_of_fixed_of_ne_commute (Z₀ := d.V) (U := d.U₁)
    (U' := d.U₁.map (MulAut.conj d.u).toMonoidHom) (V := (d.Y : Set X))
    (V' := {x | d.u * x * d.u ∈ d.Y}) h.comm h.isPGroup (fun x hx z hz => ?_) hU₁
    (fun s hs => hconj s (d.U₁_le_leviShort hs)) (fun s hs => hcV s (d.U₁_le_leviShort hs))
    (hU₁.map _) (fun s hs => hconj s (hU'L hs)) (fun s hs => hcV s (hU'L hs))
    (fun x hx hfix => ?_) (fun x hx hfix => conj_u_mem_Y_of_fixed d (hAD hx) hfix)
    fun y hy z hz hyV hzV => d.mul_ne_mul_of_mem_Y_of_conj_u_mem_Y hy hz hyV hzV
  · exact (mem_normalizer_iff.1 (d.S_le_normalizer_V (d.D_le_S (hAD hx))) z).1 hz
  · exact d.mem_Y_of_forall_conj_x₁_mem_V (hAD hx) fun b => hfix _ (d.x₁_mem_U₁ b)

theorem false_of_isKLConfig_x₆_of_trialityD4Data {X : Type} [Group X] [Finite X] {f a : ℕ}
    (d : TrialityD4Data X (2 ^ f)) {N A : Subgroup X} (h : IsKLConfig (d.x₆ 1) a N A)
    (h3 : ¬ 3 * f ∣ a) : False := by
  have hL := leviShort_le_of_isKLConfig d (one_le_of_trialityD4Data d) h h3
  have hAV := le_V_of_isKLConfig d h hL (le_D_of_isKLConfig d h hL)
  obtain ⟨g, hg, hg3⟩ := d.exists_mem_leviShort_orderOf_eq_three
  have h1 := h.eq_one g (hL hg) (by rw [hg3]; decide) fun x hx =>
    (mem_centralizer_iff.1 (d.leviShort_le_centralizer_V hg) x (hAV hx)).symm
  rw [h1, orderOf_one] at hg3
  exact absurd hg3 (by norm_num)

theorem dvd_of_isStrothInvolution_of_isConj_x₄ {X : Type} [Group X] {f a : ℕ}
    (d : TrialityD4Data X (2 ^ f)) {t : X} (h : IsStrothInvolution t a)
    (ht : IsConj t (d.x₄ 1)) : 3 * f ∣ a := by
  have hf := one_le_of_trialityD4Data d
  obtain ⟨τ, hτ, hinv⟩ := d.exists_inv_x₁_one
  obtain ⟨k, hk⟩ := isConj_iff.1 (ht.trans (d.isConj_x₁_x₄ 1).symm)
  refine h.dvd_of_inv (k⁻¹ * τ * k) (3 * f) (by omega) ?_ ?_
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj k⁻¹) τ
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [h1, hτ, ← pow_mul, mul_comm f 3]
  · have ht' : t = k⁻¹ * d.x₁ 1 * k := by rw [← hk]; group
    rw [ht']
    calc k⁻¹ * d.x₁ 1 * k * (k⁻¹ * τ * k) * (k⁻¹ * d.x₁ 1 * k)⁻¹
        = k⁻¹ * (d.x₁ 1 * τ * (d.x₁ 1)⁻¹) * k := by group
      _ = (k⁻¹ * τ * k)⁻¹ := by rw [hinv]; group

theorem false_of_isKLConfig_of_lieModel_trialityD4
    {X : Type} [Group X] [Finite X] {m x a : ℕ}
    (hX : CFSG.Blueprint.LieModel X .trialityD4 m 2 x) {t : X} {N A : Subgroup X}
    (h : IsKLConfig t a N A) (h3 : ¬ 3 * x ∣ a) : False := by
  obtain ⟨-, hx, rfl⟩ := hX.admissible
  obtain ⟨d⟩ := nonempty_trialityD4Data_of_lieModel hx hX
  obtain ⟨g, hg | hg⟩ := d.involution_conj t h.involution.orderOf_eq_two
  · have ht : (d.ofMulEquiv (MulAut.conj g⁻¹)).x₆ 1 = t := by
      show MulAut.conj g⁻¹ (d.x₆ 1) = t
      rw [MulAut.conj_apply, inv_inv, ← hg]
      group
    exact false_of_isKLConfig_x₆_of_trialityD4Data _ (by rw [ht]; exact h) h3
  · exact h3 (dvd_of_isStrothInvolution_of_isConj_x₄ d h.involution (isConj_iff.2 ⟨g, hg⟩))

end CFSG.RankThree.GF2n.Stroth80
