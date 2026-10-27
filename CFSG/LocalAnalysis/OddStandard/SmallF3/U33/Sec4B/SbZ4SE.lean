module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SE0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem rho_mem_normalizer_Y :
    rho ∈ normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro a
  constructor
  · exact fun ha => hp.normal_Y.2 rho hp.rho_mem_M a ha
  · intro ha
    have h := hp.normal_Y.2 rho⁻¹ (inv_mem hp.rho_mem_M) _ ha
    have heq : rho⁻¹ * (rho * a * rho⁻¹) * rho⁻¹⁻¹ = a := by group
    rwa [heq] at h

theorem sigma_mem_normalizer_Y :
    lam * t ∈ normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro a
  constructor
  · exact fun ha => hp.normal_Y.2 (lam * t) hp.sigma_mem_M a ha
  · intro ha
    have h := hp.normal_Y.2 (lam * t)⁻¹ (inv_mem hp.sigma_mem_M) _ ha
    have heq : (lam * t)⁻¹ * ((lam * t) * a * (lam * t)⁻¹) * (lam * t)⁻¹⁻¹ = a := by group
    rwa [heq] at h

theorem exists_complement :
    ∃ V' : Subgroup G, V' ≤ ctxYq t tau x₁ x₂ rho ∧ Nat.card V' = 4 ∧
      fourGrp x₁ x₂ ⊓ V' = ⊥ ∧ (∀ f ∈ V', rho * f * rho⁻¹ ∈ V') ∧
      ∀ f ∈ V', (lam * t) * f * (lam * t)⁻¹ ∈ V' := by
  obtain ⟨V', hle, hcard, hinf, hρ, hσ⟩ :=
    S4A.m11_exists_complement (ctxYq t tau x₁ x₂ rho) (fourGrp x₁ x₂) hp.card_Y
      (fun y hy => by simpa [pow_two] using hp.Y_sq hy)
      hp.rho_mem_normalizer_Y hp.sigma_mem_normalizer_Y hp.rho_pow_three hp.sigma_sq
      hp.sigma_rho
      (fun y hy hyρ => by
        have hQ : y ∈ ctxQ t tau x₁ x₂ rho := hp.Y_le_Q hy
        have hc : y ∈ centralizer ({rho} : Set G) :=
          mem_centralizer_iff.mpr fun h hh => by
            rw [Set.mem_singleton_iff.mp hh]; exact hyρ
        have h1 : y ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hQ, hc⟩
        rw [hp.CQ_rho] at h1
        exact Subgroup.mem_bot.mp h1)
      hp.V_le_Y hp.card_V (fun x hx => hp.rho_conj_V hx)
      (fun x hx => hp.normal_V.2 (lam * t) hp.sigma_mem_M x hx)
  exact ⟨V', hle, hcard, hinf, hρ, hσ⟩

theorem Y_eq_sup {V' : Subgroup G} (hle : V' ≤ ctxYq t tau x₁ x₂ rho) (hcard : Nat.card V' = 4)
    (hinf : fourGrp x₁ x₂ ⊓ V' = ⊥) :
    ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V' := by
  have hle' : fourGrp x₁ x₂ ⊔ V' ≤ ctxYq t tau x₁ x₂ rho := sup_le hp.V_le_Y hle
  refine (Subgroup.eq_of_le_of_card_ge hle' ?_).symm
  rw [hp.card_Y]
  have hc := S4A.m11_card_mul_le_sup hinf
  rw [hp.card_V, hcard] at hc
  norm_num at hc
  omega

theorem Q_eq_sup {V' : Subgroup G} (hle : V' ≤ ctxYq t tau x₁ x₂ rho) (hcard : Nat.card V' = 4)
    (hinf : fourGrp x₁ x₂ ⊓ V' = ⊥) :
    baseGrp x₁ x₂ ⊓ V' = ⊥ ∧ ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ V' := by
  have hBinf : baseGrp x₁ x₂ ⊓ V' = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbB, hbV⟩ := Subgroup.mem_inf.mp hb
    have hbY : b ∈ ctxYq t tau x₁ x₂ rho := hle hbV
    have hb' : b ∈ baseGrp x₁ x₂ ⊓ ctxYq t tau x₁ x₂ rho := ⟨hbB, hbY⟩
    rw [hp.B_inf_Y] at hb'
    have hb'' : b ∈ fourGrp x₁ x₂ ⊓ V' := ⟨hb', hbV⟩
    rw [hinf] at hb''
    exact Subgroup.mem_bot.mp hb''
  refine ⟨hBinf, ?_⟩
  have hle' : baseGrp x₁ x₂ ⊔ V' ≤ ctxQ t tau x₁ x₂ rho :=
    sup_le hp.base_le_Q (hle.trans hp.Y_le_Q)
  refine (Subgroup.eq_of_le_of_card_ge hle' ?_).symm
  rw [hp.card_Q]
  have hc := S4A.m11_card_mul_le_sup hBinf
  rw [hp.card_B, hcard] at hc
  norm_num at hc ⊢
  omega

theorem comm_inj_V' {V' : Subgroup G} (hle : V' ≤ ctxYq t tau x₁ x₂ rho)
    (hinf : fourGrp x₁ x₂ ⊓ V' = ⊥) {v v' : G} (hv : v ∈ V') (hv' : v' ∈ V')
    (h : z4Comm t v = z4Comm t v') : v = v' := by
  have hvQ : v ∈ ctxQ t tau x₁ x₂ rho := hp.Y_le_Q (hle hv)
  have hv'Q : v' ∈ ctxQ t tau x₁ x₂ rho := hp.Y_le_Q (hle hv')
  have hdV : v * v'⁻¹ ∈ V' := mul_mem hv (inv_mem hv')
  have hdY : v * v'⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hle hdV
  have hcomm : z4Comm t (v * v'⁻¹) = 1 := by
    rw [hp.comm_mul hp.t_mem_X hvQ (inv_mem hv'Q), hp.comm_inv hp.t_mem_X hv'Q, h]
    group
  have hV : v * v'⁻¹ ∈ fourGrp x₁ x₂ := (hp.comm_t_eq_one_iff hdY).mp hcomm
  have hboth : v * v'⁻¹ ∈ fourGrp x₁ x₂ ⊓ V' := ⟨hV, hdV⟩
  rw [hinf] at hboth
  have hd1 : v * v'⁻¹ = 1 := Subgroup.mem_bot.mp hboth
  exact mul_inv_eq_one.mp hd1

theorem exists_comm_eq_V' {V' : Subgroup G} (hle : V' ≤ ctxYq t tau x₁ x₂ rho)
    (hY : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V') :
    ∀ u ∈ fourGrp x₁ x₂, ∃ v ∈ V', z4Comm t v = u := by
  intro u hu
  obtain ⟨a, haY, ha⟩ := hp.exists_comm_eq u hu
  have haY' : a ∈ fourGrp x₁ x₂ ⊔ V' := by rw [← hY]; exact haY
  obtain ⟨v, hvV, v', hv'V, hav⟩ :=
    mem_sup_of_normalizes (A := fourGrp x₁ x₂) (C := V') (fun c hc a ha => by
      have hcomm : c * a = a * c := hp.Y_comm _ (hle hc) _ (hp.V_le_Y ha)
      have heq : c * a * c⁻¹ = a := by rw [hcomm]; group
      rw [heq]; exact ha) haY'
  refine ⟨v', hv'V, ?_⟩
  have hvQ : v ∈ ctxQ t tau x₁ x₂ rho := hp.V_le_Q hvV
  have hv'Q : v' ∈ ctxQ t tau x₁ x₂ rho := hp.Y_le_Q (hle hv'V)
  have h1 : z4Comm t a = z4Comm t v' := by
    rw [hav, hp.comm_mul hp.t_mem_X hvQ hv'Q, hp.comm_V hp.t_mem_O hvV, one_mul]
  exact h1.symm.trans ha

theorem exists_VBase :
    ∃ (V' : Subgroup G) (v₁ v₂ : G), Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂ := by
  obtain ⟨V', hle, hcard, hinf, hρ, hσ⟩ := hp.exists_complement
  have hY : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V' := hp.Y_eq_sup hle hcard hinf
  obtain ⟨hBinf, hQ⟩ := hp.Q_eq_sup hle hcard hinf
  obtain ⟨v₁, hv₁V, hv₁c⟩ := hp.exists_comm_eq_V' hle hY (x₁ ^ 2) hp.y_mem_V
  obtain ⟨v₂, hv₂V, hv₂c⟩ := hp.exists_comm_eq_V' hle hY (x₂ ^ 2) hp.w_mem_V
  have hv₁sq : v₁ * v₁ = 1 := by simpa [pow_two] using hp.Y_sq (hle hv₁V)
  have hv₂sq : v₂ * v₂ = 1 := by simpa [pow_two] using hp.Y_sq (hle hv₂V)
  have hv₁v₂comm : v₁ * v₂ = v₂ * v₁ := hp.Y_comm _ (hle hv₁V) _ (hle hv₂V)
  have hv₁v₂c : z4Comm t (v₁ * v₂) = (x₁ * x₂) ^ 2 := by
    have hy : (x₁ ^ 2) * (x₁ ^ 2) = 1 := by simpa [pow_two] using hp.y_sq
    rw [hp.comm_mul hp.t_mem_X (hp.Y_le_Q (hle hv₁V)) (hp.Y_le_Q (hle hv₂V)), hv₁c, hv₂c,
      hp.x₂_sq, ← mul_assoc, hy, one_mul]
  refine ⟨V', v₁, v₂, ?_⟩
  refine ⟨?_, hcard, hQ, hBinf, hY, hinf, ?_, hv₁V, hv₂V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨IsMulCommutative.of_comm (fun a b =>
      Subtype.ext (hp.Y_comm _ (hle a.2) _ (hle b.2))), ?_⟩
    intro x hx
    exact hp.Y_sq (hle hx)
  · exact S4A.mem_normalizer_of_conj_mem hρ
  · intro h1
    have h : z4Comm t v₁ = 1 := by rw [h1]; unfold z4Comm; group
    rw [hv₁c] at h
    exact hp.y_ne_one h
  · intro hv₂zp
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hv₂zp
    have h2 : v₁ ^ (2 : ℕ) = 1 := hp.Y_sq (hle hv₁V)
    have hem : v₁ ^ n = v₁ ^ (n % (2 : ℤ)) := zpow_eq_zpow_emod' n h2
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · have hv₂1 : v₂ = 1 := by rw [← hn, hem, h0]; simp
      have hz : z4Comm t v₂ = 1 := by rw [hv₂1]; unfold z4Comm; group
      rw [hv₂c] at hz
      exact hp.x₂_sq_ne_one hz
    · have hv₂v₁ : v₂ = v₁ := by rw [← hn, hem, h1]; simp
      have hxz : x₂ ^ 2 = x₁ ^ 2 := by rw [← hv₂c, hv₂v₁, hv₁c]
      exact hp.y_ne_w hxz.symm
  · apply le_antisymm
    · intro v hv
      have hvY : v ∈ ctxYq t tau x₁ x₂ rho := hle hv
      have hcomm : z4Comm t v ∈ fourGrp x₁ x₂ :=
        hp.comm_mem hp.t_mem_X (hp.Y_le_O hvY)
      rw [hp.mem_V_iff] at hcomm
      rw [S4B.mem_closure_pair_of_invol hv₁sq hv₂sq hv₁v₂comm]
      rcases hcomm with h | h | h | h
      · exact Or.inl (hp.comm_inj_V' hle hinf hv (one_mem V')
          (by rw [h]; unfold z4Comm; group))
      · exact Or.inr (Or.inl (hp.comm_inj_V' hle hinf hv hv₁V (by rw [h, hv₁c])))
      · exact Or.inr (Or.inr (Or.inr
          (hp.comm_inj_V' hle hinf hv (mul_mem hv₁V hv₂V) (by rw [h, hv₁v₂c]))))
      · exact Or.inr (Or.inr (Or.inl (hp.comm_inj_V' hle hinf hv hv₂V (by rw [h, hv₂c]))))
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hv₁V
      · exact hv₂V
  · have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hp.V_le_Y hp.y_mem_V
    have hc : v₁ * x₁ ^ 2 = x₁ ^ 2 * v₁ := hp.Y_comm _ (hle hv₁V) _ hy
    have h1 : t * v₁ * t⁻¹ = x₁ ^ 2 * v₁ := by
      have h := hv₁c
      unfold z4Comm at h
      rwa [mul_inv_eq_iff_eq_mul] at h
    rw [h1, hc]
  · have hw : x₂ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hp.V_le_Y hp.w_mem_V
    have hc : v₂ * x₂ ^ 2 = x₂ ^ 2 * v₂ := hp.Y_comm _ (hle hv₂V) _ hw
    have h1 : t * v₂ * t⁻¹ = x₂ ^ 2 * v₂ := by
      have h := hv₂c
      unfold z4Comm at h
      rwa [mul_inv_eq_iff_eq_mul] at h
    rw [h1, hc]
  · apply hp.comm_inj_V' hle hinf (hσ v₁ hv₁V) hv₂V
    rw [hp.comm_conj (g := t) (c := lam * t) hp.sigma_comm_t.symm v₁, hv₁c, hp.sigma_y, hv₂c]

end Z4Pre

end CFSG.OddStandard.SmallF3.HarrisU33
