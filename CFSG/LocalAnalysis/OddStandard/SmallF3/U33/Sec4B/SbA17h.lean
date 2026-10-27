module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17Y

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma l17_t_normalizes_P (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, t * x * t⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
  (l17_P_normal hc.toCtx13).2 t (l17_mem_K hc.toCtx13).1

private lemma l17_t_normalizes_Q (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ x ∈ ctxQ t tau x₁ x₂ rho, t * x * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  hc.normal_Q_K.2 t (l17_mem_K hc.toCtx13).1

private lemma l17_t_comm_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t * rho = rho * t := by
  have htcl : t ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
  exact Subgroup.mem_centralizer_singleton_iff.mp ((ctx13_T_facts hc).1 htcl)

private lemma l17_t_sq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : t * t = 1 := by
  simpa [pow_two] using (ctx13_relations hc).1

private lemma l17_commutator_eq_inv (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {p : G}
    (hp : p ∈ ctxP t tau x₁ x₂ rho) :
    ⁅p, t⁆ = (p⁻¹ * (t * p * t⁻¹))⁻¹ := by
  have hpt1P : t * p⁻¹ * t⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
    l17_t_normalizes_P hc p⁻¹ (Subgroup.inv_mem _ hp)
  have hcomm : p * (t * p⁻¹ * t⁻¹) = (t * p⁻¹ * t⁻¹) * p :=
    l17_P_comm hc p hp (t * p⁻¹ * t⁻¹) hpt1P
  rw [commutatorElement_def, mul_inv_rev, inv_inv]
  rw [show p * t * p⁻¹ * t⁻¹ = p * (t * p⁻¹ * t⁻¹) by group]
  rw [hcomm]
  rw [show (t * p * t⁻¹)⁻¹ = t * p⁻¹ * t⁻¹ by group]

private lemma l17_commutator_mem_Q (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {p : G}
    (hp : p ∈ ctxP t tau x₁ x₂ rho) : ⁅p, t⁆ ∈ ctxQ t tau x₁ x₂ rho := by
  have hta := (l17_fpf hc).trivial_action (l17_t_comm_rho hc.toCtx13) (l17_t_sq hc.toCtx13)
    (l17_t_normalizes_P hc) (l17_t_normalizes_Q hc) p hp
  rw [l17_commutator_eq_inv hc hp]
  exact (ctxQ t tau x₁ x₂ rho).inv_mem hta

private lemma l17_commutator_mem_Y_of_C (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {c : G}
    (hcP : c ∈ ctxP t tau x₁ x₂ rho) (hctau : tau * c = c * tau) :
    ⁅c, t⁆ ∈ ctxYq t tau x₁ x₂ rho := by
  have hcQ : ⁅c, t⁆ ∈ ctxQ t tau x₁ x₂ rho := l17_commutator_mem_Q hc hcP
  have hcomm : tau * ⁅c, t⁆ = ⁅c, t⁆ * tau := by
    have hctau' : Commute tau c := hctau
    have httau' : Commute tau t := ((ctx13_relations hc.toCtx13).2.2.2.2.2.1).symm
    have h1 : Commute tau (c * t) := hctau'.mul_right httau'
    have h2 : Commute tau ((c * t) * c⁻¹) := h1.mul_right hctau'.inv_right
    have h3 : Commute tau (((c * t) * c⁻¹) * t⁻¹) := h2.mul_right httau'.inv_right
    simpa [commutatorElement_def] using h3.eq
  have hfix : tau * ⁅c, t⁆ * tau⁻¹ = ⁅c, t⁆ := by rw [hcomm]; group
  have hinv : tau * ⁅c, t⁆ * tau⁻¹ = (⁅c, t⁆)⁻¹ := hc.tau_inv_Q _ hcQ
  have heq : ⁅c, t⁆ = (⁅c, t⁆)⁻¹ := by
    calc ⁅c, t⁆ = tau * ⁅c, t⁆ * tau⁻¹ := hfix.symm
      _ = (⁅c, t⁆)⁻¹ := hinv
  have hsq : (⁅c, t⁆) ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr heq
  rw [mem_ctxYq_iff hc.q_iso]
  exact ⟨hcQ, hsq⟩

private lemma l17_commutator_mem_Y_of_Q (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : ⁅q, t⁆ ∈ ctxYq t tau x₁ x₂ rho := by
  have hqP : q ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc.toCtx13 hq
  have hqtQ : ⁅q, t⁆ ∈ ctxQ t tau x₁ x₂ rho := l17_commutator_mem_Q hc hqP
  have hqtP : ⁅q, t⁆ ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc.toCtx13 hqtQ
  have hq2V : q ^ 2 ∈ fourGrp x₁ x₂ := l17_Q_sq_mem hc.toCtx13 q hq
  have htq2 : t * q ^ 2 = q ^ 2 * t := (l17_cent_V hc.toCtx13 (q ^ 2) hq2V).1
  have hcomm : Commute q ⁅q, t⁆ := l17_P_comm hc q hqP ⁅q, t⁆ hqtP
  have hpow : (⁅q, t⁆) ^ 2 = ⁅q ^ 2, t⁆ := Commute.commutatorElement_pow_left hcomm 2
  have h1 : ⁅q ^ 2, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr htq2.symm
  have hsq : (⁅q, t⁆) ^ 2 = 1 := by rw [hpow, h1]
  rw [mem_ctxYq_iff hc.q_iso]
  exact ⟨hqtQ, hsq⟩

private lemma l17_commutator_sq_tau (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {p : G}
    (hp : p ∈ ctxP t tau x₁ x₂ rho) : ⁅p ^ 2, tau⁆ = 1 := by
  have hp2Q : p ^ 2 ∈ ctxQ t tau x₁ x₂ rho := (l17_fpf hc).sq_mem p hp
  have hp4 : p ^ 4 = 1 := l17_exp_four hc p hp
  have hp2sq : p ^ 2 * p ^ 2 = 1 := by
    have h : (p ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num]
      exact hp4
    rwa [pow_two] at h
  have hp2inv : (p ^ 2)⁻¹ = p ^ 2 := inv_eq_of_mul_eq_one_right hp2sq
  have hfix : tau * p ^ 2 * tau⁻¹ = p ^ 2 := by
    rw [hc.tau_inv_Q (p ^ 2) hp2Q, hp2inv]
  have hcomm : p ^ 2 * tau = tau * p ^ 2 := by
    have h' : tau * p ^ 2 = p ^ 2 * tau := by
      calc tau * p ^ 2 = tau * p ^ 2 * tau⁻¹ * tau := by group
        _ = p ^ 2 * tau := by rw [hfix]
    exact h'.symm
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem l17_CP_tau (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, tau * x = x * tau → x ∈ ctxYq t tau x₁ x₂ rho := by
  intro x hxP hxcomm
  have hCP : ctxP t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G) ≤
      ctxP t tau x₁ x₂ rho := inf_le_left
  have hCρ : ∀ y ∈ ctxP t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G),
      rho * y * rho⁻¹ ∈ ctxP t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G) := by
    intro y hy
    obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.mp hy
    have hrhoK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.2.2.2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (l17_P_normal hc.toCtx13).2 rho hrhoK y hyP
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hy' : Commute y tau := Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hrho : Commute tau rho := hc.tau_rho
      have h1 : Commute tau (rho * y) := hrho.mul_right hy'.symm
      exact (h1.mul_right hrho.inv_right).eq.symm
  rcases (l17_fpf hc).sup_eq hCP hCρ with hCQ | hCQ
  · have hxC : x ∈ ctxP t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hxP, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxcomm.symm
    have hxQ : x ∈ ctxQ t tau x₁ x₂ rho := hCQ hxC
    have hinv : tau * x * tau⁻¹ = x⁻¹ := hc.tau_inv_Q x hxQ
    have hfix : tau * x * tau⁻¹ = x := by rw [hxcomm]; group
    have hx2 : x ^ 2 = 1 := by
      have heq : x = x⁻¹ := by
        calc x = tau * x * tau⁻¹ := hfix.symm
          _ = x⁻¹ := hinv
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr heq
    rw [mem_ctxYq_iff hc.q_iso]
    exact ⟨hxQ, hx2⟩
  · exfalso
    have hdeltaY : ∀ p ∈ ctxP t tau x₁ x₂ rho, ⁅p, t⁆ ∈ ctxYq t tau x₁ x₂ rho := by
      intro p hp
      obtain ⟨c, hcC, hcq⟩ := hCQ p hp
      have hcP : c ∈ ctxP t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hcC).1
      have hcCent : c ∈ centralizer ({tau} : Set G) := (Subgroup.mem_inf.mp hcC).2
      have hctau : tau * c = c * tau :=
        (Subgroup.mem_centralizer_singleton_iff.mp hcCent).symm
      have hqQ : c⁻¹ * p ∈ ctxQ t tau x₁ x₂ rho := hcq
      have hqP : c⁻¹ * p ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc.toCtx13 hqQ
      have hcp : p = c * (c⁻¹ * p) := by group
      have hX : ⁅c⁻¹ * p, t⁆ ∈ ctxP t tau x₁ x₂ rho :=
        l17_Q_le_P hc.toCtx13 (l17_commutator_mem_Q hc hqP)
      rw [hcp]
      have hmul : ⁅c * (c⁻¹ * p), t⁆ = ⁅c⁻¹ * p, t⁆ * ⁅c, t⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hconj : c * ⁅c⁻¹ * p, t⁆ * c⁻¹ = ⁅c⁻¹ * p, t⁆ := by
          rw [l17_P_comm hc c hcP ⁅c⁻¹ * p, t⁆ hX]
          group
        rw [hconj]
      rw [hmul]
      exact (ctxYq t tau x₁ x₂ rho).mul_mem (l17_commutator_mem_Y_of_Q hc hqQ)
        (l17_commutator_mem_Y_of_C hc hcP hctau)
    have ht_cent : ∀ a ∈ ctxYq t tau x₁ x₂ rho, t * a * t⁻¹ = a := by
      intro a ha
      obtain ⟨p, hpP, hp2⟩ := l17_sq_surj hc a ha
      have hmem : ⁅p, t⁆ ∈ ctxYq t tau x₁ x₂ rho := hdeltaY p hpP
      have hsq : (⁅p, t⁆) ^ 2 = 1 := (mem_ctxYq_iff hc.q_iso ⁅p, t⁆).mp hmem |>.2
      have hptP : ⁅p, t⁆ ∈ ctxP t tau x₁ x₂ rho :=
        l17_Q_le_P hc.toCtx13 (l17_commutator_mem_Q hc hpP)
      have hcomm : Commute p ⁅p, t⁆ := l17_P_comm hc p hpP ⁅p, t⁆ hptP
      have hpow : (⁅p, t⁆) ^ 2 = ⁅p ^ 2, t⁆ := Commute.commutatorElement_pow_left hcomm 2
      have h1 : ⁅p ^ 2, t⁆ = 1 := by rw [← hpow]; exact hsq
      have hcomm2 : p ^ 2 * t = t * p ^ 2 := commutatorElement_eq_one_iff_mul_comm.mp h1
      rw [← hp2]
      calc t * p ^ 2 * t⁻¹ = (t * p ^ 2) * t⁻¹ := by group
        _ = (p ^ 2 * t) * t⁻¹ := by rw [← hcomm2]
        _ = p ^ 2 := by group
    have hYle : ctxYq t tau x₁ x₂ rho ≤ centralizer ({t} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * t = (t * a * t⁻¹) * t := by rw [ht_cent a ha]
        _ = t * a := by group
    have hYinf : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) =
        ctxYq t tau x₁ x₂ rho :=
      le_antisymm inf_le_left (le_inf le_rfl hYle)
    have hYeq : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ := by
      rw [← hc.Y_cent.1]
      exact hYinf.symm
    have hcard := l17_card_Y hc.toCtx13
    rw [hYeq, l17_card_V hc.toCtx13] at hcard
    norm_num at hcard

theorem l17_comm_tau (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∃ p ∈ ctxP t tau x₁ x₂ rho, p * tau * p⁻¹ * tau⁻¹ = a := by
  intro a ha
  have htauK : tau ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.1
  obtain ⟨N, hNleP, _himg, hsurj, hcard⟩ :=
    exists_comm_image (A := ctxP t tau x₁ x₂ rho) (g := tau) (l17_P_comm hc)
      (fun x hx => (l17_P_normal hc.toCtx13).2 tau htauK x hx)
  have hinf : ctxP t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G) =
      ctxYq t tau x₁ x₂ rho := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.mp hy
      exact l17_CP_tau hc y hyP
        (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
    · intro y hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact l17_Q_le_P hc.toCtx13 (ctxYq_le_ctxQ hy)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc.tau_cent_Y y hy).symm
  have hcardN : Nat.card N = 16 := by
    have hP := (l17_card_P hc).1
    rw [hinf, l17_card_Y hc.toCtx13, hP] at hcard
    norm_num at hcard
    omega
  have hNY : N ≤ ctxYq t tau x₁ x₂ rho := by
    intro n hn
    obtain ⟨p, hpP, hpn⟩ := hsurj n hn
    have hnP : n ∈ ctxP t tau x₁ x₂ rho := hNleP hn
    have hptP : ⁅p, tau⁆ ∈ ctxP t tau x₁ x₂ rho := by
      rw [show ⁅p, tau⁆ = p * tau * p⁻¹ * tau⁻¹ by rw [commutatorElement_def], ← hpn]
      exact hnP
    have hn2 : n ^ 2 = 1 := by
      have hcomm : Commute p ⁅p, tau⁆ := l17_P_comm hc p hpP ⁅p, tau⁆ hptP
      have hpow : (⁅p, tau⁆) ^ 2 = ⁅p ^ 2, tau⁆ :=
        Commute.commutatorElement_pow_left hcomm 2
      have h1 : ⁅p ^ 2, tau⁆ = 1 := l17_commutator_sq_tau hc hpP
      calc n ^ 2 = (p * tau * p⁻¹ * tau⁻¹) ^ 2 := by rw [hpn]
        _ = (⁅p, tau⁆) ^ 2 := by rw [commutatorElement_def]
        _ = 1 := by rw [hpow, h1]
    exact l17_omega hc n hnP hn2
  have hNYeq : N = ctxYq t tau x₁ x₂ rho :=
    Subgroup.eq_of_le_of_card_ge hNY (by rw [hcardN, l17_card_Y hc.toCtx13])
  have haN : a ∈ N := by rw [hNYeq]; exact ha
  obtain ⟨p, hpP, hpn⟩ := hsurj a haN
  exact ⟨p, hpP, hpn.symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
