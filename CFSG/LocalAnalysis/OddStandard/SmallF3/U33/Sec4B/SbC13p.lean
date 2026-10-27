module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13Mm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13n

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

private abbrev c13SpanSet (t tau x₁ x₂ rho : G) : Set G :=
  {g : G | ∃ A : Subgroup G, A ≤ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) ∧
    CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 32 ∧ g ∈ A}

private lemma c13_mem_zpowers_eq_one_or_eq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem c13_exists_E32 (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    ∃ A : Subgroup G, A ≤ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 32 ∧ tau * q ∈ A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htau2 : tau * tau = 1 := (c13_tau_data hc.toCtx13A).2.1
  have htau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2
  let a : G := tau * q
  have ha2 : a * a = 1 := by
    change (tau * q) * (tau * q) = 1
    have h1 : tau * q * tau = q⁻¹ := by
      have := hc.tau_inv_Q q hq
      rwa [htau_inv] at this
    calc (tau * q) * (tau * q) = (tau * q * tau) * q := by group
      _ = q⁻¹ * q := by rw [h1]
      _ = 1 := by group
  have ha_comm_Y : ∀ y ∈ ctxYq t tau x₁ x₂ rho, a * y = y * a := by
    intro y hy
    have hyQ : y ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hy
    have hqy : q * y = y * q := hc.Q_comm q hq y hyQ
    have hty : tau * y = y * tau := hc.tau_cent_Y y hy
    change (tau * q) * y = y * (tau * q)
    calc (tau * q) * y = tau * (q * y) := by group
      _ = tau * (y * q) := by rw [hqy]
      _ = (tau * y) * q := by group
      _ = (y * tau) * q := by rw [hty]
      _ = y * (tau * q) := by group
  have hz_le : zpowers a ≤
      Subgroup.centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_iff.mpr (fun y hy => (ha_comm_Y y hy).symm))
  have hcomm : ∀ h ∈ ctxYq t tau x₁ x₂ rho, ∀ k ∈ zpowers a, h * k = k * h :=
    fun h hh k hk => Subgroup.mem_centralizer_iff.mp (hz_le hk) h hh
  have ha_not_Y : a ∉ ctxYq t tau x₁ x₂ rho := by
    intro haY
    have haQ : a ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ haY
    have htauQ : tau ∈ ctxQ t tau x₁ x₂ rho := by
      have h : tau = a * q⁻¹ := by
        rw [show a = tau * q from rfl]
        group
      have hmem : a * q⁻¹ ∈ ctxQ t tau x₁ x₂ rho := mul_mem haQ (inv_mem hq)
      rwa [← h] at hmem
    have hbot : tau ∈ (⊥ : Subgroup G) := by
      have : tau ∈ ctxQ t tau x₁ x₂ rho ⊓ closure ({t, tau} : Set G) :=
        ⟨htauQ, Subgroup.subset_closure (by simp)⟩
      rwa [l12_Q_inf_tt hc.toCtx11] at this
    have htau1 : tau = 1 := Subgroup.mem_bot.mp hbot
    exact l12_tau_not_mem_V hc.toCtx10.toCtx4 (by rw [htau1]; exact Subgroup.one_mem _)
  have hinf : ctxYq t tau x₁ x₂ rho ⊓ zpowers a = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxY, hxZ⟩ := Subgroup.mem_inf.mp hx
    rcases c13_mem_zpowers_eq_one_or_eq ha2 hxZ with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxY) ha_not_Y
  have hcard_z : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by rwa [pow_two])
      (fun h => ha_not_Y (by rw [h]; exact Subgroup.one_mem _))
  have hcard_A : Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊔ zpowers a) = 32 := by
    have h := card_sup_mul_card_inf (H := ctxYq t tau x₁ x₂ rho) (K := zpowers a) hcomm
    rw [hinf, Subgroup.card_bot, mul_one, card_ctxYq hc.q_iso, hcard_z] at h
    omega
  have hA_le : ctxYq t tau x₁ x₂ rho ⊔ zpowers a ≤
      ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) := by
    refine sup_le (ctxYq_le_ctxQ.trans le_sup_left) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem (H := ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G))
      (Subgroup.mem_sup_right (show tau ∈ closure ({t, tau} : Set G) from
        Subgroup.subset_closure (by simp)))
      (Subgroup.mem_sup_left (show q ∈ ctxQ t tau x₁ x₂ rho from hq))
  exact ⟨ctxYq t tau x₁ x₂ rho ⊔ zpowers a, hA_le,
    isElemAbelian_sup hc.Y_elem (isElemAbelian_zpowers ha2) hcomm, hcard_A,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩

private lemma c13_tau_mem_spanSet (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    tau ∈ closure (c13SpanSet t tau x₁ x₂ rho) := by
  obtain ⟨A, hAR, hAe, hAcard, htauA⟩ := c13_exists_E32 hc (q := 1) (Subgroup.one_mem _)
  exact Subgroup.subset_closure ⟨A, hAR, hAe, hAcard, by simpa using htauA⟩

private lemma c13_Qtau_eq_span_closure (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ⊔ zpowers tau = closure (c13SpanSet t tau x₁ x₂ rho) := by
  have h1 : closure (c13SpanSet t tau x₁ x₂ rho) ≤
      ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    rw [Subgroup.closure_le]
    rintro g ⟨A, hAR, hAe, hAcard, hgA⟩
    exact c13_E32_le hc hAR hAe hAcard hgA
  have h2 : ctxQ t tau x₁ x₂ rho ⊔ zpowers tau ≤
      closure (c13SpanSet t tau x₁ x₂ rho) := by
    have htau2 : tau * tau = 1 := (c13_tau_data hc.toCtx13A).2.1
    refine sup_le ?_ ?_
    · intro q hq
      obtain ⟨A, hAR, hAe, hAcard, htauqA⟩ := c13_exists_E32 hc hq
      have hmem : tau * q ∈ closure (c13SpanSet t tau x₁ x₂ rho) :=
        Subgroup.subset_closure ⟨A, hAR, hAe, hAcard, htauqA⟩
      have hq_eq : q = tau * (tau * q) := by rw [← mul_assoc, htau2, one_mul]
      rw [hq_eq]
      exact Subgroup.mul_mem _ (c13_tau_mem_spanSet hc) hmem
    · rw [Subgroup.zpowers_le]
      exact c13_tau_mem_spanSet hc
  exact le_antisymm h2 h1

private lemma c13_conj_mem_spanSet (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {m : G}
    (hm : m ∈ ctxK t tau x₁ x₂ rho) {g : G} (hg : g ∈ c13SpanSet t tau x₁ x₂ rho) :
    m * g * m⁻¹ ∈ c13SpanSet t tau x₁ x₂ rho := by
  obtain ⟨A, hAR, hAe, hAcard, hgA⟩ := hg
  have hm' : m ∈ normalizer
      ((ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) : Subgroup G) : Set G) := hm
  have hnorm := Subgroup.mem_normalizer_iff.mp hm'
  refine ⟨A.map (MulAut.conj m).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : m * a * m⁻¹ ∈
        (ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) : Subgroup G) :=
      (hnorm a).mp (hAR ha)
    simpa [MulAut.conj_apply] using h1
  · refine ⟨?_, ?_⟩
    · haveI : IsMulCommutative ↥A := hAe.1
      infer_instance
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      change (MulAut.conj m a) ^ 2 = 1
      rw [← map_pow, hAe.2 a ha]
      simp
  · rw [Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj m).toMonoidHom)
      (MulAut.conj m).injective]
    exact hAcard
  · exact Subgroup.mem_map.mpr ⟨g, hgA, by rfl⟩

private lemma c13_conj_mem_closure_spanSet (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {m : G}
    (hm : m ∈ ctxK t tau x₁ x₂ rho) {x : G}
    (hx : x ∈ closure (c13SpanSet t tau x₁ x₂ rho)) :
    m * x * m⁻¹ ∈ closure (c13SpanSet t tau x₁ x₂ rho) := by
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact Subgroup.subset_closure (c13_conj_mem_spanSet hc hm hg)
  | one => simpa using Subgroup.one_mem _
  | mul y z hy hz ihy ihz =>
      have h : m * (y * z) * m⁻¹ = (m * y * m⁻¹) * (m * z * m⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y hy ihy =>
      have h : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ihy

theorem c13_K_le_normalizer (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ctxK t tau x₁ x₂ rho ≤
      normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ closure (c13SpanSet t tau x₁ x₂ rho) := by
      rw [← c13_Qtau_eq_span_closure hc]
      exact hx
    have h1 := c13_conj_mem_closure_spanSet hc hn hx'
    rwa [← c13_Qtau_eq_span_closure hc] at h1
  · intro hx
    have hx' : n * x * n⁻¹ ∈ closure (c13SpanSet t tau x₁ x₂ rho) := by
      rw [← c13_Qtau_eq_span_closure hc]
      exact hx
    have hn' : n⁻¹ ∈ ctxK t tau x₁ x₂ rho := Subgroup.inv_mem _ hn
    have h1 := c13_conj_mem_closure_spanSet hc hn' hx'
    have h2 : n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ = x := by group
    rw [h2] at h1
    rwa [← c13_Qtau_eq_span_closure hc] at h1

theorem c13_K_le (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ctxK t tau x₁ x₂ rho ≤
        normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) ∧
      normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) ≤
        normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) ∧
      normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) ≤
        normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
  ⟨c13_K_le_normalizer hc, c13_normalizer_Qtau_le_Q hc, c13_normalizer_Q_le_Y t tau x₁ x₂ rho⟩

theorem c13_normal_Q_K (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxQ t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho) := by
  refine ⟨c13_Q_le_K hc.toCtx11, ?_⟩
  intro g hg k hk
  have hK := c13_K_le hc
  have hgQ : g ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    hK.2.1 (hK.1 hg)
  exact (Subgroup.mem_normalizer_iff.mp hgQ k).mp hk

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
