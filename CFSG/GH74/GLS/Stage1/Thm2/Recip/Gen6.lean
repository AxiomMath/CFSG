module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen4
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

theorem conj_eq_one_of_mem_center {Q : Type*} [Group Q] {q : Q} (h : q ∈ center Q) :
    (MulAut.conj q : MulAut Q) = 1 := by
  ext g
  have := Subgroup.mem_center_iff.mp h g
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [← this]
  group

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_of_mem_pPrimeCoreOf {K : Subgroup G} {o : G} (ho : o ∈ pPrimeCoreOf 2 K) :
    Odd (orderOf o) := by
  have h1 : orderOf (⟨o, ho⟩ : ↥(pPrimeCoreOf 2 K)) ∣ Nat.card (pPrimeCoreOf 2 K) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (TwoThin.card_pPrimeCoreOf_odd K).of_dvd_nat h1

omit [Finite G] in
theorem mul_eq_of_inv_mul_eq (A A' x : G) (hx : x * x = 1) (h : A'⁻¹ * A = x) :
    A * A' = A * A * x := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h1 : A' = A * x := by
    calc A' = A * (A'⁻¹ * A)⁻¹ := by group
      _ = A * x⁻¹ := by rw [h]
      _ = A * x := by rw [hxinv]
  rw [h1]
  group

theorem diag_inner (h44 : II4_44) (hAut : II4_Aut) (hG : IsKProperSimple G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup G} (hK : IsIntrinsic x K) {z c : G} (hz : z ∈ K)
    (hz4 : orderOf z = 4) (hz2 : IsPGroup 2 ↥(zpowers z)) (hc : c ∈ cSec K) :
    InducesInner (z * c) K ∧ z * c ∉ cSec K ∧ ¬ InducesFAut (z * c) K := by
  have hzN : z ∈ normalizer (K : Set G) := le_normalizer hz
  have hcN : c ∈ normalizer (K : Set G) := hc.1
  have hzcN : z * c ∈ normalizer (K : Set G) := mul_mem hzN hcN
  have hphi : phi K (z * c) hzcN = MulAut.conj (hatMk K ⟨z, hz⟩) := by
    have h1 : phi K (z * c) hzcN = phi K z hzN * phi K c hcN := phi_mul K hzN hcN
    have h2 : phi K c hcN = 1 := (phi_eq_one_iff K hcN).mpr hc
    have h3 : phi K z hzN = MulAut.conj (hatMk K ⟨z, hz⟩) := phi_of_mem K hz
    rw [h1, h2, h3, mul_one]
  have hQ := h44 G hG x hx K hK.1 hK.2.1
  have hzz : z * z = x := mul_self_eq_of_orderOf_four hK hx hz hz4
  have hxc : hatMk K ⟨x, hK.2.2⟩ ∈ center (Hat K) := hatMk_mem_center hK.2.2 hK.mem_cSec
  have hz2' : hatMk K ⟨z, hz⟩ * hatMk K ⟨z, hz⟩ = hatMk K ⟨x, hK.2.2⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hzz
  have hz4' : orderOf (hatMk K ⟨z, hz⟩) = 4 := by
    have := orderOf_hatMk (K := K) (S := zpowers z) (zpowers_le.mpr hz) hz2 (mem_zpowers z)
    rw [this, hz4]
  have hzn : hatMk K ⟨z, hz⟩ ∉ center (Hat K) := by
    intro hcen
    have h1 : orderOf (⟨hatMk K ⟨z, hz⟩, hcen⟩ : center (Hat K)) ∣ Nat.card (center (Hat K)) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hz4', hQ.2] at h1
    norm_num at h1
  refine ⟨?_, ?_, ?_⟩
  · rw [← phi_mem_inn_iff K hzcN, hphi]
    exact ⟨_, rfl⟩
  · intro hcs
    have h1 := (phi_eq_one_iff K hzcN).mpr hcs
    rw [hphi] at h1
    exact hzn (mem_center_of_conj_eq_one h1)
  · rintro ⟨hN', hF⟩
    have hphi' : inducedQuotAut K (pPrimeCore 2 ↥K) ⟨z * c, hN'⟩ =
        MulAut.conj (hatMk K ⟨z, hz⟩) := hphi
    rw [hphi'] at hF
    exact (hAut (Hat K) hQ).1 _ hzn (by rw [hz2']; exact hxc) hF

theorem exists_order_four_conj (h44 : II4_44) (hG : IsKProperSimple G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup G} (hK : IsIntrinsic x K) {s : G} (hs : s * s = 1)
    (hsN : s ∈ normalizer (K : Set G)) (hs' : InducesInner s K ∧ s ∉ cSec K) :
    ∃ q : Hat K, phi K s hsN = MulAut.conj q ∧ orderOf q = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := h44 G hG x hx K hK.1 hK.2.1
  have hφ2 : phi K s hsN * phi K s hsN = 1 := phi_mul_self K hsN hs
  obtain ⟨q, hq⟩ := (phi_mem_inn_iff K hsN).mpr hs'.1
  refine ⟨q, hq.symm, ?_⟩
  have hqq : (MulAut.conj (q * q) : MulAut (Hat K)) = 1 := by
    rw [map_mul, hq, hφ2]
  have hqqc : q * q ∈ center (Hat K) := mem_center_of_conj_eq_one hqq
  have hqn : q ∉ center (Hat K) := by
    intro hc
    apply hs'.2
    rw [← phi_eq_one_iff K hsN, ← hq]
    exact conj_eq_one_of_mem_center hc
  have hsq4 : (q * q) * (q * q) = 1 := by
    have h1 : orderOf (⟨q * q, hqqc⟩ : center (Hat K)) ∣ Nat.card (center (Hat K)) :=
      orderOf_dvd_natCard _
    rw [hQ.2] at h1
    have h2 : (⟨q * q, hqqc⟩ : center (Hat K)) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 := congrArg Subtype.val h2
    simpa [pow_two] using h3
  have hsq1 : ¬ q * q = 1 := by
    intro h1
    rcases hat_sq_eq_one hK hx h1 with h | h
    · apply hqn
      rw [h]
      exact one_mem _
    · apply hqn
      rw [h]
      exact hatMk_mem_center hK.2.2 hK.mem_cSec
  have h4 : orderOf q = 2 ^ (1 + 1) := by
    apply orderOf_eq_prime_pow
    · simpa [pow_two] using hsq1
    · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, pow_two q, pow_two (q * q)]
      exact hsq4
  simpa using h4

theorem exists_adjust (h44 : II4_44) (hAut : II4_Aut) (hG : IsKProperSimple G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup G} (hK : IsIntrinsic x K) {s t : G} (hs : s * s = 1)
    (ht : t * t = 1) (hs' : InducesInner s K ∧ s ∉ cSec K) (ht' : InducesInner t K ∧ t ∉ cSec K) :
    ∃ h ∈ K, (h * s * h⁻¹) * t ∈ cSec K := by
  have hsN : s ∈ normalizer (K : Set G) := innSub_le_normalizer K (mem_innSub_iff.mpr hs'.1)
  have htN : t ∈ normalizer (K : Set G) := innSub_le_normalizer K (mem_innSub_iff.mpr ht'.1)
  have hQ := h44 G hG x hx K hK.1 hK.2.1
  obtain ⟨qs, hqs, hqs4⟩ := exists_order_four_conj h44 hG hx hK hs hsN hs'
  obtain ⟨qt, hqt, hqt4⟩ := exists_order_four_conj h44 hG hx hK ht htN ht'
  obtain ⟨c, hc⟩ := isConj_iff.mp ((hAut (Hat K) hQ).2.1 qs qt hqs4 hqt4)
  obtain ⟨h', rfl⟩ := hatMk_surjective K c
  refine ⟨(h' : G), h'.2, ?_⟩
  have hhN : (h' : G) ∈ normalizer (K : Set G) := le_normalizer h'.2
  have hs'N : (h' : G) * s * (h' : G)⁻¹ ∈ normalizer (K : Set G) :=
    mul_mem (mul_mem hhN hsN) (inv_mem hhN)
  have e1 : phi K ((h' : G) * s * (h' : G)⁻¹) hs'N =
      phi K (h' : G) hhN * phi K s hsN * phi K (h' : G)⁻¹ (inv_mem hhN) :=
    (phi_mul K (mul_mem hhN hsN) (inv_mem hhN)).trans (by rw [phi_mul K hhN hsN])
  have e2 : phi K (h' : G) hhN = MulAut.conj (hatMk K h') := phi_of_mem K h'.2
  have e3 : phi K (h' : G)⁻¹ (inv_mem hhN) = MulAut.conj (hatMk K h')⁻¹ := by
    have := phi_of_mem K (inv_mem h'.2)
    rw [this, ← map_inv]
    try rfl
  have hphi : phi K ((h' : G) * s * (h' : G)⁻¹) hs'N = phi K t htN := by
    rw [e1, e2, e3, hqs, hqt, ← map_mul, ← map_mul, hc]
  have h1 : phi K ((h' : G) * s * (h' : G)⁻¹ * t) (mul_mem hs'N htN) = 1 := by
    rw [phi_mul K hs'N htN, hphi]
    exact phi_mul_self K htN ht
  exact (phi_eq_one_iff K _).mp h1

theorem mem_pPrimeCoreOf_or_mul (h44 : II4_44) (hG : IsKProperSimple G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup G} (hK : IsIntrinsic x K) {m : G} (hm : m ∈ K)
    (hmc : m ∈ cSec K) : m ∈ pPrimeCoreOf 2 K ∨ ∃ o ∈ pPrimeCoreOf 2 K, m = x * o := by
  have hcard := (h44 G hG x hx K hK.1 hK.2.1).2
  have hmz := hatMk_mem_center hm hmc
  have hxz := hatMk_mem_center hK.2.2 hK.mem_cSec
  by_cases h1 : hatMk K ⟨m, hm⟩ = 1
  · left
    exact (hatMk_eq_one_iff K ⟨m, hm⟩).mp h1
  · right
    have hx1 : hatMk K ⟨x, hK.2.2⟩ ≠ 1 := by
      intro h
      have h2 := (hatMk_eq_one_iff K ⟨x, hK.2.2⟩).mp h
      exact ne_one_of_orderOf_eq_two hx (eq_one_of_mem_pPrimeCoreOf h2
        (isPGroup_zpowers_of_mul_self_eq_one (mul_self_eq_one_of_orderOf_eq_two hx)))
    have heq := eq_of_mem_center_of_card_two hcard hmz hxz h1 hx1
    refine ⟨x⁻¹ * m, ?_, by group⟩
    have h3 : hatMk K ⟨x⁻¹ * m, mul_mem (inv_mem hK.2.2) hm⟩ = 1 := by
      have e : (⟨x⁻¹ * m, mul_mem (inv_mem hK.2.2) hm⟩ : ↥K) = ⟨x, hK.2.2⟩⁻¹ * ⟨m, hm⟩ := rfl
      rw [e, map_mul, map_inv, heq]
      group
    exact (hatMk_eq_one_iff K _).mp h3

theorem mem_sup_of_not_mem_cSec {x s : G} {K₁ K₂ M₁ M₂ : Subgroup G} (hK₁ : IsIntrinsic x K₁)
    (hK₂ : IsIntrinsic x K₂) (hM₁ : IsIntrinsic x M₁) (hM₂ : IsIntrinsic x M₂)
    (hMne : M₁ ≠ M₂) (hs : s ∈ K₁ ⊔ K₂) (hs₁ : s ∉ cSec M₁) (hs₂ : s ∉ cSec M₂) :
    s ∈ M₁ ⊔ M₂ := by
  have key : ∀ M : Subgroup G, IsIntrinsic x M → s ∉ cSec M → M = K₁ ∨ M = K₂ := by
    intro M hM hsM
    by_contra hcon
    push Not at hcon
    have h1 : K₁ ≤ cSec M := le_cSec_of_ne hK₁.1 hM.1 (fun e => hcon.1 e.symm)
    have h2 : K₂ ≤ cSec M := le_cSec_of_ne hK₂.1 hM.1 (fun e => hcon.2 e.symm)
    exact hsM ((sup_le h1 h2) hs)
  rcases key M₁ hM₁ hs₁ with h1 | h1 <;> rcases key M₂ hM₂ hs₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hMne
  · rw [h1, h2]
    exact hs
  · rw [h1, h2, sup_comm]
    exact hs
  · exact absurd (h1.trans h2.symm) hMne

theorem exists_conj_of_diag (h44 : II4_44) (hAut : II4_Aut) (hG : IsKProperSimple G) {x : G}
    (hx : orderOf x = 2) {K₁ K₂ : Subgroup G} (h₁ : IsIntrinsic x K₁) (h₂ : IsIntrinsic x K₂)
    (hne : K₁ ≠ K₂) {s t : G} (hs : s * s = 1) (ht : t * t = 1) (hsE : s ∈ K₁ ⊔ K₂)
    (htE : t ∈ K₁ ⊔ K₂) (hs₁ : InducesInner s K₁ ∧ s ∉ cSec K₁)
    (hs₂ : InducesInner s K₂ ∧ s ∉ cSec K₂) (ht₁ : InducesInner t K₁ ∧ t ∉ cSec K₁)
    (ht₂ : InducesInner t K₂ ∧ t ∉ cSec K₂) :
    ∃ r : G, r⁻¹ * s * r = t ∨ r⁻¹ * s * r = t * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 := mul_self_eq_one_of_orderOf_eq_two hx
  have h12 : K₁ ≤ cSec K₂ := le_cSec_of_ne h₁.1 h₂.1 hne
  have h21 : K₂ ≤ cSec K₁ := le_cSec_of_ne h₂.1 h₁.1 (Ne.symm hne)
  have hEx : K₁ ⊔ K₂ ≤ centralizer ({x} : Set G) := sup_le h₁.1.1 h₂.1.1
  have hK₂N : K₂ ≤ normalizer (K₁ : Set G) := fun z hz => (h21 hz).1
  have hK₁N : K₁ ≤ normalizer (K₂ : Set G) := fun z hz => (h12 hz).1
  have hEN₁ : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) := sup_le (fun _ hl => le_normalizer hl) hK₂N
  have hEN₂ : K₁ ⊔ K₂ ≤ normalizer (K₂ : Set G) := sup_le hK₁N (fun _ hl => le_normalizer hl)
  have hO₁ : pPrimeCoreOf 2 K₁ ≤ pPrimeCoreOf 2 (K₁ ⊔ K₂) :=
    pPrimeCoreOf_le_of_normal 2 le_sup_left
      ((Subgroup.normal_subgroupOf_iff le_sup_left).mpr fun h k hh hk =>
        (mem_normalizer_iff.mp (hEN₁ hk) h).mp hh)
  have hO₂ : pPrimeCoreOf 2 K₂ ≤ pPrimeCoreOf 2 (K₁ ⊔ K₂) :=
    pPrimeCoreOf_le_of_normal 2 le_sup_right
      ((Subgroup.normal_subgroupOf_iff le_sup_right).mpr fun h k hh hk =>
        (mem_normalizer_iff.mp (hEN₂ hk) h).mp hh)
  obtain ⟨g₁, hg₁K, hg₁⟩ := exists_adjust h44 hAut hG hx h₁ hs ht hs₁ ht₁
  have hs₁sq : (g₁ * s * g₁⁻¹) * (g₁ * s * g₁⁻¹) = 1 := by
    calc (g₁ * s * g₁⁻¹) * (g₁ * s * g₁⁻¹) = g₁ * (s * s) * g₁⁻¹ := by group
      _ = 1 := by rw [hs]; group
  have hs₁₂ : InducesInner (g₁ * s * g₁⁻¹) K₂ ∧ g₁ * s * g₁⁻¹ ∉ cSec K₂ := by
    refine ⟨?_, fun hcs => hs₂.2 ?_⟩
    · have hg : g₁ ∈ innSub K₂ := cSec_le_innSub K₂ (h12 hg₁K)
      exact mem_innSub_iff.mp (mul_mem (mul_mem hg (mem_innSub_iff.mpr hs₂.1)) (inv_mem hg))
    · have hg : g₁ ∈ cSec K₂ := h12 hg₁K
      have := mul_mem (mul_mem (inv_mem hg) hcs) hg
      rwa [show g₁⁻¹ * (g₁ * s * g₁⁻¹) * g₁ = s by group] at this
  obtain ⟨g₂, hg₂K, hg₂⟩ := exists_adjust h44 hAut hG hx h₂ hs₁sq ht hs₁₂ ht₂
  have htN₁ : t ∈ normalizer (K₁ : Set G) := innSub_le_normalizer K₁ (mem_innSub_iff.mpr ht₁.1)
  have hd₁ : (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹) * t ∈ cSec K₁ := by
    have hg2c : g₂ ∈ cSec K₁ := h21 hg₂K
    have h1 : t⁻¹ * g₂ * t⁻¹⁻¹ ∈ cSec K₁ := cSec_conj K₁ (inv_mem htN₁) hg2c
    have h2 := mul_mem (mul_mem hg2c hg₁) (inv_mem h1)
    rwa [show g₂ * ((g₁ * s * g₁⁻¹) * t) * (t⁻¹ * g₂ * t⁻¹⁻¹)⁻¹ =
      (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹) * t by group] at h2
  set d := (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹) * t with hd
  have hdE : d ∈ K₁ ⊔ K₂ := by
    have hg₁E : g₁ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left hg₁K
    have hg₂E : g₂ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_right hg₂K
    exact mul_mem (mul_mem (mul_mem hg₂E (mul_mem (mul_mem hg₁E hsE) (inv_mem hg₁E)))
      (inv_mem hg₂E)) htE
  obtain ⟨m₁, hm₁, m₂, hm₂, hdm⟩ := exists_mul_of_mem_sup hK₂N hdE
  have hm₂c : m₂ ∈ cSec K₁ := h21 hm₂
  have hm₁c : m₁ ∈ cSec K₁ := by
    have := mul_mem hd₁ (inv_mem hm₂c)
    rw [hdm, mul_inv_cancel_right] at this
    exact this
  have hm₁c₂ : m₁ ∈ cSec K₂ := h12 hm₁
  have hm₂c₂ : m₂ ∈ cSec K₂ := by
    have := mul_mem (inv_mem hm₁c₂) hg₂
    rw [hdm, show m₁⁻¹ * (m₁ * m₂) = m₂ by group] at this
    exact this
  have hxK₁ : ∀ o ∈ pPrimeCoreOf 2 K₁, o * x = x * o := fun o ho =>
    h₁.comm_of_mem (TwoThin.pPrimeCoreOf_le K₁ ho)
  have hdO : d ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) ∨ ∃ o ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂), d = x * o := by
    rcases mem_pPrimeCoreOf_or_mul h44 hG hx h₁ hm₁ hm₁c with h1 | ⟨o₁, ho₁, e₁⟩
    · rcases mem_pPrimeCoreOf_or_mul h44 hG hx h₂ hm₂ hm₂c₂ with h2 | ⟨o₂, ho₂, e₂⟩
      · left
        rw [hdm]
        exact mul_mem (hO₁ h1) (hO₂ h2)
      · right
        refine ⟨m₁ * o₂, mul_mem (hO₁ h1) (hO₂ ho₂), ?_⟩
        rw [hdm, e₂]
        calc m₁ * (x * o₂) = (m₁ * x) * o₂ := by group
          _ = (x * m₁) * o₂ := by rw [hxK₁ m₁ h1]
          _ = x * (m₁ * o₂) := by group
    · rcases mem_pPrimeCoreOf_or_mul h44 hG hx h₂ hm₂ hm₂c₂ with h2 | ⟨o₂, ho₂, e₂⟩
      · right
        refine ⟨o₁ * m₂, mul_mem (hO₁ ho₁) (hO₂ h2), ?_⟩
        rw [hdm, e₁]
        group
      · left
        rw [hdm, e₁, e₂]
        have : x * o₁ * (x * o₂) = o₁ * o₂ := by
          calc x * o₁ * (x * o₂) = x * (o₁ * x) * o₂ := by group
            _ = x * (x * o₁) * o₂ := by rw [hxK₁ o₁ ho₁]
            _ = (x * x) * (o₁ * o₂) := by group
            _ = o₁ * o₂ := by rw [hx1, one_mul]
        rw [this]
        exact mul_mem (hO₁ ho₁) (hO₂ ho₂)
  have htE' : t ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := le_normalizer htE
  have hOt : ∀ o ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂), t⁻¹ * o * t ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := fun o ho => by
    have := TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (inv_mem htE') ho
    rwa [inv_inv] at this
  have htx : t * x = x * t := mem_centralizer_singleton_iff.mp (hEx htE)
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hs2d : g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹ = d * t := by
    calc g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹ = d * t⁻¹ := by rw [hd]; group
      _ = d * t := by rw [ht']
  have hs₂eq : ∃ t'' o' : G, (t'' = t ∨ t'' = x * t) ∧ o' ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) ∧
      g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹ = t'' * o' := by
    rcases hdO with h | ⟨o, ho, e⟩
    · refine ⟨t, t⁻¹ * d * t, Or.inl rfl, hOt d h, ?_⟩
      rw [hs2d]
      group
    · refine ⟨x * t, t⁻¹ * o * t, Or.inr rfl, hOt o ho, ?_⟩
      rw [hs2d, e]
      group
  obtain ⟨t'', o', ht'', ho', he⟩ := hs₂eq
  have ht''sq : t'' * t'' = 1 := by
    rcases ht'' with h | h
    · rw [h]
      exact ht
    · rw [h]
      calc x * t * (x * t) = x * (t * x) * t := by group
        _ = x * (x * t) * t := by rw [htx]
        _ = (x * x) * (t * t) := by group
        _ = 1 := by rw [hx1, ht, one_mul]
  have hs₂sq : (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹) * (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹) = 1 := by
    calc (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹) * (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹)
        = g₂ * ((g₁ * s * g₁⁻¹) * (g₁ * s * g₁⁻¹)) * g₂⁻¹ := by group
      _ = 1 := by rw [hs₁sq]; group
  have hinv : t'' * o' * t''⁻¹ = o'⁻¹ := by
    have h1 : (t'' * o') * (t'' * o') = 1 := by rw [← he]; exact hs₂sq
    have ht''inv : t''⁻¹ = t'' := inv_eq_of_mul_eq_one_right ht''sq
    have h2 : t'' * o' * t'' = o'⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc t'' * o' * t'' * o' = (t'' * o') * (t'' * o') := by group
        _ = 1 := h1
    rw [ht''inv]
    exact h2
  obtain ⟨k, -, hkconj⟩ :=
    exists_conj_of_involutions_of_odd (odd_orderOf_of_mem_pPrimeCoreOf ho') hinv
  have hk' : k⁻¹ * t'' * k = g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹ := by
    rw [hkconj]
    exact he.symm
  have hfin : (g₁⁻¹ * g₂⁻¹ * k⁻¹)⁻¹ * s * (g₁⁻¹ * g₂⁻¹ * k⁻¹) = t'' := by
    calc (g₁⁻¹ * g₂⁻¹ * k⁻¹)⁻¹ * s * (g₁⁻¹ * g₂⁻¹ * k⁻¹)
        = k * (g₂ * (g₁ * s * g₁⁻¹) * g₂⁻¹) * k⁻¹ := by group
      _ = k * (k⁻¹ * t'' * k) * k⁻¹ := by rw [hk']
      _ = t'' := by group
  refine ⟨g₁⁻¹ * g₂⁻¹ * k⁻¹, ?_⟩
  rcases ht'' with h | h
  · left
    rw [hfin, h]
  · right
    rw [hfin, h, htx]

end CFSG.GH74.GLS.Stage1.Thm2.Recip
