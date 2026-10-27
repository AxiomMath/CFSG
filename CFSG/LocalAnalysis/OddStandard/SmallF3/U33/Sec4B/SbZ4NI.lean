module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

private theorem isElemAbelian_zpowers_of_mul_self {g : G} (hgg : g * g = 1) :
    CFSG.Open.IsElemAbelian 2 (zpowers g) := by
  refine ⟨inferInstance, ?_⟩
  intro x hx
  rcases z4_mem_zpowers_of_mul_self hgg hx with h | h
  · rw [h]; exact one_pow 2
  · rw [h, pow_two, hgg]

theorem E8_eq_sup : closure ({t, tau, lam} : Set G) =
    closure ({t, tau} : Set G) ⊔ zpowers lam := by
  have hset : ({t, tau, lam} : Set G) = ({t, tau} : Set G) ∪ {lam} := by
    ext x; simp [or_comm, or_left_comm, or_assoc]
  rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure lam]

theorem T_eq_sup : closure ({t, tau} : Set G) = zpowers t ⊔ zpowers tau := by
  rw [show ({t, tau} : Set G) = {t} ∪ {tau} by ext x; simp [or_comm, or_left_comm, or_assoc],
    Subgroup.closure_union, ← Subgroup.zpowers_eq_closure t, ← Subgroup.zpowers_eq_closure tau]

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

private theorem lam_ne_one : lam ≠ 1 := by
  intro h
  have h1 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [h]; group
  rw [hz.nGood.lam_conj_y] at h1
  exact hz.y_ne_w h1.symm

private theorem lam_cent_T :
    lam ∈ centralizer (closure ({t, tau} : Set G) : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hz.t_lam_comm
      · exact hz.tau_lam
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
      calc x⁻¹ * lam = x⁻¹ * (lam * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * lam) * x⁻¹ := by rw [← hx]
        _ = lam * x⁻¹ := by group

private theorem lam_norm_T : ∀ k ∈ zpowers lam, ∀ h ∈ closure ({t, tau} : Set G),
    k * h * k⁻¹ ∈ closure ({t, tau} : Set G) := by
  intro k hk h hh
  have hkC : k ∈ centralizer (closure ({t, tau} : Set G) : Set G) :=
    Subgroup.zpowers_le.mpr (lam_cent_T hz) hk
  have hcomm : h * k = k * h := mem_centralizer_iff.mp hkC h hh
  have hkh : k * h * k⁻¹ = h := by rw [← hcomm]; group
  rw [hkh]
  exact hh

private theorem lam_not_mem_T : lam ∉ closure ({t, tau} : Set G) := by
  have hyT : closure ({t, tau} : Set G) ≤ centralizer ({x₁ ^ 2} : Set G) := by
    rw [Subgroup.closure_le]
    rintro h (rfl | rfl)
    · exact mem_centralizer_iff.mpr (fun a ha => by
        rw [Set.mem_singleton_iff.mp ha]
        exact (hz.t_comm_V (x₁ ^ 2) hz.y_mem_V).symm)
    · exact mem_centralizer_iff.mpr (fun a ha => by
        rw [Set.mem_singleton_iff.mp ha]
        exact (hz.tau_cent_Y (x₁ ^ 2) (hz.V_le_Y hz.y_mem_V)).symm)
  intro hh
  have h1 : x₁ ^ 2 * lam = lam * x₁ ^ 2 := mem_centralizer_iff.mp (hyT hh) (x₁ ^ 2) rfl
  have h2 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [← h1]; group
  rw [hz.nGood.lam_conj_y] at h2
  exact hz.y_ne_w h2.symm

private theorem tau_cent_zpowers_t : tau ∈ centralizer (zpowers t : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Commute.zpow_left (show Commute t tau from hz.t_comm_tau) n).eq

private theorem tau_norm_zpowers_t : ∀ k ∈ zpowers tau, ∀ h ∈ zpowers t,
    k * h * k⁻¹ ∈ zpowers t := by
  intro k hk h hh
  have hkC : k ∈ centralizer (zpowers t : Set G) :=
    Subgroup.zpowers_le.mpr (tau_cent_zpowers_t hz) hk
  have hcomm : h * k = k * h := mem_centralizer_iff.mp hkC h hh
  have hkh : k * h * k⁻¹ = h := by rw [← hcomm]; group
  rw [hkh]
  exact hh

private theorem inf_zpowers_t_tau : zpowers t ⊓ zpowers tau = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  rcases z4_mem_zpowers_of_mul_self hz.t_mul_self hg.1 with h | h
  · exact h
  · rcases z4_mem_zpowers_of_mul_self hz.tau_mul_self hg.2 with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hz.t_ne_tau

private theorem card_T : Nat.card ↥(closure ({t, tau} : Set G)) = 4 := by
  rw [T_eq_sup, S4B.card_sup_eq_mul (tau_norm_zpowers_t hz) (inf_zpowers_t_tau hz)]
  have ht : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hz.t_mul_self) hz.t_ne_one
  have htau : Nat.card (zpowers tau) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hz.tau_mul_self) hz.tau_ne_one
  rw [ht, htau]

private theorem card_lam : Nat.card (zpowers lam) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hz.lam_mul_self) (lam_ne_one hz)

private theorem inf_T_zpowers_lam : closure ({t, tau} : Set G) ⊓ zpowers lam = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  rcases z4_mem_zpowers_of_mul_self hz.lam_mul_self hg.2 with h | h
  · exact h
  · exact absurd (h ▸ hg.1) (lam_not_mem_T hz)

theorem mem_E8_iff {g : G} :
    g ∈ closure ({t, tau, lam} : Set G) ↔
      g = 1 ∨ g = t ∨ g = tau ∨ g = t * tau ∨ g = lam ∨ g = t * lam ∨
        g = tau * lam ∨ g = t * tau * lam := by
  constructor
  · intro hg
    rw [E8_eq_sup] at hg
    obtain ⟨h, hh, k, hk, rfl⟩ :=
      (S4B.mem_sup_iff_of_normalizes (H := closure ({t, tau} : Set G))
        (K := zpowers lam) (lam_norm_T hz)).mp hg
    rcases (S4B.mem_closure_pair_of_invol hz.t_mul_self hz.tau_mul_self hz.t_comm_tau).mp hh
      with h1 | h1 | h1 | h1
    · rcases z4_mem_zpowers_of_mul_self hz.lam_mul_self hk with h2 | h2
      · left; simp only [h1, h2, one_mul, mul_one]
      · right; right; right; right; left; simp only [h1, h2, one_mul, mul_one]
    · rcases z4_mem_zpowers_of_mul_self hz.lam_mul_self hk with h2 | h2
      · right; left; simp only [h1, h2, one_mul, mul_one]
      · right; right; right; right; right; left; simp only [h1, h2, one_mul, mul_one]
    · rcases z4_mem_zpowers_of_mul_self hz.lam_mul_self hk with h2 | h2
      · right; right; left; simp only [h1, h2, one_mul, mul_one]
      · right; right; right; right; right; right; left; simp only [h1, h2, one_mul, mul_one]
    · rcases z4_mem_zpowers_of_mul_self hz.lam_mul_self hk with h2 | h2
      · right; right; right; left; simp only [h1, h2, one_mul, mul_one]
      · right; right; right; right; right; right; right; simp only [h1, h2, one_mul, mul_one]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · exact mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
        (subset_closure (by simp))

private theorem cent_Y_of_mul_tau {e u : G} (hu : u ∈ zpowers tau)
    (h : ∀ a ∈ ctxYq t tau x₁ x₂ rho, (e * u) * a = a * (e * u)) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, e * a = a * e := by
  intro a ha
  have hua : u * a = a * u := by
    rcases z4_mem_zpowers_of_mul_self hz.tau_mul_self hu with hu1 | hut
    · rw [hu1, one_mul, mul_one]
    · rw [hut]; exact hz.tau_cent_Y a ha
  have h1 : e * a * u = a * e * u := by
    calc e * a * u = e * (a * u) := by rw [mul_assoc]
      _ = e * (u * a) := by rw [← hua]
      _ = (e * u) * a := by rw [mul_assoc]
      _ = a * (e * u) := h a ha
      _ = a * e * u := by rw [mul_assoc]
  exact mul_right_cancel h1

theorem card_E8 : Nat.card ↥(closure ({t, tau, lam} : Set G)) = 8 := by
  rw [E8_eq_sup, S4B.card_sup_eq_mul (lam_norm_T hz) (inf_T_zpowers_lam hz), card_T hz, card_lam hz]

theorem E8_cosets : ∀ g ∈ closure ({t, tau, lam} : Set G),
    g ∈ zpowers tau ∨ t⁻¹ * g ∈ zpowers tau ∨ lam⁻¹ * g ∈ zpowers tau ∨
      (t * lam)⁻¹ * g ∈ zpowers tau := by
  intro g hg
  rcases (mem_E8_iff hz).mp hg with h | h | h | h | h | h | h | h
  · left; rw [h]; exact one_mem _
  · right; left
    rw [h, show t⁻¹ * t = 1 by rw [inv_mul_cancel]]
    exact one_mem _
  · left; rw [h]; exact mem_zpowers tau
  · right; left
    rw [h, show t⁻¹ * (t * tau) = tau by rw [← mul_assoc, inv_mul_cancel, one_mul]]
    exact mem_zpowers tau
  · right; right; left
    rw [h, show lam⁻¹ * lam = 1 by rw [inv_mul_cancel]]
    exact one_mem _
  · right; right; right
    rw [h, show (t * lam)⁻¹ * (t * lam) = 1 by rw [inv_mul_cancel]]
    exact one_mem _
  · right; right; left
    rw [h, show lam⁻¹ * (tau * lam) = tau by
      rw [hz.tau_lam, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact mem_zpowers tau
  · right; right; right
    rw [h, show (t * lam)⁻¹ * (t * tau * lam) = tau by
      rw [mul_inv_rev]
      calc (lam⁻¹ * t⁻¹) * (t * tau * lam)
          = lam⁻¹ * (t⁻¹ * (t * tau * lam)) := by group
        _ = lam⁻¹ * ((t⁻¹ * t) * (tau * lam)) := by group
        _ = lam⁻¹ * (tau * lam) := by rw [inv_mul_cancel, one_mul]
        _ = tau := by rw [hz.tau_lam, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact mem_zpowers tau

theorem E8_cent_Y : ∀ g ∈ closure ({t, tau, lam} : Set G),
    (∀ a ∈ ctxYq t tau x₁ x₂ rho, g * a = a * g) → g ∈ zpowers tau := by
  intro g hg hcent
  rcases (mem_E8_iff hz).mp hg with h | h | h | h | h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h] at hcent
    exact absurd hcent hz.nPre.not_cent_t_Y
  · rw [h]; exact mem_zpowers tau
  · rw [h] at hcent
    refine absurd (cent_Y_of_mul_tau hz (e := t) (u := tau) (mem_zpowers tau) ?_)
      hz.nPre.not_cent_t_Y
    intro a ha
    exact hcent a ha
  · have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hz.V_le_Y hz.y_mem_V
    rw [h] at hcent
    have h2 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
      rw [hcent (x₁ ^ 2) hy]; group
    rw [hz.nGood.lam_conj_y] at h2
    exact absurd h2.symm hz.y_ne_w
  · have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hz.V_le_Y hz.y_mem_V
    rw [h, hz.t_lam_comm] at hcent
    have h2 : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 := by
      rw [hcent (x₁ ^ 2) hy]; group
    rw [hz.sigma_y] at h2
    exact absurd h2.symm hz.y_ne_w
  · have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hz.V_le_Y hz.y_mem_V
    rw [h, hz.tau_lam] at hcent
    have hc : ∀ a ∈ ctxYq t tau x₁ x₂ rho, lam * a = a * lam :=
      cent_Y_of_mul_tau hz (e := lam) (u := tau) (mem_zpowers tau) hcent
    have h2 : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
      rw [hc (x₁ ^ 2) hy]; group
    rw [hz.nGood.lam_conj_y] at h2
    exact absurd h2.symm hz.y_ne_w
  · have hy : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho := hz.V_le_Y hz.y_mem_V
    rw [h] at hcent
    have hct : ∀ a ∈ ctxYq t tau x₁ x₂ rho,
        ((t * lam) * tau) * a = a * ((t * lam) * tau) := by
      intro a ha
      have hh := hcent a ha
      rwa [show t * tau * lam = (t * lam) * tau by rw [mul_assoc, hz.tau_lam]; group] at hh
    have hc : ∀ a ∈ ctxYq t tau x₁ x₂ rho, (t * lam) * a = a * (t * lam) :=
      cent_Y_of_mul_tau hz (e := t * lam) (u := tau) (mem_zpowers tau) hct
    have h2 : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 := by
      have hh : (lam * t) * x₁ ^ 2 = x₁ ^ 2 * (lam * t) := by
        have h3 := hc (x₁ ^ 2) hy
        rwa [hz.t_lam_comm] at h3
      rw [hh]; group
    rw [hz.sigma_y] at h2
    exact absurd h2.symm hz.y_ne_w

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
