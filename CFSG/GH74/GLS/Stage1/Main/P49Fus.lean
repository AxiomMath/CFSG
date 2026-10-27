module

public import CFSG.GH74.GLS.Stage1.Main.P49FusA
public import CFSG.GH74.GLS.Stage1.Main.P49Syl
public import CFSG.GH74.GLS.Stage1.Main.P49Setup
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Glue2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section FusB

variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y u₁ u₂ : G}

theorem y_sq_one49 (h : Ctx49 G z S K F U x y) : y * y = 1 := by
  have : y ^ 2 = 1 := by rw [← h.y_two]; exact pow_orderOf_eq_one y
  rwa [sq] at this

theorem y_inv_u₂49 (hsd : SD_facts) (h : Ctx49 G z S K F U x y)
    (c : R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂) :
    y * u₂ * y⁻¹ = u₂ * z := by
  have hy2 := y_sq_one49 h
  have hRz : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.std.Rz_eq
  have hyQ : y ∉ S ⊓ cSec K := fun hy => h.y_R (hRz ▸ mem_sup_right hy)
  have hysd : ∃ n, IVK.IsSemidihedralTwoGroup ↥((S ⊓ cSec K) ⊔ zpowers y) n := by
    have := h.y_sd
    rwa [h.std.Qz_eq] at this
  obtain ⟨hC, -⟩ := hsd G (S ⊓ cSec K) z y c.quatQ c.cfg.z_Q c.hz2 c.hz1 hy2 hyQ
    (fun p hp => c.cfg.Q_norm y h.y_S p hp) hysd
  rcases (c.norm_u h.y_S).2 with e | e
  · exfalso
    have hcomm : y * u₂ = u₂ * y := by
      calc y * u₂ = (y * u₂ * y⁻¹) * y := by group
        _ = u₂ * y := by rw [e]
    rcases hC u₂ c.u₂_mem hcomm with h1 | h1
    · exact c.u₂_ne.1 h1
    · exact c.u₂_ne.2 h1
  · exact e

end FusB

section FusC


variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y u₁ u₂ : G}

theorem y_data49 (h : Ctx49 G z S K F U x y) :
    y ∉ S ⊓ cSec K ∧ ∃ n, IVK.IsSemidihedralTwoGroup ↥((S ⊓ cSec K) ⊔ zpowers y) n := by
  have hRz : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.std.Rz_eq
  refine ⟨fun hy => h.y_R (hRz ▸ mem_sup_right hy), ?_⟩
  have := h.y_sd
  rwa [h.std.Qz_eq] at this

theorem no_inv_M_outside49 (hc : Closed49) (h : Ctx49 G z S K F U x y)
    (c : R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂)
    {g : G} (hgS : g ∈ S) (hgu : g * u₂ = u₂ * g) (hgg : g * g = 1) (hgR : g ∉ Rz S z) : False := by
  have hz2 := c.hz2
  have hz1 := c.hz1
  have hPQ := c.cfg.PQ_comm
  have hRz : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.std.Rz_eq
  have hyS := h.y_S
  have hyR := h.y_R
  have hy2 := y_sq_one49 h
  have hyu := y_inv_u₂49 hc.hsd h c
  obtain ⟨hyQ, hysd⟩ := y_data49 h
  have hidx : ((Rz S z).subgroupOf S).index = 2 := h.idx
  have hr : g * y⁻¹ ∈ Rz S z := by
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g, hgS⟩)
      (b := ⟨y⁻¹, S.inv_mem hyS⟩)).2 (by
        simp only [Subgroup.mem_subgroupOf]
        exact iff_of_false hgR (fun hh => hyR (by simpa using inv_mem hh)))
    simpa [Subgroup.mem_subgroupOf] using key
  obtain ⟨p, hp, q, hq, hpq⟩ := M.mem_sup_of_commute hPQ (hRz ▸ hr)
  have hpS : p ∈ S := hp.1
  have hqS : q ∈ S := hq.1
  have hgpq : g = p * q * y := by rw [← hpq]; group
  have hPy : y * p * y⁻¹ ∈ S ⊓ K := c.cfg.P_norm y hyS p hp
  have hQy : y * q * y⁻¹ ∈ S ⊓ cSec K := c.cfg.Q_norm y hyS q hq
  have h1 : g * u₂ * g⁻¹ = u₂ := by
    calc g * u₂ * g⁻¹ = (u₂ * g) * g⁻¹ := by rw [hgu]
      _ = u₂ := by group
  have h2 : g * u₂ * g⁻¹ = (p * (q * u₂ * q⁻¹) * p⁻¹) * z := by
    rw [hgpq]
    calc p * q * y * u₂ * (p * q * y)⁻¹ = p * q * (y * u₂ * y⁻¹) * q⁻¹ * p⁻¹ := by group
      _ = p * q * (u₂ * z) * q⁻¹ * p⁻¹ := by rw [hyu]
      _ = p * ((q * u₂ * q⁻¹) * (q * z * q⁻¹)) * p⁻¹ := by group
      _ = p * ((q * u₂ * q⁻¹) * z) * p⁻¹ := by rw [szs49 c hqS]
      _ = (p * (q * u₂ * q⁻¹) * p⁻¹) * (p * z * p⁻¹) := by group
      _ = (p * (q * u₂ * q⁻¹) * p⁻¹) * z := by rw [szs49 c hpS]
  have h3 : p * (q * u₂ * q⁻¹) * p⁻¹ = q * u₂ * q⁻¹ := by
    have hmem : q * u₂ * q⁻¹ ∈ S ⊓ cSec K := mul_mem (mul_mem hq c.u₂_mem) (inv_mem hq)
    have hc' := hPQ p hp _ hmem
    calc p * (q * u₂ * q⁻¹) * p⁻¹ = (q * u₂ * q⁻¹) * p * p⁻¹ := by rw [hc']
      _ = q * u₂ * q⁻¹ := by group
  have h4 : q * u₂ * q⁻¹ = u₂ * z := by
    have h5 : u₂ = (q * u₂ * q⁻¹) * z := by rw [← h3, ← h2, h1]
    have h6 : (q * u₂ * q⁻¹) * z * z = q * u₂ * q⁻¹ := by
      rw [mul_assoc (q * u₂ * q⁻¹) z z, hz2, mul_one]
    calc q * u₂ * q⁻¹ = (q * u₂ * q⁻¹) * z * z := h6.symm
      _ = u₂ * z := by rw [← h5]
  have hqnc : ¬ (q * u₂ = u₂ * q) := by
    intro hcomm
    have : q * u₂ * q⁻¹ = u₂ := by
      calc q * u₂ * q⁻¹ = (u₂ * q) * q⁻¹ := by rw [hcomm]
        _ = u₂ := by group
    rw [h4] at this
    exact hz1 (by simpa using this)
  have hqpy : (y * p * y⁻¹) * q = q * (y * p * y⁻¹) := (hPQ _ hPy q hq)
  have hsq : (p * (y * p * y⁻¹)) * (q * (y * q * y⁻¹)) = 1 := by
    have e : g * g = (p * (y * p * y⁻¹)) * (q * (y * q * y⁻¹)) * (y * y) := by
      rw [hgpq]
      calc p * q * y * (p * q * y) = p * (q * (y * p * y⁻¹)) * (y * q * y⁻¹) * (y * y) := by group
        _ = p * ((y * p * y⁻¹) * q) * (y * q * y⁻¹) * (y * y) := by rw [hqpy]
        _ = (p * (y * p * y⁻¹)) * (q * (y * q * y⁻¹)) * (y * y) := by group
    rw [hgg, hy2, mul_one] at e
    exact e.symm
  have hqq : q * (y * q * y⁻¹) = (p * (y * p * y⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have hqqP : q * (y * q * y⁻¹) ∈ S ⊓ K := by rw [hqq]; exact inv_mem (mul_mem hp hPy)
  have hqqQ : q * (y * q * y⁻¹) ∈ S ⊓ cSec K := mul_mem hq hQy
  have hqy2 : (q * y) * (q * y) = q * (y * q * y⁻¹) * (y * y) := by group
  have hqy2' : (q * y) * (q * y) = 1 := by
    rcases c.cfg.PQ_inf _ hqqP hqqQ with e | e
    · rw [hqy2, e, hy2, mul_one]
    · exfalso
      refine hc.hsdq G (S ⊓ cSec K) z y c.quatQ c.cfg.z_Q hz2 hz1 hy2 hyQ
        (fun p hp => c.cfg.Q_norm y hyS p hp) hysd q hq ?_
      rw [hqy2, e, hy2, mul_one]
  obtain ⟨p', hp', hp'eq⟩ := (hc.hsd G (S ⊓ cSec K) z y c.quatQ c.cfg.z_Q hz2 hz1 hy2 hyQ
    (fun p hp => c.cfg.Q_norm y hyS p hp) hysd).2 q hq hqy2'
  have hqeq : q = p'⁻¹ * y * p' * y⁻¹ := by
    calc q = (q * y) * y⁻¹ := by group
      _ = (p'⁻¹ * y * p') * y⁻¹ := by rw [← hp'eq]
  have hcomm := commutator_u₂49 c (S.inv_mem hp'.1) hyS
  simp only [inv_inv] at hcomm
  exact hqnc (by rw [hqeq]; exact hcomm)

end FusC

section FusD


variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y u₁ u₂ : G}

theorem inv_M_conj49 (hlift : II4_ord4_lift) (hc : Closed49) (h : Ctx49 G z S K F U x y)
    (c : R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂) :
    ∀ g ∈ S ⊓ centralizer ({u₂} : Set G), orderOf g = 2 → IsConj z g := by
  intro g hg hg2
  have hz2 := c.hz2
  have hz1 := c.hz1
  have hgS : g ∈ S := hg.1
  have hgu : g * u₂ = u₂ * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
  have hgg : g * g = 1 := by
    have : g ^ 2 = 1 := by rw [← hg2]; exact pow_orderOf_eq_one g
    rwa [sq] at this
  have hg1 : g ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  have hRz : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.std.Rz_eq
  have hPQ := c.cfg.PQ_comm
  by_cases hgR : g ∈ Rz S z
  · obtain ⟨p, hp, q, hq, rfl⟩ := M.mem_sup_of_commute hPQ (hRz ▸ hgR)
    have hpu : p * u₂ = u₂ * p := hPQ p hp u₂ c.u₂_mem
    have hqu : q * u₂ = u₂ * q := by
      calc q * u₂ = p⁻¹ * (p * q * u₂) := by group
        _ = p⁻¹ * (u₂ * (p * q)) := by rw [hgu]
        _ = p⁻¹ * (u₂ * p) * q := by group
        _ = p⁻¹ * (p * u₂) * q := by rw [hpu]
        _ = u₂ * q := by group
    have hpq : p * q = q * p := hPQ p hp q hq
    have hsq : (p * p) * (q * q) = 1 := by
      calc (p * p) * (q * q) = p * (p * q) * q := by group
        _ = p * (q * p) * q := by rw [hpq]
        _ = (p * q) * (p * q) := by group
        _ = 1 := hgg
    have hppQ : p * p ∈ S ⊓ cSec K := by
      have : p * p = (q * q)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact inv_mem (mul_mem hq hq)
    rcases c.cfg.PQ_inf (p * p) (mul_mem hp hp) hppQ with hp1 | hpz
    · have hq1 : q * q = 1 := by rw [hp1, one_mul] at hsq; exact hsq
      rcases c.cfg.P_inv p hp hp1 with e1 | e1 <;> rcases c.Q_inv q hq hq1 with e2 | e2
      · exact absurd (by rw [e1, e2, one_mul]) hg1
      · rw [e1, e2, one_mul]
      · rw [e1, e2, mul_one]
      · exact absurd (by rw [e1, e2, hz2]) hg1
    · have hqz : q * q = z := by
        rw [hpz] at hsq
        have h1 : q * q = z⁻¹ := eq_inv_of_mul_eq_one_right hsq
        rw [h1]
        exact inv_eq_of_mul_eq_one_right hz2
      have hcomm' : u₂⁻¹ * q = q * u₂⁻¹ := by
        calc u₂⁻¹ * q = u₂⁻¹ * (q * u₂) * u₂⁻¹ := by group
          _ = u₂⁻¹ * (u₂ * q) * u₂⁻¹ := by rw [hqu]
          _ = q * u₂⁻¹ := by group
      have hu2inv : u₂⁻¹ * u₂⁻¹ = z := by
        rw [← mul_inv_rev, c.u₂_sq]
        exact inv_eq_of_mul_eq_one_right hz2
      have hsq1 : (q * u₂⁻¹) * (q * u₂⁻¹) = 1 := by
        calc (q * u₂⁻¹) * (q * u₂⁻¹) = q * (u₂⁻¹ * q) * u₂⁻¹ := by group
          _ = q * (q * u₂⁻¹) * u₂⁻¹ := by rw [hcomm']
          _ = (q * q) * (u₂⁻¹ * u₂⁻¹) := by group
          _ = 1 := by rw [hqz, hu2inv, hz2]
      have hx3 := h.x3
      have hknown := isConj_u49 c hx3
      rcases c.Q_inv (q * u₂⁻¹) (mul_mem hq (inv_mem c.u₂_mem)) hsq1 with e | e
      · have hqe : q = u₂ := mul_inv_eq_one.1 e
        rw [hqe]
        exact kconj_step hlift h.std (p := u₁) (u₁ := p) (x := u₂) c.u₁_mem hp c.u₂_mem c.u₁_sq hpz
          c.u₂_sq rfl hknown
      · have hqe : q = z * u₂ := by
          calc q = (q * u₂⁻¹) * u₂ := by group
            _ = z * u₂ := by rw [e]
        have hpz' : p * z = z * p := c.z_comm hp.1
        have hp'sq : (p * z) * (p * z) = z := by
          calc (p * z) * (p * z) = p * (z * p) * z := by group
            _ = p * (p * z) * z := by rw [hpz']
            _ = (p * p) * (z * z) := by group
            _ = z := by rw [hpz, hz2, mul_one]
        have := kconj_step hlift h.std (p := u₁) (u₁ := p * z) (x := u₂) c.u₁_mem
          (mul_mem hp c.cfg.z_P) c.u₂_mem c.u₁_sq hp'sq c.u₂_sq rfl hknown
        rw [hqe, ← mul_assoc]
        exact this
  · exfalso
    exact no_inv_M_outside49 hc h c hgS hgu hgg hgR

end FusD

section FusE


variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y : G}

theorem fusion49 (hIG : IG_15_16_ext) (hlift : II4_ord4_lift) (hc : Closed49)
    (h : Ctx49 G z S K F U x y) :
    ∀ t ∈ S, orderOf t = 2 → IsConj z t := by
  obtain ⟨u₁, u₂, c⟩ := setup9_of_ctx49 hc h
  have hSyl := sylow_G_of_std6 h.std.toStd6r1.toStd6
  have hyu := y_inv_u₂49 hc.hsd h c
  have hMidx := relIndex_M49 c h.y_S hyu
  have hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    obtain ⟨hs, ⟨a, b, hab⟩, -⟩ := h.std.simple
    rcases hs.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ with e | e
    · exfalso
      apply hab
      have hmem : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [e, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact e
  intro t ht ht2
  obtain ⟨g, -, hgM, -⟩ := hIG G ⊤ S (S ⊓ centralizer ({u₂} : Set G)) ⊥ t hSyl inf_le_left hMidx
    bot_le (fun x _ n hn => by rw [Subgroup.mem_bot] at hn ⊢; simp [hn])
    (by rw [Subgroup.card_bot]; exact odd_one) ht ht2
    (by rw [hperf]; exact Subgroup.mem_sup_left (Subgroup.mem_top t))
  have hord : orderOf (g⁻¹ * t * g) = 2 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    rw [← ht2]
    simpa [MulAut.conj_apply] using this
  have hconj := inv_M_conj49 hlift hc h c (g⁻¹ * t * g) hgM hord
  exact hconj.trans (isConj_iff.2 ⟨g, by group⟩)

end FusE

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
