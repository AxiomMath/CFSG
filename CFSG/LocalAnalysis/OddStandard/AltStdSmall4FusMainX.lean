module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusMainSetup

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.Main

open Subgroup Equiv AltStdCycTwo

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

section Step1

variable {c : Config G L Q n θ z} {H : Subgroup G} {Nbar Rbar : Subgroup (Perm (Fin n))} {k : ℕ}
  {cc : Subgroup (Perm (Fin n)) → Prop}

theorem IsHStar.exists_x (hH : IsHStar c H Nbar) (hR : FusR n c.hn8 Nbar Rbar k cc)
    (hk : ∀ P : Sylow 2 (centralizer ({z} : Set G)), Nat.card P = 2 ^ (k + 1)) :
    ∃ x ∈ normalizer (sSyl c H Rbar : Set G), x⁻¹ * z * x = z * w θ c.hn8 ∧
      x⁻¹ * w θ c.hn8 * x = w θ c.hn8 := by
  have hS := c.ot.std
  haveI := hS.simple
  obtain ⟨-, x, hxN, -, hxz, -⟩ := AltStdSmall.exists_normalizer_conj_mul hS.nonab
    (IsPGroup.of_card (hH.card_sSyl_eq hR)) z_mem_sSyl (by rw [sq]; exact z_mul_self c)
    (z_ne_one c) sSyl_le_cent (hH.sSyl_maximal hR hk) rStar_le_sSyl hH.relIndex_rStar
    hH.z_not_mem_rStar (fun r hr hc => hH.eq_of_mem_rStar_central hR hr hc)
    (hH.w_mem_commutator hR)
  refine ⟨x, hxN, hxz, ?_⟩
  obtain ⟨-, hzw⟩ := AltStdSmall.conj_mem_center_of_mem_normalizer z_mem_sSyl sSyl_le_cent hxN
  rw [hxz] at hzw
  have hwc : ∀ s ∈ sSyl c H Rbar, w θ c.hn8 * s = s * w θ c.hn8 := by
    intro s hs
    have h1 := hzw s hs
    have h2 : s * z = z * s := mem_centralizer_singleton_iff.1 (sSyl_le_cent hs)
    apply mul_left_cancel (a := z)
    calc z * (w θ c.hn8 * s) = z * w θ c.hn8 * s := by group
      _ = s * (z * w θ c.hn8) := h1
      _ = z * (s * w θ c.hn8) := by rw [← mul_assoc, h2, mul_assoc]
  have hwS : w θ c.hn8 ∈ sSyl c H Rbar := rStar_le_sSyl (hH.w_mem_rStar hR.tr_mem)
  have hSw : sSyl c H Rbar ≤ centralizer ({w θ c.hn8} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hwc s hs).symm
  obtain ⟨hvS, hvc⟩ := AltStdSmall.conj_mem_center_of_mem_normalizer hwS hSw hxN
  obtain ⟨v, hv⟩ : ∃ v, v = x⁻¹ * w θ c.hn8 * x := ⟨_, rfl⟩
  rw [← hv] at hvS hvc ⊢
  rcases mem_sSyl_iff.1 hvS with hvR | hvR
  · rcases hH.eq_of_mem_rStar_central hR hvR hvc with h1 | h1
    · exfalso
      apply w_ne_one c
      calc w θ c.hn8 = x * v * x⁻¹ := by rw [hv]; group
        _ = 1 := by rw [h1]; group
    · exact h1
  · exfalso
    have hvzc : ∀ s ∈ sSyl c H Rbar, v * z * s = s * (v * z) := by
      intro s hs
      have h2 : s * z = z * s := mem_centralizer_singleton_iff.1 (sSyl_le_cent hs)
      rw [mul_assoc, ← h2, ← mul_assoc, hvc s hs, mul_assoc]
    rcases hH.eq_of_mem_rStar_central hR hvR hvzc with h1 | h1
    ·
      have hvz : v = z := by
        calc v = v * z * z := by rw [mul_assoc, z_mul_self c, mul_one]
          _ = z := by rw [h1, one_mul]
      apply N0.conj_z_not_mem_L c x
      have : x * z * x⁻¹ = w θ c.hn8 := by
        calc x * z * x⁻¹ = x * v * x⁻¹ := by rw [hvz]
          _ = w θ c.hn8 := by rw [hv]; group
      rw [this]
      exact w_mem_L c
    ·
      have hvz : v = x⁻¹ * z * x := by
        rw [hxz]
        calc v = v * z * z := by rw [mul_assoc, z_mul_self c, mul_one]
          _ = w θ c.hn8 * z := by rw [h1]
          _ = z * w θ c.hn8 := w_comm_z c
      have hwz : w θ c.hn8 = z := by
        calc w θ c.hn8 = x * v * x⁻¹ := by rw [hv]; group
          _ = x * (x⁻¹ * z * x) * x⁻¹ := by rw [hvz]
          _ = z := by group
      exact N0.z_not_mem_L c (hwz ▸ w_mem_L c)

end Step1

@[expose] def vOne (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z x : G) : Subgroup G :=
  (E θ hn ⊔ zpowers z).comap (MulAut.conj x).toMonoidHom

theorem mem_vOne_iff {hn : 8 ≤ n} {x g : G} :
    g ∈ vOne θ hn z x ↔ x * g * x⁻¹ ∈ E θ hn ⊔ zpowers z := Iff.rfl

@[expose] def xSub (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z x : G) (H : Subgroup G) :
    Subgroup G :=
  vOne θ hn z x ⊓ H

@[expose] noncomputable def xBar (c : Config G L Q n θ z) (H : Subgroup G) (x : G) :
    Subgroup (Perm (Fin n)) :=
  ((xSub θ c.hn8 z x H).comap (centralizer ({z} : Set G)).subtype).map (rhoC c)

theorem mem_xBar_iff {c : Config G L Q n θ z} {H : Subgroup G} {x : G} {σ : Perm (Fin n)} :
    σ ∈ xBar c H x ↔
      ∃ g : centralizer ({z} : Set G), (g : G) ∈ xSub θ c.hn8 z x H ∧ rhoC c g = σ :=
  Iff.rfl

theorem w_mem_E (hn : 8 ≤ n) : w θ hn ∈ E θ hn := mem_E_of_mem_eBar θ hn (wBar_mem_eBar hn)

section V0

variable (c : Config G L Q n θ z)
include c

theorem mul_self_of_mem_V0 {g : G} (hg : g ∈ E θ c.hn8 ⊔ zpowers z) : g * g = 1 := by
  obtain ⟨i, rfl | rfl⟩ := (N0.mem_B0_iff c.hn8 c g).1 hg
  · exact N0.eps_mul_self θ c.hn8 i
  · calc z * N0.eps θ c.hn8 i * (z * N0.eps θ c.hn8 i)
        = z * (N0.eps θ c.hn8 i * z) * N0.eps θ c.hn8 i := by group
      _ = 1 := by
        rw [N0.eps_comm_z c.hn8 c, ← mul_assoc, z_mul_self c, one_mul, N0.eps_mul_self]

theorem card_V0 : Nat.card (E θ c.hn8 ⊔ zpowers z : Subgroup G) = 16 := by
  rw [card_sup_zpowers_of_mul_self (z_mul_self c) ?_ ?_, card_E]
  · intro p hp
    obtain ⟨i, rfl⟩ := (N0.mem_E_iff θ c.hn8 p).1 hp
    rw [← N0.eps_comm_z c.hn8 c, mul_inv_cancel_right]
    exact N0.eps_mem_E θ c.hn8 i
  · intro hz
    obtain ⟨i, hi⟩ := (N0.mem_E_iff θ c.hn8 z).1 hz
    exact N0.z_ne_eps c.hn8 c i hi

theorem card_vOne (x : G) : Nat.card (vOne θ c.hn8 z x) = 16 := by
  rw [← card_V0 c]
  exact Nat.card_congr
    { toFun := fun g => ⟨x * g * x⁻¹, mem_vOne_iff.1 g.2⟩
      invFun := fun v => ⟨x⁻¹ * v * x, by
        rw [mem_vOne_iff]
        simpa [mul_assoc] using v.2⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc]) }

theorem mul_self_of_mem_vOne {x g : G} (hg : g ∈ vOne θ c.hn8 z x) : g * g = 1 := by
  have h1 := mul_self_of_mem_V0 c (mem_vOne_iff.1 hg)
  have h2 : x * (g * g) * x⁻¹ = 1 := by rw [← h1]; group
  calc g * g = x⁻¹ * (x * (g * g) * x⁻¹) * x := by group
    _ = 1 := by rw [h2]; group

end V0

section VOne

variable {c : Config G L Q n θ z} {H : Subgroup G} {Nbar Rbar : Subgroup (Perm (Fin n))} {x : G}

theorem conj_w_eq {hn : 8 ≤ n} (hxw : x⁻¹ * w θ hn * x = w θ hn) : x * w θ hn * x⁻¹ = w θ hn := by
  calc x * w θ hn * x⁻¹ = x * (x⁻¹ * w θ hn * x) * x⁻¹ := by rw [hxw]
    _ = w θ hn := by group

theorem conj_z_eq_mul (c : Config G L Q n θ z) (hxz : x⁻¹ * z * x = z * w θ c.hn8)
    (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) : x * z * x⁻¹ = z * w θ c.hn8 := by
  have h1 : z = x * z * x⁻¹ * w θ c.hn8 := by
    calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
      _ = x * (z * w θ c.hn8) * x⁻¹ := by rw [hxz]
      _ = x * z * x⁻¹ * (x * w θ c.hn8 * x⁻¹) := by group
      _ = x * z * x⁻¹ * w θ c.hn8 := by rw [conj_w_eq hxw]
  calc x * z * x⁻¹ = x * z * x⁻¹ * w θ c.hn8 * w θ c.hn8 := by
        rw [mul_assoc _ (w θ c.hn8) (w θ c.hn8), w_mul_self c, mul_one]
    _ = z * w θ c.hn8 := by rw [← h1]

theorem z_mem_vOne (c : Config G L Q n θ z) (hxz : x⁻¹ * z * x = z * w θ c.hn8)
    (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) : z ∈ vOne θ c.hn8 z x := by
  rw [mem_vOne_iff, conj_z_eq_mul c hxz hxw]
  exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left (w_mem_E c.hn8))

theorem w_mem_vOne {hn : 8 ≤ n} (hxw : x⁻¹ * w θ hn * x = w θ hn) : w θ hn ∈ vOne θ hn z x := by
  rw [mem_vOne_iff, conj_w_eq hxw]
  exact mem_sup_left (w_mem_E hn)

theorem IsHStar.V0_le_sSyl (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar) :
    E θ c.hn8 ⊔ zpowers z ≤ sSyl c H Rbar :=
  sup_le ((hH.E_le_rStar htr).trans rStar_le_sSyl) (zpowers_le.2 z_mem_sSyl)

theorem IsHStar.vOne_le_sSyl (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar)
    (hxN : x ∈ normalizer (sSyl c H Rbar : Set G)) : vOne θ c.hn8 z x ≤ sSyl c H Rbar := by
  intro g hg
  have h1 : x * g * x⁻¹ ∈ sSyl c H Rbar := hH.V0_le_sSyl htr (mem_vOne_iff.1 hg)
  have h2 := (mem_normalizer_iff.1 (inv_mem hxN) _).1 h1
  simpa [mul_assoc] using h2

theorem xSub_le_vOne {hn : 8 ≤ n} : xSub θ hn z x H ≤ vOne θ hn z x := inf_le_left

theorem xSub_le_H {hn : 8 ≤ n} : xSub θ hn z x H ≤ H := inf_le_right

theorem IsHStar.xSub_le_rStar (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar)
    (hxN : x ∈ normalizer (sSyl c H Rbar : Set G)) : xSub θ c.hn8 z x H ≤ rStar c H Rbar := by
  intro g hg
  rcases mem_sSyl_iff.1 (hH.vOne_le_sSyl htr hxN (xSub_le_vOne hg)) with h | h
  · exact h
  · exfalso
    apply hH.z_not_mem
    have : z = g⁻¹ * (g * z) := by group
    rw [this]
    exact mul_mem (inv_mem (xSub_le_H hg)) (rStar_le_H h)

theorem IsHStar.w_mem_xSub (hH : IsHStar c H Nbar) (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) :
    w θ c.hn8 ∈ xSub θ c.hn8 z x H :=
  ⟨w_mem_vOne hxw, hH.w_mem⟩

theorem IsHStar.mem_vOne_iff_xSub (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar)
    (hxN : x ∈ normalizer (sSyl c H Rbar : Set G)) (hxz : x⁻¹ * z * x = z * w θ c.hn8)
    (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) {g : G} :
    g ∈ vOne θ c.hn8 z x ↔ g ∈ xSub θ c.hn8 z x H ∨ g * z ∈ xSub θ c.hn8 z x H := by
  constructor
  · intro hg
    rcases mem_sSyl_iff.1 (hH.vOne_le_sSyl htr hxN hg) with h | h
    · exact Or.inl ⟨hg, rStar_le_H h⟩
    · exact Or.inr ⟨mul_mem hg (z_mem_vOne c hxz hxw), rStar_le_H h⟩
  · rintro (h | h)
    · exact xSub_le_vOne h
    · have : g = g * z * z := by rw [mul_assoc, z_mul_self c, mul_one]
      rw [this]
      exact mul_mem (xSub_le_vOne h) (z_mem_vOne c hxz hxw)

theorem IsHStar.card_xSub (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar)
    (hxN : x ∈ normalizer (sSyl c H Rbar : Set G)) (hxz : x⁻¹ * z * x = z * w θ c.hn8)
    (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) : Nat.card (xSub θ c.hn8 z x H) = 8 := by
  have hn : ∀ p ∈ xSub θ c.hn8 z x H, z * p * z⁻¹ ∈ xSub θ c.hn8 z x H := by
    intro p hp
    have hpz : p * z = z * p := mem_centralizer_singleton_iff.1 (hH.le (xSub_le_H hp))
    rw [← hpz, mul_inv_cancel_right]
    exact hp
  have hzX : z ∉ xSub θ c.hn8 z x H := fun h => hH.z_not_mem (xSub_le_H h)
  have heq : xSub θ c.hn8 z x H ⊔ zpowers z = vOne θ c.hn8 z x := by
    ext g
    rw [mem_sup_zpowers_iff_of_mul_self (z_mul_self c) hn, hH.mem_vOne_iff_xSub htr hxN hxz hxw]
  have h1 := card_sup_zpowers_of_mul_self (z_mul_self c) hn hzX
  rw [heq, card_vOne c] at h1
  omega

theorem IsHStar.card_xBar (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar)
    (hxN : x ∈ normalizer (sSyl c H Rbar : Set G)) (hxz : x⁻¹ * z * x = z * w θ c.hn8)
    (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) : Nat.card (xBar c H x) = 8 := by
  rw [← hH.card_xSub htr hxN hxz hxw]
  have hC : ∀ g : xSub θ c.hn8 z x H, (g : G) ∈ centralizer ({z} : Set G) := fun g =>
    hH.le (xSub_le_H g.2)
  let F : xSub θ c.hn8 z x H → xBar c H x := fun g =>
    ⟨rhoC c ⟨g, hC g⟩, mem_xBar_iff.2 ⟨⟨g, hC g⟩, g.2, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      have h1 : rhoC c ⟨a, hC a⟩ = rhoC c ⟨b, hC b⟩ := congrArg Subtype.val hab
      have h2 := hH.eq_of_rhoC_eq (xSub_le_H a.2) (xSub_le_H b.2) h1
      have h3 : (a : G) = b := congrArg (fun t : centralizer ({z} : Set G) => (t : G)) h2
      exact Subtype.ext h3
    · rintro ⟨σ, hσ⟩
      obtain ⟨g, hg, rfl⟩ := mem_xBar_iff.1 hσ
      exact ⟨⟨g, hg⟩, rfl⟩
  exact (Nat.card_eq_of_bijective F hF).symm

theorem IsHStar.xBar_le (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar)
    (hxN : x ∈ normalizer (sSyl c H Rbar : Set G)) : xBar c H x ≤ Rbar := by
  intro σ hσ
  obtain ⟨g, hg, rfl⟩ := mem_xBar_iff.1 hσ
  exact rhoC_mem_of_mem_rStar (hH.xSub_le_rStar htr hxN hg)

theorem IsHStar.tr_one_mem_xBar (hH : IsHStar c H Nbar) (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) :
    tr c.hn8 1 ∈ xBar c H x :=
  mem_xBar_iff.2 ⟨⟨w θ c.hn8, L_le_cent c (w_mem_L c)⟩, hH.w_mem_xSub hxw, rhoC_w c _⟩

theorem mul_self_of_mem_xBar {σ : Perm (Fin n)} (hσ : σ ∈ xBar c H x) : σ * σ = 1 := by
  obtain ⟨g, hg, rfl⟩ := mem_xBar_iff.1 hσ
  rw [← map_mul]
  have : g * g = 1 := Subtype.ext (mul_self_of_mem_vOne c (xSub_le_vOne hg))
  rw [this, map_one]

end VOne

end CFSG.OddStandard.AltStdSmall4.Fus.Main
