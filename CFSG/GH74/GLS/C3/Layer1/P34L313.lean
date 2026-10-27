module

public import CFSG.GH74.GLS.C3.Layer1.P34T0Card

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin
open scoped Pointwise

variable {X : Type} [Group X]

@[expose] def Shearing (P : Subgroup X) (z u : X) : Prop :=
  u ≠ z ∧ ∃ g : X, g⁻¹ * u * g ∈ zpowers u ⊔ P ∧ g⁻¹ * u * g ≠ u

theorem Shearing.conj {P : Subgroup X} {z u n : X} (hz : n⁻¹ * z * n = z)
    (hn : n ∈ normalizer (P : Set X)) (h : Shearing P z u) : Shearing P z (n⁻¹ * u * n) := by
  obtain ⟨hne, g, hg, hgne⟩ := h
  refine ⟨?_, n⁻¹ * g * n, ?_, ?_⟩
  · intro h'
    apply hne
    calc u = n * (n⁻¹ * u * n) * n⁻¹ := by group
      _ = n * z * n⁻¹ := by rw [h']
      _ = n * (n⁻¹ * z * n) * n⁻¹ := by rw [hz]
      _ = z := by group
  · set φ : X →* X := (MulAut.conj n⁻¹).toMonoidHom with hφ
    have hmapP : P.map φ = P := CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.2 hn
    have hmap : (zpowers u ⊔ P).map φ = zpowers (n⁻¹ * u * n) ⊔ P := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hmapP]
      simp [hφ]
    have hmem : φ (g⁻¹ * u * g) ∈ (zpowers u ⊔ P).map φ := ⟨_, hg, rfl⟩
    rw [hmap] at hmem
    have e : (n⁻¹ * g * n)⁻¹ * (n⁻¹ * u * n) * (n⁻¹ * g * n) = φ (g⁻¹ * u * g) := by
      simp [hφ]; group
    rw [e]; exact hmem
  · intro h'
    apply hgne
    have h2 : n⁻¹ * (g⁻¹ * u * g) * n = n⁻¹ * u * n := by
      calc n⁻¹ * (g⁻¹ * u * g) * n = (n⁻¹ * g * n)⁻¹ * (n⁻¹ * u * n) * (n⁻¹ * g * n) := by group
        _ = n⁻¹ * u * n := h'
    have h3 : g⁻¹ * u * g = u := by
      have := mul_right_cancel h2
      exact mul_left_cancel this
    exact h3

variable [Finite X] {T P Q : Subgroup X} {x z f h : X}

theorem lemma313 (c : Cfg34 X T P Q x z f h) (hQ : QShapeFacts) (h37 : Lemma37 T z)
    (h312 : Lemma312 T P Q z f) : Lemma313 x z := by
  by_contra hno
  have hno' : ∀ g : X, g⁻¹ * x * g ≠ x * z := fun g hg => hno ⟨g, hg⟩
  obtain ⟨-, -, -, hQ4⟩ :=
    hQ X T Q x c.T_pgroup c.Q_le c.Q_norm c.x_mem_Q c.x_order c.x_central c.Q_shape
  have hxZ0 : x ∈ Z0 T := mem_Z0 c.x_mem c.x_sq c.x_central
  have hRz : z ∈ P ⊔ Q := mem_sup_left c.z_mem
  have hRx : x ∈ P ⊔ Q := mem_sup_right c.x_mem_Q
  have hzn : ∀ n ∈ normalizer (P : Set X), n⁻¹ * z * n = z := by
    intro n hn
    have hiff := Subgroup.mem_normalizer_iff.1 hn
    have hn' := (normalizer (P : Set X)).inv_mem hn
    have h1 : n * z = z * n := c.z_cent_of_norm n (fun a ha => (hiff a).1 ha) (fun a ha => by
      have := ((Subgroup.mem_normalizer_iff.1 hn') a).1 ha
      simpa using this)
    calc n⁻¹ * z * n = n⁻¹ * (z * n) := by group
      _ = n⁻¹ * (n * z) := by rw [h1]
      _ = z := by group
  have hxns : ¬ Shearing P z x := by
    rintro ⟨-, g, hg, hgne⟩
    have hg' : g⁻¹ * x * g ∈ ((P ⊔ zpowers x : Subgroup X) : Set X) := by
      rw [sup_comm] at hg; exact hg
    rw [c.coe_Px] at hg'
    obtain ⟨a, ha, xx, hxx, hax⟩ := hg'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxx
    have hax' : a * x ^ k = g⁻¹ * x * g := hax
    have hy2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
      calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [c.x_sq]; group
    have hy1 : g⁻¹ * x * g ≠ 1 := by
      intro h1
      apply c.x_ne_one
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hax_comm : a * x = x * a := c.PQ_comm a ha x c.x_mem_Q
    rcases zpow_involution_cases c.x_sq k with hk | hk
    ·
      rw [hk, mul_one] at hax'
      have ha2 : a * a = 1 := by rw [hax']; exact hy2
      have ha1 : a ≠ 1 := by rw [hax']; exact hy1
      have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
      obtain ⟨g', hg'⟩ := c.kf_conj_P a ha ha_ord
      have hx : x = (g' * g⁻¹)⁻¹ * z * (g' * g⁻¹) := by
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = g * a * g⁻¹ := by rw [hax']
          _ = g * (g'⁻¹ * z * g') * g⁻¹ := by rw [hg']
          _ = (g' * g⁻¹)⁻¹ * z * (g' * g⁻¹) := by group
      have := h37 (g' * g⁻¹) (by rw [← hx]; exact hxZ0)
      exact c.x_ne_z (hx.trans this)
    · rw [hk] at hax'
      have ha2 : a * a = 1 := by
        have h1 : (a * x) * (a * x) = (a * a) * (x * x) := by
          calc (a * x) * (a * x) = a * (x * a) * x := by group
            _ = a * (a * x) * x := by rw [← hax_comm]
            _ = (a * a) * (x * x) := by group
        rw [hax', hy2, c.x_sq, mul_one] at h1
        exact h1.symm
      have ha1 : a ≠ 1 := by
        intro h1
        apply hgne
        rw [← hax', h1, one_mul]
      have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
      obtain ⟨g', hg'⟩ := c.kf_conj_xP a ha ha_ord
      have e1 : x * a = g⁻¹ * x * g := by rw [← hax', hax_comm]
      have hxe : x = (g' * g⁻¹)⁻¹ * (x * z) * (g' * g⁻¹) := by
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = g * (x * a) * g⁻¹ := by rw [← e1]
          _ = g * (g'⁻¹ * (x * z) * g') * g⁻¹ := by rw [hg']
          _ = (g' * g⁻¹)⁻¹ * (x * z) * (g' * g⁻¹) := by group
      have h2 := congrArg (fun y => (g' * g⁻¹) * y * (g' * g⁻¹)⁻¹) hxe
      have h3 : (g' * g⁻¹) * ((g' * g⁻¹)⁻¹ * (x * z) * (g' * g⁻¹)) * (g' * g⁻¹)⁻¹ = x * z := by
        group
      rw [h3] at h2
      exact hno' (g' * g⁻¹)⁻¹ (by simpa using h2)
  have hxns' : ∀ n ∈ normalizer (P : Set X), ¬ Shearing P z (n⁻¹ * x * n) := by
    intro n hn hs
    have hn' : n⁻¹ ∈ normalizer (P : Set X) := (normalizer (P : Set X)).inv_mem hn
    have h1 := Shearing.conj (hzn n⁻¹ hn') hn' hs
    have e : (n⁻¹)⁻¹ * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rw [e] at h1
    exact hxns h1
  have hshear : ∀ w ∈ T, w * w = 1 → (∀ a ∈ P, w * a = a * w) → w ∉ Q ⊔ zpowers z →
      Shearing P z w := by
    intro w hwT hw2 hwP hwQ
    refine ⟨fun hwz => hwQ (by rw [hwz]; exact mem_sup_right (mem_zpowers z)), ?_⟩
    exact c.kf_shear w hwT hw2 hwP hwQ
  obtain ⟨f₀, g, hf₀, hgN, hu, hext, hCT⟩ := h312
  have hgz : g⁻¹ * z * g = z := hzn g hgN
  have hf₀T : f₀ ∈ T := by
    rcases hf₀ with rfl | rfl
    · exact c.f_mem
    · exact T.mul_mem c.f_mem c.z_mem_T
  have hfz : f * z = z * f := c.f_cent z c.z_mem
  have hf₀2 : f₀ * f₀ = 1 := by
    rcases hf₀ with rfl | rfl
    · exact c.f_sq
    · calc f * z * (f * z) = f * (z * f) * z := by group
        _ = f * (f * z) * z := by rw [← hfz]
        _ = (f * f) * (z * z) := by group
        _ = 1 := by rw [c.f_sq, c.z_sq, mul_one]
  have hf₀P : ∀ a ∈ P, f₀ * a = a * f₀ := by
    intro a ha
    rcases hf₀ with rfl | rfl
    · exact c.f_cent a ha
    · calc f * z * a = f * (z * a) := by group
        _ = f * (a * z) := by rw [← c.z_central a ha]
        _ = (f * a) * z := by group
        _ = (a * f) * z := by rw [c.f_cent a ha]
        _ = a * (f * z) := by group
  have hf₀R : f₀ ∉ P ⊔ Q := by
    rcases hf₀ with rfl | rfl
    · exact c.f_not_mem
    · intro hmem
      apply c.f_not_mem
      have := (P ⊔ Q).mul_mem hmem ((P ⊔ Q).inv_mem hRz)
      have e : f * z * z⁻¹ = f := by group
      rwa [e] at this
  have hQzR : Q ⊔ zpowers z ≤ P ⊔ Q := sup_le le_sup_right (zpowers_le.2 hRz)
  have hf₀Qz : f₀ ∉ Q ⊔ zpowers z := fun hmem => hf₀R (hQzR hmem)
  have hf₀x : f₀ * x = x * f₀ := c.x_central f₀ hf₀T
  have hf₀1 : f₀ ≠ 1 := fun h1 => hf₀R (h1 ▸ (P ⊔ Q).one_mem)
  have hx'T : g⁻¹ * x * g ∈ T := hCT x c.x_mem hf₀x.symm
  have hx'2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [c.x_sq]; group
  have hx'P : ∀ a ∈ P, (g⁻¹ * x * g) * a = a * (g⁻¹ * x * g) := by
    intro a ha
    have hb : g * a * g⁻¹ ∈ P := ((Subgroup.mem_normalizer_iff.1 hgN) a).1 ha
    have := c.PQ_comm _ hb x c.x_mem_Q
    calc (g⁻¹ * x * g) * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [← this]
      _ = a * (g⁻¹ * x * g) := by group
  have hx'Qz : g⁻¹ * x * g ∈ Q ⊔ zpowers z := by
    by_contra hnot
    exact hxns' g hgN (hshear _ hx'T hx'2 hx'P hnot)
  have hx'comm : (g⁻¹ * x * g) * (g⁻¹ * f₀ * g) = (g⁻¹ * f₀ * g) * (g⁻¹ * x * g) := by
    calc (g⁻¹ * x * g) * (g⁻¹ * f₀ * g) = g⁻¹ * (x * f₀) * g := by group
      _ = g⁻¹ * (f₀ * x) * g := by rw [hf₀x.symm]
      _ = (g⁻¹ * f₀ * g) * (g⁻¹ * x * g) := by group
  have hf₀'2 : (g⁻¹ * f₀ * g) * (g⁻¹ * f₀ * g) = 1 := by
    calc (g⁻¹ * f₀ * g) * (g⁻¹ * f₀ * g) = g⁻¹ * (f₀ * f₀) * g := by group
      _ = 1 := by rw [hf₀2]; group
  have hf₀'1 : g⁻¹ * f₀ * g ≠ 1 := by
    intro h1
    apply hf₀1
    calc f₀ = g * (g⁻¹ * f₀ * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hx'1 : g⁻¹ * x * g ≠ 1 := by
    intro h1
    apply c.x_ne_one
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hn : g⁻¹ ∈ normalizer (P : Set X) := (normalizer (P : Set X)).inv_mem hgN
  have hcase : ∀ u : X, u ∈ Q ⊔ zpowers z → u * u = 1 → (∀ t ∈ T, t * u = u * t) → u ∈ T →
      (∀ a ∈ P, u * a = a * u) → u * f₀ ≠ (g⁻¹)⁻¹ * x * g⁻¹ := by
    intro u huQz hu2 huc huT huP heq
    have hfu : f₀ * u = u * f₀ := huc f₀ hf₀T
    have hsh : Shearing P z (u * f₀) := by
      refine hshear (u * f₀) (T.mul_mem huT hf₀T) ?_ ?_ ?_
      · calc u * f₀ * (u * f₀) = u * (f₀ * u) * f₀ := by group
          _ = u * (u * f₀) * f₀ := by rw [hfu]
          _ = (u * u) * (f₀ * f₀) := by group
          _ = 1 := by rw [hu2, hf₀2, mul_one]
      · intro a ha
        calc u * f₀ * a = u * (f₀ * a) := by group
          _ = u * (a * f₀) := by rw [hf₀P a ha]
          _ = (u * a) * f₀ := by group
          _ = (a * u) * f₀ := by rw [huP a ha]
          _ = a * (u * f₀) := by group
      · intro hmem
        apply hf₀Qz
        have := (Q ⊔ zpowers z).mul_mem huQz hmem
        have e : u * (u * f₀) = f₀ := by rw [← mul_assoc, hu2, one_mul]
        rwa [e] at this
    exact hxns' g⁻¹ hn (by rw [← heq]; exact hsh)
  have hxQz : x ∈ Q ⊔ zpowers z := mem_sup_left c.x_mem_Q
  have hzQz : z ∈ Q ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hxz : x * z = z * x := c.z_cent_T x c.x_mem
  have key : ∀ q ∈ Q, q * q = 1 → q ≠ 1 → (q = g⁻¹ * x * g ∨ q = g⁻¹ * x * g * z) →
      g⁻¹ * x * g = x := by
    intro q hq hqq hq1 hqx'
    have hqne : q ≠ g⁻¹ * f₀ * g := by
      intro hqe
      apply hf₀R
      rcases hqx' with h1 | h1
      · have e : g⁻¹ * f₀ * g = g⁻¹ * x * g := hqe.symm.trans h1
        have : f₀ = x := mul_left_cancel (mul_right_cancel e)
        rw [this]; exact hRx
      · have e : g⁻¹ * f₀ * g = g⁻¹ * (x * z) * g := by
          calc g⁻¹ * f₀ * g = g⁻¹ * x * g * z := hqe.symm.trans h1
            _ = g⁻¹ * x * g * (g⁻¹ * z * g) := by rw [hgz]
            _ = g⁻¹ * (x * z) * g := by group
        have : f₀ = x * z := mul_left_cancel (mul_right_cancel e)
        rw [this]; exact (P ⊔ Q).mul_mem hRx hRz
    have hqcomm : q * (g⁻¹ * f₀ * g) = (g⁻¹ * f₀ * g) * q := by
      have hzf : z * (g⁻¹ * f₀ * g) = (g⁻¹ * f₀ * g) * z := c.PQ_comm z c.z_mem _ hu
      rcases hqx' with h1 | h1
      · rw [h1]; exact hx'comm
      · rw [h1]
        calc g⁻¹ * x * g * z * (g⁻¹ * f₀ * g) = g⁻¹ * x * g * (z * (g⁻¹ * f₀ * g)) := by group
          _ = g⁻¹ * x * g * ((g⁻¹ * f₀ * g) * z) := by rw [hzf]
          _ = (g⁻¹ * x * g * (g⁻¹ * f₀ * g)) * z := by group
          _ = ((g⁻¹ * f₀ * g) * (g⁻¹ * x * g)) * z := by rw [hx'comm]
          _ = (g⁻¹ * f₀ * g) * (g⁻¹ * x * g * z) := by group
    rcases hQ4 q hq (g⁻¹ * f₀ * g) hu hqq hf₀'2 hq1 hf₀'1 hqne hqcomm with h1 | h1 | h1
    · rcases hqx' with h2 | h2
      · exact h2.symm.trans h1.symm
      · exfalso
        apply hno' g
        calc g⁻¹ * x * g = g⁻¹ * x * g * z * z := by rw [mul_assoc _ z z, c.z_sq, mul_one]
          _ = q * z := by rw [h2]
          _ = x * z := by rw [← h1]
    · exfalso
      have hf₀e : f₀ = (g⁻¹)⁻¹ * x * g⁻¹ := by
        calc f₀ = g * (g⁻¹ * f₀ * g) * g⁻¹ := by group
          _ = g * x * g⁻¹ := by rw [← h1]
          _ = (g⁻¹)⁻¹ * x * g⁻¹ := by simp
      exact hxns' g⁻¹ hn (by rw [← hf₀e]; exact hshear f₀ hf₀T hf₀2 hf₀P hf₀Qz)
    · exfalso
      rcases hqx' with h2 | h2
      · refine hcase x hxQz c.x_sq c.x_central c.x_mem (fun a ha => (c.PQ_comm a ha x c.x_mem_Q).symm) ?_
        calc x * f₀ = g * (g⁻¹ * (x * f₀) * g) * g⁻¹ := by group
          _ = g * (g⁻¹ * x * g * (g⁻¹ * f₀ * g)) * g⁻¹ := by group
          _ = g * (q * (g⁻¹ * f₀ * g)) * g⁻¹ := by rw [h2]
          _ = g * x * g⁻¹ := by rw [← h1]
          _ = (g⁻¹)⁻¹ * x * g⁻¹ := by simp
      · have hxzQz : x * z ∈ Q ⊔ zpowers z := (Q ⊔ zpowers z).mul_mem hxQz hzQz
        refine hcase (x * z) hxzQz ?_ ?_ (T.mul_mem c.x_mem c.z_mem_T) ?_ ?_
        · calc x * z * (x * z) = x * (z * x) * z := by group
            _ = x * (x * z) * z := by rw [← hxz]
            _ = (x * x) * (z * z) := by group
            _ = 1 := by rw [c.x_sq, c.z_sq, mul_one]
        · intro t ht
          calc t * (x * z) = (t * x) * z := by group
            _ = (x * t) * z := by rw [c.x_central t ht]
            _ = x * (t * z) := by group
            _ = x * (z * t) := by rw [c.z_cent_T t ht]
            _ = x * z * t := by group
        · intro a ha
          calc x * z * a = x * (z * a) := by group
            _ = x * (a * z) := by rw [← c.z_central a ha]
            _ = (x * a) * z := by group
            _ = (a * x) * z := by rw [← c.PQ_comm a ha x c.x_mem_Q]
            _ = a * (x * z) := by group
        · calc x * z * f₀ = g * (g⁻¹ * (x * z * f₀) * g) * g⁻¹ := by group
            _ = g * (g⁻¹ * x * g * (g⁻¹ * z * g) * (g⁻¹ * f₀ * g)) * g⁻¹ := by group
            _ = g * (g⁻¹ * x * g * z * (g⁻¹ * f₀ * g)) * g⁻¹ := by rw [hgz]
            _ = g * (q * (g⁻¹ * f₀ * g)) * g⁻¹ := by rw [h2]
            _ = g * x * g⁻¹ := by rw [← h1]
            _ = (g⁻¹)⁻¹ * x * g⁻¹ := by simp
  have hx'Qz' : g⁻¹ * x * g ∈ ((Q ⊔ zpowers z : Subgroup X) : Set X) := hx'Qz
  rw [c.coe_Qz] at hx'Qz'
  obtain ⟨q₀, hq₀, zz, hzz, hdec⟩ := hx'Qz'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hzz
  have hdec' : q₀ * z ^ k = g⁻¹ * x * g := hdec
  have hxg : g⁻¹ * x * g = x := by
    rcases zpow_involution_cases c.z_sq k with hk | hk
    · rw [hk, mul_one] at hdec'
      exact key q₀ hq₀ (by rw [hdec']; exact hx'2) (by rw [hdec']; exact hx'1) (Or.inl hdec')
    · rw [hk] at hdec'
      have hzq : z * q₀ = q₀ * z := c.PQ_comm z c.z_mem q₀ hq₀
      have hq₀' : q₀ = g⁻¹ * x * g * z := by
        calc q₀ = q₀ * z * z := by rw [mul_assoc, c.z_sq, mul_one]
          _ = g⁻¹ * x * g * z := by rw [hdec']
      have hq₀2 : q₀ * q₀ = 1 := by
        have h1 : (q₀ * z) * (q₀ * z) = (q₀ * q₀) * (z * z) := by
          calc (q₀ * z) * (q₀ * z) = q₀ * (z * q₀) * z := by group
            _ = q₀ * (q₀ * z) * z := by rw [hzq]
            _ = (q₀ * q₀) * (z * z) := by group
        rw [hdec', hx'2, c.z_sq, mul_one] at h1
        exact h1.symm
      have hq₀1 : q₀ ≠ 1 := by
        intro h1
        apply c.x_ne_z
        rw [h1, one_mul] at hdec'
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = g * z * g⁻¹ := by rw [← hdec']
          _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
          _ = z := by group
      exact key q₀ hq₀ hq₀2 hq₀1 (Or.inr hq₀')
  have hgC : g ∈ centralizer ({x} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc g * x = g * (g⁻¹ * x * g) := by rw [hxg]
      _ = x * g := by group
  obtain ⟨N, hNnorm, hNT⟩ := c.kf_N
  have hQN : ∀ q ∈ Q, q ∈ N := fun q hq => by
    rw [← hNT] at hq
    exact hq.1
  have hf₀N : f₀ ∈ N := by
    have := hNnorm g hgC (g⁻¹ * f₀ * g) (hQN _ hu)
    have e : g * (g⁻¹ * f₀ * g) * g⁻¹ = f₀ := by group
    rwa [e] at this
  have hf₀Q : f₀ ∈ Q := by
    rw [← hNT]
    exact ⟨hf₀N, hf₀T⟩
  exact hf₀R (mem_sup_right hf₀Q)

end CFSG.GH74.GLS.C3.Layer1.P34
