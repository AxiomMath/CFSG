module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.SylowUniq
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_zpowers_conj_iff (g z x : G) :
    x ∈ zpowers (g * z * g⁻¹) ↔ g⁻¹ * x * g ∈ zpowers z := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    show z ^ k = g⁻¹ * (g * z * g⁻¹) ^ k * g
    rw [conj_zpow]; group
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : z ^ k = g⁻¹ * x * g := hk
    show (g * z * g⁻¹) ^ k = x
    rw [conj_zpow, hk']; group

theorem comm_of_mem_zpowers' {z q w : G} (hq : q * z = z * q) (hw : w ∈ zpowers z) :
    q * w = w * q := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  exact (Commute.zpow_right (show Commute q z from hq) k).eq

theorem eq_of_conj_mem_of_class_data [Finite G] (d : G → ℕ) (hd : ∀ c x, d (c * x * c⁻¹) = d x)
    (Q Q' : Subgroup G) (g z u : G)
    (hQ : Nat.card Q = 11 ^ 3) (hQ' : Nat.card Q' = 11 ^ 3) (hz : orderOf z = 11) (hzQ : z ∈ Q)
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z)
    (hZQ : ∀ q ∈ Q, (∀ a ∈ Q, q * a = a * q) → q ∈ zpowers z)
    (hzQc : ∀ q ∈ Q, q * z = z * q) (hQ'g : ∀ x, x ∈ Q' ↔ g⁻¹ * x * g ∈ Q)
    (hdz : ∀ x ∈ zpowers z, x ≠ 1 → d x = 2) (hdu : ∀ x ∈ Q, x ∉ zpowers z → d x = 12)
    (huQ : u ∈ Q) (hu : u ∉ zpowers z) (huQ' : u ∈ Q')
    (hC : Nat.card (centralizer ({u} : Set G)) ≤ 242) : Q' = Q := by
  set z' := g * z * g⁻¹ with hz'def
  have hz'ord : orderOf z' = 11 := by
    have := (MulAut.conj g).orderOf_eq z
    simpa [MulAut.conj_apply, hz'def, hz] using this
  have hmemz' : ∀ x, x ∈ zpowers z' ↔ g⁻¹ * x * g ∈ zpowers z := mem_zpowers_conj_iff g z
  have hcQ' : ∀ a ∈ Q', ∀ b ∈ Q', ⁅a, b⁆ ∈ zpowers z' := by
    intro a ha b hb
    rw [hmemz']
    have h := hcQ _ ((hQ'g a).1 ha) _ ((hQ'g b).1 hb)
    have e : g⁻¹ * ⁅a, b⁆ * g = ⁅g⁻¹ * a * g, g⁻¹ * b * g⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e]
  have hZQ' : ∀ q ∈ Q', (∀ a ∈ Q', q * a = a * q) → q ∈ zpowers z' := by
    intro q hq hc
    rw [hmemz']
    refine hZQ _ ((hQ'g q).1 hq) fun a ha => ?_
    have h := hc (g * a * g⁻¹) ((hQ'g _).2 (by
      rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group]; exact ha))
    calc g⁻¹ * q * g * a = g⁻¹ * (q * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * q) * g := by rw [h]
      _ = a * (g⁻¹ * q * g) := by group
  have hzQc' : ∀ q ∈ Q', q * z' = z' * q := by
    intro q hq
    have h := hzQc _ ((hQ'g q).1 hq)
    calc q * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * q := by group
  have hz'Q' : z' ∈ Q' := (hQ'g z').2 (by
    have : g⁻¹ * z' * g = z := by simp only [hz'def]; group
    rw [this]; exact hzQ)
  have hu'z : u ∉ zpowers z' := by
    intro h
    rw [hmemz'] at h
    have hu1 : u ≠ 1 := fun h1 => hu (h1 ▸ one_mem _)
    have h2 : d (g⁻¹ * u * g) = 2 := hdz _ h (by
      intro h1
      apply hu1
      have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      rw [this, h1]; group)
    have h3 : d u = d (g⁻¹ * u * g) := by
      have := hd g (g⁻¹ * u * g)
      rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at this
      exact this
    have := hdu u huQ hu
    omega
  have hEQ : Nat.card ↥(centralizer ({u} : Set G) ⊓ Q) = 121 := by
    rw [card_centralizer_of_noncentral Q z u hz hcQ hzQc hZQ huQ hu, hQ]; norm_num
  have hEQ' : Nat.card ↥(centralizer ({u} : Set G) ⊓ Q') = 121 := by
    rw [card_centralizer_of_noncentral Q' z' u hz'ord hcQ' hzQc' hZQ' huQ' hu'z, hQ']; norm_num
  have hE := centralizer_inf_eq_of_card hEQ hEQ' hC
  have hz'E : z' ∈ centralizer ({u} : Set G) ⊓ Q' := by
    refine ⟨?_, hz'Q'⟩
    change z' ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hzQc' u huQ'
  have hz'Q : z' ∈ Q := by rw [← hE] at hz'E; exact hz'E.2
  have hz'z : z' ∈ zpowers z := by
    by_contra hn
    have h1 := hdu z' hz'Q hn
    have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz; omega
    have h2 : d z' = d z := hd g z
    have h3 := hdz z (mem_zpowers z) hz1
    omega
  have hzz' : zpowers z' = zpowers z := by
    apply eq_of_le_of_card_ge ((zpowers_le).2 hz'z)
    rw [Nat.card_zpowers, Nat.card_zpowers, hz, hz'ord]
  have hcQ'' : ∀ a ∈ Q', ∀ b ∈ Q', ⁅a, b⁆ ∈ zpowers z := fun a ha b hb => hzz' ▸ hcQ' a ha b hb
  have hzQc'' : ∀ q ∈ Q', q * z = z * q := fun q hq =>
    comm_of_mem_zpowers' (hzQc' q hq) (hzz' ▸ mem_zpowers z : z ∈ zpowers z')
  exact (eq_of_mem_of_card_centralizer_le Q Q' z u hQ hQ' hz hcQ hcQ'' hZQ hzQc hzQc'' huQ huQ'
    hu hC).symm

theorem normalizer_zpowers_le_normalizer [Finite G] (Q : Subgroup G) (z : G)
    (hQ : Nat.card Q = 11 ^ 3) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hC : centralizer ({z} : Set G) ≤ normalizer (Q : Set G))
    (hG : ¬ 11 ^ 4 ∣ Nat.card G) :
    normalizer ((zpowers z : Subgroup G) : Set G) ≤ normalizer (Q : Set G) := by
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set H := centralizer ({z} : Set G) with hH
  have hmemH : ∀ x : G, x ∈ H ↔ x * z = z * x := by
    intro x
    rw [hH, Subgroup.mem_centralizer_iff]
    constructor
    · intro h; exact (h z rfl).symm
    · intro h g hg; rw [Set.mem_singleton_iff.1 hg]; exact h.symm
  have hQH : Q ≤ H := fun q hq => (hmemH q).2 (hzc q hq)
  intro n hn
  rw [Subgroup.mem_normalizer_iff] at hn
  set Q'' : Subgroup G := Q.map (MulAut.conj n).toMonoidHom with hQ''
  have hQ''card : Nat.card Q'' = 11 ^ 3 := by
    rw [hQ'', Subgroup.card_map_of_injective (MulAut.conj n).injective, hQ]
  have hmem'' : ∀ x, x ∈ Q'' ↔ n⁻¹ * x * n ∈ Q := by
    intro x
    rw [hQ'', Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show n⁻¹ * (n * y * n⁻¹) * n ∈ Q
      rw [show n⁻¹ * (n * y * n⁻¹) * n = y by group]; exact hy
    · intro h
      exact ⟨_, h, by show n * (n⁻¹ * x * n) * n⁻¹ = x; group⟩
  have hQ''H : Q'' ≤ H := by
    intro x hx
    rw [hmemH]
    have hy := (hmem'' x).1 hx
    have hw : n⁻¹ * z * n ∈ zpowers z := by
      rw [hn (n⁻¹ * z * n)]
      rw [show n * (n⁻¹ * z * n) * n⁻¹ = z by group]
      exact mem_zpowers z
    have h1 := comm_of_mem_zpowers' (hzc _ hy) hw
    have : x * z = z * x := by
      have e : x * z = n * ((n⁻¹ * x * n) * (n⁻¹ * z * n)) * n⁻¹ := by group
      have e' : z * x = n * ((n⁻¹ * z * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
      rw [e, e', h1]
    exact this
  have hHdvd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hQ₀card : Nat.card (Q.subgroupOf H) = 11 ^ 3 := by
    rw [← hQ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hQ''₀card : Nat.card (Q''.subgroupOf H) = 11 ^ 3 := by
    rw [← hQ''card]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ''H).toEquiv
  have hfac : (Nat.card H).factorization 11 = 3 := by
    have h3 : 11 ^ 3 ∣ Nat.card H := hQ₀card ▸ Subgroup.card_subgroup_dvd_card (Q.subgroupOf H)
    have h4 : ¬ 11 ^ 4 ∣ Nat.card H := fun h => hG (h.trans hHdvd)
    have a := (Nat.Prime.pow_dvd_iff_le_factorization h11.out hHne).mp h3
    have b : ¬ 4 ≤ (Nat.card H).factorization 11 := fun h =>
      h4 ((Nat.Prime.pow_dvd_iff_le_factorization h11.out hHne).mpr h)
    omega
  let P₀ : Sylow 11 H := Sylow.ofCard (Q.subgroupOf H) (by rw [hQ₀card, hfac])
  let P₁ : Sylow 11 H := Sylow.ofCard (Q''.subgroupOf H) (by rw [hQ''₀card, hfac])
  have hnormal : (P₀ : Subgroup H).Normal := by
    show (Q.subgroupOf H).Normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQH]
    exact hC
  have : (P₀).Normal := hnormal
  have hP : P₁ = P₀ := by
    have := Sylow.unique_of_normal P₀ hnormal
    exact Subsingleton.elim _ _
  have hQQ : Q'' = Q := by
    have h1 : Q''.subgroupOf H = Q.subgroupOf H := congrArg (fun P : Sylow 11 H => (P : Subgroup H)) hP
    have h2 := congrArg (Subgroup.map H.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hQ''H, Subgroup.map_subgroupOf_eq_of_le hQH] at h2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 := hmem'' (n * h * n⁻¹)
  rw [hQQ] at h1
  rw [h1, show n⁻¹ * (n * h * n⁻¹) * n = h by group]

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
