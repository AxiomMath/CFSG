module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6P1
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Case1
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V2

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

section Tail


@[expose] def Tail24 {G : Type} [Group G] [Finite G] (d : Data G) (z₀ : G) : Prop :=
  IsElemAbelian 2 d.s56V → ∀ s y : G, s ∈ Hg d → s * s = 1 → (∀ z ∈ Zz d z₀, s * z = z * s) →
    y ∈ Hg d → y * s = s * y → IsPGroup 3 (zpowers y) → (∃ z ∈ Zz d z₀, y * z ≠ z * y) →
    Nat.card (Zz d z₀) = 4 → Nat.card ↥(d.s56V ⊓ centralizer ({s} : Set G)) = 2 ^ 5 → False

end Tail

section Step24


theorem step24_of_tail
    (tail : ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}, d.Thm49Statement → d.Hyp →
      d.S56Z0 z₀ → Node07 d → Node10 d z₀ → Node11 d z₀ → Node12 d z₀ → Node13 d → Node14 d →
      Node16 d z₀ → Node19 d z₀ → Node20 d z₀ → Node21 d z₀ → Node22 d z₀ → Node23a d z₀ →
      Node23b d z₀ → Node23c d z₀ → Tail24 d z₀) : Step24 := by
  intro G _ _ d z₀ h49 hd hz h07 h10 h11 h12 h13 h14 h16 h19 h20 h21 h22 h23a h23b h23c
  have htail := tail h49 hd hz h07 h10 h11 h12 h13 h14 h16 h19 h20 h21 h22 h23a h23b h23c
  have ht2 : d.t * d.t = 1 := hd.t_mul_self
  have htH : d.t ∈ Hg d := hd.s56_M_le_normalizer_V h49 d.s56_t_mem_M
  have hEV : d.E ≤ d.s56V := hd.s56_E_le_V h49
  have hEc : ∀ e ∈ d.E, e * d.t = d.t * e := fun e he =>
    mem_centralizer_singleton_iff.1 (hd.A_facts.2.1 (d.s56_E_le_A he))
  have hzE : d.z ∈ d.E := hd.s56_z_mem_E
  have hz0V : z₀ ∈ d.s56V := Subgroup.mem_inf.2 ⟨hz.mem_Q, hz.mem_Q2⟩
  have hz0t : ¬ z₀ * d.t = d.t * z₀ := by
    intro hc
    have h1 : d.t * (z₀ * d.t * z₀⁻¹) = d.z := hz.eps
    have h2 : z₀ * d.t * z₀⁻¹ = d.t := by
      rw [hc]; group
    rw [h2, ht2] at h1
    exact hd.s56_z_ne_one h1.symm
  have htV : d.t ∉ d.s56V := fun htV =>
    hz0t ((hd.s56_V_shape h49 hz).2.2.2.2.1 z₀ (mem_sup_right (mem_zpowers z₀)) d.t htV)
  have heps : ∀ e ∈ d.E, ∃ v ∈ d.s56V, v * d.t * v⁻¹ = d.t * e := fun e he => by
    obtain ⟨v, hv, hve⟩ := hd.s56_V_eps_surj h49 hz e he
    exact ⟨v, hv, by rw [hd.s56_conj_t v, hve]⟩
  ext x
  constructor
  · rintro ⟨hxG, hxH⟩
    rcases h14.1 x hxG hxH with ⟨⟨h, hhH, hD⟩, -⟩ | ⟨hP1, hP1card, k, hks, hBk, hVk⟩
    · exact P6.mem_conj_of_conjA ht2 hEc hEV htV heps hhH hD
    · exfalso
      have hV : IsElemAbelian 2 d.s56V := by
        rw [hVk]
        exact P6.isElemAbelian_map_conj hP1 k
      have hz0sq : z₀ * z₀ = 1 := by rw [← sq]; exact hV.2 z₀ hz0V
      have hzsq : d.z * d.z = 1 := by rw [← sq, ← hd.s56_orderOf_z, pow_orderOf_eq_one]
      have hzV : d.z ∈ d.s56V := hEV hzE
      have hZV : Zz d z₀ ≤ d.s56V := sup_le (zpowers_le.2 hzV) (zpowers_le.2 hz0V)
      have hznot : z₀ ∉ zpowers d.z := by
        intro hmem
        obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
        apply hz0t
        rw [← hn]
        exact (Commute.zpow_left (show Commute d.z d.t from hEc d.z hzE) n).eq
      have hZ4 : Nat.card (Zz d z₀) = 4 := by
        have hn : ∀ p ∈ zpowers d.z, z₀ * p * z₀⁻¹ ∈ zpowers d.z := fun p hp => by
          have hpV : p ∈ d.s56V := hZV (mem_sup_left hp)
          have : z₀ * p * z₀⁻¹ = p := by
            rw [mul_inv_eq_iff_eq_mul]
            exact P6.mul_comm_of_isElemAbelian hV hz0V hpV
          rwa [this]
        have h := P6.card_sup_zpowers hz0sq hn hznot
        rw [hd.s56_card_zpowers_z] at h
        exact h
      have hZH : ∀ h ∈ Hg d, ∀ z ∈ Zz d z₀, h * z * h⁻¹ ∈ Zz d z₀ := h23a.2.2.1.2
      have hBcard : Nat.card d.B = 2 ^ 6 := hd.B_facts.2.2.2.1
      obtain ⟨-, -, hs2, hcard, hZs, y, hyH, hys, hy3, hyz⟩ :=
        P6.p1_case_core hVk hP1 hP1card h11.2.2.2.2.1 h11.2.2.2.2.2.1 ht2 hks hBk hBcard hxH hZV hZ4 hZH
      exact htail hV x y hxH hs2 hZs hyH hys hy3 hyz hZ4 hcard
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, rfl⟩, mul_mem (mul_mem hh htH) (inv_mem hh)⟩

end Step24

end CFSG.LocalAnalysis.EvenBN.Tits.N
