module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K7
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S15

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section Generic

variable {Γ : Type*} [Group Γ]

theorem conj_mem_inf_centralizer_preIn (S : Subgroup Γ) {K' : Subgroup (MulAut ↥S)}
    (hK' : K' ≤ imgIn S (normalizer (S : Set Γ))) {g : Γ} (hg : g ∈ normalizer (S : Set Γ))
    (hgK : actFun S g ∈ normalizer (K' : Set (MulAut ↥S))) {x : Γ}
    (hx : x ∈ S ⊓ centralizer ((preIn S K' : Subgroup Γ) : Set Γ)) :
    g * x * g⁻¹ ∈ S ⊓ centralizer ((preIn S K' : Subgroup Γ) : Set Γ) := by
  have h1 : g ∈ normalizer ((preIn S K' : Subgroup Γ) : Set Γ) :=
    (mem_normalizer_preIn_iff S hK' hg).2 hgK
  have h2 := mem_normalizer_inf' hg (mem_normalizer_centralizer h1)
  exact (mem_normalizer_iff.1 h2 x).1 hx

theorem conj_mem_centralizerMod {K W Y : Subgroup Γ} {g : Γ} (hgK : g ∈ normalizer (K : Set Γ))
    (hgW : g ∈ normalizer (W : Set Γ)) (hgY : g ∈ normalizer (Y : Set Γ)) {c : Γ}
    (hc : c ∈ centralizerMod K W Y) : g * c * g⁻¹ ∈ centralizerMod K W Y := by
  obtain ⟨hcK, hcW, hcY⟩ := hc
  refine ⟨(mem_normalizer_iff.1 hgK c).1 hcK, mul_mem (mul_mem hgW hcW) (inv_mem hgW), ?_⟩
  intro y hy
  have hy' : g⁻¹ * y * g ∈ Y := (mem_normalizer_iff''.1 hgY y).1 hy
  have h1 := hcY _ hy'
  have h2 := (mem_normalizer_iff.1 hgW _).1 h1
  have e : g * (c * (g⁻¹ * y * g) * c⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
      g * c * g⁻¹ * y * (g * c * g⁻¹)⁻¹ * y⁻¹ := by group
  rw [e] at h2
  exact h2

end Generic

section K8

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem Ks_normalizes_Us (h49 : d.Thm49Statement) (hd : d.Hyp) (h18 : Node18 d) :
    ∀ k ∈ Ks d, ∀ u ∈ Us d, k * u * k⁻¹ ∈ Us d := by
  intro k hk u hu
  obtain ⟨u₁, hu₁, h₁⟩ := Ks_conj_tU h49 hd h18 k hk 1 (one_mem _)
  obtain ⟨u₂, hu₂, h₂⟩ := Ks_conj_tU h49 hd h18 k hk u hu
  have e : k * u * k⁻¹ = (k * (star d d.t * 1) * k⁻¹)⁻¹ * (k * (star d d.t * u) * k⁻¹) := by group
  rw [e, h₁, h₂]
  have e2 : (star d d.t * u₁)⁻¹ * (star d d.t * u₂) = u₁⁻¹ * u₂ := by group
  rw [e2]
  exact mul_mem (inv_mem hu₁) hu₂

theorem Ks_le_normalizer_Us (h49 : d.Thm49Statement) (hd : d.Hyp) (h18 : Node18 d) :
    Ks d ≤ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact Ks_normalizes_Us h49 hd h18 k hk u hu
  · intro hu
    have h1 := Ks_normalizes_Us h49 hd h18 k⁻¹ (inv_mem hk) _ hu
    have e : k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ = u := by group
    rwa [e] at h1

theorem mem_Kg_iff {g : G} : g ∈ Kg d ↔ g ∈ Hg d ∧ star d g ∈ Ks d :=
  mem_preIn_iff d.s56V (Ks d)

theorem t_mem_Kg (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    d.t ∈ Kg d :=
  mem_Kg_iff.2 ⟨t_mem_Hg h49 hd, star_t_mem_Ks h49 hd hz h10⟩

theorem z0_not_mem_E (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) : z₀ ∉ d.E := by
  intro h
  have := (hd.s56_V_eps_eq_one_iff h49 hz.mem_V).2 h
  rw [hz.eps] at this
  exact hd.s56_z_ne_one this

theorem t_conj_z0 (hd : d.Hyp) (hz : d.S56Z0 z₀) : d.t * z₀ * d.t⁻¹ = d.z * z₀ := by
  have h1 := hd.s56_conj_t z₀
  have ht := hd.t_mul_self
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht
  rw [hz.eps, mul_inv_eq_iff_eq_mul] at h1
  rw [htinv]
  calc d.t * z₀ * d.t = d.t * (z₀ * d.t) := by group
    _ = d.t * (d.t * d.z * z₀) := by rw [h1]
    _ = (d.t * d.t) * d.z * z₀ := by group
    _ = d.z * z₀ := by rw [ht, one_mul]

theorem Kg_normalizes_Zz (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) (h18 : Node18 d) :
    ∀ k ∈ Kg d, ∀ x ∈ Zz d z₀, k * x * k⁻¹ ∈ Zz d z₀ := by
  intro k hk x hx
  obtain ⟨hkH, hkK⟩ := mem_Kg_iff.1 hk
  have hx' : x ∈ d.s56V ⊓ centralizer ((Ug d : Subgroup G) : Set G) := by
    rw [h17.1]
    exact hx
  have h2 : k * x * k⁻¹ ∈ d.s56V ⊓ centralizer ((Ug d : Subgroup G) : Set G) :=
    conj_mem_inf_centralizer_preIn d.s56V (Us_le_Hs h49 hd hz h10) hkH
      (Ks_le_normalizer_Us h49 hd h18 hkK) hx'
  rw [h17.1] at h2
  exact h2

theorem Kg_comm_z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) : ∀ k ∈ Kg d, k * d.z = d.z * k := by
  intro k hk
  obtain ⟨hkH, hkK⟩ := mem_Kg_iff.1 hk
  have hz' : d.z ∈ d.s56V ⊓ centralizer ((U0g d : Subgroup G) : Set G) := by
    rw [h17.2.1]
    exact mem_zpowers _
  have h2 : k * d.z * k⁻¹ ∈ d.s56V ⊓ centralizer ((U0g d : Subgroup G) : Set G) :=
    conj_mem_inf_centralizer_preIn d.s56V (U0s_le_Hs h49 hd hz h10) hkH hkK.1 hz'
  rw [h17.2.1] at h2
  rcases eq_one_or_of_mem_zpowers hd.s56_z_sq h2 with h | h
  · exfalso
    apply hd.s56_z_ne_one
    have h' : k * d.z * k⁻¹ = 1 := h
    calc d.z = k⁻¹ * (k * d.z * k⁻¹) * k := by group
      _ = 1 := by rw [h']; group
  · have h' : k * d.z * k⁻¹ = d.z := h
    rw [mul_inv_eq_iff_eq_mul] at h'
    exact h'

theorem zz0_conj (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) (h18 : Node18 d) :
    ∀ k ∈ Kg d, k * z₀ * k⁻¹ = z₀ ∨ k * z₀ * k⁻¹ = d.z * z₀ := by
  intro k hk
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hz₀z₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hzz₀ : d.z * z₀ = z₀ * d.z := (hz.cen hd.s56_z_mem_E).symm
  have hmem : k * z₀ * k⁻¹ ∈ Zz d z₀ :=
    Kg_normalizes_Zz h49 hd hz h10 h17 h18 k hk z₀ (mem_sup_right (mem_zpowers z₀))
  have hcz : k * d.z = d.z * k := Kg_comm_z h49 hd hz h10 h17 k hk
  rcases (CFSG.LocalAnalysis.EvenBN.Tits.N.mem_sup_zpowers_iff hzz hz₀z₀ hzz₀ _).1 hmem with
    h | h | h | h
  · exfalso
    apply z0_not_mem_E h49 hd hz
    have h1 : z₀ = 1 := by
      calc z₀ = k⁻¹ * (k * z₀ * k⁻¹) * k := by group
        _ = 1 := by rw [h]; group
    rw [h1]
    exact one_mem _
  · exfalso
    apply z0_not_mem_E h49 hd hz
    have h1 : z₀ = d.z := by
      calc z₀ = k⁻¹ * (k * z₀ * k⁻¹) * k := by group
        _ = k⁻¹ * d.z * k := by rw [h]
        _ = k⁻¹ * (d.z * k) := by group
        _ = k⁻¹ * (k * d.z) := by rw [hcz]
        _ = d.z := by group
    rw [h1]
    exact hd.s56_z_mem_E
  · exact Or.inl h
  · exact Or.inr h

theorem node19_conj3 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) (h18 : Node18 d) :
    (∀ k ∈ Kg d, ∀ x ∈ Zz d z₀, k * x * k⁻¹ ∈ Zz d z₀) ∧ ∀ k ∈ Kg d, k * d.z = d.z * k :=
  ⟨Kg_normalizes_Zz h49 hd hz h10 h17 h18, Kg_comm_z h49 hd hz h10 h17⟩

theorem node19_conj4 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) (h18 : Node18 d) :
    ((Kg d ⊓ centralizer ({z₀} : Set G)).subgroupOf (Kg d)).Normal ∧
      Kg d = (Kg d ⊓ centralizer ({z₀} : Set G)) ⊔ zpowers d.t := by
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hzc := Kg_comm_z h49 hd hz h10 h17
  have hconj := zz0_conj h49 hd hz h10 h17 h18
  refine ⟨⟨fun n hn g => ?_⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnK, hnC⟩ := Subgroup.mem_inf.1 hn
    have hgK : (g : G) ∈ Kg d := g.2
    have hcoe : ((g * n * g⁻¹ : ↥(Kg d)) : G) = (g : G) * (n : G) * (g : G)⁻¹ := rfl
    rw [hcoe]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgK hnK) (inv_mem hgK), ?_⟩
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have hnz₀ : z₀ * (n : G) = (n : G) * z₀ := mem_centralizer_iff.1 hnC z₀ rfl
    have hnz : (n : G) * d.z = d.z * n := hzc n hnK
    have hy : ((g : G)⁻¹ * z₀ * g) * n = n * ((g : G)⁻¹ * z₀ * g) := by
      have h1 := hconj (g : G)⁻¹ (inv_mem hgK)
      rw [inv_inv] at h1
      rcases h1 with h1 | h1
      · rw [h1]
        exact hnz₀
      · rw [h1]
        calc d.z * z₀ * (n : G) = d.z * (z₀ * n) := by group
          _ = d.z * (n * z₀) := by rw [hnz₀]
          _ = (d.z * n) * z₀ := by group
          _ = (n * d.z) * z₀ := by rw [hnz]
          _ = n * (d.z * z₀) := by group
    show z₀ * ((g : G) * n * (g : G)⁻¹) = ((g : G) * n * (g : G)⁻¹) * z₀
    calc z₀ * ((g : G) * n * (g : G)⁻¹)
        = g * (((g : G)⁻¹ * z₀ * g) * n) * (g : G)⁻¹ := by group
      _ = g * (n * ((g : G)⁻¹ * z₀ * g)) * (g : G)⁻¹ := by rw [hy]
      _ = ((g : G) * n * (g : G)⁻¹) * z₀ := by group
  · apply le_antisymm
    · intro k hk
      have hcomm0 : ∀ k' ∈ Kg d, k' * z₀ * k'⁻¹ = z₀ → k' ∈ Kg d ⊓ centralizer ({z₀} : Set G) := by
        intro k' hk' h'
        refine Subgroup.mem_inf.2 ⟨hk', mem_centralizer_iff.2 fun h hh => ?_⟩
        rw [Set.mem_singleton_iff.1 hh]
        rw [mul_inv_eq_iff_eq_mul] at h'
        exact h'.symm
      rcases hconj k hk with h | h
      · exact mem_sup_left (hcomm0 k hk h)
      · have htK := t_mem_Kg h49 hd hz h10 (d := d) (z₀ := z₀)
        have hkt : k * d.t ∈ Kg d := mul_mem hk htK
        have hkz : k * d.z * k⁻¹ = d.z := by
          have := hzc k hk
          rw [mul_inv_eq_iff_eq_mul]
          exact this
        have e : k * d.t * z₀ * (k * d.t)⁻¹ = z₀ := by
          calc k * d.t * z₀ * (k * d.t)⁻¹ = k * (d.t * z₀ * d.t⁻¹) * k⁻¹ := by group
            _ = k * (d.z * z₀) * k⁻¹ := by rw [t_conj_z0 hd hz]
            _ = (k * d.z * k⁻¹) * (k * z₀ * k⁻¹) := by group
            _ = d.z * (d.z * z₀) := by rw [hkz, h]
            _ = (d.z * d.z) * z₀ := by group
            _ = z₀ := by rw [hzz, one_mul]
        have hk0 := hcomm0 _ hkt e
        have : k = (k * d.t) * d.t⁻¹ := by group
        rw [this]
        exact mul_mem (mem_sup_left hk0) (mem_sup_right (inv_mem (mem_zpowers d.t)))
    · exact sup_le inf_le_left (zpowers_le.2 (t_mem_Kg h49 hd hz h10))

end K8

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
