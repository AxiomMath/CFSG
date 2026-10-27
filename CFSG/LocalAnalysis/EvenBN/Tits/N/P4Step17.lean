module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Alt2D
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Syl

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section Step17

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem E_eq_V_inf_centralizer (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.E = d.s56V ⊓ centralizer ({d.t} : Set G) := by
  apply le_antisymm
  · intro e he
    exact Subgroup.mem_inf.2 ⟨hd.s56_E_le_V h49 he,
      Subgroup.mem_centralizer_singleton_iff.2 (hd.L_comm_t (d.s56_E_le_L he))⟩
  · intro v hv
    obtain ⟨hvV, hvt⟩ := Subgroup.mem_inf.1 hv
    have hε : d.s56Eps v = 1 := hd.s56_eps_of_comm (Subgroup.mem_centralizer_singleton_iff.1 hvt)
    exact (hd.s56_V_eps_eq_one_iff h49 hvV).1 hε

theorem CHt_eq_CMt (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Hg d ⊓ centralizer ({d.t} : Set G) = CMt d := by
  apply le_antisymm
  · intro h hh
    obtain ⟨hhH, hht⟩ := Subgroup.mem_inf.1 hh
    have hcomm : h * d.t = d.t * h := Subgroup.mem_centralizer_singleton_iff.1 hht
    have hcz : centralizer ({d.t} : Set G) = centralizer ((zpowers d.t : Subgroup G) : Set G) := by
      ext g
      rw [mem_centralizer_iff, mem_centralizer_iff]
      constructor
      · intro hg w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have : g * d.t = d.t * g := (hg d.t rfl).symm
        exact (Commute.zpow_left (show Commute d.t g from this.symm) n).eq
      · intro hg w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hg d.t (mem_zpowers d.t)
    have hTn : h ∈ normalizer ((zpowers d.t : Subgroup G) : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact (Commute.zpow_left (show Commute d.t h from hcomm.symm) n).eq.symm.symm
    have hEn : h ∈ normalizer (d.E : Set G) := by
      rw [E_eq_V_inf_centralizer h49 hd]
      refine mem_normalizer_inf' hhH ?_
      rw [hcz]
      exact mem_normalizer_centralizer hTn
    have hAn : h ∈ normalizer ((d.E ⊔ zpowers d.t : Subgroup G) : Set G) :=
      mem_normalizer_sup' hEn hTn
    exact Subgroup.mem_inf.2 ⟨hAn, hht⟩
  · exact inf_le_inf_right _ (M_le_Hg h49 hd)

theorem exists_tInv_sylow_Cv (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ∃ S : Subgroup G, fusionIsSylowIn 2 S (Cv d) ∧ ∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S :=
  exists_tInv_sylow hd.t_mul_self (mem_normalizer_centralizer (t_mem_Hg h49 hd))

theorem alt1_of_node16 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h14 : Node14 d) (h16 : Node16 d z₀) (h17s : Node17s d z₀)
    {S : Subgroup G} (hS : fusionIsSylowIn 2 S (Cv d)) (hSt : ∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S) :
    Trans S (OrbSet d S) ∧ img d (Hg d ⊓ centralizer ({d.t} : Set G)) =
      centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d := by
  rcases h16.2 S hS hSt with h | h
  · exact h
  · exfalso
    obtain ⟨-, β, hβH, hCs, hβi, hβc, hTr, hCV⟩ := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, y₁, hy⟩ := h09
    obtain ⟨hU, hU16, hrest⟩ := h17s
    obtain ⟨h17c, h17i, h17t⟩ := hrest y₁ hy
    exact no_alt2 h49 hd hz h10 hU hU16 hy h17c h17i h17t h14.2.1.2 hβH hCs hβi hβc hTr hCV

theorem node17_4 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h14 : Node14 d) (h16 : Node16 d z₀) (h17s : Node17s d z₀) :
    img d (CMt d) = centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d := by
  obtain ⟨S, hS, hSt⟩ := exists_tInv_sylow_Cv h49 hd
  have := (alt1_of_node16 h49 hd hz h09 h10 h14 h16 h17s hS hSt).2
  rwa [CHt_eq_CMt h49 hd] at this

theorem node17_5 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h14 : Node14 d) (h16 : Node16 d z₀) (h17s : Node17s d z₀) :
    ∀ S : Subgroup G, fusionIsSylowIn 2 S (Cv d) → (∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S) →
      Trans S (OrbSet d S) :=
  fun _ hS hSt => (alt1_of_node16 h49 hd hz h09 h10 h14 h16 h17s hS hSt).1

theorem node17_6 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h14 : Node14 d) (h16 : Node16 d z₀) (h17s : Node17s d z₀) :
    ∀ h ∈ Hg d, star d (h * d.t * h⁻¹) ∉ Us d := by
  intro h hh hmem
  have h4 := node17_4 h49 hd hz h09 h10 h14 h16 h17s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, y₁, hy⟩ := h09
  obtain ⟨hU, hU16, hrest⟩ := h17s
  obtain ⟨h17c, h17i, h17t⟩ := hrest y₁ hy
  have hF := isF20_Us h49 hd hz h10 hU hU16 hy
  have hPe := P_eq h49 hd y₁
  have hPle : Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) ≤ img d (CMt d) := by
    refine sup_le (sup_le (Us_le_img_CMt h49 hd hz) (imgIn_mono _ (Xg_le_CMt hd))) ?_
    rw [star_eq, ← imgIn_zpowers d.s56V (y1_mem_Hg h49 hd hy)]
    exact imgIn_mono _ (zpowers_le.2 (hy.mem_CMt hd))
  rw [hPe] at h17c h17i h17t hPle
  obtain ⟨p, hp, hpp⟩ := hF.exists_sq_Pgrp hmem
  have hstar : star d (h * d.t * h⁻¹) = star d h * star d d.t * (star d h)⁻¹ :=
    actFun_conj d.s56V hh (t_mem_Hg h49 hd)
  have hsH : star d h ∈ Hs d := actFun_mem_imgIn hh hh
  have hpH : p ∈ Hs d := imgIn_mono _ (CMt_le_Hg h49 hd) (hPle hp)
  have hkH : (star d h)⁻¹ * p * star d h ∈ Hs d :=
    mul_mem (mul_mem (inv_mem hsH) hpH) hsH
  have hkk : ((star d h)⁻¹ * p * star d h) * ((star d h)⁻¹ * p * star d h) = star d d.t := by
    have : ((star d h)⁻¹ * p * star d h) * ((star d h)⁻¹ * p * star d h) =
        (star d h)⁻¹ * (p * p) * star d h := by group
    rw [this, hpp, hstar]
    group
  set k := (star d h)⁻¹ * p * star d h with hk
  have hkc : k ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d := by
    refine Subgroup.mem_inf.2 ⟨?_, hkH⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * star d d.t = k * (k * k) := by rw [hkk]
      _ = (k * k) * k := by group
      _ = star d d.t * k := by rw [hkk]
  rw [← h4, h17c] at hkc
  have hN : zpowers (star d d.t) ≤ normalizer ((IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) :
      Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
    intro a ha
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute (star d d.t) q from h17t q hq) n).eq.symm
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers (star d d.t))
    (IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁)) hN
  have hk' : k ∈ ((zpowers (star d d.t) : Set (MulAut ↥d.s56V)) *
      ((IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) : Subgroup (MulAut ↥d.s56V)) :
        Set (MulAut ↥d.s56V))) := by
    rw [← hset]
    exact hkc
  obtain ⟨a, ha, q, hq, hkaq⟩ := hk'
  have htt : star d d.t * star d d.t = 1 := star_t_mul_self h49 hd
  have haq : a = 1 ∨ a = star d d.t := eq_one_or_eq_of_mem_zpowers htt ha
  have hkq : k * k = q * q := by
    have hkaq' : k = a * q := hkaq.symm
    rcases haq with h1 | h1
    · rw [hkaq', h1]; group
    · have hc : star d d.t * q = q * star d d.t := h17t q hq
      rw [hkaq', h1]
      calc star d d.t * q * (star d d.t * q) = (star d d.t * (q * star d d.t)) * q := by group
        _ = (star d d.t * (star d d.t * q)) * q := by rw [← hc]
        _ = (star d d.t * star d d.t) * q * q := by group
        _ = q * q := by rw [htt, one_mul]
  have htq : star d d.t = q * q := by rw [← hkk, hkq]
  have htP : star d d.t ∈ zpowers (star d d.t) ⊓
      IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) :=
    Subgroup.mem_inf.2 ⟨mem_zpowers _, by rw [htq]; exact mul_mem hq hq⟩
  rw [h17i, Subgroup.mem_bot] at htP
  exact star_t_ne h49 hd hz htP

theorem node17 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h14 : Node14 d) (h16 : Node16 d z₀) (h17s : Node17s d z₀) :
    Node17 d z₀ := by
  have hU16 : Nat.card (Us d) = 16 := h17s.2.1
  exact ⟨node17_1 h49 hd hz h10 hU16, node17_2 h49 hd hz h10 hU16, node17_3 h49 hd hz h10,
    node17_4 h49 hd hz h09 h10 h14 h16 h17s, node17_5 h49 hd hz h09 h10 h14 h16 h17s,
    node17_6 h49 hd hz h09 h10 h14 h16 h17s⟩

end Step17

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Final17


theorem step17_holds : Step17 := by
  intro G _ _ d z₀ h49 hd hz h09 h10 h14 _ h16 h17s
  exact P4.node17 h49 hd hz h09 h10 h14 h16 h17s

end Final17

end CFSG.LocalAnalysis.EvenBN.Tits.N
