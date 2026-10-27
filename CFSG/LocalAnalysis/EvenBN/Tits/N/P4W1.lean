module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Alt2D
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K8

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section Generic

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem trivOn_mono_left {B B' C : Subgroup Λ} (hBC : B ≤ C) (hB'C : B' ≤ C) (h : B ≤ B') :
    trivOn B C hBC ≤ trivOn B' C hB'C := fun φ hφ =>
  mem_trivOn.2 fun c hc => h (mem_trivOn.1 hφ c hc)

end Generic

section W1

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


@[expose] noncomputable def Zzs (d : Data G) (z₀ : G) : Subgroup ↥d.s56V := (Zz d z₀).subgroupOf d.s56V

theorem Z1s_le_Zzs : Z1s d ≤ Zzs d z₀ := fun _ hv => mem_sup_left hv

theorem Zz_le_E0 (hd : d.Hyp) : Zz d z₀ ≤ d.E ⊔ zpowers z₀ :=
  sup_le (zpowers_le.2 (mem_sup_left hd.s56_z_mem_E)) (zpowers_le.2 (mem_sup_right (mem_zpowers z₀)))

theorem Zzs_le_E0s (hd : d.Hyp) : Zzs d z₀ ≤ E0s d z₀ := fun _ hv => Zz_le_E0 hd hv

theorem z0_ne_one' (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) : z₀ ≠ 1 := fun h =>
  z0_not_mem_E h49 hd hz (h ▸ one_mem _)

theorem card_Zz (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Nat.card ↥(Zz d z₀) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₀z₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hnorm : zpowers z₀ ≤ normalizer ((zpowers d.z : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_comm fun s hs => hz.cen (hd.s56_zpowers_le_E hs)
  have hinf : zpowers d.z ⊓ zpowers z₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    rcases eq_one_or_eq_of_mem_zpowers_invol hz₀z₀ hy2 with h | h
    · rw [Subgroup.mem_bot]
      exact h
    · exact absurd (h ▸ hd.s56_zpowers_le_E hy1) (z0_not_mem_E h49 hd hz)
  have hord : orderOf z₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz₀z₀) (z0_ne_one' h49 hd hz)
  show Nat.card ↥(zpowers d.z ⊔ zpowers z₀ : Subgroup G) = 4
  rw [card_sup_of_inf_eq_bot' hnorm hinf, hd.s56_card_zpowers_z, Nat.card_zpowers, hord]

theorem card_E0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Nat.card ↥(d.E ⊔ zpowers z₀ : Subgroup G) = 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₀z₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hnorm : zpowers z₀ ≤ normalizer ((d.E : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_comm fun s hs => hz.cen hs
  have hinf : d.E ⊓ zpowers z₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    rcases eq_one_or_eq_of_mem_zpowers_invol hz₀z₀ hy2 with h | h
    · rw [Subgroup.mem_bot]
      exact h
    · exact absurd (h ▸ hy1) (z0_not_mem_E h49 hd hz)
  have hord : orderOf z₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hz₀z₀) (z0_ne_one' h49 hd hz)
  rw [card_sup_of_inf_eq_bot' hnorm hinf, hd.A_facts.1, Nat.card_zpowers, hord]

theorem card_Zzs (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Nat.card ↥(Zzs d z₀) = 4 := by
  rw [Zzs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Zz_le_V hd h49 hz)).toEquiv,
    card_Zz h49 hd hz h10]

theorem card_E0s (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Nat.card ↥(E0s d z₀) = 64 := by
  rw [E0s, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E0_le_V h49 hd hz)).toEquiv,
    card_E0 h49 hd hz h10]

theorem card_V' (h10 : Node10 d z₀) : Nat.card ↥d.s56V = 1024 := by
  rw [h10.card_V]
  norm_num

theorem star_x5_fix_Zzs (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (l : ↥d.s56V) (hl : star d d.x₅ l = l) : l ∈ Zzs d z₀ := by
  rcases (star_x5_fix_iff h49 hd hz h10 l).1 hl with h | h | h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact mem_sup_left (mem_zpowers d.z)
  · rw [h]
    exact mem_sup_right (mem_zpowers z₀)
  · rw [h]
    exact mul_mem (mem_sup_left (mem_zpowers d.z)) (mem_sup_right (mem_zpowers z₀))

theorem exists_Kg_of_mem_Ks {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) : ∃ g ∈ Kg d, star d g = k := by
  obtain ⟨g, hg, hgk⟩ := exists_star_of_mem_Ks hk
  exact ⟨g, mem_Kg_iff.2 ⟨hg, by rw [hgk]; exact hk⟩, hgk⟩

theorem Ks_Zzs_forward (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) (h18 : Node18 d) {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) (c : ↥d.s56V)
    (hc : c ∈ Zzs d z₀) : k c ∈ Zzs d z₀ := by
  obtain ⟨g, hg, rfl⟩ := exists_Kg_of_mem_Ks hk
  have hgH := (mem_Kg_iff.1 hg).1
  show ((star d g c : ↥d.s56V) : G) ∈ Zz d z₀
  rw [star_eq, actFun_apply_coe d.s56V hgH]
  exact Kg_normalizes_Zz h49 hd hz h10 h17 h18 g hg c hc

theorem Ks_Zzs_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) (h18 : Node18 d) {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) (c : ↥d.s56V) :
    c ∈ Zzs d z₀ ↔ k c ∈ Zzs d z₀ :=
  ⟨Ks_Zzs_forward h49 hd hz h10 h17 h18 hk c, fun h => by
    have := Ks_Zzs_forward h49 hd hz h10 h17 h18 (inv_mem hk) (k c) h
    simpa using this⟩

theorem Ks_E0s_forward (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) (c : ↥d.s56V) (hc : c ∈ E0s d z₀) :
    k c ∈ E0s d z₀ := by
  obtain ⟨g, hg, rfl⟩ := exists_Kg_of_mem_Ks hk
  have hgH := (mem_Kg_iff.1 hg).1
  have hc' : (c : G) ∈ centralizerMod d.s56V (zpowers d.z) (U0g d) := by
    rw [h17.2.2.1]
    exact hc
  have hgz : g ∈ normalizer ((zpowers d.z : Subgroup G) : Set G) := by
    refine mem_normalizer_of_comm fun s hs => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (Commute.zpow_right (show Commute g d.z from Kg_comm_z h49 hd hz h10 h17 g hg) n).eq
  have hgU0 : g ∈ normalizer ((U0g d : Subgroup G) : Set G) :=
    (mem_normalizer_preIn_iff d.s56V (U0s_le_Hs h49 hd hz h10) hgH).2 (mem_Kg_iff.1 hg).2.1
  have h2 := conj_mem_centralizerMod hgH hgz hgU0 hc'
  rw [h17.2.2.1] at h2
  show ((star d g c : ↥d.s56V) : G) ∈ d.E ⊔ zpowers z₀
  rw [star_eq, actFun_apply_coe d.s56V hgH]
  exact h2

theorem Ks_E0s_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) (c : ↥d.s56V) :
    c ∈ E0s d z₀ ↔ k c ∈ E0s d z₀ :=
  ⟨Ks_E0s_forward h49 hd hz h10 h17 hk c, fun h => by
    have := Ks_E0s_forward h49 hd hz h10 h17 (inv_mem hk) (k c) h
    simpa using this⟩

theorem Ks_fixes_z (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17 : Node17 d z₀) {k : MulAut ↥d.s56V} (hk : k ∈ Ks d) : k (zV h49 hd) = zV h49 hd := by
  obtain ⟨g, hg, rfl⟩ := exists_Kg_of_mem_Ks hk
  exact (actFun_fixes_iff d.s56V (mem_Kg_iff.1 hg).1 (zV h49 hd)).2
    (Kg_comm_z h49 hd hz h10 h17 g hg)

theorem star_x5_mem_Ks (h49 : d.Thm49Statement) (hd : d.Hyp) : star d d.x₅ ∈ Ks d := by
  have h : img d (Xg d) ≤ Ks d := node19b h49 hd (z₀ := 1)
  exact h (actFun_mem_imgIn (mem_zpowers d.x₅) (x5_mem_Hg h49 hd))

theorem star_x5_fixes_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    star d d.x₅ (z0V hz) = z0V hz :=
  (actFun_fixes_iff d.s56V (x5_mem_Hg h49 hd) (z0V hz)).2 hz.comm_x

theorem star_t_mem_trivOn_flag (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) :
    star d d.t ∈ trivOn (Zzs d z₀) (E0s d z₀) (Zzs_le_E0s hd) :=
  trivOn_mono_left (Z1s_le_E0s hd) (Zzs_le_E0s hd) Z1s_le_Zzs (star_t_mem_trivOn h49 hd hz h10)

theorem star_t_mem_trivOn_top (h49 : d.Thm49Statement) (hd : d.Hyp) :
    star d d.t ∈ trivOn (E0s d z₀) ⊤ le_top := by
  rw [mem_trivOn]
  intro c _
  show (((star d d.t c * c⁻¹ : ↥d.s56V)) : G) ∈ d.E ⊔ zpowers z₀
  have : (((star d d.t c * c⁻¹ : ↥d.s56V)) : G) = d.s56Eps (c : G) := by
    rw [← star_t_apply h49 hd c]
    rfl
  rw [this]
  exact mem_sup_left (hd.s56_eps_mem_E (V_le_M c.2))

end W1

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
