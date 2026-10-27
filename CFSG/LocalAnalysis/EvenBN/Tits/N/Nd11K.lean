module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise commutatorElement

section K

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem nd11k_F_comm_z0 (h07 : Node07 d) (h08 : Node08 d z₀) {f : G} (hf : f ∈ d.F) :
    f * z₀ = z₀ * f := by
  have hz0 := z0_mem_Pe h07 h08
  obtain ⟨-, hFPe, -, -, hPel, -⟩ := h08
  exact congrArg Subtype.val (hPel.1.is_comm.comm ⟨f, hFPe hf⟩ ⟨z₀, hz0⟩)

theorem nd11k_Pe_decomp (h08 : Node08 d z₀) {w : G} (hw : w ∈ Pe11 d) :
    ∃ f ∈ d.F, ∃ x ∈ (Pe11 d ⊓ d.s56V : Subgroup G), f * x = w := by
  obtain ⟨-, -, -, -, -, -, -, hdec⟩ := h08
  have hw' : w ∈ (Pe11 d : Set G) := hw
  rw [hdec] at hw'
  obtain ⟨f, hf, x, hx, hfx⟩ := Set.mem_mul.1 hw'
  exact ⟨f, hf, x, hx, hfx⟩

theorem nd11k_V_comm (h10 : Node10 d z₀) {a b : G} (ha : a ∈ d.s56V) (hb : b ∈ d.s56V) :
    a * b = b * a := by
  obtain ⟨-, hVel, -⟩ := h10
  exact congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem nd11k_mem_K0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {x : G} (hx : x ∈ (Pe11 d ⊓ d.s56V : Subgroup G)) : x ∈ K0 d z₀ := by
  obtain ⟨hxPe, hxV⟩ := mem_inf.1 hx
  exact mem_K0_iff.2 ⟨⟨s56_V_le_Q2 d hxV, Pe_le_P h49 hd hxPe⟩, nd11k_V_comm h10 hxV hz.mem_V⟩

theorem nd11k_K0_le_P : K0 d z₀ ≤ d.s56P := fun _ hk => (mem_K0_iff.1 hk).1.2

theorem nd11k_Kc_le_P (hd : d.Hyp) : K0 d z₀ ⊔ d.F ≤ d.s56P :=
  sup_le nd11k_K0_le_P fun _ hf => hd.s56_B_le_P (s56_F_le_B d hf)

theorem nd11k_Kc_le_cent (h07 : Node07 d) (h08 : Node08 d z₀) :
    K0 d z₀ ⊔ d.F ≤ centralizer ({z₀} : Set G) :=
  sup_le (fun _ hk => mem_centralizer_singleton_iff.2 (mem_K0_iff.1 hk).2)
    fun _ hf => mem_centralizer_singleton_iff.2 (nd11k_F_comm_z0 h07 h08 hf)

theorem nd11k_KF_comm {k f : G} (hk : k ∈ K0 d z₀) (hf : f ∈ d.F) : k * f = f * k :=
  ((s56_mem_P_iff d).1 (nd11k_K0_le_P hk)).2 f hf

theorem nd11k_Kc_eq_mul :
    ((K0 d z₀ ⊔ d.F : Subgroup G) : Set G) = (K0 d z₀ : Set G) * (d.F : Set G) :=
  S56.coe_sup_eq_mul_of_comm fun _ hk _ hf => nd11k_KF_comm hk hf

theorem K0_comm (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    ∀ a ∈ K0 d z₀, ∀ b ∈ K0 d z₀, a * b = b * a := by
  intro a ha b hb
  obtain ⟨⟨haQ, -⟩, haz⟩ := mem_K0_iff.1 ha
  obtain ⟨⟨hbQ, -⟩, hbz⟩ := mem_K0_iff.1 hb
  exact (C2_facts h49 hd hz h09 h10).1 a haQ haz b hbQ hbz

theorem K0_card (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    Nat.card (K0 d z₀) = 2 ^ 8 := by
  obtain ⟨-, -, -, -, -, -, h9, -, -⟩ := h10
  have hM : ∀ m ∈ d.s56Q2 ⊓ d.s56P, m ∈ d.M := fun m hm =>
    ((s56_mem_Q2_iff).1 (mem_inf.1 hm).1).1
  have ht0 : d.t * z₀ * d.t⁻¹ * z₀⁻¹ = d.z := by
    rw [inv_eq_of_mul_eq_one_right hd.t_mul_self]
    calc d.t * z₀ * d.t * z₀⁻¹ = d.t * (z₀ * d.t * z₀⁻¹) := by group
      _ = d.t * (d.t * d.z) := by rw [hd.s56_z0_conj_t hz]
      _ = (d.t * d.t) * d.z := by group
      _ = d.z := by rw [hd.t_mul_self, one_mul]
  have h := card_eq_two_mul_card_inf_centralizer (d.s56Q2 ⊓ d.s56P) d.z z₀ hd.s56_z_sq
    hd.s56_z_ne_one (fun m hm => mem_centralizer_singleton_iff.1 (hd.M_le_centralizer_z (hM m hm)))
    (fun m hm => hd.s56_M_comm_z0 h49 hz (hM m hm))
    (m₀ := d.t) (mem_inf.2 ⟨P2b.t_mem_Q2 hd, hd.s56_B_le_P (s56_t_mem_B d)⟩) ht0
  rw [h9] at h
  unfold K0
  omega

theorem K0_inf_B (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    K0 d z₀ ⊓ d.B = d.E ⊓ d.F := by
  have hz0V := hz.mem_V
  refine le_antisymm (fun b hb => ?_) (fun e he => ?_)
  · obtain ⟨hbK, hbB⟩ := mem_inf.1 hb
    obtain ⟨⟨hbQ, -⟩, hbz⟩ := mem_K0_iff.1 hbK
    have hbF : b ∈ d.F := by
      rcases (hd.s56_mem_B_iff).1 hbB with hf | hf
      · exact hf
      · exfalso
        have h1 : d.t * b ∈ centralizer ({z₀} : Set G) :=
          mem_centralizer_singleton_iff.2 (nd11k_F_comm_z0 h07 h08 hf)
        have h2 : b ∈ centralizer ({z₀} : Set G) := mem_centralizer_singleton_iff.2 hbz
        have h3 : d.t ∈ centralizer ({z₀} : Set G) := by
          have : d.t = (d.t * b) * b⁻¹ := by group
          rw [this]
          exact mul_mem h1 (inv_mem h2)
        exact hd.s56_t_not_comm_z0 hz (mem_centralizer_singleton_iff.1 h3)
    obtain ⟨-, -, -, -, -, -, -, -, -, ⟨e, he, hT, -⟩, -, -⟩ := h07
    obtain ⟨-, -, -, hT'⟩ := hT
    have hcomm : e * b = b * e := ((s56_mem_Q2_iff).1 hbQ).2 e he
    have hfix : e * b * e⁻¹ = b := by rw [hcomm]; group
    have hbA : b ∈ d.A := (mem_inf.1 (((hT' b hbB).2).1 hfix)).1
    have hbE : b ∈ d.E := by
      rw [← hd.A_inf_L]
      exact mem_inf.2 ⟨hbA, s56_F_le_L d hbF⟩
    exact mem_inf.2 ⟨hbE, hbF⟩
  · obtain ⟨heE, heF⟩ := mem_inf.1 he
    have heB : e ∈ d.B := s56_F_le_B d heF
    refine mem_inf.2 ⟨mem_K0_iff.2 ⟨⟨?_, hd.s56_B_le_P heB⟩, nd11k_F_comm_z0 h07 h08 heF⟩, heB⟩
    exact (s56_mem_Q2_iff).2 ⟨s56_E_le_M d heE, fun e' he' => hd.s56_E_comm he' heE⟩

theorem epsImg_K0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    epsImg h49 hd (K0 d z₀) = d.E ⊓ d.F := by
  have hle : epsImg h49 hd (K0 d z₀) ≤ d.E ⊓ d.F := by
    intro f hf
    obtain ⟨s, hs, hsP, rfl⟩ := (mem_epsImg h49 hd).1 hf
    exact mem_inf.2 ⟨hd.s56_eps_mem_E ((s56_mem_Q2_iff).1 (mem_K0_iff.1 hs).1.1).1,
      hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N hsP)⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h := card_eq_epsImg h49 hd (nd11k_K0_le_P (d := d) (z₀ := z₀))
  rw [K0_card h49 hd hz h07 h08 h09 h10, K0_inf_B h49 hd hz h07 h08 h09 h10,
    hd.s56_card_E_inf_F] at h
  rw [hd.s56_card_E_inf_F]
  omega

theorem Pe_le_Kc (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    Pe11 d ≤ K0 d z₀ ⊔ d.F := by
  intro w hw
  obtain ⟨f, hf, x, hx, rfl⟩ := nd11k_Pe_decomp h08 hw
  exact mul_mem (mem_sup_right hf) (mem_sup_left (nd11k_mem_K0 h49 hd hz h10 hx))

theorem Kc_comm (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    ∀ a ∈ K0 d z₀ ⊔ d.F, ∀ b ∈ K0 d z₀ ⊔ d.F, a * b = b * a := by
  intro a ha b hb
  have ha' : a ∈ (K0 d z₀ : Set G) * (d.F : Set G) := by rw [← nd11k_Kc_eq_mul]; exact ha
  have hb' : b ∈ (K0 d z₀ : Set G) * (d.F : Set G) := by rw [← nd11k_Kc_eq_mul]; exact hb
  obtain ⟨k₁, hk₁, f₁, hf₁, rfl⟩ := Set.mem_mul.1 ha'
  obtain ⟨k₂, hk₂, f₂, hf₂, rfl⟩ := Set.mem_mul.1 hb'
  have hkk : k₁ * k₂ = k₂ * k₁ := K0_comm h49 hd hz h07 h08 h09 h10 k₁ hk₁ k₂ hk₂
  have hff : f₁ * f₂ = f₂ * f₁ := hd.s56_F_comm hf₁ hf₂
  calc k₁ * f₁ * (k₂ * f₂) = k₁ * (f₁ * k₂) * f₂ := by group
    _ = k₁ * (k₂ * f₁) * f₂ := by rw [← nd11k_KF_comm hk₂ hf₁]
    _ = (k₁ * k₂) * (f₁ * f₂) := by group
    _ = (k₂ * k₁) * (f₂ * f₁) := by rw [hkk, hff]
    _ = k₂ * (k₁ * f₂) * f₁ := by group
    _ = k₂ * (f₂ * k₁) * f₁ := by rw [nd11k_KF_comm hk₁ hf₂]
    _ = k₂ * f₂ * (k₁ * f₁) := by group

theorem Kc_le_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    K0 d z₀ ⊔ d.F ≤ P1 d := by
  refine sup_le ?_ (F_le_P1 h49 hd h08)
  intro k hk
  obtain ⟨⟨-, hkP⟩, -⟩ := mem_K0_iff.1 hk
  refine mem_P1_iff.2 ⟨hkP, fun w hw => ?_⟩
  obtain ⟨f, hf, x, hx, rfl⟩ := nd11k_Pe_decomp h08 hw
  have hkx : k * x = x * k :=
    K0_comm h49 hd hz h07 h08 h09 h10 k hk x (nd11k_mem_K0 h49 hd hz h10 hx)
  have hkf : k * f = f * k := nd11k_KF_comm hk hf
  calc f * x * k = f * (x * k) := by group
    _ = f * (k * x) := by rw [hkx]
    _ = (f * k) * x := by group
    _ = (k * f) * x := by rw [hkf]
    _ = k * (f * x) := by group

theorem Kc_inf_B (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    (K0 d z₀ ⊔ d.F) ⊓ d.B = d.F := by
  refine le_antisymm (fun b hb => ?_) (le_inf le_sup_right (s56_F_le_B d))
  obtain ⟨hbK, hbB⟩ := mem_inf.1 hb
  rcases (hd.s56_mem_B_iff).1 hbB with hf | hf
  · exact hf
  · exfalso
    have h1 : d.t * b ∈ K0 d z₀ ⊔ d.F := mem_sup_right hf
    have h3 : d.t ∈ K0 d z₀ ⊔ d.F := by
      have : d.t = (d.t * b) * b⁻¹ := by group
      rw [this]
      exact mul_mem h1 (inv_mem hbK)
    exact hd.s56_t_not_comm_z0 hz (mem_centralizer_singleton_iff.1 (nd11k_Kc_le_cent h07 h08 h3))

theorem epsImg_Kc (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    epsImg h49 hd (K0 d z₀ ⊔ d.F) = d.E ⊓ d.F := by
  have hK := epsImg_K0 h49 hd hz h07 h08 h09 h10
  refine le_antisymm (fun f hf => ?_) (hK ▸ epsImg_mono h49 hd le_sup_left)
  obtain ⟨s, hs, hsP, rfl⟩ := (mem_epsImg h49 hd).1 hf
  have hs' : s ∈ (K0 d z₀ : Set G) * (d.F : Set G) := by rw [← nd11k_Kc_eq_mul]; exact hs
  obtain ⟨k, hk, g, hg, rfl⟩ := Set.mem_mul.1 hs'
  have hkP := nd11k_K0_le_P hk
  have hgB : g ∈ d.B := s56_F_le_B d hg
  have h1 : d.s56Eps (k * g) = d.s56Eps k := by
    rw [hd.s56_eps_mul_P h49 hkP (hd.s56_B_le_P hgB), hd.s56_eps_eq_one_of_mem_B hgB, mul_one]
  rw [h1, ← hK]
  exact eps_mem_epsImg h49 hd hk hkP

theorem Kc_card (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    Nat.card (K0 d z₀ ⊔ d.F : Subgroup G) = 2 ^ 9 := by
  have h := card_eq_epsImg h49 hd (nd11k_Kc_le_P (z₀ := z₀) hd)
  rw [Kc_inf_B h49 hd hz h07 h08 h09 h10, epsImg_Kc h49 hd hz h07 h08 h09 h10,
    hd.s56_card_E_inf_F, hd.B_facts.1] at h
  rw [h]
  norm_num

theorem Kc_relIndex (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    (K0 d z₀ ⊔ d.F).relIndex d.s56P = 4 := by
  have h := Subgroup.relIndex_mul_card (H := K0 d z₀ ⊔ d.F) (K := d.s56P)
  rw [inf_eq_left.2 (nd11k_Kc_le_P (z₀ := z₀) hd), Kc_card h49 hd hz h07 h08 h09 h10,
    card_P h10] at h
  omega

end K

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
