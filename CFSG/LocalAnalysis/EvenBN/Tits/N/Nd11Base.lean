module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bQ2
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Step08
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09Reg
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11Ab

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise commutatorElement

section Base

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem C2_facts (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) :
    (∀ a ∈ d.s56Q2, a * z₀ = z₀ * a → ∀ b ∈ d.s56Q2, b * z₀ = z₀ * b → a * b = b * a) ∧
    (∀ a ∈ d.s56Q2, a * z₀ = z₀ * a → a * a ∈ zpowers d.z) ∧
    (d.ρ.range = titsD.subgroupOf titsA → ∀ a ∈ d.s56Q2, a * z₀ = z₀ * a → a * a = 1) := by
  obtain ⟨hyc, hVel, -, -, hQD, hQtop, -⟩ := h10
  obtain ⟨-, -, -, -, -, -, -, -, ht9, -, -, hex5, -⟩ := h09
  have hVc : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVs : ∀ a ∈ d.s56V, a * a = 1 := fun a ha => by
    have := hVel.2 a ha
    simpa [pow_two] using this
  have hz0V : z₀ ∈ d.s56V := hz.mem_V
  have htz : d.t * z₀ ≠ z₀ * d.t := hd.s56_t_not_comm_z0 hz
  have hVz : ∀ v ∈ d.s56V, v * z₀ = z₀ * v := fun v hv => hVc v hv z₀ hz0V
  have hnot_tv : ∀ v ∈ d.s56V, d.t * v * z₀ = z₀ * (d.t * v) → False := by
    intro v hv h
    apply htz
    apply mul_right_cancel (b := v)
    calc d.t * z₀ * v = d.t * (z₀ * v) := by group
      _ = d.t * (v * z₀) := by rw [hVz v hv]
      _ = d.t * v * z₀ := by group
      _ = z₀ * (d.t * v) := h
      _ = z₀ * d.t * v := by group
  rcases hd.centralizer_A with ⟨hr, -⟩ | ⟨hr, -⟩
  ·
    have hQ := hQD hr
    have hCV : ∀ a ∈ d.s56Q2, a * z₀ = z₀ * a → a ∈ d.s56V := by
      intro a ha haz
      rcases P2b.Q2_cases_D h49 hd hQ ha with h | ⟨v, hv, rfl⟩
      · exact h
      · exact (hnot_tv v hv haz).elim
    refine ⟨fun a ha haz b hb hbz => hVc _ (hCV a ha haz) _ (hCV b hb hbz), fun a ha haz => ?_,
      fun _ a ha haz => hVs a (hCV a ha haz)⟩
    rw [hVs a (hCV a ha haz)]
    exact one_mem _
  ·
    obtain ⟨y, hy5, hyT, hyz⟩ := hex5 hr
    have hyc' := (hyc y hy5 hyT hyz).1
    have hy2 := P2b.y_sq hd hz hy5 hyT hyz ht9
    have hQ := hQtop y hy5
    have hyV : ∀ v ∈ d.s56V, y * v = v * y := fun v hv => hyc' v (s56_V_le_Q2 d hv)
    have hCV : ∀ a ∈ d.s56Q2, a * z₀ = z₀ * a → a ∈ d.s56V ∨ ∃ v ∈ d.s56V, a = y * v := by
      intro a ha haz
      rcases P2b.Q2_cases_top h49 hd hQ hyc' hy2 ha with
        h | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · exact Or.inl h
      · exact (hnot_tv v hv haz).elim
      · exact Or.inr ⟨v, hv, rfl⟩
      · exfalso
        apply hnot_tv v hv
        apply mul_left_cancel (a := y)
        calc y * (d.t * v * z₀) = y * (d.t * v) * z₀ := by group
          _ = z₀ * (y * (d.t * v)) := haz
          _ = (z₀ * y) * (d.t * v) := by group
          _ = (y * z₀) * (d.t * v) := by rw [hyz]
          _ = y * (z₀ * (d.t * v)) := by group
    have hcomm : ∀ a b : G, (a ∈ d.s56V ∨ ∃ v ∈ d.s56V, a = y * v) →
        (b ∈ d.s56V ∨ ∃ v ∈ d.s56V, b = y * v) → a * b = b * a := by
      rintro a b (ha | ⟨v, hv, rfl⟩) (hb | ⟨v', hv', rfl⟩)
      · exact hVc a ha b hb
      · calc a * (y * v') = (a * y) * v' := by group
          _ = (y * a) * v' := by rw [← hyV a ha]
          _ = y * (a * v') := by group
          _ = y * (v' * a) := by rw [hVc a ha v' hv']
          _ = (y * v') * a := by group
      · calc y * v * b = y * (v * b) := by group
          _ = y * (b * v) := by rw [hVc v hv b hb]
          _ = (y * b) * v := by group
          _ = (b * y) * v := by rw [hyV b hb]
          _ = b * (y * v) := by group
      · calc y * v * (y * v') = y * (v * y) * v' := by group
          _ = y * (y * v) * v' := by rw [← hyV v hv]
          _ = y * y * (v * v') := by group
          _ = y * y * (v' * v) := by rw [hVc v hv v' hv']
          _ = y * (y * v') * v := by group
          _ = y * (v' * y) * v := by rw [hyV v' hv']
          _ = y * v' * (y * v) := by group
    refine ⟨fun a ha haz b hb hbz => hcomm a b (hCV a ha haz) (hCV b hb hbz), fun a ha haz => ?_,
      fun hD => absurd (hD.symm.trans hr) s56_subgroupOf_ne_top⟩
    rcases hCV a ha haz with h | ⟨v, hv, rfl⟩
    · rw [hVs a h]
      exact one_mem _
    · rw [P2b.sq_mul_of_comm (hyV v hv), hy2, hVs v hv, mul_one]
      exact mem_zpowers _


theorem z0_sq (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) : z₀ * z₀ = 1 := by
  obtain ⟨-, hVel, -⟩ := h10
  have := hVel.2 z₀ hz.mem_V
  simpa [pow_two] using this

theorem Pe_inv (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hsq : z₀ * z₀ = 1)
    {y : G} (hy : IsY d y) {n : G} (hn : n ∈ d.N) {r : G} (hr : r ∈ Pe11 d) :
    n * r * n⁻¹ ∈ Pe11 d := by
  obtain ⟨hyN, hy3, hy1⟩ := hy.facts
  rw [Pe11_eq_s56Pe11] at hr ⊢
  rw [hd.s56_Pe11_eq_R1 h49 hz hsq hyN hy3 hy1] at hr ⊢
  exact hd.s56_R1_invariant h49 hz hsq hyN hy3 hy1 hn hr

theorem mem_P1_iff {x : G} : x ∈ P1 d ↔ x ∈ d.s56P ∧ ∀ w ∈ Pe11 d, w * x = x * w :=
  mem_inf.trans (and_congr_right fun _ => mem_centralizer_iff)

theorem Pe_le_P (h49 : d.Thm49Statement) (hd : d.Hyp) : Pe11 d ≤ d.s56P := by
  rw [Pe11_eq_s56Pe11]
  exact hd.s56_Pe11_le_P h49

theorem z0_mem_Pe (h07 : Node07 d) (h08 : Node08 d z₀) : z₀ ∈ Pe11 d := by
  obtain ⟨y, hy⟩ := h07.1
  obtain ⟨-, -, -, hgen, -⟩ := h08
  rw [hgen y hy]
  exact mem_sup_right (Subgroup.subset_closure (by simp))

theorem F_le_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (h08 : Node08 d z₀) : d.F ≤ P1 d := by
  obtain ⟨-, hFPe, -, -, hPel, -⟩ := h08
  intro f hf
  refine mem_P1_iff.2 ⟨hd.s56_B_le_P (s56_F_le_B d hf), fun w hw => ?_⟩
  exact congrArg Subtype.val (hPel.1.is_comm.comm ⟨w, hw⟩ ⟨f, hFPe hf⟩)

theorem Pe_le_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (h08 : Node08 d z₀) : Pe11 d ≤ P1 d := by
  have hPel := h08.2.2.2.2.1
  intro f hf
  refine mem_P1_iff.2 ⟨Pe_le_P h49 hd hf, fun w hw => ?_⟩
  exact congrArg Subtype.val (hPel.1.is_comm.comm ⟨w, hw⟩ ⟨f, hf⟩)

theorem P1_inv (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hsq : z₀ * z₀ = 1)
    {y : G} (hy : IsY d y) {n : G} (hn : n ∈ d.N) {x : G} (hx : x ∈ P1 d) :
    n * x * n⁻¹ ∈ P1 d := by
  obtain ⟨hxP, hxc⟩ := mem_P1_iff.1 hx
  refine mem_P1_iff.2 ⟨hd.s56_N_conj_P h49 hn hxP, fun w hw => ?_⟩
  have hw' : n⁻¹ * w * n⁻¹⁻¹ ∈ Pe11 d := Pe_inv h49 hd hz hsq hy (inv_mem hn) hw
  have h := hxc _ hw'
  calc w * (n * x * n⁻¹) = n * ((n⁻¹ * w * n⁻¹⁻¹) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * w * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
    _ = (n * x * n⁻¹) * w := by group

theorem t_not_mem_P1 (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d) (h08 : Node08 d z₀) :
    d.t ∉ P1 d := by
  intro h
  exact hd.s56_t_not_comm_z0 hz (((mem_P1_iff.1 h).2 z₀ (z0_mem_Pe h07 h08)).symm)

theorem P1_inf_B (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) : P1 d ⊓ d.B = d.F := by
  refine le_antisymm (fun b hb => ?_) (le_inf (F_le_P1 h49 hd h08) (s56_F_le_B d))
  obtain ⟨hbP, hbB⟩ := mem_inf.1 hb
  rcases (hd.s56_mem_B_iff).1 hbB with hf | hf
  · exact hf
  · exfalso
    apply t_not_mem_P1 hd hz h07 h08
    have : d.t = (d.t * b) * b⁻¹ := by group
    rw [this]
    exact mul_mem (F_le_P1 h49 hd h08 hf) (inv_mem hbP)

theorem CF_CNt_trivial (h49 : d.Thm49Statement) (hd : d.Hyp) {x : G} (hx : x ∈ d.F)
    (hc : ∀ c ∈ d.N ⊓ centralizer ({d.t} : Set G), x * c = c * x) : x = 1 := by
  have hU : x ∈ d.s56U11 := Data.s56_CF_K_le_U11 hx fun k hk => hc k (hd.s56_K_le_CNt hk)
  obtain ⟨hŷNC, -, -, -, -, hŷ11, hŷz⟩ := hd.s56_Y_facts
  have hyc := hc _ hŷNC
  have h11F : d.pv 11 ∈ d.F := Data.s56_pv11_mem_F d
  have hzF : d.z ∈ d.F := Data.s56_U11_le_F d (Data.s56_z_mem_U11 d)
  have e : x * d.s56Y * x⁻¹ = d.s56Y := by
    calc x * d.s56Y * x⁻¹ = d.s56Y * x * x⁻¹ := by rw [← hyc]
      _ = d.s56Y := by group
  have hyx : d.s56Y * x * d.s56Y⁻¹ = x := by
    calc d.s56Y * x * d.s56Y⁻¹ = x * d.s56Y * d.s56Y⁻¹ := by rw [← hyc]
      _ = x := by group
  rcases (Data.s56_mem_U11_iff).1 hU with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    rw [hŷ11] at hyx
    exact Data.s56_pv11_ne_z d hyx.symm
  · exfalso
    rw [hŷz] at hyx
    have h1 : d.pv 11 = 1 := by
      have := hyx
      calc d.pv 11 = (d.pv 11 * d.z) * d.z⁻¹ := by group
        _ = d.z * d.z⁻¹ := by rw [this]
        _ = 1 := by group
    exact s56_pv11_ne_one d h1
  · exfalso
    have hmul : d.s56Y * (d.pv 11 * d.z) * d.s56Y⁻¹ = d.z * (d.pv 11 * d.z) := by
      calc d.s56Y * (d.pv 11 * d.z) * d.s56Y⁻¹
          = (d.s56Y * d.pv 11 * d.s56Y⁻¹) * (d.s56Y * d.z * d.s56Y⁻¹) := by group
        _ = d.z * (d.pv 11 * d.z) := by rw [hŷ11, hŷz]
    rw [hyx] at hmul
    have h2 : d.z * (d.pv 11 * d.z) = d.pv 11 * d.z * d.z := by
      have := hd.s56_F_comm hzF (mul_mem h11F hzF)
      rw [this]
    rw [h2] at hmul
    have h3 : d.z = 1 := by
      have : d.pv 11 * d.z = d.pv 11 * d.z * d.z := hmul
      have h4 : d.pv 11 * d.z * d.z = d.pv 11 := by rw [mul_assoc, hd.s56_z_sq, mul_one]
      rw [h4] at this
      exact mul_left_cancel (a := d.pv 11) (by rw [mul_one]; exact this)
    exact hd.s56_z_ne_one h3

theorem P1_CNt (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) :
    P1 d ⊓ centralizer ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨-, -, -, -, -, hPt, -⟩ := h09
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxP1, hxC⟩ := mem_inf.1 hx
  have hxc : ∀ c ∈ d.N ⊓ centralizer ({d.t} : Set G), c * x = x * c := fun c hc => mem_centralizer_iff.1 hxC c hc
  have hxt : d.t * x = x * d.t := hxc d.t (hd.s56_t_mem_CNt)
  have hxB : x ∈ d.B := by
    rw [← hPt]
    exact mem_inf.2 ⟨(mem_P1_iff.1 hxP1).1, mem_centralizer_singleton_iff.2 hxt.symm⟩
  have hxF : x ∈ d.F := by
    rw [← P1_inf_B h49 hd hz h07 h08]
    exact mem_inf.2 ⟨hxP1, hxB⟩
  exact CF_CNt_trivial h49 hd hxF fun c hc => (hxc c hc).symm


@[expose] noncomputable def epsImg (h49 : d.Thm49Statement) (hd : d.Hyp) (S : Subgroup G) : Subgroup G :=
  (S.subgroupOf d.s56P).map (node09Eps h49 hd)

theorem mem_epsImg (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G} {f : G} :
    f ∈ epsImg h49 hd S ↔ ∃ s ∈ S, ∃ _ : s ∈ d.s56P, d.s56Eps s = f := by
  unfold epsImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨s, hsP⟩, hs, rfl⟩
    exact ⟨s, Subgroup.mem_subgroupOf.1 hs, hsP, rfl⟩
  · rintro ⟨s, hs, hsP, rfl⟩
    exact ⟨⟨s, hsP⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩

theorem eps_mem_epsImg (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G} {s : G} (hs : s ∈ S)
    (hsP : s ∈ d.s56P) : d.s56Eps s ∈ epsImg h49 hd S :=
  (mem_epsImg h49 hd).2 ⟨s, hs, hsP, rfl⟩

theorem epsImg_mono (h49 : d.Thm49Statement) (hd : d.Hyp) {S S' : Subgroup G} (h : S ≤ S') :
    epsImg h49 hd S ≤ epsImg h49 hd S' := fun f hf => by
  obtain ⟨s, hs, hsP, rfl⟩ := (mem_epsImg h49 hd).1 hf
  exact (mem_epsImg h49 hd).2 ⟨s, h hs, hsP, rfl⟩

theorem epsImg_le_F (h49 : d.Thm49Statement) (hd : d.Hyp) (S : Subgroup G) :
    epsImg h49 hd S ≤ d.F := by
  intro f hf
  obtain ⟨s, hs, hsP, rfl⟩ := (mem_epsImg h49 hd).1 hf
  exact hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N hsP)

theorem card_eq_epsImg (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G} (hS : S ≤ d.s56P) :
    Nat.card S = Nat.card (S ⊓ d.B : Subgroup G) * Nat.card (epsImg h49 hd S) := by
  have h := card_eq_card_inf_ker_mul_card_map (node09Eps h49 hd) (S.subgroupOf d.s56P)
  have e : S.subgroupOf d.s56P ⊓ d.B.subgroupOf d.s56P = (S ⊓ d.B).subgroupOf d.s56P :=
    (Subgroup.comap_inf S d.B d.s56P.subtype).symm
  rw [node09Eps_ker, e,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hS : S ⊓ d.B ≤ d.s56P)).toEquiv] at h
  exact h

theorem epsImg_eq_F (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G}
    (hSinv : ∀ n ∈ d.N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) (hcard : 16 ≤ Nat.card (epsImg h49 hd S)) :
    epsImg h49 hd S = d.F := by
  refine node09_eq_F_of_invariant h49 hd (epsImg_le_F h49 hd S) ?_ hcard
  intro c hc x hx
  obtain ⟨s, hs, hsP, rfl⟩ := (mem_epsImg h49 hd).1 hx
  have hcN : c ∈ d.N := (mem_inf.1 hc).1
  have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  refine (mem_epsImg h49 hd).2 ⟨c * s * c⁻¹, hSinv c hcN s hs, hd.s56_N_conj_P h49 hcN hsP, ?_⟩
  exact hd.s56_eps_conj hct s

theorem P_eq_zpowers_mul (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G} (hSP : S ≤ d.s56P)
    (hFS : d.F ≤ S) (hSinv : ∀ n ∈ d.N, ∀ s ∈ S, n * s * n⁻¹ ∈ S)
    (hcard : 16 ≤ Nat.card (epsImg h49 hd S)) :
    (d.s56P : Set G) = (zpowers d.t : Set G) * (S : Set G) := by
  have hε := epsImg_eq_F h49 hd hSinv hcard
  ext p
  constructor
  · intro hp
    have hpF : d.s56Eps p ∈ epsImg h49 hd S := by
      rw [hε]
      exact hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N hp)
    obtain ⟨s, hs, hsP, hsε⟩ := (mem_epsImg h49 hd).1 hpF
    have hps : p * s⁻¹ ∈ d.B := by
      refine hd.s56_mem_B_of_eps_one h49 (mul_mem hp (inv_mem hsP)) ?_
      rw [hd.s56_eps_mul_P h49 hp (inv_mem hsP), hd.s56_eps_inv_P h49 hsP, hsε]
      exact hd.s56_eps_sq_P h49 hp
    rcases (hd.s56_mem_B_iff).1 hps with hf | hf
    · refine ⟨1, one_mem _, p, ?_, one_mul p⟩
      have : p = (p * s⁻¹) * s := by group
      rw [this]
      exact mul_mem (hFS hf) hs
    · refine ⟨d.t, mem_zpowers _, (d.t * (p * s⁻¹)) * s, mul_mem (hFS hf) hs, ?_⟩
      calc d.t * ((d.t * (p * s⁻¹)) * s) = (d.t * d.t) * p := by group
        _ = p := by rw [hd.t_mul_self, one_mul]
  · rintro ⟨a, ha, s, hs, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact mul_mem (zpow_mem (hd.s56_B_le_P (s56_t_mem_B d)) k) (hSP hs)


@[expose] noncomputable def K0 (d : Data G) (z₀ : G) : Subgroup G :=
  d.s56Q2 ⊓ d.s56P ⊓ centralizer ({z₀} : Set G)

theorem mem_K0_iff {x : G} : x ∈ K0 d z₀ ↔ (x ∈ d.s56Q2 ∧ x ∈ d.s56P) ∧ x * z₀ = z₀ * x := by
  unfold K0
  rw [mem_inf, mem_inf, mem_centralizer_singleton_iff]


theorem card_P (h10 : Node10 d z₀) : Nat.card d.s56P = 2 ^ 11 := by
  obtain ⟨-, -, -, -, -, -, h9, -, hrel⟩ := h10
  have h := Subgroup.relIndex_mul_card (H := d.s56Q2) (K := d.s56P)
  rw [hrel, h9] at h
  rw [← h]
  norm_num

end Base

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
