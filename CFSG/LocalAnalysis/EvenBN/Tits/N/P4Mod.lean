module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Aut
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S17

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Generic

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_inf' {A B : Subgroup Γ} {g : Γ} (hA : g ∈ normalizer (A : Set Γ))
    (hB : g ∈ normalizer (B : Set Γ)) : g ∈ normalizer ((A ⊓ B : Subgroup Γ) : Set Γ) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

theorem mem_normalizer_centralizer {S : Subgroup Γ} {x : Γ} (hx : x ∈ normalizer (S : Set Γ)) :
    x ∈ normalizer ((centralizer (S : Set Γ) : Subgroup Γ) : Set Γ) := by
  have key : ∀ y : Γ, y ∈ normalizer (S : Set Γ) → ∀ c ∈ centralizer (S : Set Γ),
      y * c * y⁻¹ ∈ centralizer (S : Set Γ) := by
    intro y hy c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : y⁻¹ * s * y ∈ S := (mem_normalizer_iff''.1 hy s).1 hs
    have := hc _ hs'
    calc s * (y * c * y⁻¹) = y * ((y⁻¹ * s * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * s * y)) * y⁻¹ := by rw [this]
      _ = (y * c * y⁻¹) * s := by group
  rw [mem_normalizer_iff]
  intro c
  exact ⟨key x hx c, fun hc => by
    have := key x⁻¹ (inv_mem hx) _ hc
    simpa [mul_assoc] using this⟩

theorem mem_centralizer_preIn_iff (S : Subgroup Γ) {K' : Subgroup (MulAut ↥S)}
    (hK' : K' ≤ imgIn S (normalizer (S : Set Γ))) {v : Γ} (hv : v ∈ S) :
    v ∈ centralizer ((preIn S K' : Subgroup Γ) : Set Γ) ↔ ∀ k ∈ K', k ⟨v, hv⟩ = ⟨v, hv⟩ := by
  rw [mem_centralizer_iff]
  constructor
  · intro h k hk
    obtain ⟨g, hgN, rfl⟩ := (mem_imgIn_normalizer_iff S).1 (hK' hk)
    have hg : g ∈ preIn S K' := (mem_preIn_iff S K').2 ⟨hgN, hk⟩
    exact (actFun_fixes_iff S hgN ⟨v, hv⟩).2 (h g hg)
  · intro h g hg
    obtain ⟨hgN, hgK⟩ := (mem_preIn_iff S K').1 hg
    exact (actFun_fixes_iff S hgN ⟨v, hv⟩).1 (h _ hgK)

theorem mem_centralizerMod_preIn_iff (S : Subgroup Γ) {K' : Subgroup (MulAut ↥S)}
    (hK' : K' ≤ imgIn S (normalizer (S : Set Γ))) (W : Subgroup Γ) {v : Γ} (hv : v ∈ S) :
    v ∈ centralizerMod S W (preIn S K') ↔
      v ∈ normalizer (W : Set Γ) ∧ ∀ k ∈ K', ((k ⟨v, hv⟩ : ↥S) : Γ) * v⁻¹ ∈ W := by
  constructor
  · rintro ⟨-, hvN, h⟩
    refine ⟨hvN, fun k hk => ?_⟩
    obtain ⟨g, hgN, rfl⟩ := (mem_imgIn_normalizer_iff S).1 (hK' hk)
    have hg : g ∈ preIn S K' := (mem_preIn_iff S K').2 ⟨hgN, hk⟩
    have h1 := W.inv_mem (h g hg)
    rw [actFun_apply_coe S hgN]
    have e : (v * g * v⁻¹ * g⁻¹)⁻¹ = g * v * g⁻¹ * v⁻¹ := by group
    rw [e] at h1
    exact h1
  · rintro ⟨hvN, h⟩
    refine ⟨hv, hvN, fun y hy => ?_⟩
    obtain ⟨hyN, hyK⟩ := (mem_preIn_iff S K').1 hy
    have h1 := h _ hyK
    rw [actFun_apply_coe S hyN] at h1
    have e : v * y * v⁻¹ * y⁻¹ = (y * v * y⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem h1

end Generic

section Mod

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


@[expose] noncomputable def Qp (d : Data G) : Subgroup G := d.s56Q ⊓ CMt d

theorem mem_Qp_iff {g : G} : g ∈ Qp d ↔ g ∈ d.s56Q ∧ g ∈ d.M ∧ g * d.t = d.t * g := by
  unfold Qp CMt
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem Qp_le_Q : Qp d ≤ d.s56Q := inf_le_left

theorem Qp_le_CMt : Qp d ≤ CMt d := inf_le_right

theorem Qp_le_M : Qp d ≤ d.M := Qp_le_CMt.trans CMt_le_M

theorem Qp_le_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : Qp d ≤ Hg d :=
  Qp_le_CMt.trans (CMt_le_Hg h49 hd)

theorem exists_V_mul_Qp (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {q : G}
    (hq : q ∈ d.s56Q) : ∃ v ∈ d.s56V, v⁻¹ * q ∈ Qp d := by
  obtain ⟨v, hv, hvc⟩ := exists_V_mul h49 hd hz (Q_le_M h49 hd hq)
  exact ⟨v, hv, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (V_le_Q hv)) hq, hvc⟩⟩

theorem img_Qp (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    img d (Qp d) = img d d.s56Q := by
  refine le_antisymm (imgIn_mono _ Qp_le_Q) (fun x hx => ?_)
  obtain ⟨g, hgQ, hgN, rfl⟩ := (mem_imgIn_iff d.s56V d.s56Q).1 hx
  obtain ⟨v, hvV, hvc⟩ := exists_V_mul_Qp h49 hd hz hgQ
  refine (mem_imgIn_iff d.s56V _).2 ⟨v⁻¹ * g, hvc,
    mul_mem (inv_mem (le_normalizer hvV)) hgN, ?_⟩
  rw [actFun_mul d.s56V (inv_mem (le_normalizer hvV)) hgN, actFun_inv d.s56V (le_normalizer hvV),
    show actFun d.s56V v = 1 from star_V h10 hvV, inv_one, one_mul]

theorem Us_eq_img_Qp (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Us d = img d (Qp d) := by
  rw [Us_eq_img_Q h49 hd hz h10, img_Qp h49 hd hz h10]

theorem mem_Us_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {u : MulAut ↥d.s56V} : u ∈ Us d ↔ ∃ q ∈ Qp d, star d q = u := by
  rw [Us_eq_img_Qp h49 hd hz h10, img_eq, mem_imgIn_iff]
  constructor
  · rintro ⟨q, hq, -, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, Qp_le_Hg h49 hd hq, rfl⟩

theorem x5_mem_normalizer_Qp (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.x₅ ∈ normalizer ((Qp d : Subgroup G) : Set G) :=
  mem_normalizer_inf' (hd.s56_M_le_normalizer_Q h49 hd.s56_x5_mem_M)
    (Subgroup.le_normalizer (Xg_le_CMt hd (mem_zpowers d.x₅)))

theorem E_cent_Qp (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU16 : Nat.card (Us d) = 16) {e : G} (he : e ∈ d.E) (hc : ∀ q ∈ Qp d, q * e = e * q) :
    e ∈ zpowers d.z := by
  set R : Subgroup G := d.E ⊓ centralizer ((Qp d : Subgroup G) : Set G) with hR
  have hzR : zpowers d.z ≤ R := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨hd.s56_z_mem_E, ?_⟩
    rw [mem_centralizer_iff]
    intro q hq
    exact hd.s56_M_comm_zpowers (Qp_le_M hq) (mem_zpowers d.z)
  have hRE : R ≤ d.E := inf_le_left
  have hxR : d.x₅ ∈ normalizer (R : Set G) :=
    mem_normalizer_inf' (hd.s56_ME hd.s56_x5_mem_M)
      (mem_normalizer_centralizer (x5_mem_normalizer_Qp h49 hd))
  have heR : e ∈ R := Subgroup.mem_inf.2 ⟨he, mem_centralizer_iff.2 hc⟩
  rcases hd.s56_stable_sub_E hzR hRE hxR with h1 | h1
  · rw [h1] at heR
    exact heR
  · exfalso
    have hQV : Qp d ≤ d.s56V := by
      intro q hq
      refine Subgroup.mem_inf.2 ⟨Qp_le_Q hq, (Data.s56_mem_Q2_iff).2 ⟨Qp_le_M hq, fun e' he' => ?_⟩⟩
      have : e' ∈ R := by rw [h1]; exact he'
      exact ((mem_centralizer_iff.1 (Subgroup.mem_inf.1 this).2) q hq).symm
    have hUbot : Us d = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨q, hq, rfl⟩ := (mem_Us_iff h49 hd hz h10).1 hu
      rw [star_V h10 (hQV hq)]
      exact one_mem _
    rw [hUbot, Subgroup.card_bot] at hU16
    omega

theorem V_cent_Qp (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU16 : Nat.card (Us d) = 16) {v : G} (hv : v ∈ d.s56V) (hc : ∀ q ∈ Qp d, q * v = v * q) :
    v ∈ zpowers d.z ⊔ zpowers z₀ := by
  have hεE : d.s56Eps v ∈ d.E := hd.s56_V_eps_mem_E hv
  have hεc : ∀ q ∈ Qp d, q * d.s56Eps v = d.s56Eps v * q := by
    intro q hq
    obtain ⟨-, -, hqt⟩ := mem_Qp_iff.1 hq
    have h1 := hd.s56_eps_conj hqt v
    have h2 : q * v * q⁻¹ = v := by rw [hc q hq]; group
    rw [h2] at h1
    calc q * d.s56Eps v = (q * d.s56Eps v * q⁻¹) * q := by group
      _ = d.s56Eps v * q := by rw [← h1]
  have hεz : d.s56Eps v ∈ zpowers d.z := E_cent_Qp h49 hd hz h10 hU16 hεE hεc
  rcases eq_one_or_of_mem_zpowers hd.s56_z_sq hεz with h1 | h1
  · exact mem_sup_left (E_cent_Qp h49 hd hz h10 hU16 ((hd.s56_V_eps_eq_one_iff h49 hv).1 h1) hc)
  · have hvz : v * z₀ ∈ d.s56V := mul_mem hv hz.mem_V
    have hε1 : d.s56Eps (v * z₀) = 1 := by
      rw [hd.s56_eps_mul_Q2' hv.2 hz.mem_Q2, h1, hz.eps]
      exact hd.s56_z_sq
    have hvzE : v * z₀ ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 hvz).1 hε1
    have hvzc : ∀ q ∈ Qp d, q * (v * z₀) = (v * z₀) * q := by
      intro q hq
      have := hz.comm_Q q (Qp_le_Q hq)
      calc q * (v * z₀) = (q * v) * z₀ := by group
        _ = (v * q) * z₀ := by rw [hc q hq]
        _ = v * (q * z₀) := by group
        _ = v * (z₀ * q) := by rw [this]
        _ = (v * z₀) * q := by group
    have hvzz := E_cent_Qp h49 hd hz h10 hU16 hvzE hvzc
    have e : v = (v * z₀) * z₀⁻¹ := by group
    rw [e]
    exact mul_mem (mem_sup_left hvzz) (inv_mem (mem_sup_right (mem_zpowers z₀)))

theorem Zz_le_V (hd : d.Hyp) (h49 : d.Thm49Statement) (hz : d.S56Z0 z₀) : Zz d z₀ ≤ d.s56V :=
  sup_le (zpowers_le.2 (hd.s56_E_le_V h49 hd.s56_z_mem_E)) (zpowers_le.2 hz.mem_V)

theorem Zz_comm_Qp (hd : d.Hyp) (hz : d.S56Z0 z₀) {v : G} (hv : v ∈ Zz d z₀) {q : G}
    (hq : q ∈ Qp d) : q * v = v * q := by
  have hle : Zz d z₀ ≤ centralizer ((Qp d : Subgroup G) : Set G) := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · rw [mem_centralizer_iff]
      intro q hq
      exact hd.s56_M_comm_zpowers (Qp_le_M hq) (mem_zpowers d.z)
    · rw [mem_centralizer_iff]
      intro q hq
      exact hz.comm_Q q (Qp_le_Q hq)
  exact (mem_centralizer_iff.1 (hle hv) q hq)

theorem star_t_apply (h49 : d.Thm49Statement) (hd : d.Hyp) (v : ↥d.s56V) :
    ((star d d.t v : ↥d.s56V) : G) * (v : G)⁻¹ = d.s56Eps v.1 := by
  rw [star_eq, actFun_apply_coe d.s56V (t_mem_Hg h49 hd)]
  have h1 := hd.s56_conj_t v.1
  have ht := hd.t_mul_self
  have h2 : d.t * v.1 * d.t⁻¹ * (v.1)⁻¹ = d.s56Eps v.1 := by
    have : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht
    rw [this]
    calc d.t * v.1 * d.t * (v.1)⁻¹ = d.t * (v.1 * d.t * (v.1)⁻¹) := by group
      _ = d.t * (d.t * d.s56Eps v.1) := by rw [h1]
      _ = d.s56Eps v.1 := by rw [← mul_assoc, ht, one_mul]
  exact h2

theorem eps_mem_zpowers_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) {v : G} (hv : v ∈ d.s56V) :
    d.s56Eps v ∈ zpowers d.z ↔ v ∈ d.E ⊔ zpowers z₀ := by
  constructor
  · intro h
    rcases eq_one_or_of_mem_zpowers hd.s56_z_sq h with h1 | h1
    · exact mem_sup_left ((hd.s56_V_eps_eq_one_iff h49 hv).1 h1)
    · have hvz : v * z₀ ∈ d.s56V := mul_mem hv hz.mem_V
      have hε1 : d.s56Eps (v * z₀) = 1 := by
        rw [hd.s56_eps_mul_Q2' hv.2 hz.mem_Q2, h1, hz.eps]
        exact hd.s56_z_sq
      have hvzE : v * z₀ ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 hvz).1 hε1
      have e : v = (v * z₀) * z₀⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_left hvzE) (inv_mem (mem_sup_right (mem_zpowers z₀)))
  · intro h
    have hz2 : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
    have hz0c : ∀ e ∈ d.E, e * z₀ = z₀ * e := fun e he => (hz.cen he).symm
    rcases (Data.mem_sup_zpowers_iff hz2 hz0c).1 h with h1 | h1
    · rw [(hd.s56_V_eps_eq_one_iff h49 hv).2 h1]
      exact one_mem _
    · have hvz : z₀ * v ∈ d.s56V := mul_mem hz.mem_V hv
      have hε : d.s56Eps (z₀ * v) = 1 := (hd.s56_V_eps_eq_one_iff h49 hvz).2 h1
      rw [hd.s56_eps_mul_Q2' hz.mem_Q2 hv.2, hz.eps] at hε
      have : d.s56Eps v = d.z⁻¹ := eq_inv_of_mul_eq_one_right hε
      rw [this]
      exact inv_mem (mem_zpowers d.z)

theorem Us_le_Hs (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Us d ≤ imgIn d.s56V (normalizer (d.s56V : Set G)) := by
  rw [Us_eq_img_Qp h49 hd hz h10, img_eq]
  exact imgIn_le_range d.s56V (Qp d)

theorem star_t_mem_Hs (h49 : d.Thm49Statement) (hd : d.Hyp) :
    star d d.t ∈ imgIn d.s56V (normalizer (d.s56V : Set G)) :=
  actFun_mem_imgIn (t_mem_Hg h49 hd) (t_mem_Hg h49 hd)

theorem U0s_le_Hs (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    U0s d ≤ imgIn d.s56V (normalizer (d.s56V : Set G)) :=
  sup_le (Us_le_Hs h49 hd hz h10) (zpowers_le.2 (star_t_mem_Hs h49 hd))

theorem fix_Us_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU16 : Nat.card (Us d) = 16) {v : G} (hv : v ∈ d.s56V) :
    (∀ u ∈ Us d, u ⟨v, hv⟩ = ⟨v, hv⟩) ↔ v ∈ Zz d z₀ := by
  constructor
  · intro h
    apply V_cent_Qp h49 hd hz h10 hU16 hv
    intro q hq
    have := h (star d q) ((mem_Us_iff h49 hd hz h10).2 ⟨q, hq, rfl⟩)
    exact (actFun_fixes_iff d.s56V (Qp_le_Hg h49 hd hq) ⟨v, hv⟩).1 this
  · intro hvZ u hu
    obtain ⟨q, hq, rfl⟩ := (mem_Us_iff h49 hd hz h10).1 hu
    exact (actFun_fixes_iff d.s56V (Qp_le_Hg h49 hd hq) ⟨v, hv⟩).2 (Zz_comm_Qp hd hz hvZ hq)

theorem node17_1 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU16 : Nat.card (Us d) = 16) :
    d.s56V ⊓ centralizer ((Ug d : Subgroup G) : Set G) = Zz d z₀ := by
  ext v
  constructor
  · rintro ⟨hvV, hvC⟩
    exact (fix_Us_iff h49 hd hz h10 hU16 hvV).1
      ((mem_centralizer_preIn_iff d.s56V (Us_le_Hs h49 hd hz h10) hvV).1 hvC)
  · intro hvZ
    have hvV := Zz_le_V hd h49 hz hvZ
    exact ⟨hvV, (mem_centralizer_preIn_iff d.s56V (Us_le_Hs h49 hd hz h10) hvV).2
      ((fix_Us_iff h49 hd hz h10 hU16 hvV).2 hvZ)⟩

theorem star_t_fixes_z (h49 : d.Thm49Statement) (hd : d.Hyp) :
    star d d.t ⟨d.z, hd.s56_E_le_V h49 hd.s56_z_mem_E⟩ = ⟨d.z, hd.s56_E_le_V h49 hd.s56_z_mem_E⟩ :=
  (actFun_fixes_iff d.s56V (t_mem_Hg h49 hd) _).2
    (hd.L_comm_t (d.s56_E_le_L hd.s56_z_mem_E)).symm

theorem fix_U0s_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU16 : Nat.card (Us d) = 16) {v : G} (hv : v ∈ d.s56V) :
    (∀ u ∈ U0s d, u ⟨v, hv⟩ = ⟨v, hv⟩) ↔ v ∈ zpowers d.z := by
  have hzV : d.z ∈ d.s56V := hd.s56_E_le_V h49 hd.s56_z_mem_E
  constructor
  · intro h
    have hvZ : v ∈ Zz d z₀ :=
      (fix_Us_iff h49 hd hz h10 hU16 hv).1 (fun u hu => h u (mem_sup_left hu))
    have htv : d.t * v = v * d.t :=
      (actFun_fixes_iff d.s56V (t_mem_Hg h49 hd) ⟨v, hv⟩).1
        (h _ (mem_sup_right (mem_zpowers _)))
    have hε : d.s56Eps v = 1 := hd.s56_eps_of_comm htv.symm
    have hvE : v ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 hv).1 hε
    have hz2 : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
    have hzc : ∀ p ∈ zpowers d.z, p * z₀ = z₀ * p := fun p hp =>
      (hz.cen (hd.s56_zpowers_le_E hp)).symm
    rcases (Data.mem_sup_zpowers_iff hz2 hzc).1 hvZ with h1 | h1
    · exact h1
    · exfalso
      have hz0E : z₀ ∈ d.E := by
        have : z₀ = (z₀ * v) * v⁻¹ := by group
        rw [this]
        exact mul_mem (hd.s56_zpowers_le_E h1) (inv_mem hvE)
      have := (hd.s56_V_eps_eq_one_iff h49 hz.mem_V).2 hz0E
      rw [hz.eps] at this
      exact hd.s56_z_ne_one this
  · intro hvz u hu
    have hUz : ∀ u ∈ U0s d, u ⟨d.z, hzV⟩ = ⟨d.z, hzV⟩ := by
      have hle : U0s d ≤ MulAction.stabilizer (MulAut ↥d.s56V) (⟨d.z, hzV⟩ : ↥d.s56V) := by
        refine sup_le (fun u hu => ?_) ?_
        · exact (fix_Us_iff h49 hd hz h10 hU16 hzV).2 (mem_sup_left (mem_zpowers d.z)) u hu
        · rw [Subgroup.zpowers_le]
          exact star_t_fixes_z h49 hd
      exact fun u hu => hle hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hvz
    have hfix : u (⟨d.z, hzV⟩ ^ n) = ⟨d.z, hzV⟩ ^ n := by
      rw [map_zpow, hUz u hu]
    exact hfix

theorem node17_2 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU16 : Nat.card (Us d) = 16) :
    d.s56V ⊓ centralizer ((U0g d : Subgroup G) : Set G) = zpowers d.z := by
  ext v
  constructor
  · rintro ⟨hvV, hvC⟩
    exact (fix_U0s_iff h49 hd hz h10 hU16 hvV).1
      ((mem_centralizer_preIn_iff d.s56V (U0s_le_Hs h49 hd hz h10) hvV).1 hvC)
  · intro hvz
    have hvV : v ∈ d.s56V := hd.s56_E_le_V h49 (hd.s56_zpowers_le_E hvz)
    exact ⟨hvV, (mem_centralizer_preIn_iff d.s56V (U0s_le_Hs h49 hd hz h10) hvV).2
      ((fix_U0s_iff h49 hd hz h10 hU16 hvV).2 hvz)⟩

theorem Qp_comm_E0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {q : G} (hq : q ∈ Qp d) {e : G} (he : e ∈ d.E ⊔ zpowers z₀) :
    q * e * q⁻¹ * e⁻¹ ∈ zpowers d.z := by
  have hz2 : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hzc : ∀ p ∈ d.E, p * z₀ = z₀ * p := fun p hp => (hz.cen hp).symm
  have hqQ0 := (hd.s56_mem_Q0_iff h49).1 (Q_le_Q0 hd (Qp_le_Q hq))
  rcases (Data.mem_sup_zpowers_iff hz2 hzc).1 he with h1 | h1
  · exact hqQ0.2 e h1
  · have e_eq : e = z₀ * (z₀ * e) := by rw [← mul_assoc, hz2, one_mul]
    have hqz : q * z₀ * q⁻¹ = z₀ := by rw [hz.comm_Q q (Qp_le_Q hq)]; group
    have hw := hqQ0.2 _ h1
    have hwc : z₀ * (q * (z₀ * e) * q⁻¹ * (z₀ * e)⁻¹) = (q * (z₀ * e) * q⁻¹ * (z₀ * e)⁻¹) * z₀ :=
      hz.cen (hd.s56_zpowers_le_E hw)
    have e2 : q * e * q⁻¹ * e⁻¹ = z₀ * (q * (z₀ * e) * q⁻¹ * (z₀ * e)⁻¹) * z₀⁻¹ := by
      calc q * e * q⁻¹ * e⁻¹ = q * (z₀ * (z₀ * e)) * q⁻¹ * (z₀ * (z₀ * e))⁻¹ := by rw [← e_eq]
        _ = (q * z₀ * q⁻¹) * (q * (z₀ * e) * q⁻¹ * (z₀ * e)⁻¹) * z₀⁻¹ := by group
        _ = z₀ * (q * (z₀ * e) * q⁻¹ * (z₀ * e)⁻¹) * z₀⁻¹ := by rw [hqz]
    rw [e2, hwc]
    have : (q * (z₀ * e) * q⁻¹ * (z₀ * e)⁻¹) * z₀ * z₀⁻¹ = q * (z₀ * e) * q⁻¹ * (z₀ * e)⁻¹ := by group
    rw [this]
    exact hw

@[expose] noncomputable def Z1s (d : Data G) : Subgroup ↥d.s56V := (zpowers d.z).subgroupOf d.s56V

@[expose] noncomputable def E0s (d : Data G) (z₀ : G) : Subgroup ↥d.s56V :=
  (d.E ⊔ zpowers z₀).subgroupOf d.s56V

theorem Z1s_le_E0s (hd : d.Hyp) : Z1s d ≤ E0s d z₀ := by
  intro v hv
  have h1 : (v : G) ∈ zpowers d.z := hv
  exact mem_sup_left (hd.s56_zpowers_le_E h1)

theorem Us_le_trivOn (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Us d ≤ trivOn (Z1s d) (E0s d z₀) (Z1s_le_E0s hd) := by
  intro u hu
  obtain ⟨q, hq, rfl⟩ := (mem_Us_iff h49 hd hz h10).1 hu
  rw [mem_trivOn]
  intro c hc
  have hc' : (c : G) ∈ d.E ⊔ zpowers z₀ := hc
  show (((star d q c * c⁻¹ : ↥d.s56V)) : G) ∈ zpowers d.z
  have : (((star d q c * c⁻¹ : ↥d.s56V)) : G) = q * (c : G) * q⁻¹ * (c : G)⁻¹ := by
    show ((star d q c : ↥d.s56V) : G) * ((c : ↥d.s56V) : G)⁻¹ = _
    rw [star_eq, actFun_apply_coe d.s56V (Qp_le_Hg h49 hd hq)]
  rw [this]
  exact Qp_comm_E0 h49 hd hz h10 hq hc'

theorem star_t_mem_trivOn (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) : star d d.t ∈ trivOn (Z1s d) (E0s d z₀) (Z1s_le_E0s hd) := by
  rw [mem_trivOn]
  intro c hc
  have hc' : (c : G) ∈ d.E ⊔ zpowers z₀ := hc
  show (((star d d.t c * c⁻¹ : ↥d.s56V)) : G) ∈ zpowers d.z
  have : (((star d d.t c * c⁻¹ : ↥d.s56V)) : G) = d.s56Eps (c : G) := by
    rw [← star_t_apply h49 hd c]
    rfl
  rw [this]
  exact (eps_mem_zpowers_iff h49 hd hz h10 c.2).2 hc'

theorem U0s_le_trivOn (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    U0s d ≤ trivOn (Z1s d) (E0s d z₀) (Z1s_le_E0s hd) :=
  sup_le (Us_le_trivOn h49 hd hz h10) (zpowers_le.2 (star_t_mem_trivOn h49 hd hz h10))

theorem trivial_U0s_iff (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {v : G} (hv : v ∈ d.s56V) :
    (∀ u ∈ U0s d, ((u ⟨v, hv⟩ : ↥d.s56V) : G) * v⁻¹ ∈ zpowers d.z) ↔ v ∈ d.E ⊔ zpowers z₀ := by
  constructor
  · intro h
    have h1 := h (star d d.t) (mem_sup_right (mem_zpowers _))
    have h2 : ((star d d.t ⟨v, hv⟩ : ↥d.s56V) : G) * v⁻¹ = d.s56Eps v :=
      star_t_apply h49 hd ⟨v, hv⟩
    rw [h2] at h1
    exact (eps_mem_zpowers_iff h49 hd hz h10 hv).1 h1
  · intro hvE u hu
    have := mem_trivOn.1 (U0s_le_trivOn h49 hd hz h10 hu) ⟨v, hv⟩ hvE
    exact this

theorem E0_le_V (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    d.E ⊔ zpowers z₀ ≤ d.s56V :=
  sup_le (hd.s56_E_le_V h49) (zpowers_le.2 hz.mem_V)

theorem node17_3 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    centralizerMod d.s56V (zpowers d.z) (U0g d) = d.E ⊔ zpowers z₀ := by
  ext v
  constructor
  · intro hv
    have hvV : v ∈ d.s56V := hv.1
    exact (trivial_U0s_iff h49 hd hz h10 hvV).1
      ((mem_centralizerMod_preIn_iff d.s56V (U0s_le_Hs h49 hd hz h10) (zpowers d.z) hvV).1 hv).2
  · intro hv
    have hvV : v ∈ d.s56V := E0_le_V h49 hd hz hv
    refine (mem_centralizerMod_preIn_iff d.s56V (U0s_le_Hs h49 hd hz h10) (zpowers d.z) hvV).2
      ⟨?_, (trivial_U0s_iff h49 hd hz h10 hvV).2 hv⟩
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro w hw
    exact (hd.s56_M_comm_zpowers (d.s56_V_le_M hvV) hw).symm

end Mod

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
