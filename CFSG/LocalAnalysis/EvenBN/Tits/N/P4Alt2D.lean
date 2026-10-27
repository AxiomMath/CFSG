module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Setup
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Alt2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Alt2D

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


@[expose] noncomputable def Es (d : Data G) : Subgroup ↥d.s56V := d.E.subgroupOf d.s56V

@[expose] noncomputable def zV (h49 : d.Thm49Statement) (hd : d.Hyp) : ↥d.s56V :=
  ⟨d.z, hd.s56_E_le_V h49 hd.s56_z_mem_E⟩

theorem Z1s_eq (h49 : d.Thm49Statement) (hd : d.Hyp) : Z1s d = zpowers (zV h49 hd) := by
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (show (v : G) ∈ zpowers d.z from hv)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa [zV] using hn)⟩
  · intro hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (⟨n, by simp [zV]⟩ : ((zV h49 hd ^ n : ↥d.s56V) : G) ∈ zpowers d.z)

theorem V_comm (h10 : Node10 d z₀) (a b : ↥d.s56V) : a * b = b * a :=
  Subtype.ext (h10.comm_V a.2 b.2)

theorem V_sq (h10 : Node10 d z₀) (a : ↥d.s56V) : a * a = 1 :=
  Subtype.ext (h10.sq_V a.2)

theorem star_t_fixes_E (h49 : d.Thm49Statement) (hd : d.Hyp) {e : ↥d.s56V} (he : e ∈ Es d) :
    star d d.t e = e :=
  (actFun_fixes_iff d.s56V (t_mem_Hg h49 hd) e).2 (hd.L_comm_t (d.s56_E_le_L he)).symm

theorem star_t_mul_mem_Es (h49 : d.Thm49Statement) (hd : d.Hyp) (l : ↥d.s56V) :
    star d d.t l * l⁻¹ ∈ Es d := by
  show ((star d d.t l * l⁻¹ : ↥d.s56V) : G) ∈ d.E
  have : ((star d d.t l * l⁻¹ : ↥d.s56V) : G) = d.s56Eps (l : G) := star_t_apply h49 hd l
  rw [this]
  exact hd.s56_V_eps_mem_E l.2

theorem exists_star_t_eq (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {e : ↥d.s56V}
    (he : e ∈ Es d) : ∃ l : ↥d.s56V, star d d.t l * l⁻¹ = e := by
  obtain ⟨v, hv, hve⟩ := hd.s56_V_eps_surj h49 hz (e : G) he
  refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
  show ((star d d.t ⟨v, hv⟩ : ↥d.s56V) : G) * ((⟨v, hv⟩ : ↥d.s56V) : G)⁻¹ = (e : G)
  rw [star_t_apply h49 hd ⟨v, hv⟩]
  exact hve

theorem Us_faithful_E (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    ∀ u ∈ Us d, (∀ e ∈ Es d, u e = e) → u = 1 := by
  intro u hu hfix
  obtain ⟨q, hq, rfl⟩ := (mem_Us_iff h49 hd hz h10).1 hu
  obtain ⟨hqQ, hqM, -⟩ := mem_Qp_iff.1 hq
  have hqQ2 : q ∈ d.s56Q2 := by
    refine (Data.s56_mem_Q2_iff).2 ⟨hqM, fun e he => ?_⟩
    have hV : e ∈ d.s56V := hd.s56_E_le_V h49 he
    have := (actFun_fixes_iff d.s56V (Qp_le_Hg h49 hd hq) ⟨e, hV⟩).1 (hfix ⟨e, hV⟩ he)
    exact this.symm
  have hqV : q ∈ d.s56V := Subgroup.mem_inf.2 ⟨hqQ, hqQ2⟩
  exact star_V h10 hqV

theorem exists_Es_notin_Z1s (h49 : d.Thm49Statement) (hd : d.Hyp) : ∃ e ∈ Es d, e ∉ Z1s d := by
  by_contra hno
  push Not at hno
  have hle : d.E ≤ zpowers d.z := by
    intro e he
    exact hno ⟨e, hd.s56_E_le_V h49 he⟩ he
  have := Subgroup.card_le_of_le hle
  rw [hd.A_facts.1, hd.s56_card_zpowers_z] at this
  omega

theorem eq_one_or_zV (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀) {ζ : ↥d.s56V}
    (hζ : ζ ∈ Z1s d) : ζ = 1 ∨ ζ = zV h49 hd := by
  rw [Z1s_eq h49 hd] at hζ
  exact eq_one_or_eq_of_mem_zpowers (V_sq h10 _) hζ

theorem transv_facts (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀) {β : G}
    (hβH : β ∈ Hg d) (hTr : IsTransv β d.s56V d.z (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z)) :
    star d β * star d β = 1 ∧ star d β ≠ 1 ∧ star d β (zV h49 hd) = zV h49 hd ∧
      ∀ l : ↥d.s56V, star d β l * l⁻¹ ∈ Z1s d := by
  obtain ⟨-, hcax, ⟨y₀, hy₀V, hy₀ax⟩, hall⟩ := hTr
  have hzV : d.z ∈ d.s56V := hd.s56_E_le_V h49 hd.s56_z_mem_E
  have hβconj : ∀ l : ↥d.s56V, ((star d β l : ↥d.s56V) : G) = β * (l : G) * β⁻¹ := fun l => by
    rw [star_eq, actFun_apply_coe d.s56V hβH]
  have hfixz : star d β (zV h49 hd) = zV h49 hd := by
    apply Subtype.ext
    rw [hβconj]
    exact ((hall d.z hzV).2).2 hcax
  have hZ : ∀ l : ↥d.s56V, star d β l * l⁻¹ ∈ Z1s d := by
    intro l
    show ((star d β l * l⁻¹ : ↥d.s56V) : G) ∈ zpowers d.z
    have : ((star d β l * l⁻¹ : ↥d.s56V) : G) = β * (l : G) * β⁻¹ * (l : G)⁻¹ := by
      show ((star d β l : ↥d.s56V) : G) * (l : G)⁻¹ = _
      rw [hβconj]
    rw [this]
    rcases ((hall l l.2).1) with h | h
    · rw [h]; simp
    · rw [h]
      have hc : (l : G) * d.z * (l : G)⁻¹ = d.z := by
        have := h10.comm_V l.2 hzV
        rw [this]; group
      rw [hc]
      exact mem_zpowers d.z
  refine ⟨?_, ?_, hfixz, hZ⟩
  · refine MulEquiv.ext (fun l => ?_)
    obtain ⟨ζ, hζ, hζdef⟩ : ∃ ζ ∈ Z1s d, star d β l = ζ * l :=
      ⟨star d β l * l⁻¹, hZ l, by group⟩
    have hζfix : star d β ζ = ζ := by
      rcases eq_one_or_zV h49 hd h10 hζ with h | h
      · rw [h]; exact map_one _
      · rw [h]; exact hfixz
    show star d β (star d β l) = (1 : MulAut ↥d.s56V) l
    rw [hζdef, map_mul, hζfix, hζdef, ← mul_assoc, V_sq h10 ζ, one_mul]
    rfl
  · intro h1
    have h2 : star d β ⟨y₀, hy₀V⟩ = ⟨y₀, hy₀V⟩ := by rw [h1]; rfl
    have h3 : β * y₀ * β⁻¹ = y₀ := by
      have := congrArg Subtype.val h2
      rwa [hβconj] at this
    exact hy₀ax (((hall y₀ hy₀V).2).1 h3)

theorem pv7_star (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    star d (d.pv 7) ∈ Us d ∧ star d (d.pv 7) ≠ 1 ∧ d.pv 7 ∈ Hg d := by
  have hQ : d.pv 7 ∈ d.s56Q := hd.s56_F_le_Q h49 hd.s56_pv7_mem_F
  have hH : d.pv 7 ∈ Hg d := M_le_Hg h49 hd (Q_le_M h49 hd hQ)
  refine ⟨?_, ?_, hH⟩
  · rw [Us_eq_img_Q h49 hd hz h10]
    exact actFun_mem_imgIn hQ hH
  · intro h1
    have hc : d.pv 7 ∈ centralizer (d.s56V : Set G) := (actFun_eq_one_iff d.s56V hH).1 h1
    have hV : d.pv 7 ∈ d.s56V := by
      rw [← Q_inf_Cv h49 hd h10]
      exact Subgroup.mem_inf.2 ⟨hQ, hc⟩
    have hQ2 : d.pv 7 ∈ d.s56Q2 := hV.2
    have h2 := ((Data.s56_mem_Q2_iff).1 hQ2).2 (d.pv 8) (Data.s56_pv8_mem_E d)
    have hz1 := Data.s56_pv7_conj_pv8 d
    have h3 : d.pv 7 * d.pv 8 * (d.pv 7)⁻¹ = d.pv 8 := by
      rw [← h2]
      group
    rw [h3] at hz1
    apply hd.s56_z_ne_one
    exact (mul_eq_left.1 hz1.symm)

theorem fusion_t_pv7 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hSt : StarConj d (d.t * d.pv 7)) :
    ∃ h ∈ Hs d, ∃ u₀ ∈ Us d, u₀ ≠ 1 ∧ h * star d d.t * h⁻¹ = star d d.t * u₀ := by
  obtain ⟨hu₀, hu₀1, hH7⟩ := pv7_star h49 hd hz h10
  obtain ⟨h, hh, hst⟩ := hSt
  refine ⟨star d h, actFun_mem_imgIn hh hh, star d (d.pv 7), hu₀, hu₀1, ?_⟩
  have h1 : star d (h * d.t * h⁻¹) = star d h * star d d.t * (star d h)⁻¹ :=
    actFun_conj d.s56V hh (t_mem_Hg h49 hd)
  have h2 : star d (d.t * d.pv 7) = star d d.t * star d (d.pv 7) :=
    actFun_mul d.s56V (t_mem_Hg h49 hd) hH7
  rw [← h1, hst, h2]

theorem no_alt2 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hU : IsElemAbelian 2 (Us d)) (hU16 : Nat.card (Us d) = 16) {y₁ : G} (hy : IsV1 d z₀ y₁)
    (h17c : img d (CMt d) = zpowers (star d d.t) ⊔ (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁)))
    (h17i : zpowers (star d d.t) ⊓ (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁)) = ⊥)
    (h17t : ∀ a ∈ (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)),
      star d d.t * a = a * star d d.t)
    (hSt : StarConj d (d.t * d.pv 7)) {β : G} (hβH : β ∈ Hg d)
    (hCs : centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d =
      img d (CMt d) ⊔ zpowers (star d β))
    (hβi : img d (CMt d) ⊓ zpowers (star d β) = ⊥)
    (hβc : ∀ c ∈ img d (CMt d), c * star d β = star d β * c)
    (hTr : IsTransv β d.s56V d.z (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z))
    (hCV : d.s56V ⊓ centralizer ({d.t * β} : Set G) = d.E ⊔ zpowers z₀) : False := by
  have hF := isF20_Us h49 hd hz h10 hU hU16 hy
  have hPe := P_eq h49 hd y₁
  have hPle : Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) ≤ img d (CMt d) := by
    have : Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) ≤ img d (CMt d) := by
      refine sup_le (sup_le (Us_le_img_CMt h49 hd hz) (imgIn_mono _ (Xg_le_CMt hd))) ?_
      rw [star_eq, ← imgIn_zpowers d.s56V (y1_mem_Hg h49 hd hy)]
      exact imgIn_mono _ (zpowers_le.2 (hy.mem_CMt hd))
    exact this
  rw [hPe] at h17c h17i h17t hPle
  obtain ⟨hββ, hβ1, hβz, hβZ⟩ := transv_facts h49 hd h10 hβH hTr
  have htC : star d d.t ∈ img d (CMt d) :=
    actFun_mem_imgIn (t_mem_CMt (d := d)) (t_mem_Hg h49 hd)
  have hHt : d.t * β ∈ normalizer (d.s56V : Set G) :=
    mul_mem (t_mem_Hg h49 hd) hβH
  refine alt2_false (L := ↥d.s56V) (V_comm h10) (Z1 := Z1s d) (E := Es d) (E0 := E0s d z₀)
    (z := zV h49 hd) (Z1s_eq h49 hd) (fun h => hd.s56_z_ne_one (congrArg Subtype.val h))
    (V_sq h10 _) (fun v hv => hd.s56_zpowers_le_E hv) (fun v hv => mem_sup_left hv) hF (Hs d)
    (star_t_mul_self h49 hd) h17t h17i hββ hβ1 (hβc _ htC).symm
    (fun p hp => (hβc p (hPle hp)).symm) ?_ ?_ ?_ ?_ ?_ hβZ (star_t_mul_mem_Es h49 hd)
    (fun e he => star_t_fixes_E h49 hd he) (fun e he => exists_star_t_eq h49 hd hz he)
    (Us_faithful_E h49 hd hz h10) (exists_Es_notin_Z1s h49 hd) ?_ ?_
    (fusion_t_pv7 h49 hd hz h10 hSt)
  ·
    rw [h17c] at hβi
    rw [inf_comm]
    exact hβi
  · rw [h17c] at hCs
    exact hCs
  · intro u hu ζ hζ
    exact (fix_Us_iff h49 hd hz h10 hU16 ζ.2).2 (mem_sup_left hζ) u hu
  · intro l hl
    exact (fix_U0s_iff h49 hd hz h10 hU16 l.2).1 hl
  · intro l
    constructor
    · intro hl
      exact (trivial_U0s_iff h49 hd hz h10 l.2).1 hl
    · intro hl u hu
      exact (trivial_U0s_iff h49 hd hz h10 l.2).2 hl u hu
  ·
    intro e he
    have he' : (e : G) ∈ d.s56V ⊓ centralizer ({d.t * β} : Set G) := by
      rw [hCV]
      exact he
    have h1 : (d.t * β) * (e : G) = (e : G) * (d.t * β) :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 he').2).symm
    have h2 := (actFun_fixes_iff d.s56V hHt e).2 h1
    rw [actFun_mul d.s56V (t_mem_Hg h49 hd) hβH] at h2
    exact h2
  · refine ⟨⟨z₀, hz.mem_V⟩, mem_sup_right (mem_zpowers z₀), ?_, ?_⟩
    · intro h
      exact t_not_comm_z0 hd hz
        ((actFun_fixes_iff d.s56V (t_mem_Hg h49 hd) ⟨z₀, hz.mem_V⟩).1 h)
    · intro u hu
      exact (fix_Us_iff h49 hd hz h10 hU16 hz.mem_V).2 (mem_sup_right (mem_zpowers z₀)) u hu

end Alt2D

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
