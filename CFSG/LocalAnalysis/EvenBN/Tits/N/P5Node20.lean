module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S20Set
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KMain
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Six20
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5StarG

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem img_Ig_inf (h49 : d.Thm49Statement) (hd : d.Hyp) {y₁ : G}
    (hk : KSet (Hs d) (img d (CMt d)) (Us d) (Ks d) (W0s d) (Ws d) (star d d.x₅) (star d y₁)
      (star d d.t)) :
    img d (Ig d ⊓ centralizer ({d.t} : Set G)) = img d (CMt d) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨g, hg, hgN, rfl⟩ := (mem_imgIn_iff d.s56V _).1 hx
    rw [hk.C_cent]
    refine ⟨mem_centralizer_singleton_iff.2 ?_, actFun_mem_imgIn hgN hgN⟩
    exact actFun_comm_of_comm d.s56V (mem_centralizer_singleton_iff.1 hg.2)
  · intro x hx
    obtain ⟨g, hgC, hgN, rfl⟩ := (mem_imgIn_iff d.s56V _).1 hx
    have hgI : g ∈ Ig d :=
      (mem_preIn_iff d.s56V (Is d)).2 ⟨hgN, hk.C_le_NHs (actFun_mem_imgIn hgC hgN)⟩
    exact actFun_mem_imgIn (K := Ig d ⊓ centralizer ({d.t} : Set G)) ⟨hgI, hgC.2⟩ hgN

theorem step20_holds : Step20 := by
  intro G _ _ d z₀ h49 hd hz h09 h14 h17s h17 h18 h19
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨y₀, hy₀⟩⟩ := h09
  obtain ⟨-, -, -, hSC⟩ := h14
  have hk := kset_of_nodes h49 hd hz h17s h17 h18 h19 hy₀
  have hmax := hk.maxElemAbelian2_K
  have hTI : sylT d ≤ Ig d := by
    intro g hg
    have hgC : g ∈ CMt d := sylT_le_CMt hd hg
    have hgN : g ∈ normalizer (d.s56V : Set G) := CMt_le_Hg h49 hd hgC
    exact (mem_preIn_iff d.s56V (Is d)).2 ⟨hgN, hk.C_le_NHs (actFun_mem_imgIn hgC hgN)⟩
  have h620 : ∀ h ∈ Hg d, h * d.t * h⁻¹ ∈ Ig d →
      (zpowers (star d (h * d.t * h⁻¹)) ⊔
          (Ws d ⊓ centralizer ({star d (h * d.t * h⁻¹)} : Set (MulAut ↥d.s56V))) =
        (U0s d).map (MulAut.conj (star d h)).toMonoidHom) ∧ h ∈ Ig d := by
    intro h hhH hth
    have hs : star d (h * d.t * h⁻¹) ∈ normalizer ((Ws d : Subgroup _) : Set (MulAut ↥(d.s56V))) :=
      ((mem_preIn_iff d.s56V (Is d)).1 hth).2.1
    have hgHs : star d h ∈ Hs d := actFun_mem_imgIn hhH hhH
    have hconj : star d (h * d.t * h⁻¹) = star d h * star d d.t * (star d h)⁻¹ :=
      actFun_conj d.s56V hhH (t_mem_Hg h49 hd)
    obtain ⟨h1, h2⟩ := hk.six20 hmax hgHs (by rw [← hconj]; exact hs)
    refine ⟨?_, (mem_preIn_iff d.s56V (Is d)).2 ⟨hhH, h2, hgHs⟩⟩
    rw [hconj]
    exact h1
  refine ⟨hmax, fun T' hT' => hk.maxElemAbelian2_W_sup hT', hTI, hk.W_inf_centralizer_t,
    hk.sylow_W, ?_, h620, ?_⟩
  ·
    intro y₁ hy
    have hk' := kset_of_nodes h49 hd hz h17s h17 h18 h19 hy
    have hX := img_Xg h49 hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · show imgIn (Ws d) (img d (Ig d ⊓ centralizer ({d.t} : Set G))) = _
      rw [img_Ig_inf h49 hd hk']
      exact hk'.imgIn_C_eq
    · show _ = zpowers (actFun (Ws d) (star d d.t)) ⊔
        (imgIn (Ws d) (img d (Xg d)) ⊔ zpowers (actFun (Ws d) (star d y₁)))
      rw [hX]
      exact hk'.centralizer_alpha_eq
    · show zpowers (actFun (Ws d) (star d d.t)) ⊓
        (imgIn (Ws d) (img d (Xg d)) ⊔ zpowers (actFun (Ws d) (star d y₁))) = ⊥
      rw [hX]
      exact hk'.inf_alpha_bot
    · intro a ha
      have ha' : a ∈ (imgIn (Ws d) (zpowers (star d d.x₅)) ⊔
          zpowers (actFun (Ws d) (star d y₁)) : Subgroup (MulAut ↥(Ws d))) := by
        rw [← hX]; exact ha
      exact hk'.comm_alpha a ha'
  ·
    obtain ⟨h, hhH, hh⟩ := hSC
    have htT : d.t ∈ sylT d := t_mem_sylT hd
    have hvT : d.pv 2 ∈ sylT d := pv2_mem_sylT hd
    have htvI : d.t * d.pv 2 ∈ Ig d := mul_mem (hTI htT) (hTI hvT)
    have hIs : star d (d.t * d.pv 2) ∈ Is d := ((mem_preIn_iff d.s56V (Is d)).1 htvI).2
    have hhtI : h * d.t * h⁻¹ ∈ Ig d := by
      refine (mem_preIn_iff d.s56V (Is d)).2 ⟨?_, ?_⟩
      · exact mul_mem (mul_mem hhH (t_mem_Hg h49 hd)) (Subgroup.inv_mem _ hhH)
      · show star d (h * d.t * h⁻¹) ∈ Is d
        rw [hh]; exact hIs
    have hhI : h ∈ Ig d := (h620 h hhH hhtI).2
    refine ⟨h, hhI, ?_⟩
    have hhN : star d h ∈ normalizer ((Ws d : Subgroup _) : Set (MulAut ↥d.s56V)) :=
      ((mem_preIn_iff d.s56V (Is d)).1 hhI).2.1
    have htN : star d d.t ∈ normalizer ((Ws d : Subgroup _) : Set (MulAut ↥d.s56V)) :=
      hk.t_mem_normalizer_W
    show actFun (Ws d) (star d (d.t * d.pv 2)) =
      actFun (Ws d) (star d h) * actFun (Ws d) (star d d.t) * (actFun (Ws d) (star d h))⁻¹
    rw [← hh, ← actFun_conj (Ws d) hhN htN]
    have : star d (h * d.t * h⁻¹) = star d h * star d d.t * (star d h)⁻¹ :=
      actFun_conj d.s56V hhH (t_mem_Hg h49 hd)
    rw [this]

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
