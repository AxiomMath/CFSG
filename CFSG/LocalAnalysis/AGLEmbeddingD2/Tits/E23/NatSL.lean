module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SLAgree
public import CFSG.CGT.PushingUpLit.BHS5.SLFixed
public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixGen
public import CFSG.CGT.PushingUpLit.BHS5.JStepSL

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS.NatSL2
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commutator_ne_bot_of_sl {E A : Subgroup (MulAut V)} {n : ℕ}
    (hnat : IsSLNatSection E (commV E) (commV E ⊓ fixV E) n) (hAE : A ≤ E) (hA : A ≠ ⊥) :
    ⁅E, A⁆ ≠ ⊥ := by
  intro hc
  apply hA
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine IsSLNatSection.eq_one_of_central hnat (hAE ha) fun y hy => ?_
  have h1 : ⁅y, a⁆ ∈ ⁅E, A⁆ := Subgroup.commutator_mem_commutator hy ha
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

omit [Finite V] in
theorem eq_one_of_slType2 {D : Set (Subgroup (MulAut V))} {E : Subgroup (MulAut V)}
    (hSL : SLType2 D E) {e : MulAut V} (he : e ∈ E)
    (htriv : ∀ w ∈ commV E, e w * w⁻¹ ∈ fixV E) : e = 1 := by
  obtain ⟨n, -, ⟨hinv, θ, β, hsurj, hker, hequiv⟩, -, -⟩ := hSL
  have hθ : θ ⟨e, he⟩ = 1 := by
    refine CFSG.QuasithinUnique.Setup.Campbell.eq_one_of_forall_smul_vec fun y => ?_
    obtain ⟨p, hp⟩ := hsurj (Multiplicative.ofAdd y)
    have hep : e p ∈ commV E := hinv e he p p.2
    have hk : (⟨e p, hep⟩ : ↥(commV E)) * p⁻¹ ∈ β.ker := by
      rw [hker]
      refine Subgroup.mem_subgroupOf.2 ⟨(commV E).mul_mem hep ((commV E).inv_mem p.2), ?_⟩
      exact htriv p p.2
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    have h1 := hequiv ⟨e, he⟩ p hep
    rw [hk, hp] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd, toAdd_ofAdd] at h2
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact h2.symm
  have : (⟨e, he⟩ : ↥E) = 1 := θ.injective (by rw [hθ, map_one])
  exact congrArg Subtype.val this

variable {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}
  (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)

include h hV hF

theorem exists_fixed_of_slType2 {E : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    (hSL : SLType2 (Hyp51.offSet P) E) {R : Subgroup (MulAut V)} (hR : R ∈ Hyp51.offSet P)
    (hRE : R ≤ E) : ∃ w ∈ commV E, w ∈ fixV R ∧ w ∉ fixV E := by
  have h43 := h.hyp43 hV
  obtain ⟨n, hn, hnat, -, hsyl⟩ := hSL
  obtain ⟨u, hu, hufix, hunfix⟩ := exists_fixed_commV_sl hV hn (hF.le_P h hV hE)
    (hF.isSubnormal h hV hE) hR.1 hR.2.1 hnat
    (commutator_ne_bot_of_sl hnat hRE (h43.ne_bot R hR)) ((hsyl R).1 ⟨hR, hRE⟩)
    (isPGroup_of_isElemAbelian2 (h43.elemAb R hR)) (hRE.trans Subgroup.le_normalizer)
    Subgroup.le_normalizer
  exact ⟨u, hu, hufix, hunfix⟩

theorem exists_agree_of_slType2 {E : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    (hSL : SLType2 (Hyp51.offSet P) E) {R : Subgroup (MulAut V)} (hR : R ∈ Hyp51.offSet P)
    (hRE : R ≤ E) {x : MulAut V} (hxE : conjSub x E = E) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hxfix : ∀ w ∈ commV E, w ∈ fixV R → x w = w) :
    ∃ u ∈ R, ∀ w ∈ commV E, x w * (u w)⁻¹ ∈ fixV E := by
  classical
  have h43 := h.hyp43 hV
  obtain ⟨n, hn, hnat, -, hsyl⟩ := id hSL
  set W := commV E with hWdef
  have hEst : E ≤ stabSub W := Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hEcen : E ⊓ centSub W = ⊥ := IsSLNatSection.inf_centSub_eq_bot hnat
  have hL := isSLNatSection_autSub hnat hEst
  obtain ⟨D⟩ := IsSLNatSection.nonempty_natData hL (by omega)
  obtain ⟨hAN, hAE, hcardA, hquad, hidx⟩ := two_sixteen_sl hV hn hR.2.1 hR.1 (hF.le_P h hV hE)
    (hF.isSubnormal h hV hE) hnat (commutator_ne_bot_of_sl hnat hRE (h43.ne_bot R hR))
  have hAst : R ≤ stabSub W := hAN.trans (normalizer_commV_le_stabSub E)
  have hG := sylowGood_autSub hn hAst hL hAE hcardA hquad hidx
  have hRsyl : IsSylowOf 2 R E := (hsyl R).1 ⟨hR, hRE⟩
  have hRbar := isSylowOf_autSub hEst hEcen hRsyl
  obtain ⟨w₀, hw₀, hRw⟩ := D.exists_stab_of_sylow hRbar
  have hfixR : fixV (D.stab w₀) = D.Vw w₀ := D.fixV_stab hG hw₀
  have hxE' : conjSub x⁻¹ E = E := by
    conv_lhs => rw [← hxE]
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hxst : x ∈ stabSub W := by
    intro u
    constructor
    · intro hu
      have := map_mem_commV_conj E x⁻¹ hu
      rwa [hxE', ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at this
    · intro hu
      have := map_mem_commV_conj E x hu
      rwa [hxE] at this
  have hxst' : x⁻¹ ∈ stabSub W := (stabSub W).inv_mem hxst
  set y : MulAut ↥W := resHom W ⟨x, hxst⟩ with hy
  have hconj : ∀ z : MulAut V, ∀ hz : z ∈ stabSub W, conjSub z E = E →
      ∀ l ∈ autSub E W, resHom W ⟨z, hz⟩ * l * (resHom W ⟨z, hz⟩)⁻¹ ∈ autSub E W := by
    intro z hz hzE l hl
    obtain ⟨e, heE, rfl⟩ := mem_autSub.1 hl
    refine mem_autSub.2 ⟨⟨z, hz⟩ * e * ⟨z, hz⟩⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have := mem_conjSub_of_mem (g := z) heE
    rw [hzE] at this
    exact this
  have hyL : ∀ l ∈ autSub E W, y * l * y⁻¹ ∈ autSub E W := hconj x hxst hxE
  have hyL' : ∀ l ∈ autSub E W, y⁻¹ * l * y ∈ autSub E W := by
    intro l hl
    have := hconj x⁻¹ hxst' hxE' l hl
    have e1 : resHom W ⟨x⁻¹, hxst'⟩ = y⁻¹ := by
      rw [hy, ← map_inv]
      rfl
    rw [e1, inv_inv] at this
    exact this
  have hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx2
    refine ⟨k, ?_⟩
    rw [hy, ← map_pow]
    have : (⟨x, hxst⟩ : ↥(stabSub W)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hyfix : ∀ v ∈ D.Vw w₀, y v = v := by
    intro v hv
    rw [← hfixR, ← hRw] at hv
    have hvR : (v : V) ∈ fixV R := by
      intro r hr
      have := hv (resHom W ⟨r, hAst hr⟩) (mem_autSub.2 ⟨⟨r, hAst hr⟩, hr, rfl⟩)
      exact congrArg Subtype.val this
    exact Subtype.ext (hxfix v v.2 hvR)
  obtain ⟨g, hgw, hgv⟩ := E23.NatSL2.NatData.exists_agree D hw₀ hyL hyL' hy2 hyfix
  have hgst : g ∈ stabVec w₀ := by
    rw [mem_stabVec, smul_def']
    exact hgw
  have hιR : D.ι g ∈ autSub R W := by
    rw [hRw]
    exact D.ι_mem_stab_iff.2 hgst
  obtain ⟨u', hu'R, hu'⟩ := mem_autSub.1 hιR
  refine ⟨u', hu'R, fun w hw => ?_⟩
  set w' : ↥W := ⟨w, hw⟩
  have hvec : D.vec (y w' * (resHom W u' w')⁻¹) = 0 := by
    rw [D.vec_div, hgv, hu', D.vec_ι, smul_def', sub_self]
  have hc := (D.vec_eq_zero_iff _).1 hvec
  intro e he
  have := hc (resHom W ⟨e, hEst he⟩) (mem_autSub.2 ⟨⟨e, hEst he⟩, he, rfl⟩)
  exact congrArg Subtype.val this

end CFSG.AGLEmbeddingD2.Tits.E23
