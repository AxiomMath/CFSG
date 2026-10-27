module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBD6
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D7

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace S3Sec29JB

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J R : Subgroup G}

theorem exists_B0_not_mem_normalizer_L (hK31e : Kg31e G) (hK21d : Kg21d) (hKS : S3Sec29C.S16cKG)
    (h : Ctx29w G x K A B Q y y D J) (hsl : HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd)
    (h295 : B ⊓ cSec K ⊓ cSec J = ⊥) {L : Subgroup G} (hBL : B ≤ normalizer (L : Set G))
    (hQL : Q ≤ normalizer (L : Set G)) (hyL : y ∈ cSec L) (hJL : J ≤ cSec L)
    (hR : IsSylowOf 2 R (Jss y L ⊔ Q ⊔ zpowers y))
    (hRB : ∀ g ∈ B ⊓ cSec K, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (h297a : ∀ r ∈ R ⊓ centralizer ({x} : Set G), r * r ∈ Q → r ∈ Q ∨ r * y⁻¹ ∈ Q)
    (h297c : Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) = ⊥) (hMu : MuPkgL K A Q y L) :
    ∃ g ∈ B ⊓ cSec K, g ∉ normalizer (J : Set G) := by
  by_contra hall
  push Not at hall
  have hJ := S3Sec29D2.J_comp h
  set JS := Jss y L with hJS
  set B0 := B ⊓ cSec K with hB0
  have hB0N : B0 ≤ normalizer (J : Set G) := fun g hg => hall g hg
  have hBy := S3Sec29D2.B_le_centralizer_y h
  have hB0y : B0 ≤ centralizer ({y} : Set G) := inf_le_left.trans hBy
  have hy2 : y * y = 1 := S3Sec29D6.mul_self_of_orderOf_two h.y_ord
  have hyC : y ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨g₀, hg₀B, hg₀N⟩ := S3Sec29D2.exists_not_mem_normalizer hK31e h hsl
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := S3Sec29D2.exists_E h
  obtain ⟨-, -, -, -, hB04⟩ := S3Sec29D2.B_decomp h ⟨hEK, hAE, hEel, hE4⟩
  obtain ⟨z, hz⟩ := S3Sec29D5.exists_sl2Data hJ hsl
  have hzy := piC_y_eq_central_L hKS h hBL hQL hyL hJL hR hRB h297a h297c hMu hz
  obtain ⟨eJ⟩ := B1.PilotS5.hat_equiv_imgBar hJ
  obtain ⟨F, hF, hFin, hodd, ⟨e'⟩⟩ := hsl
  let e : ↥(S3.imgBar y J) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    eJ.symm.trans (e'.trans (specialLinearGroupEquivStatedSL 2 F).symm)
  let ρ := S3Sec29C.actHom hB0y hB0N
  have hρ : ∀ (b : ↥B0) (c : ↥(S3.imgBar y J)),
      ((ρ b c : ↥(S3.imgBar y J)) : CentralizerBar y) = piC y b * c * (piC y b)⁻¹ :=
    fun b c => S3Sec29C.actHom_apply hB0y hB0N b c
  have hρ_inj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hbc : (b : G) ∈ cSec J := S3Sec29C.mem_cSec_of_piC hJ (hB0y b.2) fun g hg => by
      have hgC := hJ.1 hg
      have hmem : piC y g ∈ S3.imgBar y J :=
        S3.mem_imgBar.2 ⟨⟨g, hgC⟩, hg, (piC_of_mem y hgC).symm⟩
      have := congrArg (fun σ : MulAut ↥(S3.imgBar y J) =>
        ((σ ⟨piC y g, hmem⟩ : ↥(S3.imgBar y J)) : CentralizerBar y)) hb
      simpa [hρ] using this
    have : (b : G) ∈ B ⊓ cSec K ⊓ cSec J := Subgroup.mem_inf.2 ⟨b.2, hbc⟩
    rw [h295, Subgroup.mem_bot] at this
    exact Subtype.ext this
  let ρ' : ↥B0 →* MulAut (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (MulAut.congr e).toMonoidHom.comp ρ
  have hρ'_inj : Function.Injective ρ' := (MulAut.congr e).injective.comp hρ_inj
  have hV2 : ∀ v ∈ ρ'.range, v * v = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (S3Sec29D2.B_sq h b (Subgroup.mem_inf.1 b.2).1)
    rw [this, map_one]
  have hV4 : 4 ≤ Nat.card ↥ρ'.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρ'_inj).toEquiv, hB04]
  obtain ⟨v, ⟨b, rfl⟩, hv1, s, hs⟩ := hK21d F hodd ρ'.range hV2 hV4
  have hb1 : b ≠ 1 := fun h1 => hv1 (by rw [h1, map_one])
  have hbB : (b : G) ∈ B := (Subgroup.mem_inf.1 b.2).1
  have hbC : (b : G) ∈ centralizer ({y} : Set G) := hB0y b.2
  have hbb : (b : G) * b = 1 := S3Sec29D2.B_sq h b hbB
  set t : ↥(S3.imgBar y J) := e.symm s with ht
  have hact : ∀ c : ↥(S3.imgBar y J), ρ b c = t * c * t⁻¹ := by
    intro c
    have h1 : ρ' b (e c) = s * e c * s⁻¹ := by rw [hs]; rfl
    have h2 : ρ' b (e c) = e (ρ b c) := by
      simp [ρ', MulAut.congr_apply]
    apply e.injective
    rw [← h2, h1, map_mul, map_mul, map_inv, ht, e.apply_symm_apply]
  have huJ : ∀ c ∈ S3.imgBar y J, piC y b * c * (piC y b)⁻¹ =
      (t : CentralizerBar y) * c * (t : CentralizerBar y)⁻¹ := by
    intro c hc
    rw [← hρ b ⟨c, hc⟩, hact]
    rfl
  have hut : ∃ c ∈ S3.imgBar y J, piC y b * c * (piC y b)⁻¹ ≠ c := by
    by_contra hall'
    push Not at hall'
    apply hb1
    apply hρ_inj
    rw [map_one]
    ext c
    rw [hρ]
    exact hall' c c.2
  have hg₀C : g₀ ∈ centralizer ({y} : Set G) := hBy hg₀B
  have hcg := S3Sec29D5.commConj_of_not_mem_normalizer hJ hg₀C hg₀N
  have hzc : ∀ v : CentralizerBar y, v * (z : CentralizerBar y) = (z : CentralizerBar y) * v := by
    intro v; rw [hzy]; exact S3Sec29D5.piC_y_comm v
  have hu2 : piC y b * piC y b = 1 := by rw [← piC_mul y hbC hbC, hbb, piC_one]
  have hug : piC y b * piC y g₀ = piC y g₀ * piC y b := by
    rw [← piC_mul y hbC hg₀C, ← piC_mul y hg₀C hbC, S3Sec29D2.B_comm h b hbB g₀ hg₀B]
  obtain ⟨a, w, ha, hw, hau, hwu, haa, hww, hwa⟩ :=
    S3Sec29D3.exists_D8 hcg hz hzc t.2 hu2 huJ hut hug
  set T := JS ⊔ zpowers y with hT
  have hJT : J ≤ T := (S3Sec29D5.le_Jss hJ hJL).trans le_sup_left
  have hg₀L : g₀ ∈ normalizer ((L : Subgroup G) : Set G) := hBL hg₀B
  have hsupT : S3.imgBar y J ⊔ (S3.imgBar y J).map (MulAut.conj (piC y g₀)).toMonoidHom ≤
      S3.imgBar y T := by
    refine sup_le (S3.imgBar_mono y hJT) ?_
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨c', hc'J, rfl⟩ := S3.mem_imgBar.1 hc
    have hc'C : (c' : G) ∈ centralizer ({y} : Set G) := c'.2
    have hxc : g₀ * c' * g₀⁻¹ ∈ T :=
      Subgroup.mem_sup_left (S3Sec29D5.conj_le_Jss hJ hJL hg₀C hg₀L ⟨c', hc'J, rfl⟩)
    refine S3.mem_imgBar.2 ⟨⟨g₀ * c' * g₀⁻¹, mul_mem (mul_mem hg₀C hc'C) (inv_mem hg₀C)⟩, hxc, ?_⟩
    rw [← piC_of_mem y (mul_mem (mul_mem hg₀C hc'C) (inv_mem hg₀C)), S3Sec29D4.piC_conj hg₀C hc'C,
      piC_of_mem y hc'C]
    rfl
  have hbL : (b : G) ∈ normalizer ((L : Subgroup G) : Set G) := hBL hbB
  have hbT : (b : G) ∈ normalizer ((T : Subgroup G) : Set G) := by
    refine S3Sec29D7.mem_normalizer_sup ?_ ?_
    · exact S3Sec29D5.le_normalizer_Jss (T := zpowers (b : G)) (Subgroup.zpowers_le.2 hbC)
        (Subgroup.zpowers_le.2 hbL) (Subgroup.mem_zpowers _)
    · refine S3Theta52.mem_normalizer_of_le_centralizer ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hbC).symm
  have hyT : y ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haa' : a * a = piC y y := by rw [haa, hzy]
  obtain ⟨a', w', ha', hw', haa'', hww', hwa'⟩ := S3Sec29D4.exists_D8_lift hbC hbb hbT hyT
    (hsupT ha) (hsupT hw) hau hwu haa' hww hwa hy2
  have hbQ : (b : G) ∈ Q := h.B0_le_Q b.2
  have hb2 : orderOf (b : G) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hbb) (fun h1 => hb1 (Subtype.ext h1))
  obtain ⟨M, hM, h3, hyM, -, hN, hFix⟩ := hMu b hbQ hb2
  set P := centralizer ({(b : G)} : Set G) ⊓ centralizer ({y} : Set G) ⊓ cSec L with hP
  have hPv : P ≤ centralizer ({(b : G)} : Set G) := inf_le_left.trans inf_le_left
  have hPM : P ≤ normalizer (M : Set G) := fun g hg => hN g (Subgroup.mem_inf.1 hg).1
  have hui := S3Sec29C.unique_involution hM h3 hyM h.y_ord hPv hPM hFix
  have hZ := B1.PilotS3.center_trivial_of_shape3 hM h3
  have hyMc : y ∉ cSec M := fun hc => by
    have h1 : y = 1 := S3Ctx29.eq_one_of_mem_cSec hZ (Subgroup.zpowers_le.2 hyM)
      (S3Sec29D6.isPGroup_zpowers_of_orderOf_two h.y_ord) (Subgroup.mem_zpowers y) hc
    have := h.y_ord
    rw [h1, orderOf_one] at this
    omega
  have hTP : T ⊓ centralizer ({(b : G)} : Set G) ≤ P := by
    intro g hg
    obtain ⟨hgT, hgb⟩ := Subgroup.mem_inf.1 hg
    have hTy : T ≤ centralizer ({y} : Set G) :=
      sup_le (S3Sec29D5.Jss_le_centralizer _) (Subgroup.zpowers_le.2 hyC)
    have hTL : T ≤ cSec L :=
      sup_le (S3Sec29D5.Jss_le_cSec _) (Subgroup.zpowers_le.2 hyL)
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgb, hTy hgT⟩, hTL hgT⟩
  have hya : y * a' = a' * y :=
    (Subgroup.mem_centralizer_singleton_iff.1 ((hTP ha').1.2)).symm
  exact S3Sec29D7.false_of_D8 hui hyMc hPM (hTP ha') (hTP hw') haa'' hww' hwa' hya

end S3Sec29JB

end CFSG.GH74.Generic.BProg.B3
