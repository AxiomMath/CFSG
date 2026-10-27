module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FC

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

variable {G : Type} [Group G] [Finite G]

theorem k148f_barAut_inv {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (w : PQuot 3 L) :
    (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hx⟩)⁻¹ w = lemma102_conjQ 3 hx w := by
  apply (MulEquiv.symm_apply_eq _).2
  exact (barAut_comp_conjQ hx w).symm

theorem k148f_indRel_iff {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (a b : PQuot 3 L) :
    indRel 3 L x a b ↔ (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hx⟩)⁻¹ a = b := by
  rw [k148f_barAut_inv hx]
  constructor
  · rintro ⟨l, l', rfl, rfl, hl⟩
    rw [lemma102_conjQ_mk]
    congr 1
    apply Subtype.ext
    exact hl.symm
  · rintro rfl
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective a
    refine ⟨l, ⟨x⁻¹ * (l : G) * x, ?_⟩, rfl, ?_, rfl⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) (l : G)).1 l.2
      rwa [inv_inv] at this
    · rw [lemma102_conjQ_mk]
      rfl

theorem k148f_fieldOn {K J₀ : Subgroup G} {x y : G} (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hJ₀K : J₀ ≤ K) (hJ₀ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J₀)
    (hxJ₀ : x ∈ Subgroup.normalizer (J₀ : Set G))
    {φ : MulAut (PQuot 3 (barX 3 K J₀))} (hφ : K148FFieldAut 3 (PQuot 3 (barX 3 K J₀)) φ)
    (hgraph : ∀ m : ↥(barX 3 K J₀), ∃ m' : ↥(barX 3 K J₀),
      (m' : PQuot 3 K) = (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩)⁻¹ (m : PQuot 3 K) ∧
        φ (QuotientGroup.mk m) = QuotientGroup.mk m') :
    FieldOn 3 x J₀ := by
  let e : PQuot 3 J₀ ≃* PQuot 3 (barX 3 K J₀) := CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv hJ₀K
  let ψ : MulAut (PQuot 3 J₀) := (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 J₀ ⟨x, hxJ₀⟩)⁻¹
  have hcomp : ∀ a : PQuot 3 J₀, φ (e a) = e (ψ a) := by
    intro a
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨m', hm'P, hφm'⟩ := hgraph (CFSG.HardMathSupport.Solomon.Coordinator.l514t_barXMap hJ₀K j)
    have hψ : ψ (QuotientGroup.mk j) = QuotientGroup.mk (lemma102_conjHomL hxJ₀ j) := by
      show (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 J₀ ⟨x, hxJ₀⟩)⁻¹ (QuotientGroup.mk j) = _
      rw [k148f_barAut_inv hxJ₀, lemma102_conjQ_mk]
    rw [hψ, CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv_mk,
      CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv_mk, QuotientGroup.mk'_apply, hφm',
      QuotientGroup.mk'_apply]
    congr 1
    apply Subtype.ext
    rw [hm'P]
    show (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩)⁻¹ _ = _
    rw [k148f_barAut_inv hxN]
    rfl
  have hY : commutator (PQuot 3 J₀) = ⊤ := (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ₀).1
  have hψF := k148f_fieldAut_transport hY e hcomp hφ
  have hrel : indRel 3 J₀ x = fun a b => ψ a = b :=
    funext fun a => funext fun b => propext (k148f_indRel_iff hxJ₀ a b)
  refine ⟨hxJ₀, ?_⟩
  simp only [hrel]
  exact hψF

theorem i148five_of_facts (G : Type) [Group G] [Finite G] (hFB : K148FG2CompFact) (hTwo : K148FTwoFact)
    (hLang : K148FLangFact) (hC1 : K148FC1LayerFact) : I148fiveAt G := by
  intro X K I' J x y n hK hchev hTD4 hx3 hy3 hxy hyx hNI hI' hG2 hyK hJ hL2
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨q, hq2, hcenter, hP⟩ := k148f_setup hK hTD4 hchev
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hNI.1
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hyK.1 (Subgroup.mem_zpowers y)
  have hyin : InducesInnerMod 3 K y := k148f_inner hK hTD4 hyK
  obtain ⟨c, hc⟩ := k148f_elem hyN hyin
  have hc3 : c ^ 3 = 1 := k148f_pow_three hcenter hyN hy3 hc
  have hτ3 := k148f_barAut_pow_three hxN hx3
  have hτout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩) :=
    fun h => hNI.2 ((inducesInnerMod_iff_barAut_mem_inner hxN).2 h)
  have hτc := k148f_comm_fix hcenter hxN hyN hxy hc
  have hI'K : I' ≤ K := (hI'.1).trans inf_le_left
  have hJK' : J ≤ K := hJ.1.trans (inf_le_left.trans hI'K)
  have hS'comp := k148f_comp_F hxN hx3 hI'
  have hG2S : catalogIs (PQuot 3 (barX 3 K I')) isG2Quot :=
    k148f_cat_congr (CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv hI'K) hG2
  have hDC : I' ⊓ Subgroup.centralizer ({y} : Set G) ≤ K := inf_le_left.trans hI'K
  have hSJ0 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop115b.barX_glaPComponent_of_le hp3 hDC hJ
  rcases hLang (PQuot 3 K) q hq2 hP _ hτ3 hτout (barX 3 K I') hS'comp hG2S with
    ⟨hf2, hcatF⟩ | ⟨hf1, hU33⟩
  ·
    obtain ⟨hFs, h3F⟩ := k148f_G2_simple' hq2 hf2 hP hcatF
    have hS'eq : barX 3 K I' = CFSG.RankThree.PartTwo.Sec4.autFix
        (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩) :=
      k148f_comp_eq_of_simple hFs hS'comp
    have hFuniq : ∀ S : Subgroup (PQuot 3 K),
        GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix
          (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩)) S → S = barX 3 K I' :=
      fun S hS => (k148f_comp_eq_of_simple hFs hS).trans hS'eq.symm
    have huniq := k148f_unique_X hxN hx3 hI' hFuniq
    have hyI' := k148f_y_norm hyN hxy hI' huniq
    have hS'simple : IsSimpleGroup ↥(barX 3 K I') := by rw [hS'eq]; exact hFs
    have h3S' : 3 ∣ Nat.card ↥(barX 3 K I') := by rw [hS'eq]; exact h3F
    have hbarX := k148f_barX_inf hyN hyI' hy3 hI'K hS'simple h3S' hc
    have hSJ1 := hSJ0
    rw [hbarX, hS'eq] at hSJ1
    have hcL2 : catalogIs (PSimple 3 (barX 3 K J)) (isL2n n) :=
      k148f_cat_congr (k148f_psimple_congr (CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv hJK')) hL2
    have hcN : c ∈ Subgroup.normalizer ((CFSG.RankThree.PartTwo.Sec4.autFix
        (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩) : Subgroup (PQuot 3 K)) : Set (PQuot 3 K)) :=
      k148f_normalizes_fix hτc
    have hn : n = q.exponent := (hFB (PQuot 3 K) _ q.exponent c hcatF hcN hc3 (barX 3 K J) hSJ1 n hcL2).2
    have hJL : ∃ S : Subgroup (PQuot 3 K), GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix
        (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩) ⊓
          Subgroup.centralizer ({c} : Set (PQuot 3 K))) S ∧
        catalogIs (PSimple 3 S) (isL2n q.exponent) :=
      ⟨barX 3 K J, hSJ1, by rw [← hn]; exact hcL2⟩
    obtain ⟨M₀, hM₀, huniqM, hcatM, -, φ, -, -, hφgraph, hφF⟩ :=
      hC1 (PQuot 3 K) q hq2 hf2 hP _ hτ3 hτout hcatF c hc3 hτc hJL
    have hbarXK : barX 3 K (K ⊓ Subgroup.centralizer ({y} : Set G)) =
        Subgroup.centralizer ({c} : Set (PQuot 3 K)) := k148f_barX_yK hyN hy3 hc
    have hM₀' : GLAPComponent 3 (barX 3 K (K ⊓ Subgroup.centralizer ({y} : Set G))) M₀ := by
      rw [hbarXK]; exact hM₀
    obtain ⟨J₀, hJ₀, hJ₀u, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.l514t_comp_unique_transfer
      (inf_le_left : K ⊓ Subgroup.centralizer ({y} : Set G) ≤ K) hM₀'
      (fun S hS => huniqM S (by rw [hbarXK] at hS; exact hS))
    have hJ₀K : J₀ ≤ K := hJ₀.1.trans inf_le_left
    have hbX : barX 3 K J₀ = M₀ := by
      have h1 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop115b.barX_glaPComponent_of_le hp3 (inf_le_left : K ⊓ Subgroup.centralizer ({y} : Set G) ≤ K) hJ₀
      rw [hbarXK] at h1
      exact huniqM _ h1
    subst hbX
    have hcatJ : catalogIs (PSimple 3 J₀) (isL2n (3 * n)) := by
      rw [hn]
      exact k148f_cat_congr (k148f_psimple_congr
        (CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv hJ₀K)).symm hcatM
    have hxJ₀ : x ∈ Subgroup.normalizer (J₀ : Set G) := by
      have hxKy : x ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) :=
        k148f_normalizer_inf hxN hxy.symm
      have hG := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ₀ x
      rw [mem_normalizer_iff_gLBConj_eq.1 hxKy] at hG
      exact mem_normalizer_iff_gLBConj_eq.2 (hJ₀u _ hG)
    exact ⟨J₀, hJ₀, hJ₀u, hcatJ, k148f_fieldOn hxN hJ₀K hJ₀ hxJ₀ hφF hφgraph⟩
  ·
    exfalso
    obtain ⟨huniqF, hsimpleF, hclass⟩ := hTwo (PQuot 3 K) q hq2 hf1 hP _ hτ3 hτout
    have hS'simple : IsSimpleGroup ↥(barX 3 K I') := hsimpleF _ hS'comp
    have h3S' : 3 ∣ Nat.card ↥(barX 3 K I') := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.three_dvd_card_of_glaPComponent hS'comp
    have hFuniq : ∀ S : Subgroup (PQuot 3 K),
        GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix
          (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨x, hxN⟩)) S → S = barX 3 K I' :=
      fun S hS => huniqF S _ hS hS'comp
    have huniq := k148f_unique_X hxN hx3 hI' hFuniq
    have hyI' := k148f_y_norm hyN hxy hI' huniq
    have hbarX := k148f_barX_inf hyN hyI' hy3 hI'K hS'simple h3S' hc
    have hSJ1 := hSJ0
    rw [hbarX] at hSJ1
    have hcL2 : catalogIs (PSimple 3 (barX 3 K J)) (isL2n n) :=
      k148f_cat_congr (k148f_psimple_congr (CFSG.HardMathSupport.Solomon.Coordinator.l514t_coreQuotEquiv hJK')) hL2
    exact hclass c hc3 hτc _ hS'comp (barX 3 K J) hSJ1 n hcL2

end CFSG.LocalAnalysis.GLTheoremA.K148F

end
