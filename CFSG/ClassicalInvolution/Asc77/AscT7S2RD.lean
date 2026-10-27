module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RC
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RA
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
import CFSG.ClassicalInvolution.Asc77.AscIHSectMA
import CFSG.ClassicalInvolution.Asc77.AscT3CIIClose
public import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKD
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RB
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.RouteD.G2D4T3Free
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge


public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)
open scoped commutatorElement

namespace T7S2R

section Triv

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem htriv_of_comm_join (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hu2 : u * u = 1) {c₀ : G} (hc₀C : c₀ ∈ Subgroup.centralizer ({u} : Set G))
    (hcomm : ∀ y ∈ memberJoin (exactFamily Ω u) u,
      oddQuotMk u ⟨c₀, hc₀C⟩ * y = y * oddQuotMk u ⟨c₀, hc₀C⟩) :
    ∀ y ∈ rLayer Ω u, c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u) := by
  intro y hy
  rw [rLayer_eq_exactLayer hp hq hΩ hu2] at hy ⊢
  have hyC : y ∈ Subgroup.centralizer ({u} : Set G) := exactLayer_le_centralizer Ω u hy
  have hyJ : oddQuotMk u ⟨y, hyC⟩ ∈ memberJoin (exactFamily Ω u) u := by
    rw [← range_layerToOddQuot_eq]
    exact ⟨⟨y, hy⟩, rfl⟩
  have h1 := hcomm _ hyJ
  have hYc : conjSub c₀ (exactLayer Ω u) = exactLayer Ω u :=
    conjSub_exactLayer hΩ.conjInvariant hc₀C
  have hcy : c₀ * y * c₀⁻¹ ∈ exactLayer Ω u := by
    have := conj_mem_conjSub (n := c₀) hy
    rwa [hYc] at this
  have hwY : c₀ * y * c₀⁻¹ * y⁻¹ ∈ exactLayer Ω u := (exactLayer Ω u).mul_mem hcy
    ((exactLayer Ω u).inv_mem hy)
  have hwC : c₀ * y * c₀⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({u} : Set G) :=
    exactLayer_le_centralizer Ω u hwY
  have hone : oddQuotMk u ⟨c₀ * y * c₀⁻¹ * y⁻¹, hwC⟩ = 1 := by
    have e : (⟨c₀ * y * c₀⁻¹ * y⁻¹, hwC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) =
        ⟨c₀, hc₀C⟩ * ⟨y, hyC⟩ * ⟨c₀, hc₀C⟩⁻¹ * ⟨y, hyC⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  have hwO : c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G)) :=
    mem_oddCoreOf_iff.mpr ⟨hwC, oddQuotMk_eq_one_iff.mp hone⟩
  exact T3CII.oddCoreOf_inf_le (exactLayer_le_centralizer Ω u) ⟨hwO, hwY⟩

end Triv

end T7S2R

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}


theorem Hyp21.zt_of_not_sectionConnected (h : Hyp21 p f Ω K K' z u J t W)
    (hS4 : T7S2R.Ih8S4Star p f) (hdisc : ¬ SectionConnected Ω u) :
    (∀ y ∈ rLayer Ω u, z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u)) ∨
      (∀ y ∈ rLayer Ω u, (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u)) := by
  have hs : TwinFrameSetting p f Ω K K' J z u t := TwinFrameSetting.of_hyp21 p f h
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  have hd := hs.frame
  have hK : K ∈ Ω := hd.mem
  have hz := hd.hz
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
  have hBab := twinFrame_isElemAbelian hp hΩ hd
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hc : UCoset z u t u := Or.inl rfl
  have hc1 : u ≠ 1 := hs.uc_ne_one hc
  have hcc : u * u = 1 := hd.hu2
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hcc
  have hnonab : ∃ x y : G, x * y ≠ y * x := exists_noncomm_of_isClassicalMember hcK
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G := Balance.not_subset_center_of_ne_one hnonab hc1
  obtain ⟨J', hJ'tw, hJ'ne⟩ := hs.exists_twin_J
  have hJΩ : J ∈ Ω := hd.hJ.1
  have hJ'Ω : J' ∈ Ω := hJ'tw.1
  have hJt : IsUniqueInvolution J t := hd.ht
  have hJ't : IsUniqueInvolution J' t := by
    obtain ⟨t', hJt', hJ't'⟩ := hJ'tw.2
    have : t' = t := hJt'.eq hJt
    rwa [this] at hJ't'
  have hcJ : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hJΩ hJt
  have hcJ' : IsClassicalMember p f J' t := isClassicalMember_of_twin hΩ hJ'Ω hJ't
  have hMJ : J ∈ tqMembers Ω u := ⟨hJΩ, hs.tq_uc hc hJΩ hJt⟩
  have hMJ' : J' ∈ tqMembers Ω u := ⟨hJ'Ω, hs.tq_uc hc hJ'Ω hJ't⟩
  obtain ⟨D⟩ := lieSystemAt_exactFamily hΩ.conjInvariant hΩ.classical hc2 hs.below hnc ⟨J, hMJ⟩
  have hs' : SecData p f u (exactFamily Ω u) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨J, hMJ⟩
  have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
    G2D4Models.h3s_of_nonToral_free G2D4Models.g2NonToralGenerate_all
  have hTS : TransSection p f (secFam Ω u) :=
    T7S2R.transSection_secFam hp hq hΩ hc2 hnc hs.below (h3s _ hs.below) hMJ hdisc
  obtain ⟨hbY, hKJ, hKJ', hneKJ, hzKJ, hzKJ'⟩ :=
    secFam_twin hp hq hΩ hc2 hMJ hMJ' hcJ hcJ' hJ'ne
  let hDl : OmegaLie p f (secFam Ω u) := LieSystemData.toOmegaLie D (omegaGen_secFam hs')
  have hne : (secFam Ω u).Nonempty := ⟨_, hKJ⟩
  have hdisc' : ¬ T3.DStarConnected (secFam Ω u) := fun hc' =>
    hdisc ((T7S2R.sectionConnected_iff_secFam hΩ hc2).mpr hc')
  have hcard : D.card = 1 := hDl.card_eq_one_of_transitive hTS.hyp hTS.gen hTS.trans hne
  let j : Fin D.card := ⟨0, by omega⟩
  have htag := T7S2R.tag_of_disc hp hq G2D4Models.ih8G2D4_unconditional ih8D4Star hS4 hTS hDl hne
    hKJ ⟨hKJ', _, hzKJ, hzKJ'⟩ hneKJ.symm hdisc' j
  have htag : (D.tag j = .PSp ∧ D.rank j = 2) ∨ (D.tag j = .PSL ∧ D.rank j = 4) ∨
      (D.tag j = .PSU ∧ D.rank j = 4) := htag
  have hG2 : D.tag j ≠ .G2 := by
    rcases htag with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> decide
  have hD4 : D.tag j ≠ .trialityD4 := by
    rcases htag with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> decide
  have hsurj : Function.Surjective (D.hom j) :=
    hDl.hom_surjective_of_gen hcard (omegaGen_secFam hs') j
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψdef
  have hrange : ψ.range = memberJoin (exactFamily Ω u) u := by
    rw [← range_sectionQuotientHom (normalizesLayer_exactFamily hΩ.conjInvariant)]
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨D.hom j k, rfl⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := hsurj q
      exact ⟨k, rfl⟩
  have hMj : modOdd u (exactCore u J) ≤ ψ.range := by
    rw [hrange]
    exact modOdd_le_exactJoin (exactCore_mem_exactFamily hMJ)
  have hM'j : modOdd u (exactCore u J') ≤ ψ.range := by
    rw [hrange]
    exact modOdd_le_exactJoin (exactCore_mem_exactFamily hMJ')
  obtain ⟨htC, R, R', x₁, x₁', hpair, hshape, hRM, hR'M, hψx₁⟩ :=
    T7S2R.vertexTwin' hp hq hΩ hc2 hBab huB (b := t) htB hMJ hMJ' hcJ hcJ' hJ'ne D j hMj hM'j
      hG2 hD4
  have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
  have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
  have hTV : CFSG.ClassicalInvolution.ModelFacts.Orth15.TwinOuterVacOn (D.tag j)
      (compModel D j) :=
    CFSG.ClassicalInvolution.ModelFacts.Orth15.twinOuterVac_of_small hp hq' (D.admissible j) htag
  have hker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j
  have hzC : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hBab huB hzB
  obtain ⟨RK, RK', hRK, hRK', hcommK, hRKt, hRK't, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    hs.exists_sylow_frame
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK.subnormal
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hKz (hRK.1 hx))
  have hxt : x * t = t * x := hRKt x hx
  have hxy_c : x * y = y * x := hcommK x hx y hy
  have hxu : x * u = u * x := by
    rw [← hxy]
    calc x * (x * y) = x * (y * x) := by rw [hxy_c]
      _ = (x * y) * x := by group
  have hxC : x ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxu
  have hxJ : x ∈ trivialOnQuot J :=
    sylow_le_trivialOnQuot hp hq hΩ hK hJΩ hz hJt hd.t_ne_z.symm hRK hRKt hx
  have hxJ' : x ∈ trivialOnQuot J' :=
    sylow_le_trivialOnQuot hp hq hΩ hK hJ'Ω hz hJ't hd.t_ne_z.symm hRK hRKt hx
  have hqs : ∀ R₀ : Subgroup (compModel D j).K,
      R₀ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D →
        CFSG.Open.IsQuasisimple ↥(R₀.map ψ) := fun R₀ hR₀ =>
    isQuasisimple_map_of_ker_le_center ψ hker
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (by omega) R₀ hR₀)
  have hqJ : CFSG.Open.IsQuasisimple ↥(modOdd u (exactCore u J)) := by
    rw [← hRM]
    exact hqs R hpair.mem
  have hqJ' : CFSG.Open.IsQuasisimple ↥(modOdd u (exactCore u J')) := by
    rw [← hR'M]
    exact hqs R' hpair.mem'
  have hcommJ := oddQuotMk_centralizes_modOdd_exactCore hcJ hc2 hMJ.2 hxJ hxC hqJ
  have hcommJ' := oddQuotMk_centralizes_modOdd_exactCore hcJ' hc2 hMJ'.2 hxJ' hxC hqJ'
  have hNormal : (ψ.range).Normal := by
    rw [hrange]
    exact memberJoin_normal_of_normalizes (normalizesLayer_exactFamily hΩ.conjInvariant)
  have hxn : oddQuotMk u ⟨x, hxC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot u)) := by
    have := hNormal
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hψnorm : ∀ w : (compModel D j).K,
      ψ w ∈ Subgroup.normalizer (ψ.range : Set (OddQuot u)) :=
    FrameVertex.mem_normalizer_range ψ
  set v : ↥(inducedAutOn ψ.range) := toInducedAutOn ψ.range ⟨oddQuotMk u ⟨x, hxC⟩, hxn⟩ with hv
  have hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd u (exactCore u J) := hRM ▸ Subgroup.mem_map_of_mem ψ hr
    congr 1
    exact Subtype.ext (hcommJ (ψ r) hr')
  have hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd u (exactCore u J') := hR'M ▸ Subgroup.mem_map_of_mem ψ hr
    congr 1
    exact Subtype.ext (hcommJ' (ψ r) hr')
  have hxx : oddQuotMk u ⟨x, hxC⟩ * oddQuotMk u ⟨x, hxC⟩ = oddQuotMk u ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hx2
  have hzn : oddQuotMk u ⟨z, hzC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot u)) := by
    rw [← hxx]
    exact Subgroup.mul_mem _ hxn hxn
  have htn : oddQuotMk u ⟨t, htC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot u)) := by
    rw [← hψx₁]
    exact hψnorm x₁
  have hvv : v * v = toInducedAutOn ψ.range ⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ := by
    rw [hv, ← map_mul]
    congr 1
    exact Subtype.ext hxx
  have hzz : oddQuotMk u ⟨z, hzC⟩ * oddQuotMk u ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) = 1 :=
      Subtype.ext hz.sq
    rw [this, map_one]
  have hvv2 : v * v * (v * v) = 1 := by
    rw [hvv, ← map_mul]
    have : (⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ * ⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ :
        ↥(Subgroup.normalizer (ψ.range : Set (OddQuot u)))) = 1 := Subtype.ext hzz
    rw [this, map_one]
  have key := hTV (OddQuot u) ψ R R' x₁ x₁' hpair v hvR hvR' hvv2
  rcases key with hv0 | hv1
  ·
    left
    have h2 : toInducedAutOn ψ.range ⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ = 1 := by
      rw [← hvv]
      exact hv0
    have hcomm := Lemma52Proof.commute_of_toInducedAutOn_eq_one ψ.range hzn h2
    exact T7S2R.htriv_of_comm_join hp hq hΩ hcc hzC fun y hy' => hcomm y (by rw [hrange]; exact hy')
  ·
    right
    have h1 : toInducedAutOn ψ.range ⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ =
        toInducedAutOn ψ.range ⟨oddQuotMk u ⟨t, htC⟩, htn⟩ := by
      rw [← hvv, hv1, FrameVertex.innerHom_apply]
      congr 1
      exact Subtype.ext hψx₁
    have htzC : t * z ∈ Subgroup.centralizer ({u} : Set G) := Subgroup.mul_mem _ htC hzC
    have hmul : oddQuotMk u ⟨t * z, htzC⟩ = oddQuotMk u ⟨t, htC⟩ * oddQuotMk u ⟨z, hzC⟩ :=
      map_mul (oddQuotMk u) (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) ⟨z, hzC⟩
    have htzn : oddQuotMk u ⟨t * z, htzC⟩ ∈
        Subgroup.normalizer (ψ.range : Set (OddQuot u)) := by
      rw [hmul]
      exact Subgroup.mul_mem _ htn hzn
    have h2 : toInducedAutOn ψ.range ⟨oddQuotMk u ⟨t * z, htzC⟩, htzn⟩ = 1 := by
      have h3 : (⟨oddQuotMk u ⟨t * z, htzC⟩, htzn⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot u)))) =
            ⟨oddQuotMk u ⟨t, htC⟩, htn⟩ * ⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ := Subtype.ext hmul
      rw [h3, map_mul, ← h1, ← map_mul]
      have h4 : (⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ * ⟨oddQuotMk u ⟨z, hzC⟩, hzn⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot u)))) = 1 := Subtype.ext hzz
      rw [h4, map_one]
    have hcomm := Lemma52Proof.commute_of_toInducedAutOn_eq_one ψ.range htzn h2
    exact T7S2R.htriv_of_comm_join hp hq hΩ hcc htzC fun y hy' =>
      hcomm y (by rw [hrange]; exact hy')

end Main

end CFSG.ClassicalInvolution.Asc77
