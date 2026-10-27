module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowDatum
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowCoordinates
public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoFour
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77 (radOne radTwo unipOne_le_unipAll unipTwo_le_unipAll)
open scoped commutatorElement MatrixGroups

namespace CFSG.ComponentClassification.GS79bSec5

universe u

private theorem projective_ker_center
    {G : Type u} [Group G] {F : Type} [Field F]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).ker = Subgroup.center A := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have h1 : QuotientGroup.mk' (Subgroup.center A) x = 1 :=
      e.injective (by simpa using hx)
    have h2 : x ∈ (QuotientGroup.mk' (Subgroup.center A)).ker := by
      simpa [MonoidHom.mem_ker] using h1
    rwa [QuotientGroup.ker_mk'] at h2
  · intro hx
    have hx' : x ∈ (QuotientGroup.mk' (Subgroup.center A)).ker := by
      rwa [QuotientGroup.ker_mk']
    change e (QuotientGroup.mk' (Subgroup.center A) x) = 1
    rw [MonoidHom.mem_ker] at hx'
    simp [hx']

private theorem conj_projective_ker_odd
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F]
    {A : Subgroup G}
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (c : G) :
    let A' : Subgroup G := A.map (MulAut.conj c).toMonoidHom
    let j : A' ≃* A :=
      (Subgroup.equivMapOfInjective A (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm
    let π' : A' →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp j.toMonoidHom
    Odd (Nat.card π'.ker) ∧ π'.ker ≤ Subgroup.center A' := by
  intro A' j π'
  let π : A →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
  have hker : π.ker = Subgroup.center A := projective_ker_center A e
  have hker' : π'.ker = (Subgroup.center A).comap j.toMonoidHom := by
    ext x
    change π (j x) = 1 ↔ j x ∈ Subgroup.center A
    rw [← hker]
    rfl
  have hmap : (Subgroup.center A).map j.symm.toMonoidHom = Subgroup.center A' :=
    Subgroup.map_center_eq j.symm
  have hcomap : (Subgroup.center A).comap j.toMonoidHom =
      (Subgroup.center A).map j.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨j x, hx, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      simpa using hy
  have hker_eq : π'.ker = Subgroup.center A' := by
    rw [hker', hcomap, hmap]
  have hodd : Odd (Nat.card π'.ker) := by
    rw [hker_eq, ← hmap, Subgroup.card_map_of_injective j.symm.injective]
    exact hZ
  exact ⟨hodd, by rw [hker_eq]⟩

theorem exists_moving_element_of_standard_row
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
  let V : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map
      (A.subtype.comp φ)
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
      (A.subtype.comp φ)
  let U : Subgroup G := V ⊓ Subgroup.centralizer (V : Set G)
  ∃ y : G,
    y ∈ Subgroup.normalizer (E : Set G) ∧
    y ∈ Subgroup.normalizer (U : Set G) ∧
    ∃ u : G, u ∈ U ∧ u ≠ 1 ∧ y * t * y⁻¹ = t * u := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hq4 : 4 < Nat.card F := by omega
  have hperf : Group.IsPerfect A := Group.IsPerfect.mk hA.1.1
  let : Group.IsPerfect A := hperf
  have hFf : FusionFacts A (Nat.card F) :=
    fusionFacts_of_odd_central_psl_three (F := F) hF A (e := e) hZ hcyc
  obtain ⟨d, hdt, -, hdV, hR⟩ :=
    exists_datum_with_standard_unipotent_radicals hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  have hα : d.Alpha := by
    apply Facts.alpha hFf d hq4 hR
    obtain ⟨g, hg1, hg2⟩ := CFSG.Monster.B.Recog.exists_conj_ne_commute hnonab ht
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hdt]
      simpa [inv_inv] using hg1
    · rw [hdt]
      simpa [inv_inv] using hg2
  let V : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map (A.subtype.comp φ)
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map (A.subtype.comp φ)
  let U : Subgroup G := V ⊓ Subgroup.centralizer (V : Set G)
  have hVd : d.V = V := hdV
  have hU : U = d.V ⊓ Subgroup.centralizer (d.V : Set G) := by
    rw [hVd]
  obtain ⟨u₀, hu₀U, hu₀P, hu₀1, hu₀2, hconj⟩ :=
    Facts.exists_u₀ hFf d hq4 hR hα
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hg : c⁻¹⁻¹ * d.t * c⁻¹ ∈ d.P ⊓ Subgroup.centralizer (d.P : Set G) := by
    rw [inv_inv, hc]
    exact ⟨mul_mem hu₀U.1.1 d.t_mem_P, mul_mem hu₀P d.t_mem_centralizer_P⟩
  let A' : Subgroup G := A.map (MulAut.conj c).toMonoidHom
  let j : A' ≃* A :=
    (Subgroup.equivMapOfInjective A (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).symm
  let π : A →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
  let π' : A' →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    π.comp j.toMonoidHom
  have hkerπ : π.ker = Subgroup.center A := projective_ker_center A e
  have hoddπ : Odd (Nat.card π.ker) := by rwa [hkerπ]
  have hcopπ : Nat.Coprime (Nat.card π.ker) 2 := Nat.coprime_two_right.mpr hoddπ
  have hcentπ : π.ker ≤ Subgroup.center A := by rw [hkerπ]
  have hproj : Odd (Nat.card π'.ker) ∧ π'.ker ≤ Subgroup.center A' :=
    conj_projective_ker_odd (A := A) (e := e) hZ c
  have hoddπ' : Odd (Nat.card π'.ker) := hproj.1
  have hcentπ' : π'.ker ≤ Subgroup.center A' := hproj.2
  have hcopπ' : Nat.Coprime (Nat.card π'.ker) 2 := Nat.coprime_two_right.mpr hoddπ'
  have hsurjπ : Function.Surjective π := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center A) y
    exact ⟨a, rfl⟩
  have hsurjπ' : Function.Surjective π' := fun x => by
    obtain ⟨a, rfl⟩ := hsurjπ x
    exact ⟨j.symm a, by simp [π']⟩
  have hVA' : d.V ≤ A' := by
    intro v hv
    refine ⟨c⁻¹ * v * c, ?_, ?_⟩
    · have hvA := Facts.conj_V_le_A hFf d hq4 hR hα hg hv
      simpa [inv_inv] using hvA
    · change c * (c⁻¹ * v * c) * c⁻¹ = v
      group
  have hV' : IsSylowOf 2 d.V A' :=
    CFSG.ABGLocalTools.isSylowOf_of_card hVA' (by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact d.V_isSylow.card_eq)
  have hV'sub : IsSylowOf 2 (d.V.subgroupOf A') ⊤ := by
    have htop : (⊤ : Subgroup A').map A'.subtype = A' := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hm : IsSylowOf 2 ((d.V.subgroupOf A').map A'.subtype) ((⊤ : Subgroup A').map A'.subtype) := by
      rw [htop]
      simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVA'] using hV'
    have h := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) (B := ⊤) A').mp hm
    simpa using h
  let barV : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    (d.V.subgroupOf A').map π'
  have hbarV : IsSylowOf 2 barV ⊤ := by
    obtain ⟨Q, hQ⟩ := hV'sub
    have htop_surj : Function.Surjective (⊤ : Subgroup A').subtype := fun x =>
      ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
    let Q₁ : Sylow 2 A' := Sylow.mapSurjective (p := 2) (f := (⊤ : Subgroup A').subtype) htop_surj Q
    let Q₂ : Sylow 2 (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
      Sylow.mapSurjective (p := 2) (f := π') hsurjπ' Q₁
    have hQ₂ : (Q₂ : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) =
        barV := by
      rw [Sylow.coe_mapSurjective, Sylow.coe_mapSurjective, hQ]
    let e : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F ≃*
        (⊤ : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) :=
      (Subgroup.topEquiv).symm
    let Qtop : Sylow 2 (⊤ : Subgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) :=
      Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective Q₂
    refine ⟨Qtop, ?_⟩
    change Subgroup.map (⊤ : Subgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)).subtype
        (Subgroup.map e.toMonoidHom (Q₂ : Subgroup
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F))) = barV
    rw [Subgroup.map_map]
    have hid : (⊤ : Subgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)).subtype.comp
        e.toMonoidHom = MonoidHom.id _ := by
      ext x
      rfl
    rw [hid, Subgroup.map_id]
    exact hQ₂
  obtain ⟨R₁, R₂, hRbar⟩ :=
    exists_radicals_of_mulEquiv (Subgroup.topEquiv) hbarV
  let barE : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    (E.subgroupOf A').map π'
  have hE2' : IsPGroup 2 (E.subgroupOf A') :=
    CFSG.Open.IsElemAbelian.isPGroup (CFSG.Open.IsElemAbelian.subgroupOf hR.elem₁ A')
  have hbarEelem : CFSG.Open.IsElemAbelian 2 barE :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hR.elem₁ A') π'
  have hbarEcard : Nat.card barE = Nat.card F ^ 2 := by
    have hEA' : E ≤ A' := hR.le₁.trans hVA'
    have hsub : Nat.card (E.subgroupOf A') = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA').toEquiv
    have hinj : Function.Injective (π'.comp (E.subgroupOf A').subtype) :=
      CFSG.RankThree.OddKernel.injective_restrict_of_odd π' hoddπ' hE2'
    have hrange : (π'.comp (E.subgroupOf A').subtype).range = barE := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcard : Nat.card barE = Nat.card (E.subgroupOf A') := by
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hcard, hsub, hR.card₁]
  have hbarEle : barE ≤ barV := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem π'
      (Subgroup.mem_subgroupOf.mpr (hR.le₁ (Subgroup.mem_subgroupOf.mp he)))
  have hbarW : barE = R₁ ∨ barE = R₂ := hRbar.eq_of_card barE hbarEle hbarEelem hbarEcard
  let barU : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    ((d.V ⊓ Subgroup.centralizer (d.V : Set G)).subgroupOf A').map π'
  have hbarU : barU = barV ⊓ Subgroup.centralizer (barV :
      Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      have huU : (u : G) ∈ d.V ⊓ Subgroup.centralizer (d.V : Set G) :=
        Subgroup.mem_subgroupOf.mp hu
      refine ⟨Subgroup.mem_map_of_mem π' (Subgroup.mem_subgroupOf.mpr huU.1), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      have hvV : (v : G) ∈ d.V := Subgroup.mem_subgroupOf.mp hv
      rw [← map_mul, ← map_mul]
      exact congrArg π' (Subtype.ext (Subgroup.mem_centralizer_iff.mp huU.2 (v : G) hvV))
    · intro x hx
      obtain ⟨hxbarV, hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨xV, hxVsub, hxeq⟩ := Subgroup.mem_map.mp hxbarV
      have hxV : (xV : G) ∈ d.V := Subgroup.mem_subgroupOf.mp hxVsub
      refine Subgroup.mem_map.mpr ⟨xV, Subgroup.mem_subgroupOf.mpr ⟨hxV, ?_⟩, hxeq⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro w hw
      let wA' : A' := ⟨w, hVA' hw⟩
      have hcx : π' wA' * x = x * π' wA' :=
        Subgroup.mem_centralizer_iff.mp hxC (π' wA')
          (Subgroup.mem_map_of_mem π' (Subgroup.mem_subgroupOf.mpr hw))
      have hcv : π' xV * π' wA' = π' wA' * π' xV := by
        simpa [← hxeq] using hcx.symm
      have hinj : Function.Injective (π'.comp (d.V.subgroupOf A').subtype) :=
        CFSG.RankThree.OddKernel.injective_restrict_of_odd π' hoddπ' hV'sub.isPGroup
      have hprod : (⟨xV * wA', Subgroup.mem_subgroupOf.mpr (d.V.mul_mem hxV hw)⟩ :
          d.V.subgroupOf A') =
          ⟨wA' * xV, Subgroup.mem_subgroupOf.mpr (d.V.mul_mem hw hxV)⟩ := by
        apply hinj
        simpa [map_mul] using hcv
      have heqA' : wA' * xV = xV * wA' := congrArg Subtype.val hprod.symm
      simpa [wA'] using congrArg (fun z : A' => (z : G)) heqA'
  have hbarUcard : Nat.card barU = Nat.card F := by
    let U₀ : Subgroup G := d.V ⊓ Subgroup.centralizer (d.V : Set G)
    have hU₀A' : U₀ ≤ A' := inf_le_left.trans hVA'
    have hUleV : U₀.subgroupOf A' ≤ d.V.subgroupOf A' := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1
    have hU2 : IsPGroup 2 (U₀.subgroupOf A') := hV'sub.isPGroup.to_le hUleV
    have hsub : Nat.card (U₀.subgroupOf A') = Nat.card U₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀A').toEquiv
    have hinj : Function.Injective (π'.comp (U₀.subgroupOf A').subtype) :=
      CFSG.RankThree.OddKernel.injective_restrict_of_odd π' hoddπ' hU2
    have hmap : barU = (U₀.subgroupOf A').map π' := rfl
    have hrange : (π'.comp (U₀.subgroupOf A').subtype).range = barU := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, ← hmap]
    have hcard : Nat.card barU = Nat.card (U₀.subgroupOf A') := by
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hcard, hsub]
    exact hR.card_center
  obtain ⟨ybar, hybar, hybarU, hfixbar⟩ :=
    exists_scaling (A := (⊤ : Subgroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)))
      (Subgroup.topEquiv) hbarV hRbar hbarW (by omega)
  obtain ⟨y', hy'⟩ := hsurjπ' ybar
  have hEA' : E ≤ A' := hR.le₁.trans hVA'
  have hyE : (y' : G) ∈ Subgroup.normalizer (E : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    let eA' : A' := ⟨e, hEA' he⟩
    have hyeA' : (⟨(y' : G) * e * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hEA' he)) (A'.inv_mem y'.2)⟩ : A') =
        y' * eA' * y'⁻¹ := rfl
    have hprojmem : π' ⟨(y' : G) * e * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hEA' he)) (A'.inv_mem y'.2)⟩ ∈ barE := by
      have h1 : π' ⟨(y' : G) * e * (y' : G)⁻¹,
          A'.mul_mem (A'.mul_mem y'.2 (hEA' he)) (A'.inv_mem y'.2)⟩ =
          ybar * π' eA' * ybar⁻¹ := by
        rw [hyeA', map_mul, map_mul, map_inv, hy']
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp hybar.2 (π' eA')).mp
        ⟨eA', Subgroup.mem_subgroupOf.mpr he, rfl⟩
    obtain ⟨e₁, he₁, hπe₁⟩ := Subgroup.mem_map.mp hprojmem
    have he₁E : (e₁ : G) ∈ E := Subgroup.mem_subgroupOf.mp he₁
    have hx2 : (⟨(y' : G) * e * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hEA' he)) (A'.inv_mem y'.2)⟩ : A') ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      apply Subtype.ext
      have he2 : e * e = 1 := by
        have := hR.elem₁.2 e he
        simpa [pow_two] using this
      calc ((y' : G) * e * (y' : G)⁻¹) * ((y' : G) * e * (y' : G)⁻¹)
          = (y' : G) * (e * e) * (y' : G)⁻¹ := by group
        _ = 1 := by rw [he2]; group
    have hy2 : (e₁ : A') ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      apply Subtype.ext
      have := hR.elem₁.2 e₁ he₁E
      simpa [pow_two] using this
    have hxy : π' ⟨(y' : G) * e * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hEA' he)) (A'.inv_mem y'.2)⟩ = π' e₁ := hπe₁.symm
    have heq := CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime
      (p := 2) π' hcentπ' hcopπ' hx2 hy2 hxy
    have heqG : (y' : G) * e * (y' : G)⁻¹ = (e₁ : G) := congrArg Subtype.val heq
    rw [heqG]
    exact he₁E
  have hyU : (y' : G) ∈ Subgroup.normalizer (U : Set G) := by
    rw [hU]
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have huV : u ∈ d.V := hu.1
    have huE : u ∈ E := by
      have hu' := hu
      rw [← hR.inf_eq] at hu'
      exact hu'.1
    let uA' : A' := ⟨u, hVA' huV⟩
    have hyuA' : (⟨(y' : G) * u * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hVA' huV)) (A'.inv_mem y'.2)⟩ : A') =
        y' * uA' * y'⁻¹ := rfl
    have hybarU' : ybar ∈ Subgroup.normalizer (barU : Set
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
      rwa [hbarU]
    have hprojmem : π' ⟨(y' : G) * u * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hVA' huV)) (A'.inv_mem y'.2)⟩ ∈ barU := by
      have h1 : π' ⟨(y' : G) * u * (y' : G)⁻¹,
          A'.mul_mem (A'.mul_mem y'.2 (hVA' huV)) (A'.inv_mem y'.2)⟩ =
          ybar * π' uA' * ybar⁻¹ := by
        rw [hyuA', map_mul, map_mul, map_inv, hy']
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp hybarU' (π' uA')).mp
        ⟨uA', Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    obtain ⟨u₁, hu₁, hπu₁⟩ := Subgroup.mem_map.mp hprojmem
    have hu₁U : (u₁ : G) ∈ U := by
      rw [hU]
      exact Subgroup.mem_subgroupOf.mp hu₁
    have hx2 : (⟨(y' : G) * u * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hVA' huV)) (A'.inv_mem y'.2)⟩ : A') ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      apply Subtype.ext
      have hu2 : u * u = 1 := by
        have := hR.elem₁.2 u huE
        simpa [pow_two] using this
      calc ((y' : G) * u * (y' : G)⁻¹) * ((y' : G) * u * (y' : G)⁻¹)
          = (y' : G) * (u * u) * (y' : G)⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hu₁E : (u₁ : G) ∈ E := by
      have hu' := hu₁U
      rw [hU] at hu'
      rw [← hR.inf_eq] at hu'
      exact hu'.1
    have hy2 : (u₁ : A') ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      apply Subtype.ext
      have := hR.elem₁.2 (u₁ : G) hu₁E
      simpa [pow_two] using this
    have hxy : π' ⟨(y' : G) * u * (y' : G)⁻¹,
        A'.mul_mem (A'.mul_mem y'.2 (hVA' huV)) (A'.inv_mem y'.2)⟩ = π' u₁ := hπu₁.symm
    have heq := CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime
      (p := 2) π' hcentπ' hcopπ' hx2 hy2 hxy
    have heqG : (y' : G) * u * (y' : G)⁻¹ = (u₁ : G) := congrArg Subtype.val heq
    rw [heqG]
    simpa [hU] using hu₁U
  have hfixU : ∀ u ∈ U, (y' : G) * u * (y' : G)⁻¹ = u → u = 1 := by
    intro u hu hfix
    have hu' := hu
    rw [hU] at hu'
    have huV : u ∈ d.V := hu'.1
    have huE : u ∈ E := by
      have hu'' := hu'
      rw [← hR.inf_eq] at hu''
      exact hu''.1
    let uA' : A' := ⟨u, hVA' huV⟩
    have hfixA' : y' * uA' * y'⁻¹ = uA' := by
      apply Subtype.ext
      simpa [uA'] using hfix
    have hbarfix : ybar * π' uA' * ybar⁻¹ = π' uA' := by
      calc ybar * π' uA' * ybar⁻¹ = π' y' * π' uA' * (π' y')⁻¹ := by rw [hy']
        _ = π' (y' * uA' * y'⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = π' uA' := by rw [hfixA']
    have hbaru : π' uA' ∈ barU := by
      rw [hbarU]
      refine ⟨Subgroup.mem_map_of_mem π' (Subgroup.mem_subgroupOf.mpr huV), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      have hvV : (v : G) ∈ d.V := Subgroup.mem_subgroupOf.mp hv
      rw [← map_mul, ← map_mul]
      exact congrArg π' (Subtype.ext
        (Subgroup.mem_centralizer_iff.mp hu'.2 (v : G) hvV))
    have hbaru' : π' uA' ∈ barV ⊓ centralizer (barV : Set
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
      rwa [hbarU] at hbaru
    have hπ1 : π' uA' = 1 := hfixbar _ hbaru' hbarfix
    have hu2 : (uA' : A') ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      apply Subtype.ext
      have := hR.elem₁.2 u huE
      simpa [uA', pow_two] using this
    have hone2 : (1 : A') ^ 2 ^ 1 = 1 := by simp
    have hxy : π' uA' = π' (1 : A') := by simpa using hπ1
    have heq := CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime
      (p := 2) π' hcentπ' hcopπ' hu2 hone2 hxy
    simpa [uA'] using congrArg (fun z : A' => (z : G)) heq
  obtain ⟨a, haA, hya⟩ := Subgroup.mem_map.mp y'.2
  have hya' : c * a * c⁻¹ = (y' : G) := hya
  have hcent_ut : (y' : G) * (u₀ * d.t) * (y' : G)⁻¹ = u₀ * d.t := by
    calc (y' : G) * (u₀ * d.t) * (y' : G)⁻¹
        = (c * a * c⁻¹) * (c * d.t * c⁻¹) * (c * a * c⁻¹)⁻¹ := by
          rw [hya', hc]
      _ = c * (a * d.t * a⁻¹) * c⁻¹ := by group
      _ = c * d.t * c⁻¹ := by rw [d.comm_t_of_mem haA, mul_inv_cancel_right]
      _ = u₀ * d.t := hc
  have hyu₀ : (y' : G) * u₀ * (y' : G)⁻¹ ∈ d.V ⊓ Subgroup.centralizer (d.V : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp (by rw [← hU]; exact hyU) u₀).mp hu₀U
    exact this
  have huU : ((y' : G) * u₀ * (y' : G)⁻¹) * u₀ ∈ U := by
    rw [hU]
    exact mul_mem hyu₀ hu₀U
  have hu1 : ((y' : G) * u₀ * (y' : G)⁻¹) * u₀ ≠ 1 := by
    intro h1
    apply hu₀1
    apply hfixU u₀ (by rw [hU]; exact hu₀U)
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hu₀2]
  refine ⟨(y' : G), hyE, hyU, ((y' : G) * u₀ * (y' : G)⁻¹) * u₀, huU, hu1, ?_⟩
  calc (y' : G) * t * (y' : G)⁻¹
      = (y' : G) * d.t * (y' : G)⁻¹ := by rw [← hdt]
    _ = (y' : G) * ((u₀ * u₀) * d.t) * (y' : G)⁻¹ := by rw [hu₀2, one_mul]
    _ = ((y' : G) * u₀ * (y' : G)⁻¹) * ((y' : G) * (u₀ * d.t) * (y' : G)⁻¹) := by group
    _ = ((y' : G) * u₀ * (y' : G)⁻¹) * (u₀ * d.t) := by rw [hcent_ut]
    _ = d.t * (((y' : G) * u₀ * (y' : G)⁻¹) * u₀) := by
      have huU' := huU
      rw [hU] at huU'
      calc ((y' : G) * u₀ * (y' : G)⁻¹) * (u₀ * d.t)
          = (((y' : G) * u₀ * (y' : G)⁻¹) * u₀) * d.t := by group
        _ = d.t * (((y' : G) * u₀ * (y' : G)⁻¹) * u₀) := d.V_comm_t huU'.1
    _ = t * (((y' : G) * u₀ * (y' : G)⁻¹) * u₀) := by rw [hdt]

theorem regular_translations_of_standard_row
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
      (A.subtype.comp φ)
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  N ≤ Subgroup.normalizer (E : Set G) ∧
    CFSG.LocalAnalysis.EvenBN.LinearThree.IsRegularNormalQ J t X (Nat.card F) ∧
    ∃ κ : X →* E,
      (∀ x : X, ((κ x : E) : G) = t * ((x : G) * t * (x : G)⁻¹)) ∧
      κ.ker = (Subgroup.centralizer (J : Set G)).subgroupOf X ∧
      Function.Surjective κ ∧
      ∀ a ∈ A ⊓ Subgroup.normalizer (E : Set G), ∀ x : X,
        ∀ hx : a * (x : G) * a⁻¹ ∈ X,
          ((κ ⟨a * (x : G) * a⁻¹, hx⟩ : E) : G) =
            a * ((κ x : E) : G) * a⁻¹ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hq4 : 4 < Nat.card F := by omega
  have hperf : Group.IsPerfect A := Group.IsPerfect.mk hA.1.1
  let : Group.IsPerfect A := hperf
  have hFf : FusionFacts A (Nat.card F) :=
    fusionFacts_of_odd_central_psl_three (F := F) hF A (e := e) hZ hcyc
  obtain ⟨d, hdt, -, hdV, hR⟩ :=
    exists_datum_with_standard_unipotent_radicals hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  have hα : d.Alpha := by
    apply Facts.alpha hFf d hq4 hR
    obtain ⟨g, hg1, hg2⟩ := CFSG.Monster.B.Recog.exists_conj_ne_commute hnonab ht
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hdt]
      simpa [inv_inv] using hg1
    · rw [hdt]
      simpa [inv_inv] using hg2
  let E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map (A.subtype.comp φ)
  let V : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map (A.subtype.comp φ)
  let U : Subgroup G := V ⊓ Subgroup.centralizer (V : Set G)
  let J : Subgroup G := E ⊔ Subgroup.zpowers t
  let N : Subgroup G := Subgroup.normalizer (J : Set G)
  let X : Subgroup G := N ⊓ Subgroup.centralizer (E : Set G)
  have hVd : d.V = V := hdV
  have hUeq : U = d.V ⊓ Subgroup.centralizer (d.V : Set G) := by rw [hVd]
  have hJd : J = E ⊔ Subgroup.zpowers d.t := by dsimp only [J]; rw [hdt]
  have hVA : V ≤ A := by
    intro v hv
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hv
    exact (φ u).2
  have hEA : E ≤ A := hR.le₁.trans (by rw [hVd]; exact hVA)
  have hNE : N ≤ Subgroup.normalizer (E : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    have hwJ : w ∈ J := by rw [hJd]; exact mem_sup_left hw
    have hnw : n * w * n⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hn w).mp hwJ
    have hnw' : n * w * n⁻¹ ∈ E ⊔ Subgroup.zpowers d.t := by rwa [hJd] at hnw
    have hnc : ¬ IsConj d.t (n * w * n⁻¹) := by
      intro hc
      exact Facts.not_isConj_of_mem hFf d hq4 hR (hEA hw)
        (hc.trans (isConj_iff.mpr ⟨n⁻¹, by group⟩))
    exact (Facts.not_isConj_iff_mem hFf d hq4 hR hα (Or.inl rfl) hnw').mp hnc
  let π : A →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
  have hkerπ : π.ker = Subgroup.center A := projective_ker_center A e
  have hoddπ : Odd (Nat.card π.ker) := by rwa [hkerπ]
  have hcopπ : Nat.Coprime (Nat.card π.ker) 2 := Nat.coprime_two_right.mpr hoddπ
  have hcentπ : π.ker ≤ Subgroup.center A := by rw [hkerπ]
  have hVsub : V.subgroupOf A = (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map φ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVA]
    rw [Subgroup.map_map]
  have hEsub : E.subgroupOf A = (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map φ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEA]
    rw [Subgroup.map_map]
  have hVmap : (V.subgroupOf A).map π =
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F := by
    rw [hVsub]
    calc ((CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map φ).map π
        = (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map (π.comp φ) := by
          rw [Subgroup.map_map]
      _ = (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipAll F).map
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) := by
          rw [show π.comp φ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F from hφproj]
      _ = CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F := rfl
  have hEmap : (E.subgroupOf A).map π =
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projRad F 0 := by
    rw [hEsub]
    calc ((CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map φ).map π
        = (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map (π.comp φ) := by
          rw [Subgroup.map_map]
      _ = (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) := by
          rw [show π.comp φ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F from hφproj]
      _ = CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projRad F 0 :=
          (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projRad_zero).symm
  have hVsyl : IsSylowOf 2 V A := by rw [← hVd]; exact d.V_isSylow
  have hV2 : IsPGroup 2 (V.subgroupOf A) := hVsyl.isPGroup.comap_subtype
  have hinjV : Function.Injective (π.comp (V.subgroupOf A).subtype) :=
    CFSG.RankThree.OddKernel.injective_restrict_of_odd π hoddπ hV2
  have hUleE : U ≤ E := by
    intro u hu
    have hu' := hu
    rw [hUeq] at hu'
    rw [← hR.inf_eq] at hu'
    exact hu'.1
  have hU2 : IsPGroup 2 (U.subgroupOf A) :=
    (hR.elem₁.isPGroup.comap_subtype).to_le (by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hUleE (Subgroup.mem_subgroupOf.mp hx)))
  have hpiU_le : (U.subgroupOf A).map π ≤
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F ⊓
        Subgroup.centralizer (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have huV : (u : G) ∈ V := huU.1
    refine ⟨?_, ?_⟩
    · rw [← hVmap]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr huV)
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rw [← hVmap] at hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (Subgroup.mem_centralizer_iff.mp huU.2 (v : G) hvV))
  have hcardUmap : Nat.card ((U.subgroupOf A).map π) = Nat.card F := by
    have hsub : Nat.card (U.subgroupOf A) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hUleE.trans hEA)).toEquiv
    have hinj : Function.Injective (π.comp (U.subgroupOf A).subtype) :=
      CFSG.RankThree.OddKernel.injective_restrict_of_odd π hoddπ hU2
    have hrange : (π.comp (U.subgroupOf A).subtype).range =
        (U.subgroupOf A).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcard : Nat.card ((U.subgroupOf A).map π) = Nat.card (U.subgroupOf A) := by
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hcard, hsub, hUeq]
    exact hR.card_center
  have hcardCenter : Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F ⊓
      Subgroup.centralizer (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F :
        Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F))) = Nat.card F :=
    (radicals_projUnip (K := F)).card_center
  have hpiU : (U.subgroupOf A).map π =
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F ⊓
        Subgroup.centralizer (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) :=
    Subgroup.eq_of_le_of_card_ge (H := (U.subgroupOf A).map π)
      (K := CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F ⊓
        Subgroup.centralizer (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)))
      hpiU_le (by rw [hcardUmap, hcardCenter])
  let ιA : Multiplicative (Fin 2 → F) →* A := φ.comp (rowSLHom F)
  let ιG : Multiplicative (Fin 2 → F) →* G := A.subtype.comp ιA
  have hπιA : π.comp ιA = radCoord F 0 := by
    ext v
    have h := DFunLike.congr_fun hφproj (rowSLHom F v)
    change ((e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ)
      (rowSLHom F v) = radCoord F 0 v
    rw [h]
    exact DFunLike.congr_fun (proj_comp_rowSLHom F) v
  let ι : Multiplicative (Fin 2 → F) ≃* E := literalRowEquiv A e φ hφproj
  have hι : ∀ v, (ι v : G) = ιG v := fun v => by
    have h := literalRowEquiv_apply A e φ hφproj v
    simpa [ι, ιA, ιG, rowSLHom] using h
  have hιA_mem_E : ∀ v, (ιA v : G) ∈ E := by
    intro v
    exact Subgroup.mem_map.mpr ⟨rowSLHom F v,
      rowSLHom_range F ▸ ⟨v, rfl⟩, rfl⟩
  have hιA_sq : ∀ v, (ιA v) * (ιA v) = 1 := by
    intro v
    apply A.subtype_injective
    have := hR.elem₁.2 (ιA v : G) (hιA_mem_E v)
    simpa [map_mul, pow_two] using this
  have hAxisMem : ∀ a : F, ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) ∈ U := by
    intro a
    have hιa : ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) =
        A.subtype (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 0 a)) := by
      rw [hι]
      simp [ιG, ιA, rowSLHom]
    have hmemE : ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) ∈ E :=
      Subgroup.mem_map.mpr ⟨CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 0 a,
        ⟨0, a, rfl⟩, by rw [hιa]; rfl⟩
    have hmemV : ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) ∈ V := by
      rw [← hVd]
      exact hR.le₁ hmemE
    have hprojmem : π ⟨((ι (Multiplicative.ofAdd ![a, 0]) : E) : G), hEA hmemE⟩ ∈
        CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F ⊓
          Subgroup.centralizer (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F :
            Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
      have h1 : π ⟨((ι (Multiplicative.ofAdd ![a, 0]) : E) : G), hEA hmemE⟩ =
          radCoord F 0 (Multiplicative.ofAdd ![a, 0]) := by
        change (π.comp ιA) (Multiplicative.ofAdd ![a, 0]) = _
        rw [hπιA]
      rw [h1, radCoord_axis]
      exact proj_unipU_mem_center a
    obtain ⟨u, hu, hπu⟩ := Subgroup.mem_map.mp (by rw [hpiU]; exact hprojmem)
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have huV : (u : G) ∈ V := by rw [← hVd]; exact hR.le₁ (hUleE huU)
    have heq : (⟨⟨((ι (Multiplicative.ofAdd ![a, 0]) : E) : G), hEA hmemE⟩,
        Subgroup.mem_subgroupOf.mpr hmemV⟩ : V.subgroupOf A) =
        ⟨u, Subgroup.mem_subgroupOf.mpr huV⟩ := by
      apply hinjV
      simpa [map_mul] using hπu.symm
    have hG : ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) = (u : G) :=
      congrArg Subtype.val (congrArg Subtype.val heq)
    rw [hG]
    exact huU
  let levA : SL(2, F) →* A := φ.comp (leviOne F)
  let levG : SL(2, F) →* G := A.subtype.comp levA
  have hπlev : ∀ B : SL(2, F), π (levA B) = leviProj F 0 B := by
    intro B
    have h := DFunLike.congr_fun hφproj (leviOne F B)
    change ((e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ)
      (leviOne F B) = leviProj F 0 B
    rw [h]
    exact (leviProj_zero_apply B).symm
  have hlev_conj : ∀ (B : SL(2, F)) (v : Multiplicative (Fin 2 → F)),
      levG B * (ι v : G) * (levG B)⁻¹ =
        ι (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) := by
    intro B v
    have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 3) F =>
        A.subtype (φ z)) (leviOne_conj_rowSLHom B v)
    calc levG B * (ι v : G) * (levG B)⁻¹
        = A.subtype (φ (leviOne F B * rowSLHom F v * (leviOne F B)⁻¹)) := by
            simp [levG, levA, hι, ιG, ιA, map_mul, map_inv]
      _ = A.subtype (φ (rowSLHom F (Multiplicative.ofAdd
            ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)))) := h
      _ = (ι (Multiplicative.ofAdd
            ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) : G) := by
            rw [hι]
            simp [ιG, ιA]
  have hlevN : ∀ B : SL(2, F), levG B ∈ Subgroup.normalizer (E : Set G) := by
    intro B
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨v, hv⟩ := ι.surjective ⟨w, hw⟩
    have hwv : w = ((ι v : E) : G) := (congrArg Subtype.val hv).symm
    rw [hwv, hlev_conj B v]
    exact (ι (Multiplicative.ofAdd
      ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v))).2
  let M : Subgroup G := A ⊓ Subgroup.normalizer (E : Set G)
  let Fid : Frame (⊤ : Subgroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F))
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projUnip F) F :=
    { φ := MonoidHom.id _
      injective := fun x y h => h
      range_eq := by ext x; simp
      map_projUnip := by simp }
  let barD := Fid.leviData 0
  have hEmapA : (E.subgroupOf A).map π =
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projRad F 0 := hEmap
  have hM_acts : ∀ a ∈ M, ∃ (c : Fˣ) (B : SL(2, F)), ActsBy ιG a c B := by
    intro a ha
    have haA : a ∈ A := ha.1
    have haN : a ∈ Subgroup.normalizer (E : Set G) := ha.2
    let aA : A := ⟨a, haA⟩
    have hπaN : π aA ∈ Subgroup.normalizer
        (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projRad F 0 :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp (by rwa [← hEmapA] at hx)
      have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
      have hconjE : a * (e : G) * a⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp haN (e : G)).mp heE
      rw [← hEmapA]
      refine Subgroup.mem_map.mpr ⟨aA * e * aA⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (by simpa [aA, map_mul, map_inv] using hconjE)
      · simp [aA, map_mul, map_inv]
    have hπaN' : π aA ∈ Subgroup.normalizer
        ((CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projRad F 0).map Fid.φ :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)) := by
      simpa [Fid] using hπaN
    obtain ⟨c, B, hB⟩ := barD.exists_actsBy (x := π aA) ⟨trivial, hπaN'⟩
    refine ⟨c, B, ?_⟩
    intro v
    let xA : A := aA * ιA (Multiplicative.ofAdd v) * aA⁻¹
    let yA : A := ιA (Multiplicative.ofAdd ((c : F) • (B • v)))
    have hx2 : (xA : A) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      show (aA * ιA (Multiplicative.ofAdd v) * aA⁻¹) *
        (aA * ιA (Multiplicative.ofAdd v) * aA⁻¹) = 1
      calc (aA * ιA (Multiplicative.ofAdd v) * aA⁻¹) *
            (aA * ιA (Multiplicative.ofAdd v) * aA⁻¹)
          = aA * (ιA (Multiplicative.ofAdd v) * ιA (Multiplicative.ofAdd v)) * aA⁻¹ := by
            group
        _ = 1 := by rw [hιA_sq]; group
    have hy2 : (yA : A) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      exact hιA_sq _
    have hbar : π aA * radCoord F 0 (Multiplicative.ofAdd v) * (π aA)⁻¹ =
        radCoord F 0 (Multiplicative.ofAdd ((c : F) • (B • v))) := by
      have h := hB v
      simpa [barD, Fid, Frame.leviData_ι] using h
    have hproj : π xA = π yA := by
      rw [show π xA = π aA * π (ιA (Multiplicative.ofAdd v)) * (π aA)⁻¹ by
            simp only [xA, map_mul, map_inv],
        show π (ιA (Multiplicative.ofAdd v)) =
          radCoord F 0 (Multiplicative.ofAdd v) from DFunLike.congr_fun hπιA _,
        show π yA = radCoord F 0 (Multiplicative.ofAdd ((c : F) • (B • v))) from
          DFunLike.congr_fun hπιA _]
      exact hbar
    have heq := CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime
      (p := 2) π hcentπ hcopπ hx2 hy2 hproj
    have heqG : a * (ιG (Multiplicative.ofAdd v)) * a⁻¹ =
        ιG (Multiplicative.ofAdd ((c : F) • (B • v))) := by
      simpa [aA, xA, yA, ιG, map_mul, map_inv] using
        congrArg (fun z : A => (z : G)) heq
    simpa [ActsBy] using heqG
  let K0 : Subgroup G := ⁅M, M⁆
  have hnat : ∀ g ∈ K0, ∃ B : SL(2, F), ∀ v : Fin 2 → F,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) := by
    intro g hg
    obtain ⟨B, hB⟩ := exists_SL_of_mem_commutator (ι := ιG) hM_acts hg
    refine ⟨B, fun v => ?_⟩
    have hsmul : ∀ (B' : SL(2, F)) (w : Fin 2 → F),
        B' • w = (B' : Matrix (Fin 2) (Fin 2) F) *ᵥ w := fun _ _ => rfl
    have h := hB v
    simp only [Units.val_one, one_smul] at h
    simp only [hι]
    simpa only [hsmul] using h
  have hperf : commutator (SL(2, F)) = ⊤ := by
    obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := F) (by omega)
    exact Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
  have hsurj : ∀ B : SL(2, F), ∃ g ∈ K0, ∀ v : Fin 2 → F,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) := by
    intro B
    have hBcomm : B ∈ ⁅(⊤ : Subgroup (SL(2, F))), (⊤ : Subgroup (SL(2, F)))⁆ := by
      rw [← _root_.commutator_def, hperf]
      trivial
    have h1 := Subgroup.mem_map_of_mem levG hBcomm
    rw [Subgroup.map_commutator] at h1
    have h2 : (⊤ : Subgroup (SL(2, F))).map levG ≤ M := by
      intro x hx
      obtain ⟨B', -, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨(levA B').2, hlevN B'⟩
    refine ⟨levG B, Subgroup.commutator_mono h2 h2 h1, fun v => ?_⟩
    have := hlev_conj B (Multiplicative.ofAdd v)
    simpa [toAdd_ofAdd, hι] using this
  obtain ⟨ym, hymE, hymU, um, humU, hum1, hymt⟩ :=
    exists_moving_element_of_standard_row hnonab hF A hA hZ e φ hφsurj hφproj hcyc t ht htC
  have hAxisAdd : ∀ a b : F,
      ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) *
        ((ι (Multiplicative.ofAdd ![b, 0]) : E) : G) =
      ((ι (Multiplicative.ofAdd ![a + b, 0]) : E) : G) := by
    intro a b
    have h1 : ι (Multiplicative.ofAdd ![a, 0]) * ι (Multiplicative.ofAdd ![b, 0]) =
        ι (Multiplicative.ofAdd ![a + b, 0]) := by
      rw [← map_mul, ← ofAdd_add]
      congr 2
      ext i
      fin_cases i <;> simp
    simpa using congrArg (fun z : E => (z : G)) h1
  have hAxisOne : ((ι (Multiplicative.ofAdd ![(0 : F), 0]) : E) : G) = 1 := by simp
  have hAxisExists : ∀ u ∈ U, ∃ a : F,
      ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) = u := by
    intro u hu
    let f : F → U := fun a =>
      ⟨((ι (Multiplicative.ofAdd ![a, 0]) : E) : G), hAxisMem a⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hG : ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) =
          ((ι (Multiplicative.ofAdd ![b, 0]) : E) : G) := congrArg (fun z : U => (z : G)) hab
      have hιeq : ι (Multiplicative.ofAdd ![a, 0]) =
          ι (Multiplicative.ofAdd ![b, 0]) := Subtype.ext hG
      have hveq : (Multiplicative.ofAdd ![a, 0] : Multiplicative (Fin 2 → F)) =
          Multiplicative.ofAdd ![b, 0] := ι.injective hιeq
      have := congrFun (congrArg Multiplicative.toAdd hveq) 0
      simpa using this
    obtain ⟨a, ha⟩ := (hf.bijective_of_nat_card_le (by rw [hUeq, hR.card_center])).2 ⟨u, hu⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨a0, ha0⟩ := hAxisExists um humU
  have ha0ne : a0 ≠ 0 := by
    intro h0
    apply hum1
    rw [← ha0, h0]
    simp
  have hyAxis : ∀ a : F, ∃ a' : F,
      ym * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) * ym⁻¹ =
        ((ι (Multiplicative.ofAdd ![a', 0]) : E) : G) := by
    intro a
    have hmemU : ym * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) * ym⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hymU _).mp (hAxisMem a)
    obtain ⟨a', ha'⟩ := hAxisExists _ hmemU
    exact ⟨a', ha'.symm⟩
  have hymJ : ym ∈ N := by
    change ym ∈ Subgroup.normalizer (J : Set G)
    rw [hJd]
    refine mem_normalizer_adj d hR.le₁ hymE ?_
    have : ym * t * ym⁻¹ = t * um := hymt
    rw [hdt, this]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hUleE humU))
  have hline : ∀ c : F, ∃ x ∈ N,
      (∀ a : F, ∃ b : F,
        x * (t * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G)) * x⁻¹ =
          t * ((ι (Multiplicative.ofAdd ![b, 0]) : E) : G)) ∧
      x * t * x⁻¹ = t * ((ι (Multiplicative.ofAdd ![c, 0]) : E) : G) := by
    intro c
    by_cases hc0 : c = 0
    · refine ⟨1, N.one_mem, ?_, ?_⟩
      · intro a
        refine ⟨a, ?_⟩
        group
      · rw [hc0, hAxisOne]
        group
    · let μ : Fˣ := Units.mk0 (c / a0) (div_ne_zero hc0 ha0ne)
      let s : G := levG (diagSL μ)
      have hsA : s ∈ A := (levA (diagSL μ)).2
      have hsN : s ∈ Subgroup.normalizer (E : Set G) := hlevN (diagSL μ)
      have hsJ : s ∈ N := by
        change s ∈ Subgroup.normalizer (J : Set G)
        rw [hJd]
        exact mem_normalizer_adj_of_mem_A d hR.le₁ ⟨hsA, hsN⟩
      have hst : s * t * s⁻¹ = t := by
        rw [← hdt]
        change (levG (diagSL μ)) * d.t * (levG (diagSL μ))⁻¹ = d.t
        rw [d.comm_t_of_mem hsA, mul_inv_cancel_right]
      have hμa0 : (μ : F) * a0 = c := by
        rw [Units.val_mk0, div_mul_cancel₀ c ha0ne]
      have hlineAxis : ∀ a : F, ∃ b : F,
          s * ym * (t * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G)) *
            (s * ym)⁻¹ = t * ((ι (Multiplicative.ofAdd ![b, 0]) : E) : G) := by
        intro a
        obtain ⟨a', ha'⟩ := hyAxis a
        refine ⟨(μ : F) * (a0 + a'), ?_⟩
        calc s * ym * (t * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G)) * (s * ym)⁻¹
            = s * (ym * (t * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G)) * ym⁻¹) *
                s⁻¹ := by group
          _ = s * ((t * um) * (ym * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) *
                ym⁻¹)) * s⁻¹ := by
              rw [show ym * (t * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G)) * ym⁻¹ =
                (ym * t * ym⁻¹) *
                  (ym * ((ι (Multiplicative.ofAdd ![a, 0]) : E) : G) * ym⁻¹) by group,
                hymt, ha']
          _ = s * (t * ((ι (Multiplicative.ofAdd ![a0, 0]) : E) : G) *
                ((ι (Multiplicative.ofAdd ![a', 0]) : E) : G)) * s⁻¹ := by
              rw [← ha0, ha']
          _ = s * (t * ((ι (Multiplicative.ofAdd ![a0 + a', 0]) : E) : G)) * s⁻¹ := by
              have hprod : t * ((ι (Multiplicative.ofAdd ![a0, 0]) : E) : G) *
                  ((ι (Multiplicative.ofAdd ![a', 0]) : E) : G) =
                  t * ((ι (Multiplicative.ofAdd ![a0 + a', 0]) : E) : G) := by
                rw [mul_assoc, hAxisAdd a0 a']
              rw [hprod]
          _ = (s * t * s⁻¹) * (s * ((ι (Multiplicative.ofAdd ![a0 + a', 0]) : E) : G) *
                s⁻¹) := by group
          _ = t * ((ι (Multiplicative.ofAdd ![(μ : F) * (a0 + a'), 0]) : E) : G) := by
              rw [hst, hlev_conj]
              simp only [toAdd_ofAdd]
              rw [diagSL_mulVec]
      have hxt : s * ym * t * (s * ym)⁻¹ =
          t * ((ι (Multiplicative.ofAdd ![c, 0]) : E) : G) := by
        calc s * ym * t * (s * ym)⁻¹
            = s * (ym * t * ym⁻¹) * s⁻¹ := by group
          _ = s * (t * um) * s⁻¹ := by rw [hymt]
          _ = s * (t * ((ι (Multiplicative.ofAdd ![a0, 0]) : E) : G)) * s⁻¹ := by
              rw [← ha0]
          _ = (s * t * s⁻¹) * (s * ((ι (Multiplicative.ofAdd ![a0, 0]) : E) : G) * s⁻¹) := by
              group
          _ = t * ((ι (Multiplicative.ofAdd ![(μ : F) * a0, 0]) : E) : G) := by
              rw [hst, hlev_conj]
              simp only [toAdd_ofAdd]
              rw [diagSL_mulVec]
          _ = t * ((ι (Multiplicative.ofAdd ![c, 0]) : E) : G) := by rw [hμa0]
      exact ⟨s * ym, N.mul_mem hsJ hymJ, hlineAxis, hxt⟩
  have ht2 : t * t = 1 := by rw [← hdt]; exact d.t_mul_self
  have hWt : E ≤ Subgroup.centralizer ({t} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hdt]
    exact d.V_comm_t (hR.le₁ he)
  have hXE : N ≤ Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro n hn
    change n ∈ Subgroup.normalizer (J : Set G)
    exact hn
  have hK0M : K0 ≤ M := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy)
  have hK : K0 ≤ N ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro g hg
    have hgM : g ∈ M := hK0M hg
    refine ⟨?_, ?_⟩
    · change g ∈ Subgroup.normalizer (J : Set G)
      rw [hJd]
      exact mem_normalizer_adj_of_mem_A d hR.le₁ ⟨hgM.1, hgM.2⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← hdt]
      exact d.comm_t_of_mem hgM.1
  have hKn : ∀ x ∈ N ⊓ Subgroup.centralizer ({t} : Set G), ∀ g ∈ K0,
      x * g * x⁻¹ ∈ K0 := by
    intro x hx g hg
    have hxNA : x ∈ Subgroup.normalizer (A : Set G) :=
      hA.mem_normalizer_of_commute htC ht (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
    have hxE : x ∈ Subgroup.normalizer (E : Set G) := hNE hx.1
    have hxNN : x ∈ Subgroup.normalizer
        (Subgroup.normalizer (E : Set G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x))
        (Subgroup.normalizer (E : Set G)) = Subgroup.normalizer (E : Set G)
      calc Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x))
            (Subgroup.normalizer (E : Set G))
          = Subgroup.normalizer
              (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) (E : Subgroup G)) :=
            Subgroup.map_equiv_normalizer_eq (E : Subgroup G) (MulAut.conj x)
        _ = Subgroup.normalizer (E : Set G) := by
            rw [show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) (E : Subgroup G) = E from
              (Subgroup.mem_normalizer_iff_map_conj_eq.mp hxE)]
    have hn : ∀ y ∈ M, x * y * x⁻¹ ∈ M := by
      intro y hy
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxNA y).mp hy.1,
        (Subgroup.mem_normalizer_iff.mp hxNN y).mp hy.2⟩
    exact CFSG.OddStandard.Seitz77.conj_mem_commutator hn hg
  obtain ⟨T, hTX, hTn, hTC, hCT, htr⟩ :=
    exists_regularNormal_of_natural (K := K0) (X := N) (W := E) ι ht2 hWt hNE hXE hK hKn hnat hsurj hline
  have hTeq : T = X := by
    apply le_antisymm
    · intro y hy
      exact ⟨hTX hy, hTC hy⟩
    · intro x hx
      have hxJt : x * t * x⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hx.1 t).mp (by
          rw [hJd, ← hdt]
          exact mem_sup_right (mem_zpowers d.t))
      have hxJd : x * t * x⁻¹ ∈ E ⊔ Subgroup.zpowers d.t := by
        have := hxJt
        rwa [hJd] at this
      have hnotE : x * t * x⁻¹ ∉ E := fun hE =>
        (Facts.not_isConj_of_mem hFf d hq4 hR (hEA hE))
          (isConj_iff.mpr ⟨x, by rw [hdt]⟩)
      rcases (d.mem_adj_iff hR.le₁).mp hxJd with hE | hEt
      · exact (hnotE hE).elim
      · let e : G := (x * t * x⁻¹) * d.t
        have heE : e ∈ E := hEt
        have hy_eq : x * t * x⁻¹ = t * e := by
          calc x * t * x⁻¹ = (x * t * x⁻¹) * (d.t * d.t) := by
                rw [d.t_mul_self, mul_one]
            _ = ((x * t * x⁻¹) * d.t) * d.t := by group
            _ = e * d.t := rfl
            _ = d.t * e := d.V_comm_t (hR.le₁ heE)
            _ = t * e := by rw [hdt]
        obtain ⟨z, hzT, hzt⟩ := htr e heE
        have hCJ : z⁻¹ * x ∈ Subgroup.centralizer (J : Set G) := by
          have hzCE : z ∈ Subgroup.centralizer (E : Set G) := hTC hzT
          have hxCE : x ∈ Subgroup.centralizer (E : Set G) := hx.2
          have hCE : z⁻¹ * x ∈ Subgroup.centralizer (E : Set G) :=
            (Subgroup.centralizer (E : Set G)).mul_mem
              ((Subgroup.centralizer (E : Set G)).inv_mem hzCE) hxCE
          have hzt' : z * t * z⁻¹ = x * t * x⁻¹ := by rw [hzt, hy_eq]
          have hfix : (z⁻¹ * x) * t * (z⁻¹ * x)⁻¹ = t := by
            calc (z⁻¹ * x) * t * (z⁻¹ * x)⁻¹ = z⁻¹ * (x * t * x⁻¹) * z := by group
              _ = z⁻¹ * (z * t * z⁻¹) * z := by rw [← hzt']
              _ = t := by group
          have hct : (z⁻¹ * x) * t = t * (z⁻¹ * x) := by
            calc (z⁻¹ * x) * t = ((z⁻¹ * x) * t * (z⁻¹ * x)⁻¹) * (z⁻¹ * x) := by
                  group
              _ = t * (z⁻¹ * x) := by rw [hfix]
          have hCJd := (mem_centralizer_adj_iff d hR.le₁).mpr
            ⟨hCE, by rw [hdt]; exact hct⟩
          simpa [hJd] using hCJd
        have hzN : z ∈ N := hTX hzT
        have hzx : z⁻¹ * x ∈ T := hCT ⟨N.mul_mem (N.inv_mem hzN) hx.1, hCJ⟩
        have hx_eq : x = z * (z⁻¹ * x) := by group
        rw [hx_eq]
        exact T.mul_mem hzT hzx
  have hTeq' : T = Subgroup.normalizer ((E ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (E : Set G) := hTeq
  have hCJT : Subgroup.centralizer (J : Set G) ≤ T := fun x hx =>
    hCT ⟨Subgroup.centralizer_le_normalizer (J : Set G) hx, hx⟩
  have hXt : ∀ x ∈ T, t * (x * t * x⁻¹) ∈ E := by
    intro x hx
    have hxN : x ∈ N := hTX hx
    have hxE : x ∈ Subgroup.normalizer (E : Set G) := hNE hxN
    have := Plane.conj_mem_coset ht2 hWt hxE hxN
    rwa [inv_eq_of_mul_eq_one_right ht2] at this
  obtain ⟨κT, hκT⟩ := exists_commMap (W := E) (T := T) ht2 hTC hXt
  have hκsurj : Function.Surjective κT := by
    intro w
    obtain ⟨x, hxT, hxt⟩ := htr w w.2
    refine ⟨⟨x, hxT⟩, Subtype.ext ?_⟩
    rw [hκT]
    show t * (x * t * x⁻¹) = w
    rw [hxt, ← mul_assoc, ht2, one_mul]
  have hkerT : κT.ker = (Subgroup.centralizer (J : Set G)).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : ((κT x : E) : G) = 1 := congrArg Subtype.val hx
      rw [hκT] at h1
      have h2 : t * ((x : G) * t) = (x : G) := by
        calc t * ((x : G) * t) = t * ((x : G) * t * (x : G)⁻¹) * (x : G) := by group
          _ = 1 * (x : G) := by rw [h1]
          _ = (x : G) := one_mul _
      have hxt : (x : G) * t = t * (x : G) := by
        calc (x : G) * t = (t * t) * ((x : G) * t) := by rw [ht2, one_mul]
          _ = t * (t * ((x : G) * t)) := by group
          _ = t * (x : G) := by rw [h2]
      have hxt_d : (x : G) * d.t = d.t * (x : G) := by
        rw [hdt]
        exact hxt
      rw [show Subgroup.centralizer (J : Set G) =
          Subgroup.centralizer ((E ⊔ Subgroup.zpowers d.t : Subgroup G) : Set G) by rw [hJd]]
      exact (mem_centralizer_adj_iff d hR.le₁).mpr ⟨hTC x.2, hxt_d⟩
    · intro hx
      have hx' := (mem_centralizer_adj_iff d hR.le₁).mp (by simpa [hJd] using hx)
      have hxt : (x : G) * t = t * (x : G) := by
        rw [← hdt]
        exact hx'.2
      apply Subtype.ext
      rw [hκT, OneMemClass.coe_one, hxt]
      calc t * (t * (x : G) * (x : G)⁻¹) = t * t := by group
        _ = 1 := ht2
  have hregT : IsRegularNormalQ J t T (Nat.card F) := by
    refine ⟨hTX, hCJT, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTX).mp hTn
    · intro p hp
      have hpT : p * p ∈ T := T.mul_mem hp hp
      have hpker : (⟨p * p, hpT⟩ : T) ∈ κT.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨p * p, hpT⟩ : T) = ⟨p, hp⟩ * ⟨p, hp⟩ := rfl
        rw [e, map_mul]
        apply Subtype.ext
        have hsq : (κT ⟨p, hp⟩) * (κT ⟨p, hp⟩) = 1 := by
          apply Subtype.ext
          have := hR.elem₁.2 ((κT ⟨p, hp⟩) : G) (κT ⟨p, hp⟩).2
          simpa [pow_two] using this
        rw [hsq]
      have := Subgroup.mem_subgroupOf.mp (hkerT ▸ hpker)
      simpa using this
    · intro p hp r hr
      have hpr : p * r * p⁻¹ * r⁻¹ ∈ T :=
        T.mul_mem (T.mul_mem (T.mul_mem hp hr) (T.inv_mem hp)) (T.inv_mem hr)
      have hprker : (⟨p * r * p⁻¹ * r⁻¹, hpr⟩ : T) ∈ κT.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨p * r * p⁻¹ * r⁻¹, hpr⟩ : T) =
            ⟨p, hp⟩ * ⟨r, hr⟩ * ⟨p, hp⟩⁻¹ * ⟨r, hr⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
        apply Subtype.ext
        have hc := comm_of_isElemAbelian hR.elem₁ (κT ⟨p, hp⟩).2 (κT ⟨r, hr⟩).2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
        rw [hc]
        group
      have := Subgroup.mem_subgroupOf.mp (hkerT ▸ hprker)
      simpa using this
    · rw [inf_relIndex_left]
      show ((Subgroup.centralizer (J : Set G)).subgroupOf T).index = _
      rw [← hkerT, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hκsurj,
        Subgroup.card_top, hR.card₁]
    · intro z hzJ hconj
      have hconj' : IsConj d.t z := by simpa [← hdt] using hconj
      have hnotE : z ∉ E := fun hE =>
        (Facts.not_isConj_of_mem hFf d hq4 hR (hEA hE)) hconj' 
      have hzJd : z ∈ E ⊔ Subgroup.zpowers d.t := by
        have := hzJ
        rwa [hJd] at this
      rcases (d.mem_adj_iff hR.le₁).mp hzJd with hE | hEt
      · exact (hnotE hE).elim
      · let e : G := z * d.t
        have heE : e ∈ E := hEt
        have hz_eq : z = t * e := by
          calc z = (z * d.t) * d.t := by rw [mul_assoc, d.t_mul_self, mul_one]
            _ = e * d.t := rfl
            _ = d.t * e := d.V_comm_t (hR.le₁ heE)
            _ = t * e := by rw [hdt]
        obtain ⟨x, hxT, hxt⟩ := htr e heE
        exact ⟨x, hxT, by rw [hxt, hz_eq]⟩
  dsimp only
  rw [← hTeq']
  refine ⟨hNE, hregT, ?_⟩
  refine ⟨κT, hκT, hkerT, hκsurj, ?_⟩
  intro a ha x hx
  have hc : a * t * a⁻¹ = t := by
    rw [← hdt]
    calc a * d.t * a⁻¹ = d.t * a * a⁻¹ := by rw [d.comm_t_of_mem ha.1]
      _ = d.t := by group
  rw [hκT, hκT]
  calc t * ((a * (x : G) * a⁻¹) * t * (a * (x : G) * a⁻¹)⁻¹)
      = (a * t * a⁻¹) * (a * (x : G) * a⁻¹) * (a * t * a⁻¹) *
          (a * (x : G) * a⁻¹)⁻¹ := by rw [hc]; group
    _ = a * (t * ((x : G) * t * (x : G)⁻¹)) * a⁻¹ := by group

end CFSG.ComponentClassification.GS79bSec5

end
