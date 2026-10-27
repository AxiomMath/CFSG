module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SChain
public import CFSG.ClassicalInvolution.Q3.Q3WASTInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3V.Lift
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  planeGroup_stdPlane isHyperbolicPlane_stdPlane longBlock shortBlock)

local notation "F₃" => GaloisField 3 1


theorem exists_partner_f4 (hrow : F4Row3) (hpart : F4PartnerFact3) (hP : Q3TC.ProductP1Input3)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {Kf : Fin 4 → Subgroup G} {z₀ : G} (hR : RouteD3Setup (Kf 0) z₀)
    (hK : IsMemberFrame (conjClass3 (Kf 0)) Kf)
    {c : CCoreR 3 (conjClass3 (Kf 0)) (Kf 0) z₀} (l : LayerR c)
    (h0 : IsLabLift 3 (conjClass3 (Kf 0)) Kf 0 l.Θ) {Θ1 Θ3 : StatedSp 3 F₃ →* G}
    (h1 : IsLabLift 3 (conjClass3 (Kf 0)) Kf 1 Θ1) (h3 : IsLabLift 3 (conjClass3 (Kf 0)) Kf 3 Θ3)
    {z₃ : G} (hz₃ : IsClassicalMember3 (Kf 3) z₃) {M N : Subgroup G}
    (hM : M ∈ conjClass3 (Kf 0)) (hM1 : Commutes M (Kf 1)) (hM2 : Commutes M (Kf 2))
    (hN : N ∈ conjClass3 (Kf 0)) (hN0 : Commutes N (Kf 0)) (hN3 : Commutes N (Kf 3))
    (hMN : ¬ Commutes M N) :
    ∃ β ∈ conjClass3 (Kf 0), ∃ t : G, IsClassicalMember3 β t ∧
      (∃ W, WeakCT.LinearBlockStandardPair F₃ W (Kf 0) β) ∧
        ∃ W, WeakCT.LinearBlockStandardPair F₃ W β (Kf 3) := by
  classical
  set Ω := conjClass3 (Kf 0) with hΩdef
  have hΩ : InClass3 Ω := c.hΩ
  have hex : ExactMembers3 Ω := c.hex
  have hz₀ : IsClassicalMember3 (Kf 0) z₀ := c.hz
  have hnonab : ∀ M' ∈ Ω, ¬ Commutes M' M' := by
    rintro M' ⟨g, rfl⟩ hM'
    exact not_commutes_self3 hz₀ ((commutes_conjSub_iff g).1 hM')
  have e03 : (0 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have hK3 : (planeGroup (stdPlane F₃ 3 2)).map l.Θ = Kf 3 := (h0.lab 2).trans (congrArg Kf e03)
  have hzne : z₀ ≠ z₃ := by
    intro e
    refine layerNotMemPlane l (isHyperbolicPlane_stdPlane (2 : Fin 3)) ?_
    rw [hK3, e]
    exact hz₃.mem
  have hKK₃ : Commutes (Kf 0) (Kf 3) := hK.comm 0 3 (by decide)
  have hne03 : Kf 0 ≠ Kf 3 := fun e =>
    hnonab (Kf 0) (hK.mem 0) (by have := hKK₃; rwa [← e] at this)
  obtain ⟨hP1x, hO3x⟩ := hP G (Kf 0) z₀ hR (Kf 3) (hK.mem 3) z₃ hz₃ hKK₃ hzne
  obtain ⟨hlink3, hlinkN, hlinkV⟩ := linked_visible_f4 hΩ hnonab hK l h0 h1 h3 hz₃ hM hM1 hM2 hN
    hN0 hN3 hMN
  have hz2 : z₀ * z₀ = 1 := mul_self_of_isClassicalMember3 hz₀
  have hxne : z₀ * z₃ ≠ 1 := by
    intro h1'
    apply hzne
    have h2 : z₃ = z₀⁻¹ := eq_inv_of_mul_eq_one_right h1'
    rw [h2, inv_eq_of_mul_eq_one_right hz2]
  have hxc : ¬ ({z₀ * z₃} : Set G) ⊆ Subgroup.center G :=
    CoreAssembly.singleton_not_subset_center hnab hxne
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {z₀ * z₃} hxc
  have hKx : Kf 0 ∈ centralizingMembers Ω {z₀ * z₃} :=
    ⟨hK.mem 0, le_centralizer_mul_of_le3 (isSubnormal_le hz₀.subnormal)
      (le_centralizer_of_commutes3 hKK₃ hz₃.mem)⟩
  obtain ⟨i₁, hKi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨Kf 0, hKx, rfl⟩)
  have hall : ∀ N' ∈ centralizingMembers Ω {z₀ * z₃, z₀},
      locImg Ω (z₀ * z₃) N' ≤ (D.hom i₁).range := fun N' hN' =>
    linked_le_range3 hΩ hex hP1x hO3x D (hlinkV N' hN') hKi
  have hK3x : Kf 3 ∈ centralizingMembers Ω {z₀ * z₃} := hlink3.mem_centralizingMembers hKx
  have hNx : N ∈ centralizingMembers Ω {z₀ * z₃} := hlinkN.mem_centralizingMembers hKx
  have hKc : Kf 0 ∈ compMembers3 Ω (z₀ * z₃) D i₁ := ⟨hKx, hKi⟩
  have hK3c : Kf 3 ∈ compMembers3 Ω (z₀ * z₃) D i₁ :=
    ⟨hK3x, linked_le_range3 hΩ hex hP1x hO3x D hlink3 hKi⟩
  have hNc : N ∈ compMembers3 Ω (z₀ * z₃) D i₁ :=
    ⟨hNx, linked_le_range3 hΩ hex hP1x hO3x D hlinkN hKi⟩
  have hnA1 : ¬ IsA1Comp3 D i₁ := fun hA =>
    hne03 (eq_of_mem_compMembers_a13 hΩ hex hP1x hO3x hA hKc hK3c)
  rcases kind_cases_of_not_a1 D hnA1 with ⟨t', n', hft, hadm, hk⟩ | hk
  swap
  · exfalso
    exact not_commutes_of_m11_comp3 hΩ hex hP1x hO3x hk hKc hK3c hKK₃
  have hexc : t' ≠ .G2 ∧ t' ≠ .trialityD4 := by
    obtain ⟨w₀, hw₀⟩ := hΩ.classical N hN
    have key : (t' = .G2 ∨ t' = .trialityD4) → False := fun ht' =>
      hzne (eq_involution_of_commuting_in_g2d43 hΩ hex hP1x hO3x D ht' hadm hk hNc hKc hK3c hw₀
        hz₀ hz₃ hN0 hN3)
    exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩
  obtain ⟨X, hXr⟩ := exists_xctx3_of_comp hΩ hex hP1x hO3x D hk hft hadm hexc.1 hexc.2
  have hvisX : ∀ N' ∈ centralizingMembers Ω {z₀ * z₃, z₀},
      locImg Ω (z₀ * z₃) N' ≤ X.ψ.range := fun N' hN' => by
    rw [hXr]
    exact hall N' hN'
  obtain ⟨R₀, hR₀, hKR₀⟩ := X.fam_range (Kf 0) hKx (by rw [hXr]; exact hKi)
  obtain ⟨φP, hφP, hKP⟩ := exists_visible_equiv_f4_3 l (by rw [hK3]; exact hz₃)
  obtain ⟨ht1, hn1⟩ := shape_of_visible_f4 X hrow hft hadm hexc.1 hexc.2 hz₀ hKx hR₀ hKR₀ hvisX
    φP hφP hKP
  subst ht1 hn1
  have hcf := (yData3_odd (by norm_num) hadm).central
  obtain ⟨R₃, hR₃, hJR⟩ := X.fam_range (Kf 3) hK3x (by rw [hXr]; exact hK3c.2)
  obtain ⟨β, hβx, hW₁, hW₂⟩ := exists_partner_of_xctx hpart X hcf hz₀ hz₃ rfl hKx hK3x hKK₃ hne03
    hR₀ hR₃ hKR₀ hJR
  obtain ⟨t, ht⟩ := hΩ.classical β hβx.1
  exact ⟨β, hβx.1, t, ht, hW₁, hW₂⟩

theorem chainPiece3F4_based (hrow : F4Row3) (hpart : F4PartnerFact3)
    (hP : Q3TC.ProductP1Input3) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {Kf : Fin 4 → Subgroup G} {z₀ : G}
    (hR : RouteD3Setup (Kf 0) z₀)
    (hshape : LocalShapeC3 1 (CompData.model .PSp 3) (conjClass3 (Kf 0)) z₀)
    (hO3 : LocalOddThreeFree3 (conjClass3 (Kf 0)) z₀)
    (hK : IsMemberFrame (conjClass3 (Kf 0)) Kf)
    (hnc : ¬ Commutes (layerSub (conjClass3 (Kf 0)) Kf 0 3)
      (layerSub (conjClass3 (Kf 0)) Kf 1 2)) :
    F4Chain3 (Kf 0) := by
  classical
  set Ω := conjClass3 (Kf 0) with hΩdef
  have hΩ : InClass3 Ω := hR.inClass
  have hex : ExactMembers3 Ω := hR.setup.1
  have hz₀ : IsClassicalMember3 (Kf 0) z₀ := hR.cls
  have hKmem : Kf 0 ∈ Ω := ⟨1, conjSub_one _⟩
  have hnonab : ∀ M' ∈ Ω, ¬ Commutes M' M' := by
    rintro M' ⟨g, rfl⟩ hM'
    exact not_commutes_self3 hz₀ ((commutes_conjSub_iff g).1 hM')
  have hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g (Kf 0) := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨d⟩ := nonempty_cdictR (by norm_num : 2 ≤ 3) hΩ hKmem hz₀ hshape
  let c : CCoreR 3 Ω (Kf 0) z₀ := ⟨by norm_num, hΩ, hex, hKmem, hz₀, hR.setup.2, hO3, d⟩
  obtain ⟨l⟩ := c.nonempty_layer
  obtain ⟨γ, hγ⟩ := exists_labGamma (by norm_num) hnonab hK (l := 0) (layerIsLocLift l)
  let l' := relabelLayer l γ
  have h0 : IsLabLift 3 Ω Kf 0 l'.Θ := hγ
  have hlab : ∀ i : Fin 4, ∃ Θ : StatedSp 3 F₃ →* G, IsLabLift 3 Ω Kf i Θ := by
    intro i
    obtain ⟨g, hg⟩ := hK.mem i
    have hlift : IsLocLift 3 Ω (Kf i) ((MulAut.conj g).toMonoidHom.comp l.Θ) := by
      rw [← hg]
      exact Frame.IsLocLift.conj hΩ.conjInvariant (layerIsLocLift l) g
    exact Frame.exists_labLift (by norm_num) hnonab hK hlift
  obtain ⟨Θ1, hΘ1⟩ := hlab 1
  obtain ⟨Θ3, hΘ3⟩ := hlab 3
  obtain ⟨M, hM, hM1, hM2, N, hN, hN0, hN3, hMN⟩ := exists_gen_pair hnc
  obtain ⟨w₃, hw₃⟩ := hΩ.classical (Kf 3) (hK.mem 3)
  obtain ⟨β, hβΩ, t, ht, hW₁, hW₂⟩ := exists_partner_f4 hrow hpart hP hnab hR hK l' h0 hΘ1 hΘ3
    hw₃ hM hM1 hM2 hN hN0 hN3 hMN
  have e03 : (0 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have hK3 : (planeGroup (stdPlane F₃ 3 2)).map l'.Θ = Kf 3 :=
    (h0.lab 2).trans (congrArg Kf e03)
  have htz : t * z₀ * t⁻¹ = z₀ := by
    obtain ⟨W, hW⟩ := hW₁
    have hzt : z₀ * t = t * z₀ := Gaps.standardPair_involutions_commute Q3Z.gf3_two_ne_zero hW
      hz₀.mem ht.mem hz₀.orderOf_eq_two ht.orderOf_eq_two
    rw [mul_inv_eq_iff_eq_mul]
    exact hzt.symm
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_adapted_nodes l' ht (by rw [hK3]; exact hW₂) htz
  obtain ⟨ι, hι, D, hcard, -⟩ := hshape
  have hD : Nat.card ι ≤ 4 := by omega
  have hker := (Frame.IsLocLift.relabel (layerIsLocLift l') g).ker_le
  obtain ⟨U, hU1, hUc, hUl, hUs⟩ := f4Chain3_of_nodes hΩ hex hz₀ hsingle hR.setup.2 hO3 D hD hβΩ
    ht (hK.mem 3) hW₂ (l'.Θ.comp (MulAut.conj g).toMonoidHom) hker (hg1.trans hK3) hg2 hg3
  exact ⟨U, hU1, hUc, hUl, hUs⟩

theorem chainPiece3F4_of_model (hrow : F4Row3) (hpart : F4PartnerFact3)
    (hP : Q3TC.ProductP1Input3) : ChainPiece3F4 := by
  intro G _ _ _ hnab K z hR hshape hO3 ⟨Kf, hKf, hnc⟩
  obtain ⟨Kf', hKf', h0, hnc'⟩ := exists_frame_not_r1' hKf hnc
  have hK₀ : Kf' 0 ∈ conjClass3 K := hKf'.mem 0
  obtain ⟨z₀, hz₀⟩ := hR.inClass.classical (Kf' 0) hK₀
  have hR₀ : RouteD3Setup (Kf' 0) z₀ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR hK₀ hz₀
  have hcl : conjClass3 (Kf' 0) = conjClass3 K := Q3TC.conjClass3_eq_of_mem hK₀
  obtain ⟨g, hg⟩ := id hK₀
  have hz₀' : z₀ = g * z * g⁻¹ := involution_unique3 hz₀ (hg ▸ hR.cls.conj g)
  have hshape₀ : LocalShapeC3 1 (CompData.model .PSp 3) (conjClass3 (Kf' 0)) z₀ := by
    rw [hcl, hz₀']
    exact hshape.conjShape3 hR.inClass.conjInvariant g
  have hO3₀ : LocalOddThreeFree3 (conjClass3 (Kf' 0)) z₀ := by
    rw [hcl, hz₀']
    exact localOddThreeFree3_conj hR.inClass.conjInvariant g z hO3
  have hK' : IsMemberFrame (conjClass3 (Kf' 0)) Kf' := by
    rw [hcl]
    exact hKf'
  have hnc'' : ¬ Commutes (layerSub (conjClass3 (Kf' 0)) Kf' 0 3)
      (layerSub (conjClass3 (Kf' 0)) Kf' 1 2) := by
    rw [hcl]
    exact hnc'
  obtain ⟨U, hU, rest⟩ := chainPiece3F4_based hrow hpart hP hnab hR₀ hshape₀ hO3₀ hK' hnc''
  exact ⟨U, by rw [← hcl]; exact hU, rest⟩

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
