module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinCent
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co13Gen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.RankThree.Chevalley (baseChangeGL_rootSL2_of_field)


variable {τ : Tag} {K : Type} [Field K]

theorem map_entrywise_rootSpan (σ : K ≃+* K) (S : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ K S).map (Units.map (entrywiseHom σ.toRingHom)) = rootSpan τ K S :=
  map_rootSpan_of_forall fun α _ => map_entrywise_rootSubgroup σ α

theorem map_perpJ_entrywiseAdjointAut (σ : K ≃+* K) :
    ((rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K)).map
        (entrywiseAdjointAut τ σ).toMonoidHom =
      (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) := by
  have hS := map_entrywise_rootSpan (τ := τ) σ (perpRoots τ)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : ModGL τ K) ∈ rootSpan τ K (perpRoots τ) := hy
    rw [Subgroup.mem_subgroupOf]
    change ((entrywiseAdjointAut τ σ y : ↥(adjointGroup τ K)) : ModGL τ K) ∈ _
    rw [coe_entrywiseAdjointAut, ← hS]
    exact Subgroup.mem_map_of_mem _ hy'
  · intro hx
    rw [Subgroup.mem_subgroupOf, ← hS] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, rootSpan_le_adjointGroup K _ hy⟩, Subgroup.mem_subgroupOf.2 hy, Subtype.ext ?_⟩
    change ((entrywiseAdjointAut τ σ ⟨y, _⟩ : ↥(adjointGroup τ K)) : ModGL τ K) = x
    rw [coe_entrywiseAdjointAut]
    exact hyx

theorem baseChangeGL_rootDiagUnit_mulSingle_neg_one {L : Type} [Field L] (f : K →+* L)
    (j : Fin τ.rank) :
    baseChangeGL f (rootDiagUnit τ (Pi.mulSingle j (-1 : Kˣ))) =
      rootDiagUnit τ (Pi.mulSingle j (-1 : Lˣ)) := by
  rw [baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  by_cases h : i = j
  · subst h
    simp
  · simp [Pi.mulSingle_eq_of_ne h]

theorem glaPLayer_perpJ_inf_fix_ne_bot [Finite K] (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K)
    (hpK0 : p ∣ Nat.card (fixSubfield σ) ^ 2 - 1) :
    GLAPLayer p ((rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) ⊓
      fixSubgroup (entrywiseAdjointAut τ σ)) ≠ ⊥ := by
  classical
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  set K₀ := fixSubfield σ with hK₀
  set ι : K₀ →+* K := K₀.subtype with hι
  have hιinj : Function.Injective (baseChangeGL (τ := τ) ι) := baseChangeGL_injective ι
  have hK02 : ringChar K₀ ≠ 2 := by
    haveI : CharP K (ringChar K) := ringChar.charP K
    haveI : CharP K₀ (ringChar K) := (RingHom.charP_iff ι K₀.subtype_injective _).mpr ‹_›
    rw [ringChar.eq K₀ (ringChar K)]
    exact hK2
  have hd := hrRootData_of hτ
  set S := perpRoots τ with hSdef
  set t : ModGL τ K := rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Kˣ)) with ht
  set t₀ : ModGL τ K₀ := rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : K₀ˣ)) with ht₀
  have hιt : baseChangeGL ι t₀ = t := baseChangeGL_rootDiagUnit_mulSingle_neg_one ι _
  set M : Subgroup (ModGL τ K) := (rootSpan τ K₀ S).map (baseChangeGL ι) with hM
  set N : Subgroup (ModGL τ K) := rootSpan τ K S ⊓ fixedFieldImage τ σ with hN
  set H : Subgroup (ModGL τ K) := rootSpan τ K S ⊓ entrywiseFixedGroup τ σ with hH
  obtain ⟨-, -, -, hXΓ, -, hXn, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hMN : M ≤ N := le_inf (CFSG.SeitzReduction.F4Pilot.map_rootSpan_baseChangeGL_le ι S)
    (Subgroup.map_mono (rootSpan_le_adjointGroup K₀ S))
  have hNH : N ≤ H := inf_le_inf_left _ hXΓ
  have hHX : H ≤ adjointGroup τ K := inf_le_left.trans (rootSpan_le_adjointGroup K S)
  have hMnN : ∀ g ∈ N, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg _ hm
    obtain ⟨hgJ, hgX⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨g₀, hg₀, rfl⟩ := hgX
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    have hgt : baseChangeGL ι g₀ * t = t * baseChangeGL ι g₀ :=
      commute_of_mem_toralCentralizer (rootSpan_perpRoots_le_toralCentralizer (-1) hgJ)
    have hg₀t : g₀ * t₀ = t₀ * g₀ := by
      apply hιinj
      rw [map_mul, map_mul, hιt]
      exact hgt
    have hg₀N := toralCentralizer_neg_one_le_normalizer hK02 hd.abs_le hd.eq_highRoot
      hd.highRoot_highNode hd.iform_eq_zero_iff hd.exists_nbr
      (mem_toralCentralizer_of_commute hg₀ hg₀t)
    refine ⟨g₀ * m₀ * g₀⁻¹, (Subgroup.mem_normalizer_iff.1 hg₀N m₀).1 hm₀, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hNnH : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    obtain ⟨hhJ, hhΓ⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hnJ, hnX⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hhJ hnJ) (inv_mem hhJ), ?_⟩
    have := hXn.conj_mem ⟨n, hXΓ hnX⟩ (Subgroup.mem_subgroupOf.2 hnX) ⟨h, hhΓ⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  set X := ↥(adjointGroup τ K)
  set M' : Subgroup X := M.subgroupOf (adjointGroup τ K) with hM'
  set N' : Subgroup X := N.subgroupOf (adjointGroup τ K) with hN'
  set H' : Subgroup X := H.subgroupOf (adjointGroup τ K) with hH'
  have hH'eq : (rootSpan τ K S).subgroupOf (adjointGroup τ K) ⊓
      fixSubgroup (entrywiseAdjointAut τ σ) = H' := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_fixSubgroup, hH', Subgroup.mem_subgroupOf,
      hH, Subgroup.mem_inf, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, x.2, ?_⟩
      rw [← coe_entrywiseAdjointAut, h2]
    · rintro ⟨h1, -, h2⟩
      refine ⟨h1, Subtype.ext ?_⟩
      rw [coe_entrywiseAdjointAut]
      exact h2
  rw [hH'eq]
  have hsub : IsSubnormal M' H' := by
    refine IsSubnormal.step (fun x hx => Subgroup.mem_subgroupOf.2 (hMN
        (Subgroup.mem_subgroupOf.1 hx))) ⟨fun n hn g => ?_⟩
      (IsSubnormal.step (fun x hx => Subgroup.mem_subgroupOf.2 (hNH
        (Subgroup.mem_subgroupOf.1 hx))) ⟨fun n hn g => ?_⟩ (IsSubnormal.refl H'))
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
      exact hMnN ((g : X) : ModGL τ K) (Subgroup.mem_subgroupOf.1 g.2) _ hn
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
      exact hNnH ((g : X) : ModGL τ K) (Subgroup.mem_subgroupOf.1 g.2) _ hn
  have hMX : M ≤ adjointGroup τ K := hMN.trans (hNH.trans hHX)
  have eM : ↥M' ≃* ↥(rootSpan τ K₀ S) :=
    (Subgroup.subgroupOfEquivOfLe hMX).trans
      (Subgroup.equivMapOfInjective (rootSpan τ K₀ S) (baseChangeGL ι) hιinj).symm
  have hq0 : CFSG.Open.IsQuasisimple ↥(rootSpan τ K₀ S) := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact isQuasisimple_perpLevi_F4 hK02
    · exact isQuasisimple_perpLevi_E6 hK02
    · exact isQuasisimple_perpLevi_E7 hK02
    · exact isQuasisimple_perpLevi_E8 hK02
  have hq : CFSG.Open.IsQuasisimple ↥M' :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv eM.symm hq0
  haveI : Finite K₀ := Subtype.finite
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨A₀, hA₀⟩ := exists_orderOf_eq_sl2 hp hpK0
  obtain ⟨W, hW⟩ := exists_not_commute_sl2 hp hodd hA₀
  set i₁ := frame1 hτ
  have hi₁ := frame1_ne_frame0 hτ
  have hmemM : ∀ B : SL2 K₀, (frameSL2 τ K i₁ (fixIncl σ B) : X) ∈ M' := by
    intro B
    rw [Subgroup.mem_subgroupOf]
    refine ⟨((frameSL2 τ K₀ i₁ B : ↥(adjointGroup τ K₀)) : ModGL τ K₀),
      coe_frameSL2_mem_perp hτ hi₁ B, ?_⟩
    rw [coe_frameSL2, coe_frameSL2, baseChangeGL_rootSL2_of_field]
  have hzp : (frameSL2 τ K i₁ (fixIncl σ A₀) : X) ^ p = 1 := by
    rw [← map_pow, ← map_pow, ← hA₀, pow_orderOf_eq_one, map_one, map_one]
  have hzw : (frameSL2 τ K i₁ (fixIncl σ A₀) : X) * frameSL2 τ K i₁ (fixIncl σ W) ≠
      frameSL2 τ K i₁ (fixIncl σ W) * frameSL2 τ K i₁ (fixIncl σ A₀) := by
    intro h
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
    exact hW (fixIncl_injective σ (frameSL2_injective i₁ h))
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_isSubnormal_quasisimple hp hsub hq
    (CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute hp
      (hmemM A₀) (hmemM W) hzp hzw)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
