module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutDCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley RootOps

local instance f4PilotNonsplitNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]

theorem exists_eq_zpowers_of_isCyclic {G : Type*} [Group G] {X : Subgroup G} (hX : IsCyclic X) :
    ∃ x ∈ X, X = Subgroup.zpowers x := by
  obtain ⟨⟨x, hxX⟩, hgen⟩ := IsCyclic.exists_generator (α := X)
  refine ⟨x, hxX, le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.2 hxX)⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨y, hy⟩)
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem zpowers_le_centralizer_zpowers {G : Type*} [Group G] (x : G) :
    Subgroup.zpowers x ≤ centralizer (Subgroup.zpowers x : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact (Commute.zpow_zpow_self x b a).eq

theorem orbitCertRoot_47_eq_rootR : orbitCertRoot .F4 47 = rootR := by decide

section Basic


theorem highestRootRankOne_eq_rootSL2R : highestRootRankOne K = rootSL2R K := by
  rw [highestRootRankOne, rootSL2R, orbitCertRoot_47_eq_rootR]

end Basic

section RankOne


theorem rootSL2_rootR_injective [CharP K 2] : Function.Injective (rootSL2 .F4 K rootR) :=
  (even_Chevalley_pinned_root_SL2_maps .F4 K isRoot_rootR).1

theorem range_rootSL2_rootR [CharP K 2] : (rootSL2 .F4 K rootR).range = rootSL2R K :=
  (even_Chevalley_pinned_root_SL2_maps .F4 K isRoot_rootR).2.1

theorem baseChangeGL_rootSL2_rootR [CharP K 2] {L : Type} [Field L] (f : K →+* L) (A : SL2 K) :
    baseChangeGL f (rootSL2 .F4 K rootR A) =
      rootSL2 .F4 L rootR (Matrix.SpecialLinearGroup.map f A) :=
  baseChangeGL_rootSL2_of_charTwo f isRoot_rootR A

theorem rootSL2_rootR_HSL [CharP K 2] (c : Kˣ) :
    rootSL2 .F4 K rootR (HSL c) = rootDiagUnit .F4 (rDiag c) := by
  obtain ⟨-, -, -, -, -, -, hv, -⟩ := even_Chevalley_pinned_root_SL2_maps .F4 K isRoot_rootR
  obtain ⟨hh, hr⟩ := hv c
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun δ hδ => ?_)
  · change (rootTorusSL2 .F4 K rootR c : Module.End K (RootModule .F4 K)) (hVec .F4 K j) =
      rootDiag (rDiag c) (hVec .F4 K j)
    rw [hh, rootDiag_hVec]
  · change (rootTorusSL2 .F4 K rootR c : Module.End K (RootModule .F4 K)) (rootVec .F4 K δ) =
      rootDiag (rDiag c) (rootVec .F4 K δ)
    rw [hr δ hδ, rootDiag_rootVec _ hδ, rootChar_rDiag, iform_rootR, iform_rootR,
      show rootR 0 = 2 from rfl]
    congr 3
    omega

theorem rootSL2_rootR_mem_adjointGroup (A : SL2 K) :
    rootSL2 .F4 K rootR A ∈ adjointGroup .F4 K :=
  (exceptional_Lang_root_rank_one_data .F4 K rootR).2.2.2.2.1 A

theorem exists_nonsplit_le_highestRootRankOne [Finite K] [CharP K 2] :
    ∃ X : Subgroup (ModGL .F4 K), X ≤ highestRootRankOne K ∧ IsCyclic X ∧
      Nat.card X = Nat.card K + 1 := by
  obtain ⟨A, hA⟩ := exists_orderOf_eq_natCard_add_one (K := K)
  refine ⟨Subgroup.zpowers (rootSL2 .F4 K rootR A), ?_, Subgroup.isCyclic_zpowers _, ?_⟩
  · rw [Subgroup.zpowers_le, highestRootRankOne_eq_rootSL2R, ← range_rootSL2_rootR]
    exact ⟨A, rfl⟩
  · rw [Nat.card_zpowers, orderOf_injective _ rootSL2_rootR_injective, hA]

theorem exists_nonsplit_le_subgroupOf_highestRootRankOne [Finite K] [CharP K 2] :
    ∃ X : Subgroup (adjointGroup .F4 K),
      X ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) ∧ IsCyclic X ∧
        Nat.card X = Nat.card K + 1 := by
  obtain ⟨A, hA⟩ := exists_orderOf_eq_natCard_add_one (K := K)
  refine ⟨Subgroup.zpowers ⟨rootSL2 .F4 K rootR A, rootSL2_rootR_mem_adjointGroup A⟩, ?_,
    Subgroup.isCyclic_zpowers _, ?_⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R,
      ← range_rootSL2_rootR]
    exact ⟨A, rfl⟩
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    change orderOf (rootSL2 .F4 K rootR A) = _
    rw [orderOf_injective _ rootSL2_rootR_injective, hA]

end RankOne

section Levi


private theorem c3LeviRoots_eq_C3Set : c3LeviRoots = C3Set := by
  ext γ
  rw [mem_c3LeviRoots, mem_C3Set_iff]
  rfl

private theorem c3PerpRoots_eq_C3Set : c3PerpRoots = C3Set := by
  ext γ
  rw [mem_c3PerpRoots_iff, mem_C3Set_iff]
  rfl


private theorem c3PerpLevi_eq_rootSpan_C3Set : c3PerpLevi K = rootSpan .F4 K C3Set := by
  rw [c3PerpLevi, c3PerpRoots_eq_C3Set]

theorem map_subtype_C3Levi_eq_rootSpan_C3Set :
    (C3Levi K).map (adjointGroup .F4 K).subtype = rootSpan .F4 K C3Set := by
  rw [map_subtype_C3Levi, c3LeviRoots_eq_C3Set]

theorem mem_C3Levi_iff_mem_rootSpan_C3Set {g : adjointGroup .F4 K} :
    g ∈ C3Levi K ↔ (g : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
  rw [mem_C3Levi_iff, c3LeviRoots_eq_C3Set]

end Levi

section Full


theorem disjoint_rootSL2R_rootSpan_C3Set [Finite K] [CharP K 2] :
    Disjoint (rootSL2R K) (rootSpan .F4 K C3Set) := by
  rw [Subgroup.disjoint_def]
  intro g hgJ hgD
  have hgC : g ∈ adjointGroup .F4 K := rootSpan_le_adjointGroup K C3Set hgD
  have hgL : (⟨g, hgC⟩ : adjointGroup .F4 K) ∈ C3Levi K :=
    mem_C3Levi_iff_mem_rootSpan_C3Set.2 hgD
  have hz : (⟨⟨g, hgC⟩, hgL⟩ : C3Levi K) ∈ center (C3Levi K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : ((y : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K C3Set :=
      mem_C3Levi_iff_mem_rootSpan_C3Set.1 y.2
    have hc := Subgroup.mem_centralizer_iff.1 (rootSpan_C3Set_le_centralizer_rootSL2R hy) g hgJ
    exact Subtype.ext (Subtype.ext hc.symm)
  rw [center_C3Levi_eq_bot, Subgroup.mem_bot] at hz
  exact congrArg (fun z : C3Levi K => ((z : adjointGroup .F4 K) : ModGL .F4 K)) hz

theorem commute_rootSL2R_rootSpan_C3Set {j d : ModGL .F4 K} (hj : j ∈ rootSL2R K)
    (hd : d ∈ rootSpan .F4 K C3Set) : j * d = d * j :=
  Subgroup.mem_centralizer_iff.1 (rootSpan_C3Set_le_centralizer_rootSL2R hd) j hj

section Descent

variable [Finite K] [CharP K 2]

omit
  [Finite K] [CharP K 2] in
theorem torusLineR_le_rootSL2R : torusLineR K ≤ rootSL2R K := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_rDiag_mem_rootSL2R c

theorem exists_baseChangeGL_eq_of_mem_rootSpan_C3Set {M : Type} [Field M] [Finite M] [CharP M 2]
    (ι : K →+* M) (σ : M →+* M) (hfix : ∀ z : M, σ z = z ↔ z ∈ Set.range ι)
    {d : ModGL .F4 M} (hd : d ∈ rootSpan .F4 M C3Set) (hσd : baseChangeGL σ d = d) :
    ∃ d₀ ∈ rootSpan .F4 K C3Set, baseChangeGL ι d₀ = d := by
  have hdC : d ∈ adjointGroup .F4 M := rootSpan_le_adjointGroup M C3Set hd
  set d' : C3Levi M := ⟨⟨d, hdC⟩, mem_C3Levi_iff_mem_rootSpan_C3Set.2 hd⟩ with hd'
  have hfixd : d' ∈ (c3LeviBaseChange σ).eqLocus (MonoidHom.id _) :=
    Subtype.ext (Subtype.ext (by rw [coe_c3LeviBaseChange]; exact hσd))
  rw [← map_c3LeviBaseChange_eq_eqLocus ι σ hfix] at hfixd
  obtain ⟨d₀, -, hd₀⟩ := hfixd
  refine ⟨((d₀ : adjointGroup .F4 K) : ModGL .F4 K), mem_C3Levi_iff_mem_rootSpan_C3Set.1 d₀.2, ?_⟩
  rw [← coe_c3LeviBaseChange, hd₀]

omit
  [Finite K] in
theorem exists_baseChangeGL_eq_of_mem_rootSL2R {M : Type} [Field M] [CharP M 2]
    (ι : K →+* M) (σ : M →+* M) (hfix : ∀ z : M, σ z = z ↔ z ∈ Set.range ι)
    {j : ModGL .F4 M} (hj : j ∈ rootSL2R M) (hσj : baseChangeGL σ j = j) :
    ∃ y ∈ rootSL2R K, baseChangeGL ι y = j := by
  rw [← range_rootSL2_rootR] at hj
  obtain ⟨B₂, rfl⟩ := hj
  rw [baseChangeGL_rootSL2_rootR] at hσj
  obtain ⟨B, hB⟩ := exists_map_eq_of_map_eq ι σ hfix B₂ (rootSL2_rootR_injective hσj)
  refine ⟨rootSL2 .F4 K rootR B, ?_, by rw [baseChangeGL_rootSL2_rootR, hB]⟩
  rw [← range_rootSL2_rootR]
  exact ⟨B, rfl⟩

end Descent

theorem exists_mem_zpowers_mul_of_commute_nonsplit [Finite K] [CharP K 2] {x : ModGL .F4 K}
    (hxJ : x ∈ rootSL2R K) (hx : orderOf x = Nat.card K + 1) {g : ModGL .F4 K}
    (hg : g ∈ adjointGroup .F4 K) (hgx : g * x = x * g) :
    ∃ y ∈ Subgroup.zpowers x, ∃ d ∈ rootSpan .F4 K C3Set, g = y * d := by
  rw [← range_rootSL2_rootR] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  have hA : orderOf A = Nat.card K + 1 := by
    rw [← hx, orderOf_injective _ rootSL2_rootR_injective]
  set ι : K →+* FiniteField.Extension K 2 2 := algebraMap K (FiniteField.Extension K 2 2) with hι
  set σ : FiniteField.Extension K 2 2 →+* FiniteField.Extension K 2 2 :=
    (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom with hσ
  have hfix : ∀ z : FiniteField.Extension K 2 2, σ z = z ↔ z ∈ Set.range ι :=
    fun z => frob_eq_self_iff z
  have hσι : σ.comp ι = ι := RingHom.ext fun a => (FiniteField.Extension.frob K 2 2).commutes a
  have hK₂ : ringChar (FiniteField.Extension K 2 2) = 2 := ringChar.eq _ 2
  obtain ⟨l, P, -, hl1, -, hP⟩ := exists_inv_mul_map_mul_eq_HSL hA
  have hl3 : 3 ≤ orderOf l := by
    have hl2 : l ^ 2 ≠ 1 := fun h => hl1 (Units.ext (eq_one_of_sq_eq_one_of_charTwo (by
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one])))
    have hpos : 0 < orderOf l := orderOf_pos l
    by_contra hlt
    have hpow := pow_orderOf_eq_one l
    rcases (show orderOf l = 1 ∨ orderOf l = 2 by omega) with h | h
    · exact hl1 (orderOf_eq_one_iff.1 h)
    · rw [h] at hpow
      exact hl2 hpow
  set n := rootSL2 .F4 (FiniteField.Extension K 2 2) rootR P with hn
  have hnJ : n ∈ rootSL2R (FiniteField.Extension K 2 2) := by
    rw [← range_rootSL2_rootR]
    exact ⟨P, rfl⟩
  have hconj : n⁻¹ * baseChangeGL ι (rootSL2 .F4 K rootR A) * n =
      rootDiagUnit .F4 (rDiag l) := by
    rw [baseChangeGL_rootSL2_rootR, hn, ← map_inv, ← map_mul, ← map_mul, hP, rootSL2_rootR_HSL]
  have hm : n⁻¹ * baseChangeGL ι g * n ∈ toralCentralizer .F4 (FiniteField.Extension K 2 2)
      (rDiag l) := by
    refine mem_toralCentralizer.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem (rootSL2_rootR_mem_adjointGroup P))
        (baseChangeGL_mem_adjointGroup ι hg)) (rootSL2_rootR_mem_adjointGroup P)
    · have hgx₂ : baseChangeGL ι g * baseChangeGL ι (rootSL2 .F4 K rootR A) =
          baseChangeGL ι (rootSL2 .F4 K rootR A) * baseChangeGL ι g := by
        rw [← map_mul, hgx, map_mul]
      rw [← hconj]
      calc n⁻¹ * baseChangeGL ι (rootSL2 .F4 K rootR A) * n * (n⁻¹ * baseChangeGL ι g * n) *
            (n⁻¹ * baseChangeGL ι (rootSL2 .F4 K rootR A) * n)⁻¹ =
          n⁻¹ * (baseChangeGL ι (rootSL2 .F4 K rootR A) * baseChangeGL ι g) *
            (baseChangeGL ι (rootSL2 .F4 K rootR A))⁻¹ * n := by group
        _ = n⁻¹ * baseChangeGL ι g * n := by rw [← hgx₂]; group
  rw [(toralCentralizer_rDiag_eq_sup hK₂ hl3).1, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ torusLineR_le_normalizer] at hm
  obtain ⟨t, ht, d, hd, htd⟩ := Set.mem_mul.1 hm
  set j := n * t * n⁻¹ with hjdef
  have hjJ : j ∈ rootSL2R (FiniteField.Extension K 2 2) :=
    mul_mem (mul_mem hnJ (torusLineR_le_rootSL2R ht)) (inv_mem hnJ)
  have hg₂ : baseChangeGL ι g = j * d := by
    have hnd : n * d * n⁻¹ = d := by
      rw [commute_rootSL2R_rootSpan_C3Set hnJ hd, mul_inv_cancel_right]
    calc baseChangeGL ι g = n * (n⁻¹ * baseChangeGL ι g * n) * n⁻¹ := by group
      _ = n * (t * d) * n⁻¹ := by rw [htd]
      _ = (n * t * n⁻¹) * (n * d * n⁻¹) := by group
      _ = j * d := by rw [hnd]
  have hσg : baseChangeGL σ (baseChangeGL ι g) = baseChangeGL ι g := by
    rw [baseChangeGL_baseChangeGL, hσι]
  have hσj : baseChangeGL σ j ∈ rootSL2R (FiniteField.Extension K 2 2) := by
    rw [← range_rootSL2_rootR] at hjJ ⊢
    obtain ⟨B, hB⟩ := hjJ
    exact ⟨Matrix.SpecialLinearGroup.map σ B, by rw [← hB, baseChangeGL_rootSL2_rootR]⟩
  have hσd : baseChangeGL σ d ∈ rootSpan .F4 (FiniteField.Extension K 2 2) C3Set :=
    map_rootSpan_baseChangeGL_le σ C3Set ⟨d, hd, rfl⟩
  have hjd : baseChangeGL σ j = j ∧ baseChangeGL σ d = d := by
    have h1 : (baseChangeGL σ j)⁻¹ * j = baseChangeGL σ d * d⁻¹ := by
      have h2 : baseChangeGL σ j * baseChangeGL σ d = j * d := by
        rw [← map_mul, ← hg₂, hσg]
      calc (baseChangeGL σ j)⁻¹ * j = (baseChangeGL σ j)⁻¹ * (j * d) * d⁻¹ := by group
        _ = (baseChangeGL σ j)⁻¹ * (baseChangeGL σ j * baseChangeGL σ d) * d⁻¹ := by rw [h2]
        _ = baseChangeGL σ d * d⁻¹ := by group
    have hJ : (baseChangeGL σ j)⁻¹ * j ∈ rootSL2R (FiniteField.Extension K 2 2) :=
      mul_mem (inv_mem hσj) hjJ
    have hD : (baseChangeGL σ j)⁻¹ * j ∈ rootSpan .F4 (FiniteField.Extension K 2 2) C3Set := by
      rw [h1]
      exact mul_mem hσd (inv_mem hd)
    have h0 := (Subgroup.disjoint_def.1 disjoint_rootSL2R_rootSpan_C3Set) hJ hD
    rw [h0] at h1
    refine ⟨inv_mul_eq_one.1 h0, ?_⟩
    exact (mul_inv_eq_one.1 h1.symm)
  obtain ⟨d₀, hd₀D, hd₀⟩ := exists_baseChangeGL_eq_of_mem_rootSpan_C3Set ι σ hfix hd hjd.2
  obtain ⟨y, hyJ, hy⟩ := exists_baseChangeGL_eq_of_mem_rootSL2R ι σ hfix hjJ hjd.1
  have hgyd : g = y * d₀ := baseChangeGL_injective ι (by rw [map_mul, hy, hd₀, hg₂])
  refine ⟨y, ?_, d₀, hd₀D, hgyd⟩
  have hxJ : rootSL2 .F4 K rootR A ∈ rootSL2R K := by
    rw [← range_rootSL2_rootR]
    exact ⟨A, rfl⟩
  have hyx : Commute y (rootSL2 .F4 K rootR A) := by
    have hd₀x : Commute (rootSL2 .F4 K rootR A) d₀ := commute_rootSL2R_rootSpan_C3Set hxJ hd₀D
    rw [show y = g * d₀⁻¹ by rw [hgyd, mul_inv_cancel_right]]
    exact Commute.mul_left hgx hd₀x.symm.inv_left
  rw [← range_rootSL2_rootR] at hyJ
  obtain ⟨B, rfl⟩ := hyJ
  have hBA : B ∈ Subgroup.centralizer {A} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply rootSL2_rootR_injective
    rw [map_mul, map_mul]
    exact hyx.eq
  rw [centralizer_eq_zpowers_of_orderOf_eq hA] at hBA
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hBA
  exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow (rootSL2 .F4 K rootR) A k).symm⟩

theorem adjointGroup_inf_centralizer_nonsplit [Finite K] [CharP K 2]
    {X : Subgroup (ModGL .F4 K)} (hXJ : X ≤ highestRootRankOne K) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) :
    adjointGroup .F4 K ⊓ centralizer (X : Set (ModGL .F4 K)) = X ⊔ c3PerpLevi K ∧
      Disjoint X (c3PerpLevi K) ∧ X ≤ centralizer (c3PerpLevi K : Set (ModGL .F4 K)) := by
  rw [highestRootRankOne_eq_rootSL2R] at hXJ
  rw [c3PerpLevi_eq_rootSpan_C3Set]
  obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic hcyc
  have hx : orderOf x = Nat.card K + 1 := by rw [← Nat.card_zpowers, hX]
  have hxJ : x ∈ rootSL2R K := hXJ (Subgroup.mem_zpowers x)
  have hXD : Subgroup.zpowers x ≤ centralizer (rootSpan .F4 K C3Set : Set (ModGL .F4 K)) :=
    hXJ.trans (Subgroup.le_centralizer_iff.1 rootSpan_C3Set_le_centralizer_rootSL2R)
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le (le_inf (hXJ.trans rootSL2R_le_adjointGroup)
    (zpowers_le_centralizer_zpowers x)) (le_inf (rootSpan_le_adjointGroup K C3Set)
      (Subgroup.le_centralizer_iff.1 hXD))), disjoint_rootSL2R_rootSpan_C3Set.mono_left hXJ, hXD⟩
  obtain ⟨hgC, hgX⟩ := Subgroup.mem_inf.1 hg
  have hgx : g * x = x * g := (Subgroup.mem_centralizer_iff.1 hgX x (Subgroup.mem_zpowers x)).symm
  obtain ⟨y, hy, d, hd, rfl⟩ := exists_mem_zpowers_mul_of_commute_nonsplit hxJ hx hgC hgx
  exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hd)

theorem exists_mul_of_mem_centralizer_nonsplit [Finite K] [CharP K 2]
    {X : Subgroup (adjointGroup .F4 K)}
    (hXJ : X ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) {c : adjointGroup .F4 K}
    (hc : c ∈ centralizer (X : Set (adjointGroup .F4 K))) :
    ∃ y ∈ X, ∃ d ∈ C3Levi K, c = y * d := by
  obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic hcyc
  have hx : orderOf (x : ModGL .F4 K) = Nat.card K + 1 := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers, hX]
  have hxJ : (x : ModGL .F4 K) ∈ rootSL2R K := by
    have h := hXJ (Subgroup.mem_zpowers x)
    rwa [Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R] at h
  have hcx : (c : ModGL .F4 K) * x = x * c :=
    congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc x (Subgroup.mem_zpowers x)).symm
  obtain ⟨y, hy, d, hd, hcyd⟩ := exists_mem_zpowers_mul_of_commute_nonsplit hxJ hx c.2 hcx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨x ^ k, Subgroup.zpow_mem_zpowers x k, ⟨d, rootSpan_le_adjointGroup K C3Set hd⟩,
    mem_C3Levi_iff_mem_rootSpan_C3Set.2 hd, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_zpow, hcyd]

theorem commute_of_mem_highestRootRankOne_of_mem_C3Levi {y d : adjointGroup .F4 K}
    (hy : y ∈ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hd : d ∈ C3Levi K) :
    y * d = d * y := by
  rw [Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R] at hy
  exact Subtype.ext (commute_rootSL2R_rootSpan_C3Set hy (mem_C3Levi_iff_mem_rootSpan_C3Set.1 hd))

theorem centralizer_nonsplit [Finite K] [CharP K 2] {X : Subgroup (adjointGroup .F4 K)}
    (hXJ : X ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) :
    centralizer (X : Set (adjointGroup .F4 K)) = X ⊔ C3Levi K ∧ Disjoint X (C3Levi K) ∧
      X ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)) := by
  have hXD : X ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun d hd =>
      (commute_of_mem_highestRootRankOne_of_mem_C3Levi (hXJ hy) hd).symm
  refine ⟨le_antisymm (fun c hc => ?_) (sup_le ?_ (Subgroup.le_centralizer_iff.1 hXD)), ?_, hXD⟩
  · obtain ⟨y, hy, d, hd, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit hXJ hcyc hX hc
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hd)
  · obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic hcyc
    exact zpowers_le_centralizer_zpowers x
  · rw [Subgroup.disjoint_def]
    intro g hgX hgD
    have hgJ := hXJ hgX
    rw [Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R] at hgJ
    exact Subtype.ext ((Subgroup.disjoint_def.1 disjoint_rootSL2R_rootSpan_C3Set) hgJ
      (mem_C3Levi_iff_mem_rootSpan_C3Set.1 hgD))

end Full

end CFSG.SeitzReduction.F4Pilot
