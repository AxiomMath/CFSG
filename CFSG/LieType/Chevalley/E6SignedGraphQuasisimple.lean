module

public import CFSG.LieType.Chevalley.E6SignedGraphQuasisimpleData
public import CFSG.LieType.TitsSimplicity.Simplicity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise commutatorElement
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
  (p_components_solvable_quotient_invariance)

variable {K : Type} [Field K]

theorem commutator_mem_posFixed_of_mem_borelPart
    {x y : ModGL TwistTag.E6.tag K}
    (hx : x ∈ borelPart K) (hy : y ∈ borelPart K) : x * y * x⁻¹ * y⁻¹ ∈ posFixed K := by
  have hx' : x ∈ (torusPart K : Set (ModGL TwistTag.E6.tag K)) *
      (posFixed K : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← coe_borelPart]
    exact hx
  have hy' : y ∈ (torusPart K : Set (ModGL TwistTag.E6.tag K)) *
      (posFixed K : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← coe_borelPart]
    exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨c, hc, d, hd, rfl⟩ := hy'
  have hNa := torusPart_le_normalizer_posFixed ha
  have hNc := torusPart_le_normalizer_posFixed hc
  have e : a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = (a * b * a⁻¹) *
      ((a * c) * (d * b⁻¹) * (a * c)⁻¹) * (a * c * a⁻¹ * c⁻¹) * (c * d⁻¹ * c⁻¹) := by
    group
  rw [e, show a * c * a⁻¹ * c⁻¹ = 1 by
    rw [torusFixed_mul_comm (torusPart_le_torusFixed ha) (torusPart_le_torusFixed hc)]
    group, mul_one]
  exact mul_mem (mul_mem ((Subgroup.mem_normalizer_iff.1 hNa b).1 hb)
    ((Subgroup.mem_normalizer_iff.1 (mul_mem hNa hNc) _).1 (mul_mem hd (inv_mem hb))))
    ((Subgroup.mem_normalizer_iff.1 hNc _).1 (inv_mem hd))

theorem isSolvable_borelPart
    : Group.IsSolvable (borelPart K) := by
  set U' := (posFixed K).subgroupOf (borelPart K) with hU'
  have : U'.Normal := posFixed_subgroupOf_borelPart_normal
  have : Group.IsNilpotent U' := (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe
    (fun _ hx => Subgroup.mem_sup_right hx : posFixed K ≤ borelPart K))).2 isNilpotent_posFixed
  have : Group.IsSolvable (borelPart K ⧸ U') := Group.isSolvable_of_comm fun x y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((x * y)⁻¹ * (y * x) : borelPart K) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact commutator_mem_posFixed_of_mem_borelPart (inv_mem y.2) (inv_mem x.2)
  exact Group.isSolvable_of_ker_le_range U'.subtype (QuotientGroup.mk' U')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_borelPart_subgroupOf :
    Group.IsSolvable ((borelPart K).subgroupOf (rootGenerated K)) := by
  have := isSolvable_borelPart (K := K)
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (borelPart_le_rootGenerated (K := K))).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (borelPart_le_rootGenerated (K := K))).symm.surjective

theorem wordLength_gen
    (i : Fin 4) : wordLength (gen i) = 1 := by
  have h' := wordLength_gen_mul_of_pos (one_mem _) i
    (by rw [inv_one, one_smul]; exact (simpleVec_mem_posVecs i).2)
  rwa [mul_one, wordLength_one] at h'

theorem sup_borelPart_eq_top
    (hK : ringChar K ≠ 2) {M : Subgroup (rootGenerated K)}
    (hM : M.Normal) (hMZ : ¬M ≤ Subgroup.center (rootGenerated K)) :
    M ⊔ (borelPart K).subgroupOf (rootGenerated K) = ⊤ := by
  set M₀ := M.map (rootGenerated K).subtype with hM₀
  have hM₀S : M₀ ≤ rootGenerated K := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hconj : ∀ s ∈ rootGenerated K, ∀ m ∈ M₀, s * m * s⁻¹ ∈ M₀ := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨⟨s, hs⟩ * m * ⟨s, hs⟩⁻¹, hM.conj_mem m hm ⟨s, hs⟩, rfl⟩
  obtain ⟨m, hmM, hmB⟩ : ∃ m ∈ M₀, m ∉ borelPart K := by
    by_contra! h
    apply hMZ
    intro x hx
    refine normalCore_borelPart_le_center hK ?_
    show ∀ b : rootGenerated K, b * x * b⁻¹ ∈ (borelPart K).subgroupOf (rootGenerated K)
    intro b
    rw [Subgroup.mem_subgroupOf]
    exact h _ ⟨b * x * b⁻¹, hM.conj_mem x hx b, rfl⟩
  have hex : ∀ i : Fin 4, ∃ w ∈ relWeylTwist TwistTag.E6, ∃ a, orbitImage w a = simpleOrbit i :=
    fun i => exists_orbitImage_eq (simpleOrbit_spec i).1
  choose v hv a ha using hex
  have hva : ∀ i, v i ∈ relWeylTwist TwistTag.E6 ∧ orbitImage (v i) (a i) = simpleOrbit i :=
    fun i => ⟨hv i, ha i⟩
  have hl : ∀ w : WeylGroup TwistTag.E6.tag, ∃ d : ModGL TwistTag.E6.tag K,
      w ∈ weylGroup → d ∈ liftGroup K v a ∧ MapsRootLines d w := by
    intro w
    by_cases hw : w ∈ weylGroup
    · obtain ⟨d, hd, hdw⟩ := exists_mem_liftGroup_of_mem_weylGroup (K := K) hva hw
      exact ⟨d, fun _ => ⟨hd, hdw⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose dot hdot using hl
  have hlift : ∀ w ∈ weylGroup, dot w ∈ rootGenerated K ∧
      dot w ∈ monomialSubgroup TwistTag.E6.tag K ∧ MapsRootLines (dot w) w := fun w hw =>
    ⟨liftGroup_le_rootGenerated hva (hdot w hw).1, liftGroup_le_monomialSubgroup v a (hdot w hw).1,
      (hdot w hw).2⟩
  set E := M₀ ⊔ borelPart K with hE
  have hBE : borelPart K ≤ E := le_sup_right
  have hME : M₀ ≤ E := le_sup_left
  have hBnorm : borelPart K ≤ Subgroup.normalizer (M₀ : Set (ModGL TwistTag.E6.tag K)) :=
    fun b hb => Subgroup.mem_normalizer_iff.2 fun y =>
      ⟨fun hy => hconj b (borelPart_le_rootGenerated hb) y hy, fun hy => by
        have h := hconj b⁻¹ (inv_mem (borelPart_le_rootGenerated hb)) _ hy
        rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at h⟩
  have hEset : (E : Set (ModGL TwistTag.E6.tag K)) =
      (M₀ : Set (ModGL TwistTag.E6.tag K)) * (borelPart K : Set (ModGL TwistTag.E6.tag K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBnorm
  have hmU : m ∈ ⋃ w ∈ weylGroup, signedCell K (dot w) := by
    rw [← coe_rootGenerated_eq_iUnion hK hlift]
    exact hM₀S hmM
  obtain ⟨w, hw, hmw⟩ := Set.mem_iUnion₂.1 hmU
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_signedCell.1 hmw
  have hdE : dot w ∈ E := by
    have e : dot w = b⁻¹ * m * b'⁻¹ := by
      rw [← hbb]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBE hb)) (hME hmM)) (inv_mem (hBE hb'))
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hmB
    have hT := mem_torusPart_of_mapsRootLines_one hva (hdot 1 hw).1 (hdot 1 hw).2
    rw [← hbb]
    exact mul_mem (mul_mem hb (le_sup_left (b := posFixed K) hT)) hb'
  obtain ⟨l, hl, hlw⟩ := exists_reduced_word hw
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∈ l := by
    cases l with
    | nil => exact absurd (by simpa using hlw.symm) hw1
    | cons i l => exact ⟨i, List.mem_cons_self⟩
  have hext := simpleLift_mem_of_reduced hva hBE hlw hl (hlift w hw).1 (hlift w hw).2.1
    (hlift w hw).2.2 hdE
  have hall : ∀ i, simpleLift K v a i ∈ E := by
    by_contra! hnot
    obtain ⟨j₀, hj₀⟩ := hnot
    classical
    obtain ⟨i, j, hij, hi, hj⟩ := exists_adj_of_ne (fun i => decide (simpleLift K v a i ∈ E))
      ⟨i₀, decide_eq_true (hext i₀ hi₀)⟩ ⟨j₀, decide_eq_false hj₀⟩
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hi hj
    apply hj
    have hzi : simpleLift K v a i ∈ (M₀ : Set (ModGL TwistTag.E6.tag K)) *
        (borelPart K : Set (ModGL TwistTag.E6.tag K)) := by
      rw [← hEset]
      exact hi
    obtain ⟨m₁, hm₁, u, hu, hmu⟩ := hzi
    simp only at hmu
    obtain ⟨hzSi, -, hzwi⟩ := simpleLift_mem (K := K) hva i
    obtain ⟨hzSj, -, hzwj⟩ := simpleLift_mem (K := K) hva j
    have hzNi : simpleLift K v a i ∈ monomialSubgroup TwistTag.E6.tag K :=
      orbitSL2_nSL_mem_monomialSubgroup _ _ _
    have hzNj : simpleLift K v a j ∈ monomialSubgroup TwistTag.E6.tag K :=
      orbitSL2_nSL_mem_monomialSubgroup _ _ _
    set zi := simpleLift K v a i with hzi
    set zj := simpleLift K v a j with hzj
    obtain ⟨hlen2, hlen3⟩ := wordLength_adj hij
    have h1 : signedCell K zj * signedCell K zi = signedCell K (zj * zi) :=
      signedCell_mul_left_inc hK j (gen_mem_weylGroup i) ⟨hzSj, hzNj, hzwj⟩ ⟨hzSi, hzNi, hzwi⟩
        ⟨mul_mem hzSj hzSi, mul_mem hzNj hzNi, hzwj.mul hzwi⟩
        (by rw [hlen2, wordLength_gen])
    have h2 : signedCell K (zj * zi) * signedCell K zj = signedCell K (zj * zi * zj) :=
      signedCell_mul_right_inc hK j (mul_mem (gen_mem_weylGroup j) (gen_mem_weylGroup i))
        ⟨hzSj, hzNj, hzwj⟩ ⟨mul_mem hzSj hzSi, mul_mem hzNj hzNi, hzwj.mul hzwi⟩
        ⟨mul_mem (mul_mem hzSj hzSi) hzSj, mul_mem (mul_mem hzNj hzNi) hzNj,
          (hzwj.mul hzwi).mul hzwj⟩ (by rw [hlen3, hlen2])
    have hDj : signedCell K zj⁻¹ = signedCell K zj :=
      signedCell_eq (inv_mem hzSj) hzSj (inv_mem hzNj) hzNj
        (by have h := hzwj.inv; rwa [gen_inv] at h) hzwj
    have hmem : zj * m₁ * zj⁻¹ ∈ signedCell K (zj * zi * zj) := by
      rw [← h2, ← h1]
      refine ⟨zj * m₁, ⟨zj, mem_signedCell.2 ⟨1, one_mem _, 1, one_mem _, by group⟩, m₁,
        mem_signedCell.2 ⟨1, one_mem _, u⁻¹, inv_mem hu, ?_⟩, rfl⟩, zj⁻¹, ?_, rfl⟩
      · rw [← hmu]
        group
      · rw [← hDj]
        exact mem_signedCell.2 ⟨1, one_mem _, 1, one_mem _, by group⟩
    obtain ⟨c, hc, c', hc', hcc⟩ := mem_signedCell.1 hmem
    have heE : zj * zi * zj ∈ E := by
      have e : zj * zi * zj = c⁻¹ * (zj * m₁ * zj⁻¹) * c'⁻¹ := by
        rw [← hcc]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hBE hc)) (hME (hconj zj hzSj m₁ hm₁)))
        (inv_mem (hBE hc'))
    exact simpleLift_mem_of_reduced hva hBE (l := [j, i, j]) (w := gen j * gen i * gen j)
      (by simp [mul_assoc]) (by rw [hlen3]; rfl) (mul_mem (mul_mem hzSj hzSi) hzSj)
      (mul_mem (mul_mem hzNj hzNi) hzNj) ((hzwj.mul hzwi).mul hzwj) heE j (by simp)
  have hSE := rootGenerated_le_of_simpleLift_mem hva hK hBE hall
  rw [eq_top_iff]
  intro s _
  have hs : (s : ModGL TwistTag.E6.tag K) ∈ (M₀ : Set (ModGL TwistTag.E6.tag K)) *
      (borelPart K : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← hEset]
    exact hSE s.2
  obtain ⟨m', hm', b₀, hb₀, hmb⟩ := hs
  obtain ⟨m'', hm'', rfl⟩ := hm'
  simp only [Subgroup.coe_subtype] at hmb
  have hb₀S : b₀ ∈ rootGenerated K := by
    have e : b₀ = (m'' : ModGL TwistTag.E6.tag K)⁻¹ * s := by
      rw [← hmb]
      group
    rw [e]
    exact mul_mem (inv_mem m''.2) s.2
  have hs' : s = m'' * ⟨b₀, hb₀S⟩ := Subtype.ext hmb.symm
  rw [hs']
  exact mul_mem (Subgroup.mem_sup_left hm'')
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hb₀))

theorem isSolvable_quotient
    (hK : ringChar K ≠ 2) {M : Subgroup (rootGenerated K)}
    (hM : M.Normal) (hMZ : ¬M ≤ Subgroup.center (rootGenerated K)) :
    Group.IsSolvable (rootGenerated K ⧸ M) := by
  have htop := sup_borelPart_eq_top hK hM hMZ
  have := hM
  have := isSolvable_borelPart_subgroupOf (K := K)
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp
      ((borelPart K).subgroupOf (rootGenerated K)).subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M y
    have hg : g ∈ M ⊔ (borelPart K).subgroupOf (rootGenerated K) := htop ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
    obtain ⟨m, hm, b, hb, rfl⟩ := hg
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).2 hm, one_mul]
  exact Group.isSolvable_of_surjective hsurj

theorem isQuasisimple_rootGenerated
    (hK : ringChar K ≠ 2) :
    CFSG.IsQuasisimple (rootGenerated K) := by
  have hperf : Group.IsPerfect (rootGenerated K) :=
    Subgroup.isPerfect_iff.2 (commutator_rootGenerated hK)
  have : Nontrivial (rootGenerated K) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 rootGenerated_ne_bot
  refine CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun M hM => ?_
  by_cases hZ : M ≤ Subgroup.center (rootGenerated K)
  · exact Or.inl hZ
  · have := hM
    exact Or.inr (CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf
      isSolvable_borelPart_subgroupOf (sup_borelPart_eq_top hK hM hZ))

theorem pComponent_eq
    (hK : ringChar K ≠ 2) [Finite K] (p : ℕ) (hp : p.Prime)
    (L : Subgroup (fixedGroup K)) (hL : CFSG.IsPComponent p L) :
    L = (rootGenerated K).subgroupOf (fixedGroup K) ∧ CFSG.IsQuasisimple L := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hN : ((rootGenerated K).subgroupOf (fixedGroup K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer rootGenerated_le_fixedGroup).2
      (fixedGroup_le_normalizer hK)
  have : Group.IsSolvable (fixedGroup K ⧸ (rootGenerated K).subgroupOf (fixedGroup K)) :=
    Group.isSolvable_of_comm fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have e : ((x * y)⁻¹ * (y * x) : fixedGroup K) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      have h := Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2)
      rw [commutator_fixedGroup hK] at h
      exact h
  obtain ⟨hLN, hLN'⟩ := (p_components_solvable_quotient_invariance
    p hp ((rootGenerated K).subgroupOf (fixedGroup K)) L).1 hL
  let e : (rootGenerated K).subgroupOf (fixedGroup K) ≃* rootGenerated K :=
    Subgroup.subgroupOfEquivOfLe rootGenerated_le_fixedGroup
  have hNq : CFSG.IsQuasisimple ((rootGenerated K).subgroupOf (fixedGroup K)) :=
    (isQuasisimple_congr e).2 (isQuasisimple_rootGenerated hK)
  have hLsub : (L.subgroupOf ((rootGenerated K).subgroupOf (fixedGroup K))).IsSubnormal :=
    hLN'.choose_spec.2.1
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hLN'
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hLN'
  rcases quasisimple_subnormal_subgroups hNq hLsub with h | h
  · have hLeq : L = (rootGenerated K).subgroupOf (fixedGroup K) := by
      refine le_antisymm hLN fun g hg => ?_
      have hmem : (⟨g, hg⟩ : (rootGenerated K).subgroupOf (fixedGroup K)) ∈
          L.subgroupOf ((rootGenerated K).subgroupOf (fixedGroup K)) := by
        rw [h]
        trivial
      exact hmem
    refine ⟨hLeq, ?_⟩
    rw [hLeq]
    exact hNq
  · exfalso
    refine Group.IsPerfect.not_isMulCommutative
      (L.subgroupOf ((rootGenerated K).subgroupOf (fixedGroup K))) ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_center_iff.1 (h x.2) y).symm

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley E6SignedGraph

theorem E6_signed_graph_fixed_root_group_quasisimple
    (K : Type) [Field K]
    (hK : ringChar K ≠ 2) :
    ((borelPart K).subgroupOf (rootGenerated K)).normalCore ≤
        Subgroup.center (rootGenerated K) ∧
    (∀ (M : Subgroup (rootGenerated K)) [M.Normal], ¬M ≤ Subgroup.center (rootGenerated K) →
      M ⊔ (borelPart K).subgroupOf (rootGenerated K) = ⊤ ∧
        Group.IsSolvable (rootGenerated K ⧸ M)) ∧
    CFSG.IsQuasisimple (rootGenerated K) ∧
    ∀ [Finite K], ∀ p : ℕ, p.Prime → ∀ L : Subgroup (fixedGroup K), CFSG.IsPComponent p L →
      L = (rootGenerated K).subgroupOf (fixedGroup K) ∧ CFSG.IsQuasisimple L :=
  ⟨normalCore_borelPart_le_center hK, fun _ hM hMZ =>
    ⟨sup_borelPart_eq_top hK hM hMZ, isSolvable_quotient hK hM hMZ⟩,
    isQuasisimple_rootGenerated hK, fun p hp L hL => pComponent_eq hK p hp L hL⟩

end CFSG.LieType.Chevalley
