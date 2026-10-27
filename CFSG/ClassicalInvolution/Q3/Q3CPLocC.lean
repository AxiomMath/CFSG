module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3CPNbhd
public import CFSG.ClassicalInvolution.Q3.Q3CPTwin
public import CFSG.ClassicalInvolution.Q3.Q3YSFinal
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Def

variable {G : Type} [Group G]

@[expose] def LocCommuteAt (K : Subgroup G) (_z : G) : Prop :=
  ∀ (L M : Subgroup G) (l m : G), L ∈ conjClass3 K → M ∈ conjClass3 K →
    IsClassicalMember3 L l → IsClassicalMember3 M m → l ≠ m → l * m = m * l →
    (∃ P : Subgroup G, IsSylow2In P M ∧ P ≤ Subgroup.centralizer ({l} : Set G)) → Commutes L M

variable {K : Subgroup G} {z : G}

theorem LocCommuteAt.of_le [Finite G] (h : LocCommuteAt K z) {L M : Subgroup G} {l m : G}
    (hL : L ∈ conjClass3 K) (hM : M ∈ conjClass3 K) (hl : IsClassicalMember3 L l)
    (hm : IsClassicalMember3 M m) (hne : l ≠ m) (hc : l * m = m * l)
    (hMc : M ≤ Subgroup.centralizer ({l} : Set G)) : Commutes L M := by
  obtain ⟨P, hP⟩ := exists_isSylow2In M
  exact h L M l m hL hM hl hm hne hc ⟨P, hP, hP.1.trans hMc⟩

theorem locCommuteAt_of_not_a2Configuration [Finite G] (hz : IsClassicalMember3 K z)
    (hA2 : ¬ A2Configuration z K) : LocCommuteAt K z :=
  fun _ _ _ _ hL hM hl hm hne hc _ => commutes_of_not_a2Configuration3 hz hA2 hL hM hl hm hne hc

end Def

@[expose] def LocCommuteSyl3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → LocCommuteAt K z

section Twin

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem exists_member_commuting_involution' (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) {w : G}
    (hw : ∃ g : G, w = g * z * g⁻¹) :
    ∃ (J : Subgroup G) (t : G), J ∈ conjClass3 K ∧ IsClassicalMember3 J t ∧ t ≠ w ∧
      t * w = w * t ∧ J ≤ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨E₁, E₂, e₁, e₂, he⟩ := exists_edge3 hnab hz hΔ
  obtain ⟨g, hg⟩ := hw
  obtain ⟨g', -, hg'⟩ := conjClass3_involution hz he.mem₁ he.cls₁
  obtain ⟨h, hh⟩ := he.mem₂
  have hh' : conjSub h K = E₂ := hh
  have hc : (g * g'⁻¹) * e₁ * (g * g'⁻¹)⁻¹ = w := by rw [hg, hg']; group
  refine ⟨conjSub (g * g'⁻¹) E₂, (g * g'⁻¹) * e₂ * (g * g'⁻¹)⁻¹, ⟨g * g'⁻¹ * h, ?_⟩,
    he.cls₂.conj _, ?_, ?_, ?_⟩
  · show conjSub (g * g'⁻¹ * h) K = conjSub (g * g'⁻¹) E₂
    rw [conjSub_mul, hh']
  · intro hcon
    apply he.ne
    rw [← hc] at hcon
    exact (mul_left_cancel (mul_right_cancel hcon)).symm
  · rw [← hc]
    have := he.comm_involutions
    calc (g * g'⁻¹) * e₂ * (g * g'⁻¹)⁻¹ * ((g * g'⁻¹) * e₁ * (g * g'⁻¹)⁻¹)
        = (g * g'⁻¹) * (e₂ * e₁) * (g * g'⁻¹)⁻¹ := by group
      _ = (g * g'⁻¹) * (e₁ * e₂) * (g * g'⁻¹)⁻¹ := by rw [this]
      _ = (g * g'⁻¹) * e₁ * (g * g'⁻¹)⁻¹ * ((g * g'⁻¹) * e₂ * (g * g'⁻¹)⁻¹) := by group
  · intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    exact ((he.comm.conjSub (g * g'⁻¹)) _ (he.cls₁.conj _).mem j hj).symm

theorem satU_eq_of_involution_eq' (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K))
    (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G} {w : G} (hK₁ : K₁ ∈ conjClass3 K)
    (hK₂ : K₂ ∈ conjClass3 K) (hw₁ : IsClassicalMember3 K₁ w) (hw₂ : IsClassicalMember3 K₂ w) :
    satU (.sl2 3 1) K₁ w = satU (.sl2 3 1) K₂ w := by
  by_contra hne
  have hm₁ := (IsClassicalMemberU.ofQ3 hw₁).satU_member
  have hm₂ := (IsClassicalMemberU.ofQ3 hw₂).satU_member
  obtain ⟨-, -, -, hQ⟩ := twins_of_memberU hm₁ hm₂ (isIntrinsicU_satU _ _ _)
    (isIntrinsicU_satU _ _ _) hne
  have hQ' : ⁅K₁, K₂⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G)) :=
    (Subgroup.commutator_mono le_satU le_satU).trans hQ
  obtain ⟨g, -, hg⟩ := conjClass3_involution hz hK₁ hw₁
  obtain ⟨J, t, hJ, hJt, hne', hc', hJw⟩ := exists_member_commuting_involution' hnab hz hΔ ⟨g, hg⟩
  have c₁ : Commutes K₁ J := hC.of_le hK₁ hJ hw₁ hJt hne'.symm hc'.symm hJw
  have c₂ : Commutes K₂ J := hC.of_le hK₂ hJ hw₂ hJt hne'.symm hc'.symm hJw
  exact false_of_twin_pair hB hJ hJt hw₁ hw₂ hQ' c₁.symm c₂.symm hne' hc'

theorem noTwins3_of_loc (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z)
    {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass (satU (.sl2 3 1) K z))
    (hU : IsUniqueInvolution J z) : J = satU (.sl2 3 1) K z := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class _ J hJ
  rw [← satU_conj (.sl2 3 1) K z g] at hU ⊢
  have hm := (IsClassicalMemberU.ofQ3 (hz.conj g)).satU_member
  have hgz : g * z * g⁻¹ = z := (hm.isUniqueInvolution (MemberType.cert_sl2 3 1)).eq hU
  rw [hgz] at hm ⊢
  have hz' : IsClassicalMember3 (conjSub g K) z := hgz ▸ hz.conj g
  exact satU_eq_of_involution_eq' hnab hz hΔ hB hC ⟨g, rfl⟩ ⟨1, conjSub_one K⟩ hz' hz

theorem omega5At_of_loc (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) :
    Asc77.AscHypOmega.Omega5At (CoreAssembly.conjClass (satU (.sl2 3 1) K z))
      (satU (.sl2 3 1) K z) z := by
  intro J _ _ v _ _ _ hvz
  have hm := (IsClassicalMemberU.ofQ3 hz).satU_member
  refine Asc77.AscHypOmega.centralizer_le_normalizer_of_not_hasTwin
    (hm.isUniqueInvolution (MemberType.cert_sl2 3 1)) ?_
    (Subgroup.mem_centralizer_singleton_iff.mpr hvz)
  rintro ⟨J', hJ', hne, hU⟩
  exact hne (noTwins3_of_loc hnab hz hΔ hB hC hJ' hU)

theorem hypOmegaModU_of_loc (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) :
    HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) :=
  hypOmegaModU_conjClass (MemberType.cert_sl2 3 1) (IsClassicalMemberU.ofQ3 hz).satU_member
    (isIntrinsicU_satU _ _ _) (omega5At_of_loc hnab hz hΔ hB hC)

theorem hypOmegaGen_of_loc (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) :
    Disconnected.AschTight.HypOmegaGen (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (hypOmegaModU_of_loc hnab hz hΔ hB hC)

end Twin

section Nbhd

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem nbhd_shape3_loc (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hFour : Q3YS.ModelFourGroup3On fun _ => True) (hSp : Q3YS.Sp4KleinQuat3)
    (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) :
    ∃ (ι : Type) (_ : Finite ι)
      (D : LieSystemData3 ι (NbhdQuot (conjClass3 K) K₁) (nbhdFamily (conjClass3 K) K₁)),
      (z₁ ∉ nbrSpan3 (conjClass3 K) K₁ ∧ ShapeThin D ∧
        nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁)) ∨
      (∃ hzX : z₁ ∈ nbrSpan3 (conjClass3 K) K₁,
        ShapeDouble D (nbhdMk (conjClass3 K) K₁ z₁ hzX)) ∨
      (∃ hzX : z₁ ∈ nbrSpan3 (conjClass3 K) K₁,
        ShapeSp4 D (nbhdMk (conjClass3 K) K₁ z₁ hzX)) := by
  classical
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hK₁ : IsClassicalMember3 K₁ z₁ := he.cls₁
  have hK₂ : IsClassicalMember3 K₂ z₂ := he.cls₂
  have hz1sq : z₁ * z₁ = 1 := hK₁.isCentralInvolution.sq
  have hz2sq : z₂ * z₂ = 1 := hK₂.isCentralInvolution.sq
  have hK₂nbr : K₂ ∈ nbrs3 (conjClass3 K) K₁ := by
    refine ⟨he.mem₂, fun h => he.ne ?_, he.comm⟩
    rw [h] at hK₂
    exact involution_unique3 hK₁ hK₂
  obtain ⟨ι, hι, ⟨D⟩⟩ := lieSystemMod3_nbrSpan3 hΩ hBelow hK₁ ⟨K₂, hK₂nbr⟩
  set X := nbrSpan3 (conjClass3 K) K₁ with hX
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hρ
  refine ⟨ι, hι, D, ?_⟩
  have hK₂X : K₂ ≤ X := le_nbrSpan3 hK₂nbr
  have hz₂X : z₂ ∈ X := hK₂X hK₂.mem
  have hKΦ : modOddIn X K₂ ∈ nbhdFamily (conjClass3 K) K₁ :=
    ⟨K₂.subgroupOf X, ⟨K₂, hK₂nbr, rfl⟩, rfl⟩
  have hι0 : Nonempty ι := by
    obtain ⟨i, -⟩ := D.fundamental _ hKΦ
    exact ⟨i⟩
  have hsqρ : ∀ (x : G) (hx : x ∈ X), x * x = 1 → ρ ⟨x, hx⟩ * ρ ⟨x, hx⟩ = 1 := by
    intro x hx hx2
    rw [← map_mul]
    have : (⟨x, hx⟩ : ↥X) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  by_cases hzX : z₁ ∈ X
  ·
    have hz1ne : ρ ⟨z₁, hzX⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution X hzX hz1sq hK₁.ne_one
    have hz2ne : ρ ⟨z₂, hz₂X⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution X hz₂X hz2sq hK₂.ne_one
    have hz1sqX := hsqρ z₁ hzX hz1sq
    have hz2sqX := hsqρ z₂ hz₂X hz2sq
    have hzc : ∀ x : NbhdQuot (conjClass3 K) K₁, x * ρ ⟨z₁, hzX⟩ = ρ ⟨z₁, hzX⟩ * x := by
      intro x
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp
        (nbrSpan3_le_centralizer (conjClass3 K) K₁ x'.2) z₁ hK₁.mem).symm
    have hBD : BDNbhd (ρ ⟨z₁, hzX⟩) :=
      { ne_one := hz1ne
        mul_self := hz1sqX
        central := hzc
        mem := fun F hF hc => (nbhd_fourGroup_mem3 hB he.mem₁ hK₁ hF hc).2 }
    rcases shape_of_bdNbhd hMFZ hFour hSp D hBD with hT | hDbl | hS4
    ·
      exfalso
      obtain ⟨i₀, hone, hk₀⟩ := hT
      obtain ⟨x, y, ζ, -, -, -, -, huniq⟩ := exists_quatPair_of_sl23 D hk₀
      have hrange : (D.hom i₀).range = ⊤ := range_eq_top_of_forall_eq D hone
      have hu : ∀ u : NbhdQuot (conjClass3 K) K₁, u * u = 1 → u = 1 ∨ u = ζ := fun u hu =>
        huniq u (by rw [hrange]; exact Subgroup.mem_top _) hu
      have h1 := (hu _ hz1sqX).resolve_left hz1ne
      have h2 := (hu _ hz2sqX).resolve_left hz2ne
      exact Q3Y.mk_involutions_ne hzX hz₂X hz1sq hz2sq he.comm_involutions he.ne
        (h1.trans h2.symm)
    ·
      right
      left
      refine ⟨hzX, hDbl.exact ?_⟩
      intro i ζ hi hζ huniq hzeq
      obtain ⟨R, hR, hRΦ⟩ := D.meets i
      have hRtop : R = ⊤ := Q3Y.eq_top_of_mem_fund_sl23 hi hR
      rw [hRtop, Subgroup.map_top] at hRΦ
      obtain ⟨_, ⟨L, hL, rfl⟩, hLR⟩ := hRΦ
      obtain ⟨w, hw⟩ := hΩ.classical L hL.1
      have hLX : L ≤ X := le_nbrSpan3 hL
      have hwX : w ∈ X := hLX hw.mem
      have hw2 : w * w = 1 := hw.isCentralInvolution.sq
      have hwmem : ρ ⟨w, hwX⟩ ∈ (D.hom i).range := by
        rw [← hLR]
        exact ⟨⟨w, hwX⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩
      have hwne : ρ ⟨w, hwX⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution X hwX hw2 hw.ne_one
      have hwζ : ρ ⟨w, hwX⟩ = ζ := (huniq _ hwmem (hsqρ w hwX hw2)).resolve_left hwne
      have hwz : w = z₁ := by
        by_contra hne
        have hc : z₁ * w = w * z₁ := Subgroup.mem_centralizer_iff.mp
          (nbrSpan3_le_centralizer (conjClass3 K) K₁ hwX) z₁ hK₁.mem
        exact Q3Y.mk_involutions_ne hwX hzX hw2 hz1sq hc.symm hne (hwζ.trans hzeq.symm)
      have hLw : IsClassicalMember3 L z₁ := hwz ▸ hw
      exact false_of_commuting_twins hB he.mem₂ hK₁ hLw hK₂ he.ne.symm hL.2.2 he.comm
        (hC.of_le hL.1 he.mem₂ hLw hK₂ he.ne he.comm_involutions he.le_centralizer_left)
    · exact Or.inr (Or.inr ⟨hzX, hS4⟩)
  ·
    left
    have hno : ∀ F : Subgroup (NbhdQuot (conjClass3 K) K₁), IsElemAbelian 2 F →
        Nat.card F = 4 → False := fun F hF hc =>
      hzX (nbhd_fourGroup_mem3 hB he.mem₁ hK₁ hF hc).1
    have hT := shape_of_noFourGroup hFour hSp D hno
    exact ⟨hzX, hT, le_sup_oddCoreIn_of_shapeThin hK₂nbr D hT⟩

theorem nbhd_shape3_free (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) :
    ∃ (ι : Type) (_ : Finite ι)
      (D : LieSystemData3 ι (NbhdQuot (conjClass3 K) K₁) (nbhdFamily (conjClass3 K) K₁)),
      (z₁ ∉ nbrSpan3 (conjClass3 K) K₁ ∧ ShapeThin D ∧
        nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁)) ∨
      (∃ hzX : z₁ ∈ nbrSpan3 (conjClass3 K) K₁,
        ShapeDouble D (nbhdMk (conjClass3 K) K₁ z₁ hzX)) ∨
      (∃ hzX : z₁ ∈ nbrSpan3 (conjClass3 K) K₁,
        ShapeSp4 D (nbhdMk (conjClass3 K) K₁ z₁ hzX)) :=
  nbhd_shape3_loc (RouteD.Gaps.fundNoncentral 3) Q3YS.modelFourGroup3On_all Q3YS.sp4KleinQuat3 hz
    hBelow hB hC he

theorem nbhd_mem_or_thin_free (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) :
    z₁ ∈ nbrSpan3 (conjClass3 K) K₁ ∨
      nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁) := by
  obtain ⟨ι, -, D, h⟩ := nbhd_shape3_free hz hBelow hB hC he
  rcases h with ⟨-, -, h⟩ | ⟨hzX, -⟩ | ⟨hzX, -⟩
  · exact Or.inr h
  · exact Or.inl hzX
  · exact Or.inl hzX

end Nbhd

end CFSG.ClassicalInvolution.Q3.Q3CP
