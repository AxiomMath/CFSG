module

public import CFSG.ClassicalInvolution.Q3.Q3CPShape
public import CFSG.ClassicalInvolution.Q3.Q3YThird

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement

section Twins

variable {G : Type} [Group G] [Finite G]

theorem false_of_commuting_twins {Ω : Set (Subgroup G)} (hB : ¬ BootData3 Ω)
    {K₁ M K₂ : Subgroup G} {z₁ z₂ : G} (hK₂Ω : K₂ ∈ Ω) (hK₁ : IsClassicalMember3 K₁ z₁)
    (hM : IsClassicalMember3 M z₁) (hK₂ : IsClassicalMember3 K₂ z₂) (hne : z₂ ≠ z₁)
    (c₁M : Commutes K₁ M) (c₁₂ : Commutes K₁ K₂) (cM₂ : Commutes M K₂) : False := by
  have hz1sq : z₁ * z₁ = 1 := hK₁.isCentralInvolution.sq
  obtain ⟨a, ha, a', ha', haa, ha'a', hcaa'⟩ := hK₁.exists_quaternion_pair_sq
  obtain ⟨b, hb, -, -, hbb, -, -⟩ := hM.exists_quaternion_pair_sq
  refine Q3Y.false_of_quaternion_pair (Subgroup.centralizer (K₂ : Set G)) (ζ := z₁) (w := z₂)
    (a := a) (a' := a') (b := b) hK₁.ne_one hz1sq haa ha'a' hbb ?_ (c₁M a ha b hb)
    (c₁M a' ha' b hb) (Subgroup.mem_centralizer_iff.mpr fun k hk => (c₁₂ a ha k hk).symm)
    (Subgroup.mem_centralizer_iff.mpr fun k hk => (c₁₂ a' ha' k hk).symm)
    (Subgroup.mem_centralizer_iff.mpr fun k hk => (cM₂ b hb k hk).symm) hne ?_
  · intro hc'
    apply hK₁.ne_one
    rw [← hcaa', hc']
    group
  · intro p q hp hq hp2 hq2 hp1 hq1 hpq hc
    exact eq_or_eq_or_eq_mul_of_not_bootData3 hB hK₂Ω hK₂ hp2 hq2 hp1 hq1 hpq hc
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hp k hk))
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hq k hk))

end Twins

section Nbhd

variable {G : Type} [Group G] [Finite G]

abbrev NbhdQuot (Ω : Set (Subgroup G)) (K₁ : Subgroup G) : Type :=
  ↥(nbrSpan3 Ω K₁) ⧸ classicalInvolutionOddCore ↥(nbrSpan3 Ω K₁)

abbrev nbhdFamily (Ω : Set (Subgroup G)) (K₁ : Subgroup G) : Set (Subgroup (NbhdQuot Ω K₁)) :=
  oddQuotientFamily {L' : Subgroup ↥(nbrSpan3 Ω K₁) |
    ∃ L ∈ nbrs3 Ω K₁, L' = L.subgroupOf (nbrSpan3 Ω K₁)}

abbrev nbhdMk (Ω : Set (Subgroup G)) (K₁ : Subgroup G) (g : G) (hg : g ∈ nbrSpan3 Ω K₁) :
    NbhdQuot Ω K₁ :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrSpan3 Ω K₁)) ⟨g, hg⟩


theorem le_sup_oddCoreIn_of_shapeThin {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G}
    (hK₂ : K₂ ∈ nbrs3 Ω K₁) {ι : Type}
    (D : LieSystemData3 ι (NbhdQuot Ω K₁) (nbhdFamily Ω K₁)) (hT : ShapeThin D) :
    nbrSpan3 Ω K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 Ω K₁) := by
  obtain ⟨i₀, hone, hk₀⟩ := hT
  have hrange : (D.hom i₀).range = ⊤ := range_eq_top_of_forall_eq D hone
  have hKΦ : modOddIn (nbrSpan3 Ω K₁) K₂ ∈ nbhdFamily Ω K₁ :=
    ⟨K₂.subgroupOf (nbrSpan3 Ω K₁), ⟨K₂, hK₂, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental _ hKΦ
  have hk : D.kind i = CompData.sl23 := (hone i) ▸ hk₀
  have hRtop : R = ⊤ := Q3Y.eq_top_of_mem_fund_sl23 hk hR
  have htop : modOddIn (nbrSpan3 Ω K₁) K₂ = ⊤ := by
    rw [hKR, hRtop, ← MonoidHom.range_eq_map, hone i]
    exact hrange
  intro x hx
  have hxm : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrSpan3 Ω K₁)) ⟨x, hx⟩ ∈
      modOddIn (nbrSpan3 Ω K₁) K₂ := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk', hkx⟩ := hxm
  have hn : k⁻¹ * (⟨x, hx⟩ : ↥(nbrSpan3 Ω K₁)) ∈
      classicalInvolutionOddCore ↥(nbrSpan3 Ω K₁) := QuotientGroup.eq.mp hkx
  have hxe : x = (k : G) * ((k⁻¹ * ⟨x, hx⟩ : ↥(nbrSpan3 Ω K₁)) : G) := by simp
  rw [hxe]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk'))
    (Subgroup.mem_sup_right ⟨_, hn, rfl⟩)

variable [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem nbhd_shape3 (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hFour : Q3YS.ModelFourGroup3On fun _ => True) (hSp : Q3YS.Sp4KleinQuat3)
    (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G}
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
        (commutes_of_not_a2Configuration3 hz hA2 hL.1 he.mem₂ hLw hK₂ he.ne he.comm_involutions)
    · exact Or.inr (Or.inr ⟨hzX, hS4⟩)
  ·
    left
    have hno : ∀ F : Subgroup (NbhdQuot (conjClass3 K) K₁), IsElemAbelian 2 F →
        Nat.card F = 4 → False := fun F hF hc =>
      hzX (nbhd_fourGroup_mem3 hB he.mem₁ hK₁ hF hc).1
    have hT := shape_of_noFourGroup hFour hSp D hno
    exact ⟨hzX, hT, le_sup_oddCoreIn_of_shapeThin hK₂nbr D hT⟩

theorem nbhd_mem_or_thin (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hFour : Q3YS.ModelFourGroup3On fun _ => True) (hSp : Q3YS.Sp4KleinQuat3)
    (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) :
    z₁ ∈ nbrSpan3 (conjClass3 K) K₁ ∨
      nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁) := by
  obtain ⟨ι, -, D, h⟩ := nbhd_shape3 hMFZ hFour hSp hz hBelow hB hA2 he
  rcases h with ⟨-, -, h⟩ | ⟨hzX, -⟩ | ⟨hzX, -⟩
  · exact Or.inr h
  · exact Or.inl hzX
  · exact Or.inl hzX

end Nbhd

end CFSG.ClassicalInvolution.Q3.Q3CP
