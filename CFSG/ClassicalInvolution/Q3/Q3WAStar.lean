module

public import CFSG.ClassicalInvolution.Q3.Q3WAWeak

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.NonClassical (Linked NCEdge)

section Nbhd



variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {ι : Type}

theorem exists_nc_pair_in_block_nbr3 (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G} (h : RouteD3Setup K z)
    (hc : LocCtx3 K z)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    {A₀ : Subgroup G} {i₀ i' : ι} {a₂ q c : Subgroup G}
    (hA₀ : A₀ ∈ centralizingMembers (conjClass3 K) {z})
    (hblock : ncBlock (conjClass3 K) z A₀ = compMembers3 (conjClass3 K) z D i₀)
    (hi₀na : ¬ IsA1Comp3 D i₀) (hi'na : ¬ IsA1Comp3 D i') (hi'ne : i' ≠ i₀)
    (ha₂ : a₂ ∈ compMembers3 (conjClass3 K) z D i')
    (hKc : ∀ B ∈ compMembers3 (conjClass3 K) z D i₀, Commutes K B ∧ Commutes a₂ B)
    (hqΩ : q ∈ conjClass3 K)
    (hqcl : ∀ x ∈ conjClass3 K, (∀ B ∈ compMembers3 (conjClass3 K) z D i₀, Commutes x B) →
      ¬ Commutes q x)
    (hc₀ : c ∈ compMembers3 (conjClass3 K) z D i₀) (hqc : Commutes q c) :
    ∃ b₁ ∈ compMembers3 (conjClass3 K) z D i₀, ∃ b₂ ∈ compMembers3 (conjClass3 K) z D i₀,
      b₁ ≠ b₂ ∧ Commutes c b₁ ∧ Commutes c b₂ ∧ ¬ Commutes b₁ b₂ := by
  have hΩ := hc.hΩ
  have hex := hc.hex
  have hP1 := hc.hP1
  have hO3 := hc.hO3
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hcΩ : c ∈ conjClass3 K := hc₀.1.1
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hK, isSubnormal_le hc.hz.subnormal⟩
  obtain ⟨g, hg⟩ := single_class3 K c hcΩ
  have hyc : IsClassicalMember3 c (g * z * g⁻¹) := by
    rw [hg]
    exact hc.hz.conj g
  set y : G := g * z * g⁻¹ with hy
  have hP1y : LocalOddCentral (conjClass3 K) {y} :=
    Gaps.localOddCentral_conj hΩ.conjInvariant g z hP1
  have hO3y : LocalOddThreeFree3 (conjClass3 K) y :=
    localOddThreeFree3_conj hΩ.conjInvariant g z hO3
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hyc.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨ιy, hιy, ⟨Dy⟩⟩ := h.ih {y} hync
  have hcy : c ∈ centralizingMembers (conjClass3 K) {y} :=
    ⟨hcΩ, isSubnormal_le hyc.subnormal⟩
  have hcp : ∀ L ∈ centralizingMembers (conjClass3 K) {y}, L ≠ c → Commutes c L :=
    fun L hL hne =>
      (commutes_or_eq_of_involution3 hMFZ hΩ hex hP1y hO3y Dy hcy hL hyc).resolve_right hne
  set V := compMembers3 (conjClass3 K) z D i₀ with hV
  have hcent : ∀ x ∈ conjClass3 K, (∀ B ∈ V, Commutes x B) →
      x ∈ centralizingMembers (conjClass3 K) {y} := by
    intro x hx hxV
    refine ⟨hx, fun u hu => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxV c hc₀ u hu y hyc.mem
  have hqy : q ∈ centralizingMembers (conjClass3 K) {y} := by
    refine ⟨hqΩ, fun u hu => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hqc u hu y hyc.mem
  have hblk : ∀ x ∈ conjClass3 K, (∀ B ∈ V, Commutes x B) →
      x ∈ ncBlock (conjClass3 K) y q :=
    fun x hx hxV => Linked.single ⟨hqy, hcent x hx hxV, hqcl x hx hxV⟩
  have hKV : ∀ B ∈ V, Commutes K B := fun B hB => (hKc B hB).1
  have hKy : K ∈ centralizingMembers (conjClass3 K) {y} := hcent K hK hKV
  have hKblk : Linked (conjClass3 K) y q K := hblk K hK hKV
  have hout : ∀ x' ∈ centralizingMembers (conjClass3 K) {y}, x' ∉ ncBlock (conjClass3 K) y q →
      x' ∈ V := by
    intro x' hx'y hx'
    have hx'K : Commutes x' K := by
      by_contra hnc
      exact hx' (hKblk.trans (Linked.single ⟨hKy, hx'y, fun hc' =>
        hnc (Gaps.commutes_symm hc')⟩))
    have hx'z : x' ∈ centralizingMembers (conjClass3 K) {z} :=
      mem_centralizingMembers_of_commutes hx'y.1 hc.hz.mem hx'K
    obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hx'z
    by_cases hji : j = i₀
    · rw [hji] at hj
      exact hj
    · exact absurd (hblk x' hx'y.1 fun B hB => commutes_of_ne_comp3 hΩ hex hP1 hO3 D hji hj hB)
        hx'
  have hcblock : ∀ w, Linked (conjClass3 K) y c w → w = c := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b d _ hbd ih =>
      rw [ih] at hbd
      by_contra hdc
      exact hbd.2.2 (hcp d hbd.2.1 hdc)
  have hsize : ∀ i : ι, ¬ IsA1Comp3 D i → 1 < (compMembers3 (conjClass3 K) z D i).ncard := by
    intro i hi
    obtain ⟨N, N', hN, hN', hne⟩ := exists_ne_of_not_isA1Comp3 hΩ hex hP1 hO3 hi
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨N, hN, N', hN', hne⟩
  have hVcard : 1 < V.ncard := hsize i₀ hi₀na
  have hconj : ∀ A ∈ centralizingMembers (conjClass3 K) {z},
      conjSub g A ∈ centralizingMembers (conjClass3 K) {y} := by
    intro A hA
    have := centralizingMembers_conj hΩ.conjInvariant g z
    rw [hy, this]
    exact ⟨A, hA, rfl⟩
  have hA'C : conjSub g A₀ ∈ ncBlock (conjClass3 K) y q := by
    by_contra hA'
    have hA'y := hconj A₀ hA₀
    have hsub : ncBlock (conjClass3 K) y (conjSub g A₀) ⊆ V := by
      intro w hw
      have hw' : Linked (conjClass3 K) y (conjSub g A₀) w := hw
      have hwy := hw'.mem_centralizingMembers hA'y
      refine hout w hwy fun hwq => hA' ?_
      exact (show Linked (conjClass3 K) y q w from hwq).trans hw'.symm
    have hXcard : (ncBlock (conjClass3 K) y (conjSub g A₀)).ncard = V.ncard := by
      rw [ncard_ncBlock_conj hΩ.conjInvariant g z A₀, hblock]
    have heq : ncBlock (conjClass3 K) y (conjSub g A₀) = V :=
      Set.eq_of_subset_of_ncard_le hsub hXcard.ge (Set.toFinite _)
    have hcX0 : c ∈ ncBlock (conjClass3 K) y (conjSub g A₀) := by
      rw [heq]
      exact hc₀
    have hcX : Linked (conjClass3 K) y (conjSub g A₀) c := hcX0
    have hAc : conjSub g A₀ = c := hcblock _ hcX.symm
    have h1 : (ncBlock (conjClass3 K) y (conjSub g A₀)).ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff (Set.toFinite _)]
      intro a b ha hb
      have ha' : Linked (conjClass3 K) y c a := by rw [← hAc]; exact ha
      have hb' : Linked (conjClass3 K) y c b := by rw [← hAc]; exact hb
      rw [hcblock a ha', hcblock b hb']
    omega
  have hXVC : ncBlock (conjClass3 K) y (conjSub g A₀) = ncBlock (conjClass3 K) y q := by
    ext w
    have h1 : Linked (conjClass3 K) y q (conjSub g A₀) := hA'C
    constructor
    · intro hw
      exact h1.trans hw
    · intro hw
      exact h1.symm.trans hw
  have hblock' : ncBlock (conjClass3 K) z a₂ = compMembers3 (conjClass3 K) z D i' := by
    ext B
    exact linked_iff_mem_compMembers3 hΩ hex hP1 hO3 (quasi_or_a1_3 D i') ha₂
  have hA''y := hconj a₂ ha₂.1
  have hA''C : conjSub g a₂ ∉ ncBlock (conjClass3 K) y q := by
    intro hA''
    have h2 : ncBlock (conjClass3 K) y (conjSub g a₂) =
        ncBlock (conjClass3 K) y (conjSub g A₀) := by
      rw [hXVC]
      ext w
      have h1 : Linked (conjClass3 K) y q (conjSub g a₂) := hA''
      constructor
      · intro hw
        exact h1.trans hw
      · intro hw
        exact h1.symm.trans hw
    rw [ncBlock_conj hΩ.conjInvariant, ncBlock_conj hΩ.conjInvariant] at h2
    have h3 : ncBlock (conjClass3 K) z a₂ = ncBlock (conjClass3 K) z A₀ :=
      Set.image_injective.mpr (conjSub_injective g) h2
    have h4 : a₂ ∈ V := by
      rw [← hblock, ← h3]
      exact Relation.ReflTransGen.refl
    exact hi'ne (eq_of_locImg_le_range3 hΩ hex hP1 hO3 D ha₂.1 ha₂.2 h4.2)
  have hsubV' : ncBlock (conjClass3 K) y (conjSub g a₂) ⊆ V := by
    intro w hw
    have hw' : Linked (conjClass3 K) y (conjSub g a₂) w := hw
    have hwy := hw'.mem_centralizingMembers hA''y
    refine hout w hwy fun hwq => hA''C ?_
    exact (show Linked (conjClass3 K) y q w from hwq).trans hw'.symm
  have hV'card : 1 < (ncBlock (conjClass3 K) y (conjSub g a₂)).ncard := by
    rw [ncard_ncBlock_conj hΩ.conjInvariant g z a₂, hblock']
    exact hsize i' hi'na
  obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp hV'card
  obtain ⟨B, hB, hBne⟩ : ∃ B ∈ ncBlock (conjClass3 K) y (conjSub g a₂), B ≠ conjSub g a₂ := by
    by_cases h1 : B₁ = conjSub g a₂
    · exact ⟨B₂, hB₂, fun h2 => hne (h1.trans h2.symm)⟩
    · exact ⟨B₁, hB₁, h1⟩
  obtain ⟨b₁, hb₁, b₂, hb₂, hbne, hbnc⟩ := exists_nc_pair_of_block ⟨B, hB, hBne⟩
  have hbc : ∀ b ∈ ncBlock (conjClass3 K) y (conjSub g a₂), b ≠ c := by
    intro b hb hbc
    have hb' : Linked (conjClass3 K) y (conjSub g a₂) c := by rw [← hbc]; exact hb
    have hAc : conjSub g a₂ = c := hcblock _ hb'.symm
    have h1 : (ncBlock (conjClass3 K) y (conjSub g a₂)).ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff (Set.toFinite _)]
      intro a b ha hb
      have ha' : Linked (conjClass3 K) y c a := by rw [← hAc]; exact ha
      have hb' : Linked (conjClass3 K) y c b := by rw [← hAc]; exact hb
      rw [hcblock a ha', hcblock b hb']
    omega
  exact ⟨b₁, hsubV' hb₁, b₂, hsubV' hb₂, hbne,
    hcp b₁ (hb₁.mem_centralizingMembers hA''y) (hbc b₁ hb₁),
    hcp b₂ (hb₂.mem_centralizingMembers hA''y) (hbc b₂ hb₂), hbnc⟩

end Nbhd

end CFSG.ClassicalInvolution.Q3.Q3W
