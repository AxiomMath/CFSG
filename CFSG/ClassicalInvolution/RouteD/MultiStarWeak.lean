module

public import CFSG.ClassicalInvolution.RouteD.MultiStarComp
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Blocks

variable {Ω : Set (Subgroup G)}

@[expose] def ncBlock (Ω : Set (Subgroup G)) (x : G) (A : Subgroup G) : Set (Subgroup G) :=
  {B | Linked Ω x A B}

theorem ncEdge_conj_iff (hΩ : ConjInvariant Ω) (g x : G) {A B : Subgroup G} :
    NCEdge Ω (g * x * g⁻¹) (conjSub g A) (conjSub g B) ↔ NCEdge Ω x A B := by
  unfold NCEdge
  rw [centralizingMembers_conj hΩ, (conjSub_injective g).mem_set_image,
    (conjSub_injective g).mem_set_image, commutes_conjSub_iff]

theorem exists_linked_of_linked_conj (hΩ : ConjInvariant Ω) (g x : G) {A C : Subgroup G}
    (h : Linked Ω (g * x * g⁻¹) (conjSub g A) C) :
    ∃ C' : Subgroup G, C = conjSub g C' ∧ Linked Ω x A C' := by
  induction h with
  | refl => exact ⟨A, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨b', rfl, hb'⟩ := ih
    have hc : c ∈ centralizingMembers Ω {g * x * g⁻¹} := hbc.2.1
    have hc' : c ∈ conjSub g '' centralizingMembers Ω {x} := by
      rw [← centralizingMembers_conj hΩ]
      exact hc
    obtain ⟨c', hc'mem, rfl⟩ := hc'
    exact ⟨c', rfl, hb'.trans (Linked.single ((ncEdge_conj_iff hΩ g x).mp hbc))⟩

theorem linked_conj_iff (hΩ : ConjInvariant Ω) (g x : G) {A B : Subgroup G} :
    Linked Ω (g * x * g⁻¹) (conjSub g A) (conjSub g B) ↔ Linked Ω x A B := by
  constructor
  · intro h
    obtain ⟨C', hC', hlink⟩ := exists_linked_of_linked_conj hΩ g x h
    rw [conjSub_injective g hC']
    exact hlink
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.trans (Linked.single ((ncEdge_conj_iff hΩ g x).mpr hbc))

theorem ncBlock_conj (hΩ : ConjInvariant Ω) (g x : G) (A : Subgroup G) :
    ncBlock Ω (g * x * g⁻¹) (conjSub g A) = conjSub g '' ncBlock Ω x A := by
  ext B
  constructor
  · intro h
    obtain ⟨C', hC', hlink⟩ := exists_linked_of_linked_conj hΩ g x h
    exact ⟨C', hlink, hC'.symm⟩
  · rintro ⟨B', hB', rfl⟩
    exact (linked_conj_iff hΩ g x).mpr hB'

theorem ncard_ncBlock_conj (hΩ : ConjInvariant Ω) (g x : G) (A : Subgroup G) :
    (ncBlock Ω (g * x * g⁻¹) (conjSub g A)).ncard = (ncBlock Ω x A).ncard := by
  rw [ncBlock_conj hΩ, Set.ncard_image_of_injective _ (conjSub_injective g)]

end Blocks

section Closure

variable [Finite G] {Ω : Set (Subgroup G)}

theorem normal_of_commutes_of_sup_eq_top {X : Type*} [Group X] {N W : Subgroup X}
    (hc : Commutes N W) (h : N ⊔ W = ⊤) : N.Normal := by
  have hnormlz : N ⊔ W ≤ Subgroup.normalizer (N : Set X) := by
    refine sup_le Subgroup.le_normalizer fun w hw => ?_
    rw [Subgroup.mem_normalizer_iff]
    have hfix : ∀ w ∈ W, ∀ n ∈ N, w * n * w⁻¹ = n := by
      intro w hw n hn
      have := hc n hn w hw
      calc w * n * w⁻¹ = (n * w) * w⁻¹ := by rw [this]
        _ = n := by group
    intro n
    constructor
    · intro hn
      rw [hfix w hw n hn]
      exact hn
    · intro hn
      have h2 := hfix w⁻¹ (W.inv_mem hw) _ hn
      have h3 : n = w⁻¹ * (w * n * w⁻¹) * w⁻¹⁻¹ := by group
      rw [h3, h2]
      exact hn
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ Subgroup.normalizer (N : Set X) := hnormlz (h ▸ Subgroup.mem_top g)
  exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn

theorem mem_ncBlock_of_commutes_of_max (hΩ : ConjInvariant Ω) {K : Subgroup G} {z : G} (hz : z ∈ K)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {A₀ : Subgroup G}
    (hA₀ : A₀ ∈ centralizingMembers Ω {z})
    (hmax : ∀ A ∈ centralizingMembers Ω {z}, (ncBlock Ω z A).ncard ≤ (ncBlock Ω z A₀).ncard)
    {x : Subgroup G} (hx : x ∈ Ω) (hxV : ∀ B ∈ ncBlock Ω z A₀, Commutes x B) {C : Subgroup G}
    (hC : C ∈ Ω) (hxC : Commutes x C) {B : Subgroup G} (hB : B ∈ ncBlock Ω z A₀)
    (hCB : ¬ Commutes C B) : C ∈ ncBlock Ω z A₀ := by
  obtain ⟨g, rfl⟩ := hsingle x hx
  have hyx : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hz
  have hVcent : ∀ B' ∈ ncBlock Ω z A₀, B' ∈ centralizingMembers Ω {g * z * g⁻¹} := by
    intro B' hB'
    have hB'z : B' ∈ centralizingMembers Ω {z} := hB'.mem_centralizingMembers hA₀
    refine ⟨hB'z.1, fun b hb => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxV B' hB' _ hyx b hb).symm
  have hsub : ncBlock Ω z A₀ ⊆ ncBlock Ω (g * z * g⁻¹) A₀ := by
    intro B' hB'
    have hB'' : Linked Ω z A₀ B' := hB'
    clear hB'
    induction hB'' with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      exact ih.trans (Linked.single ⟨hVcent b hab, hVcent c (hab.tail hbc), hbc.2.2⟩)
  have hA₀y : A₀ ∈ centralizingMembers Ω {g * z * g⁻¹} := hVcent A₀ Relation.ReflTransGen.refl
  have hcard : (ncBlock Ω (g * z * g⁻¹) A₀).ncard ≤ (ncBlock Ω z A₀).ncard := by
    have hmem : A₀ ∈ conjSub g '' centralizingMembers Ω {z} := by
      rw [← centralizingMembers_conj hΩ]
      exact hA₀y
    obtain ⟨A', hA', hA'eq⟩ := hmem
    have e : (ncBlock Ω (g * z * g⁻¹) A₀).ncard = (ncBlock Ω z A').ncard := by
      rw [← hA'eq]
      exact ncard_ncBlock_conj hΩ g z A'
    rw [e]
    exact hmax A' hA'
  have heq : ncBlock Ω z A₀ = ncBlock Ω (g * z * g⁻¹) A₀ :=
    Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hCy : C ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    ⟨hC, fun c hc => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hxC _ hyx c hc).symm⟩
  have hedge : Linked Ω (g * z * g⁻¹) C B := Linked.single ⟨hCy, hVcent B hB, hCB⟩
  have hBy : B ∈ ncBlock Ω (g * z * g⁻¹) A₀ := heq ▸ hB
  rw [heq]
  exact (show Linked Ω (g * z * g⁻¹) A₀ B from hBy).trans (show Linked Ω (g * z * g⁻¹) B C from
    hedge.symm)

theorem exists_not_commuting_of_max [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hΩ : ConjInvariant Ω) (hgen : ⨆ L ∈ Ω, L = ⊤) (hne : ∀ L ∈ Ω, L ≠ ⊥) {K : Subgroup G}
    (hKΩ : K ∈ Ω) {z : G} (hz : z ∈ K) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ centralizingMembers Ω {z})
    (hmax : ∀ A ∈ centralizingMembers Ω {z}, (ncBlock Ω z A).ncard ≤ (ncBlock Ω z A₀).ncard)
    (hKV : K ∉ ncBlock Ω z A₀) (hKc : ∀ B ∈ ncBlock Ω z A₀, Commutes K B) :
    ∃ q ∈ Ω, q ∉ ncBlock Ω z A₀ ∧ (∃ B ∈ ncBlock Ω z A₀, ¬ Commutes q B) ∧ ¬ Commutes q K ∧
      ∀ x ∈ Ω, (∀ B ∈ ncBlock Ω z A₀, Commutes x B) → ¬ Commutes q x := by
  set V := ncBlock Ω z A₀ with hV
  have hVΩ : ∀ B ∈ V, B ∈ Ω := fun B hB => (hB.mem_centralizingMembers hA₀).1
  have hA₀V : A₀ ∈ V := Relation.ReflTransGen.refl
  have hclosure : ∀ q ∈ Ω, q ∉ V → (∃ B ∈ V, ¬ Commutes q B) → ∀ x ∈ Ω,
      (∀ B ∈ V, Commutes x B) → ¬ Commutes q x := by
    rintro q hq hqV ⟨B, hB, hqB⟩ x hx hxV hqx
    exact hqV (mem_ncBlock_of_commutes_of_max hΩ hz hsingle hA₀ hmax hx hxV hq
      (Gaps.commutes_symm hqx) hB hqB)
  have hex : ∃ q ∈ Ω, q ∉ V ∧ ∃ B ∈ V, ¬ Commutes q B := by
    by_contra hcon
    push Not at hcon
    let N : Subgroup G := ⨆ q : {q : Subgroup G // q ∈ Ω ∧ q ∉ V}, q.1
    let W : Subgroup G := ⨆ B : ↥V, B.1
    have hcomm : Commutes N W :=
      commutes_iSup_iSup fun q B => hcon q.1 q.2.1 q.2.2 B.1 B.2
    have hsup : N ⊔ W = ⊤ := by
      rw [eq_top_iff, ← hgen]
      refine iSup₂_le fun L hL => ?_
      by_cases hLV : L ∈ V
      · exact (le_iSup (fun B : ↥V => B.1) ⟨L, hLV⟩).trans le_sup_right
      · exact (le_iSup (fun q : {q : Subgroup G // q ∈ Ω ∧ q ∉ V} => q.1)
          ⟨L, hL, hLV⟩).trans le_sup_left
    have hN : N.Normal := normal_of_commutes_of_sup_eq_top hcomm hsup
    have hNne : N ≠ ⊥ := by
      intro hb
      have : K ≤ N := le_iSup (fun q : {q : Subgroup G // q ∈ Ω ∧ q ∉ V} => q.1) ⟨K, hKΩ, hKV⟩
      exact hne K hKΩ (eq_bot_iff.mpr (hb ▸ this))
    have hNtop : N = ⊤ := hN.eq_bot_or_eq_top.resolve_left hNne
    have hWbot : W = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have hwc : w ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact hcomm g (hNtop ▸ Subgroup.mem_top g) w hw
      rwa [center_eq_bot hnab] at hwc
    have hA₀le : A₀ ≤ W := le_iSup (fun B : ↥V => B.1) ⟨A₀, hA₀V⟩
    exact hne A₀ (hVΩ A₀ hA₀V) (eq_bot_iff.mpr (hWbot ▸ hA₀le))
  obtain ⟨q, hqΩ, hqV, hqB⟩ := hex
  exact ⟨q, hqΩ, hqV, hqB, hclosure q hqΩ hqV hqB K hKΩ hKc,
    fun x hx hxV => hclosure q hqΩ hqV hqB x hx hxV⟩

theorem exists_not_commuting_nbr_of_max [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hΩ : ConjInvariant Ω) (hgen : ⨆ L ∈ Ω, L = ⊤) (hne : ∀ L ∈ Ω, L ≠ ⊥) {K : Subgroup G}
    (hKΩ : K ∈ Ω) {z : G} (hz : z ∈ K) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hconn : ∀ X ∈ Ω, ∀ Y ∈ Ω,
      Relation.ReflTransGen (fun A B : Subgroup G => A ∈ Ω ∧ B ∈ Ω ∧ Commutes A B) X Y)
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ centralizingMembers Ω {z})
    (hmax : ∀ A ∈ centralizingMembers Ω {z}, (ncBlock Ω z A).ncard ≤ (ncBlock Ω z A₀).ncard)
    (hKV : K ∉ ncBlock Ω z A₀) (hKc : ∀ B ∈ ncBlock Ω z A₀, Commutes K B) :
    ∃ q ∈ Ω, q ∉ ncBlock Ω z A₀ ∧ (∃ B ∈ ncBlock Ω z A₀, ¬ Commutes q B) ∧
      (∃ c ∈ ncBlock Ω z A₀, Commutes q c) ∧ ¬ Commutes q K ∧
      ∀ x ∈ Ω, (∀ B ∈ ncBlock Ω z A₀, Commutes x B) → ¬ Commutes q x := by
  obtain ⟨q₀, hq₀Ω, hq₀V, hq₀B, hq₀K, hq₀cl⟩ := exists_not_commuting_of_max hnab hΩ hgen hne hKΩ
    hz hsingle hA₀ hmax hKV hKc
  set V := ncBlock Ω z A₀ with hV
  by_cases hnbr : ∃ q ∈ Ω, q ∉ V ∧ (∃ B ∈ V, ¬ Commutes q B) ∧ ∃ c ∈ V, Commutes q c
  · obtain ⟨q, hqΩ, hqV, hqB, hqc⟩ := hnbr
    refine ⟨q, hqΩ, hqV, hqB, hqc, ?_, fun x hx hxV hqx => ?_⟩
    · intro hqK
      exact hqV (mem_ncBlock_of_commutes_of_max hΩ hz hsingle hA₀ hmax hKΩ hKc hqΩ
        (Gaps.commutes_symm hqK) hqB.choose_spec.1 hqB.choose_spec.2)
    · exact hqV (mem_ncBlock_of_commutes_of_max hΩ hz hsingle hA₀ hmax hx hxV hqΩ
        (Gaps.commutes_symm hqx) hqB.choose_spec.1 hqB.choose_spec.2)
  · exfalso
    push Not at hnbr
    have hVΩ : ∀ B ∈ V, B ∈ Ω := fun B hB => (hB.mem_centralizingMembers hA₀).1
    have hclosed : ∀ A ∈ Ω, (A ∈ V ∨ ∀ B ∈ V, Commutes A B) → ∀ B ∈ Ω, Commutes A B →
        (B ∈ V ∨ ∀ B' ∈ V, Commutes B B') := by
      intro A hA hAS B hB hAB
      by_cases hBV : B ∈ V
      · exact Or.inl hBV
      · right
        by_contra hcon
        push Not at hcon
        obtain ⟨B', hB'V, hBB'⟩ := hcon
        rcases hAS with hAV | hAP
        · exact hnbr B hB hBV ⟨B', hB'V, hBB'⟩ A hAV (Gaps.commutes_symm hAB)
        · exact hBV (mem_ncBlock_of_commutes_of_max hΩ hz hsingle hA₀ hmax hA hAP hB hAB hB'V
            hBB')
    have hall : ∀ Y, Relation.ReflTransGen
        (fun A B : Subgroup G => A ∈ Ω ∧ B ∈ Ω ∧ Commutes A B) K Y →
        Y ∈ Ω ∧ (Y ∈ V ∨ ∀ B ∈ V, Commutes Y B) := by
      intro Y hY
      induction hY with
      | refl => exact ⟨hKΩ, Or.inr hKc⟩
      | tail _ hbc ih => exact ⟨hbc.2.1, hclosed _ ih.1 ih.2 _ hbc.2.1 hbc.2.2⟩
    rcases (hall q₀ (hconn K hKΩ q₀ hq₀Ω)).2 with h | h
    · exact hq₀V h
    · obtain ⟨B, hB, hqB⟩ := hq₀B
      exact hqB (h B hB)

end Closure

section WeakStar

theorem exists_maximal_block [Finite G] {K : Subgroup G} {z : G} (h : RouteDSetup p f K z)
    (D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z))
    (hmulti : ∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j) :
    ∃ (A₀ : Subgroup G) (i₀ i' : Fin D.card) (a₂ : Subgroup G),
      A₀ ∈ centralizingMembers (conjClass K) {z} ∧
      (∀ A ∈ centralizingMembers (conjClass K) {z},
        (ncBlock (conjClass K) z A).ncard ≤ (ncBlock (conjClass K) z A₀).ncard) ∧
      ncBlock (conjClass K) z A₀ = Gaps.compMembers (conjClass K) z D i₀ ∧
      ¬ IsA1Comp D i₀ ∧ ¬ IsA1Comp D i' ∧ i' ≠ i₀ ∧
      a₂ ∈ Gaps.compMembers (conjClass K) z D i' ∧
      K ∉ Gaps.compMembers (conjClass K) z D i₀ ∧
      (∀ B ∈ Gaps.compMembers (conjClass K) z D i₀, Commutes K B ∧ Commutes a₂ B) ∧
      Commutes K a₂ := by
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember h.cls⟩
  obtain ⟨A₀, hA₀, hmax⟩ : ∃ A₀ ∈ centralizingMembers (conjClass K) {z},
      ∀ A ∈ centralizingMembers (conjClass K) {z},
        (ncBlock (conjClass K) z A).ncard ≤ (ncBlock (conjClass K) z A₀).ncard :=
    Set.exists_max_image _ (fun A => (ncBlock (conjClass K) z A).ncard) (Set.toFinite _) ⟨K, hKz⟩
  obtain ⟨i₀, hi₀, -⟩ := Gaps.exists_unique_comp hΩ hex D hA₀
  have hblock : ∀ i : Fin D.card, ∀ N ∈ Gaps.compMembers (conjClass K) z D i,
      ncBlock (conjClass K) z N = Gaps.compMembers (conjClass K) z D i := by
    intro i N hN
    ext B
    exact linked_iff_mem_compMembers hΩ hex hP1 hN
  have hsize : ∀ i : Fin D.card, ¬ IsA1Comp D i →
      1 < (Gaps.compMembers (conjClass K) z D i).ncard := by
    intro i hi
    obtain ⟨N, N', hN, hN', hne⟩ := exists_ne_of_not_isA1Comp hΩ hex hi
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨N, hN, N', hN', hne⟩
  have hle : ∀ i : Fin D.card, ∀ N ∈ Gaps.compMembers (conjClass K) z D i,
      (Gaps.compMembers (conjClass K) z D i).ncard ≤
        (Gaps.compMembers (conjClass K) z D i₀).ncard := by
    intro i N hN
    have := hmax N hN.1
    rwa [hblock i N hN, hblock i₀ A₀ hi₀] at this
  obtain ⟨i, j, hij, hi, hj⟩ := hmulti
  obtain ⟨Ni, hNi⟩ := exists_mem_compMembers (D := D) (x := z) (Ω := conjClass K) i
  have hi₀na : ¬ IsA1Comp D i₀ := by
    intro hA1
    have h1 := hsize i hi
    have h2 := hle i Ni hNi
    have h3 : (Gaps.compMembers (conjClass K) z D i₀).ncard ≤ 1 :=
      (Set.ncard_le_one_iff (Set.toFinite _)).mpr fun {a b} ha hb =>
        eq_of_mem_compMembers_a1 hΩ hex hP1 hA1 ha hb
    omega
  obtain ⟨i', hi'na, hi'ne⟩ : ∃ i' : Fin D.card, ¬ IsA1Comp D i' ∧ i' ≠ i₀ := by
    by_cases hii : i = i₀
    · exact ⟨j, hj, fun e => hij (hii.trans e.symm)⟩
    · exact ⟨i, hi, hii⟩
  obtain ⟨iK, hKt, hKr, hKimg⟩ := Gaps.locImg_eq_range_of_involution (Gaps.fundNoncentral p) D hKz
    h.cls
  have hKmem : K ∈ Gaps.compMembers (conjClass K) z D iK := ⟨hKz, hKimg.le⟩
  have hiKi₀ : iK ≠ i₀ := fun e => hi₀na (e ▸ ⟨hKt, hKr⟩)
  have hiKi' : iK ≠ i' := fun e => hi'na (e ▸ ⟨hKt, hKr⟩)
  obtain ⟨a₂, ha₂⟩ := exists_mem_compMembers (D := D) (x := z) (Ω := conjClass K) i'
  refine ⟨A₀, i₀, i', a₂, hA₀, hmax, hblock i₀ A₀ hi₀, hi₀na, hi'na, hi'ne, ha₂, ?_,
    fun B hB => ⟨Gaps.commutes_of_ne_comp hΩ hP1 D hiKi₀ hKmem hB,
      Gaps.commutes_of_ne_comp hΩ hP1 D hi'ne ha₂ hB⟩,
    Gaps.commutes_of_ne_comp hΩ hP1 D hiKi' hKmem ha₂⟩
  intro hKi₀
  exact hiKi₀ (Gaps.eq_of_locImg_le_range hΩ hex D hKz hKmem.2 hKi₀.2)

theorem exists_weak_star_nbr [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (h : RouteDSetup p f K z)
    (D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z))
    (hmulti : ∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j) :
    ∃ (i₁ i₂ : Fin D.card) (a₁ a₂ c q : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp D i₁ ∧
      ¬ IsA1Comp D i₂ ∧ a₁ ∈ Gaps.compMembers (conjClass K) z D i₁ ∧
      c ∈ Gaps.compMembers (conjClass K) z D i₁ ∧
      a₂ ∈ Gaps.compMembers (conjClass K) z D i₂ ∧ q ∈ conjClass K ∧ Commutes K a₁ ∧
      Commutes K a₂ ∧ Commutes a₁ a₂ ∧ Commutes K c ∧ Commutes c a₂ ∧ Commutes q c ∧
      ¬ Commutes q K ∧ ¬ Commutes q a₁ ∧ ¬ Commutes q a₂ := by
  have hΩ := h.inClass
  have hconn : ∀ X ∈ conjClass K, ∀ Y ∈ conjClass K, Relation.ReflTransGen
      (fun A B : Subgroup G => A ∈ conjClass K ∧ B ∈ conjClass K ∧ Commutes A B) X Y := by
    intro X hX Y hY
    have hreach := h.conn.preconnected ⟨X, hX⟩ ⟨Y, hY⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    have key : ∀ v : conjClass K, Relation.ReflTransGen
        (CFSG.ClassicalInvolution.Models.commGraph (conjClass K)).Adj ⟨X, hX⟩ v →
        Relation.ReflTransGen
          (fun A B : Subgroup G => A ∈ conjClass K ∧ B ∈ conjClass K ∧ Commutes A B) X
          (v : Subgroup G) := by
      intro v hv
      induction hv with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        exact ih.tail ⟨b.2, c.2, (CFSG.ClassicalInvolution.Models.commGraph_adj.mp hbc).2⟩
    exact key ⟨Y, hY⟩ hreach
  obtain ⟨A₀, i₀, i', a₂, hA₀, hmax, hblock, hi₀na, hi'na, hi'ne, ha₂, hKV, hKc, hKa₂⟩ :=
    exists_maximal_block h D hmulti
  have hne : ∀ L ∈ conjClass K, L ≠ ⊥ := by
    intro L hL hbot
    obtain ⟨w, hw⟩ := hΩ.classical L hL
    have := hw.mem
    rw [hbot, Subgroup.mem_bot] at this
    have h2 := hw.orderOf_eq_two
    rw [this, orderOf_one] at h2
    omega
  obtain ⟨q, hqΩ, hqV, ⟨a₁, ha₁V, hqa₁⟩, ⟨c, hcV, hqc⟩, hqK, hqcl⟩ :=
    exists_not_commuting_nbr_of_max hnab hΩ.conjInvariant hΩ.generated hne (mem_conjClass_self K)
      h.cls.mem (single_class K) hconn hA₀ hmax (hblock ▸ hKV)
      (fun B hB => (hKc B (hblock ▸ hB)).1)
  rw [hblock] at ha₁V hcV hqcl
  exact ⟨i₀, i', a₁, a₂, c, q, fun e => hi'ne e.symm, hi₀na, hi'na, ha₁V, hcV, ha₂, hqΩ,
    (hKc a₁ ha₁V).1, hKa₂, Gaps.commutes_symm (hKc a₁ ha₁V).2, (hKc c hcV).1,
    Gaps.commutes_symm (hKc c hcV).2, hqc, hqK, hqa₁, hqcl a₂ ha₂.1.1 fun B hB => (hKc B hB).2⟩

theorem exists_weak_star [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (h : RouteDSetup p f K z)
    (D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z))
    (hmulti : ∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j) :
    ∃ (i₁ i₂ : Fin D.card) (a₁ a₂ q : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp D i₁ ∧
      ¬ IsA1Comp D i₂ ∧ a₁ ∈ Gaps.compMembers (conjClass K) z D i₁ ∧
      a₂ ∈ Gaps.compMembers (conjClass K) z D i₂ ∧ q ∈ conjClass K ∧ Commutes K a₁ ∧
      Commutes K a₂ ∧ Commutes a₁ a₂ ∧ ¬ Commutes q K ∧ ¬ Commutes q a₁ ∧ ¬ Commutes q a₂ := by
  obtain ⟨i₁, i₂, a₁, a₂, c, q, hne, hn₁, hn₂, ha₁, -, ha₂, hq, hKa₁, hKa₂, ha₁a₂, -, -, -, hqK,
    hqa₁, hqa₂⟩ := exists_weak_star_nbr hnab h D hmulti
  exact ⟨i₁, i₂, a₁, a₂, q, hne, hn₁, hn₂, ha₁, ha₂, hq, hKa₁, hKa₂, ha₁a₂, hqK, hqa₁, hqa₂⟩

theorem exists_commuting_pair_of_chain {V : Set (Subgroup G)} {q : Subgroup G}
    (hV : ∀ A ∈ V, ∀ B ∈ V,
      Relation.ReflTransGen (fun X Y : Subgroup G => X ∈ V ∧ Y ∈ V ∧ Commutes X Y) A B)
    {c₀ B₀ : Subgroup G} (hc₀ : c₀ ∈ V) (hqc₀ : Commutes q c₀) (hB₀ : B₀ ∈ V)
    (hqB₀ : ¬ Commutes q B₀) :
    ∃ c ∈ V, ∃ a ∈ V, Commutes c a ∧ Commutes q c ∧ ¬ Commutes q a := by
  have key : ∀ Y, Relation.ReflTransGen (fun X Y : Subgroup G => X ∈ V ∧ Y ∈ V ∧ Commutes X Y)
      c₀ Y → Commutes q Y ∨ ∃ c ∈ V, ∃ a ∈ V, Commutes c a ∧ Commutes q c ∧ ¬ Commutes q a := by
    intro Y hY
    induction hY with
    | refl => exact Or.inl hqc₀
    | @tail b d _ hbd ih =>
      rcases ih with hb | hex
      · by_cases hqd : Commutes q d
        · exact Or.inl hqd
        · exact Or.inr ⟨b, hbd.1, d, hbd.2.1, hbd.2.2, hb, hqd⟩
      · exact Or.inr hex
  rcases key B₀ (hV c₀ hc₀ B₀ hB₀) with h | h
  · exact (hqB₀ h).elim
  · exact h

theorem exists_weak_star_common_nbr [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (h : RouteDSetup p f K z)
    (D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z))
    (hmulti : ∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j)
    (hconnV : ∀ i : Fin D.card, ¬ IsA1Comp D i → ∀ A ∈ Gaps.compMembers (conjClass K) z D i,
      ∀ B ∈ Gaps.compMembers (conjClass K) z D i, Relation.ReflTransGen
        (fun X Y : Subgroup G => X ∈ Gaps.compMembers (conjClass K) z D i ∧
          Y ∈ Gaps.compMembers (conjClass K) z D i ∧ Commutes X Y) A B) :
    ∃ (i₁ i₂ : Fin D.card) (a₁ a₂ c q : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp D i₁ ∧
      ¬ IsA1Comp D i₂ ∧ a₁ ∈ Gaps.compMembers (conjClass K) z D i₁ ∧
      c ∈ Gaps.compMembers (conjClass K) z D i₁ ∧
      a₂ ∈ Gaps.compMembers (conjClass K) z D i₂ ∧ q ∈ conjClass K ∧ Commutes K a₁ ∧
      Commutes K a₂ ∧ Commutes a₁ a₂ ∧ Commutes K c ∧ Commutes c a₂ ∧ Commutes c a₁ ∧
      Commutes q c ∧ ¬ Commutes q K ∧ ¬ Commutes q a₁ ∧ ¬ Commutes q a₂ := by
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  obtain ⟨i₁, i₂, a₁, a₂, c, q, hne, hn₁, hn₂, ha₁, hc, ha₂, hq, hKa₁, hKa₂, ha₁a₂, hKc, hca₂,
    hqc, hqK, hqa₁, hqa₂⟩ := exists_weak_star_nbr hnab h D hmulti
  obtain ⟨c', hc', a', ha', hca', hqc', hqa'⟩ := exists_commuting_pair_of_chain
    (hconnV i₁ hn₁) hc hqc ha₁ hqa₁
  have hcomm : ∀ {B : Subgroup G}, B ∈ Gaps.compMembers (conjClass K) z D i₁ →
      Commutes K B ∧ Commutes B a₂ := by
    intro B hB
    obtain ⟨iK, hKt, hKr, hKimg⟩ := Gaps.locImg_eq_range_of_involution (Gaps.fundNoncentral p) D
      ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember h.cls⟩ h.cls
    have hKmem : K ∈ Gaps.compMembers (conjClass K) z D iK :=
      ⟨⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember h.cls⟩, hKimg.le⟩
    have hiK : iK ≠ i₁ := fun e => hn₁ (e ▸ (show IsA1Comp D iK from ⟨hKt, hKr⟩))
    exact ⟨Gaps.commutes_of_ne_comp hΩ hP1 D hiK hKmem hB,
      Gaps.commutes_of_ne_comp hΩ hP1 D hne hB ha₂⟩
  exact ⟨i₁, i₂, a', a₂, c', q, hne, hn₁, hn₂, ha', hc', ha₂, hq, (hcomm ha').1, hKa₂,
    (hcomm ha').2, (hcomm hc').1, (hcomm hc').2, hca', hqc', hqK, hqa', hqa₂⟩

end WeakStar

end CFSG.ClassicalInvolution.RouteD
