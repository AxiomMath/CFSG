module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.CentralExt.Unipotent

public section

namespace CFSG.AGLEmbedding.P1Lie

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.PreuniquenessRankFour.Helpers

section Abstract

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem weakCore_posUnipotent_eq_top
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {p : ℕ} (hp : p.Prime) (hrank : 2 ≤ D.rank)
    (h2 : ∀ i, 2 ≤ Open.pRank p (posUnipotentExcept D i))
    (h3 : ∀ i, 3 ≤ Open.pRank p (posUnipotentExcept D i ⊔
      (posUnipotent D ⊓ Subgroup.centralizer (posUnipotentExcept D i : Set K)))) :
    GLBWeakCore p (posUnipotent D) = ⊤ := by
  have hU3 : 3 ≤ Open.pRank p (posUnipotent D) := by
    refine (h3 ⟨0, by omega⟩).trans (pRank_mono p hp (sup_le ?_ inf_le_left))
    exact posUnipotentExcept_le_posUnipotent _
  have hB : borel D H ≤ GLBWeakCore p (posUnipotent D) :=
    (borel_le_normalizer_posUnipotent hct).trans (normalizer_le_weakCore_of_rank p hp _ hU3)
  have hn : ∀ i, n i ∈ GLBWeakCore p (posUnipotent D) := by
    intro i
    have hnorm : n i ∈ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
      Subgroup.mem_normalizer_fintype fun u hu => conj_n_mem_posUnipotentExcept hct i hu
    exact normalizer_le_weakCore p (posUnipotentExcept_le_posUnipotent i) (h2 i) (h3 i) hnorm
  rw [eq_top_iff, ← closure_borel_union_range hct]
  exact (Subgroup.closure_le _).2 (Set.union_subset hB (Set.range_subset_iff.2 hn))

end Abstract

section Counting

theorem prod_map_ite_eq {α β : Type*} [Monoid β] (L : List α) (P : α → Prop) [DecidablePred P]
    (f : α → β) :
    (L.map fun a => if P a then f a else 1).prod = ((L.filter P).map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : P a
    · simp [h, ih]
    · simp [h, ih]

variable {K : Type*} [Group K] {ι : Type*}

theorem ProdInjectiveFor.filter {X : (ι → ℤ) → Subgroup K} {L : List (ι → ℤ)}
    (h : ProdInjectiveFor X L) (P : (ι → ℤ) → Prop) [DecidablePred P] :
    ProdInjectiveFor X (L.filter P) := by
  intro f g hf hg hfg γ hγ
  have hγL : γ ∈ L := List.mem_of_mem_filter hγ
  have hP : P γ := by simpa using (List.mem_filter.1 hγ).2
  have key := h (fun a => if P a then f a else 1) (fun a => if P a then g a else 1)
    (fun a ha => by
      by_cases hPa : P a
      · simp only [hPa, ite_true]
        exact hf a (List.mem_filter.2 ⟨ha, by simpa using hPa⟩)
      · simp only [hPa, ite_false]
        exact one_mem _)
    (fun a ha => by
      by_cases hPa : P a
      · simp only [hPa, ite_true]
        exact hg a (List.mem_filter.2 ⟨ha, by simpa using hPa⟩)
      · simp only [hPa, ite_false]
        exact one_mem _)
    (by rw [prod_map_ite_eq, prod_map_ite_eq]; exact hfg) γ hγL
  simpa [hP] using key

theorem prod_card_le_card_closure [Finite K] {X : (ι → ℤ) → Subgroup K} {L : List (ι → ℤ)}
    (hinj : ProdInjectiveFor X L) (S : Finset (ι → ℤ))
    (hSL : ∀ γ ∈ S, γ ∈ L) (E : (ι → ℤ) → Subgroup K) (hEX : ∀ γ ∈ S, E γ ≤ X γ) :
    ∏ γ ∈ S, Nat.card (E γ) ≤ Nat.card (Subgroup.closure (⋃ γ ∈ S, (E γ : Set K))) := by
  classical
  set LS := L.filter (· ∈ S) with hLS
  have hinjS : ProdInjectiveFor X LS := ProdInjectiveFor.filter hinj (· ∈ S)
  have hmemLS : ∀ γ, γ ∈ LS ↔ γ ∈ S := fun γ => by
    constructor
    · intro h
      simpa [LS, List.mem_filter] using (List.mem_filter.1 h).2
    · intro h
      exact List.mem_filter.2 ⟨hSL γ h, by simpa using h⟩
  let f : (∀ γ : S, E γ) → ((ι → ℤ) → K) := fun e γ =>
    if h : γ ∈ S then (e ⟨γ, h⟩ : K) else 1
  let Θ : (∀ γ : S, E γ) → K := fun e => (LS.map (f e)).prod
  have hfX : ∀ (e : ∀ γ : S, E γ) (a : ι → ℤ), a ∈ LS → f e a ∈ X a := by
    intro e a ha
    have haS := (hmemLS a).1 ha
    simp only [f, haS, dite_true]
    exact hEX a haS (e ⟨a, haS⟩).2
  have hΘinj : Function.Injective Θ := by
    intro e e' hee'
    funext γ
    apply Subtype.ext
    have := hinjS (f e) (f e') (hfX e) (hfX e') hee' γ.1 ((hmemLS γ.1).2 γ.2)
    simpa [f, γ.2] using this
  have hΘmem : ∀ e, Θ e ∈ Subgroup.closure (⋃ γ ∈ S, (E γ : Set K)) := by
    intro e
    refine Subgroup.list_prod_mem _ ?_
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    have haS := (hmemLS a).1 ha
    simp only [f, haS, dite_true]
    exact Subgroup.subset_closure (Set.mem_biUnion haS (e ⟨a, haS⟩).2)
  have hcard := Nat.card_le_card_of_injective
    (fun e => (⟨Θ e, hΘmem e⟩ : Subgroup.closure (⋃ γ ∈ S, (E γ : Set K))))
    (fun e e' h => hΘinj (congrArg Subtype.val h))
  rw [Nat.card_pi, Finset.prod_coe_sort S (fun γ => Nat.card (E γ))] at hcard
  exact hcard

end Counting

section ElemAbelian

variable {K : Type*} [Group K] {ι : Type*}

theorem isElemAbelian_closure_iUnion {p : ℕ} (S : Finset (ι → ℤ)) (E : (ι → ℤ) → Subgroup K)
    (hE : ∀ γ ∈ S, ∀ x ∈ E γ, x ^ p = 1)
    (hcomm : ∀ γ ∈ S, ∀ δ ∈ S, ∀ x ∈ E γ, ∀ y ∈ E δ, Commute x y) :
    IsElemAbelian p (Subgroup.closure (⋃ γ ∈ S, (E γ : Set K))) := by
  have hpair : (⋃ γ ∈ S, (E γ : Set K)).Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨γ, hγ, hxγ⟩ : ∃ γ ∈ S, x ∈ E γ := by simpa using hx
    obtain ⟨δ, hδ, hyδ⟩ : ∃ δ ∈ S, y ∈ E δ := by simpa using hy
    exact hcomm γ hγ δ hδ x hxγ y hyδ
  have hcommA : IsMulCommutative (Subgroup.closure (⋃ γ ∈ S, (E γ : Set K))) :=
    Subgroup.isMulCommutative_closure hpair
  refine ⟨hcommA, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, hxγ⟩ : ∃ γ ∈ S, x ∈ E γ := by simpa using hx
    exact hE γ hγ x hxγ
  | one => simp
  | mul x y hx hy hx1 hy1 =>
    have hxy : x * y = y * x :=
      congrArg Subtype.val (hcommA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hc : Commute x y := hxy
    rw [hc.mul_pow, hx1, hy1, mul_one]
  | inv x hx hx1 => rw [inv_pow, hx1, inv_one]

end ElemAbelian

section PRank

variable {K : Type*} [Group K] [Finite K]

theorem le_pRank_of_elemAbelian {p : ℕ} (hp : p.Prime) {H E : Subgroup K} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {m : ℕ} (hm : p ^ m ≤ Nat.card E) : m ≤ Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 g g.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hmk : m ≤ k := by
    rw [hk] at hm
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hm
  exact hmk.trans (le_csSup (pRank_bddAbove p hp H) ⟨E, hEH, hE, hk⟩)

end PRank

section Generic

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

@[expose] def CommRoots (D : UniversalRootDatum K) (γ δ : Fin D.rank → ℤ) : Prop :=
  LinIndepPair γ δ ∧ openCone D.roots γ δ = ∅

omit [Finite K] in
theorem commute_of_commRoots (hext : SteinbergExtras D n H) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (h : CommRoots D γ δ) {x y : K}
    (hx : x ∈ D.rootGroup γ) (hy : y ∈ D.rootGroup δ) : Commute x y := by
  have := hext.commutator_mem γ hγ δ hδ h.1 x hx y hy
  rw [h.2] at this
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem sum_le_pRank_posUnipotentExcept (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    (w : (Fin D.rank → ℤ) → ℕ)
    (hroot : ∀ γ ∈ D.roots, ∃ E ≤ D.rootGroup γ, IsElemAbelian p E ∧ p ^ w γ ≤ Nat.card E)
    {i : Fin D.rank} (S : Finset (Fin D.rank → ℤ))
    (hS : ∀ γ ∈ S, γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i ∧
      ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (hcomm : ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → CommRoots D γ δ) :
    ∑ γ ∈ S, w γ ≤ Open.pRank p (posUnipotentExcept D i) := by
  classical
  obtain ⟨L, hnd, hmem, hs⟩ := exists_sorted_list
    (S := {γ | γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ})
    ((RootSystem.ofCartan D.isFiniteType D.divisible).finite_roots.subset fun _ h => h.1) ht
  have hinj : ProdInjectiveFor D.rootGroup L :=
    hext.prodInjective_pos L hnd (fun γ => hmem γ) hs
  choose! E hEX hEab hEcard using hroot
  have hSL : ∀ γ ∈ S, γ ∈ L := fun γ hγ =>
    (hmem γ).2 ⟨(hS γ hγ).1.1.1, (hS γ hγ).1.1.2, (hS γ hγ).2⟩
  have hroots : ∀ γ ∈ S, γ ∈ D.roots := fun γ hγ => (hS γ hγ).1.1.1
  have hEX' : ∀ γ ∈ S, E γ ≤ D.rootGroup γ := fun γ hγ => hEX γ (hroots γ hγ)
  have hcount := prod_card_le_card_closure hinj S hSL E hEX'
  have hlow : ∏ γ ∈ S, p ^ w γ ≤ ∏ γ ∈ S, Nat.card (E γ) :=
    Finset.prod_le_prod fun γ hγ => hEcard γ (hroots γ hγ)
  rw [Finset.prod_pow_eq_pow_sum] at hlow
  have hab : IsElemAbelian p (Subgroup.closure (⋃ γ ∈ S, (E γ : Set K))) := by
    refine isElemAbelian_closure_iUnion S E (fun γ hγ x hx => (hEab γ (hroots γ hγ)).2 x hx) ?_
    intro γ hγ δ hδ x hx y hy
    by_cases hγδ : γ = δ
    · subst hγδ
      have := (hEab γ (hroots γ hγ)).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact (congrArg Subtype.val this : x * y = y * x)
    · exact commute_of_commRoots hext (hroots γ hγ) (hroots δ hδ) (hcomm γ hγ δ hδ hγδ)
        (hEX' γ hγ hx) (hEX' δ hδ hy)
  have hle : Subgroup.closure (⋃ γ ∈ S, (E γ : Set K)) ≤ posUnipotentExcept D i := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨γ, hγ, hxγ⟩ : ∃ γ ∈ S, x ∈ E γ := by simpa using hx
    exact rootGroup_le_posUnipotentExcept (hS γ hγ).1 (hEX' γ hγ hxγ)
  exact le_pRank_of_elemAbelian hp hle hab (hlow.trans hcount)

end Generic


section Interface

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem weakCore_posUnipotent_eq_top_of_commuting
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime) (hrank : 2 ≤ D.rank)
    (w : (Fin D.rank → ℤ) → ℕ)
    (hroot : ∀ γ ∈ D.roots, ∃ E ≤ D.rootGroup γ, IsElemAbelian p E ∧ p ^ w γ ≤ Nat.card E)
    (hS : ∀ i : Fin D.rank, ∃ S : Finset (Fin D.rank → ℤ),
      (∀ γ ∈ S, γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i ∧
        ∀ δ ∈ D.roots, γ ≠ 2 • δ) ∧
      (∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → CommRoots D γ δ) ∧ 3 ≤ ∑ γ ∈ S, w γ) :
    GLBWeakCore p (posUnipotent D) = ⊤ := by
  have h3' : ∀ i, 3 ≤ Open.pRank p (posUnipotentExcept D i) := by
    intro i
    obtain ⟨S, hS1, hS2, hS3⟩ := hS i
    exact hS3.trans (sum_le_pRank_posUnipotentExcept hext hp w hroot S hS1 hS2)
  exact weakCore_posUnipotent_eq_top hct hp hrank (fun i => (by omega : 2 ≤ 3).trans (h3' i))
    (fun i => (h3' i).trans (pRank_mono p hp le_sup_left))

end Interface

section Param

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {K : Type*} [Group K]
  {X : (ι → ℤ) → Subgroup K} {k : Type*} [Field k] {p : ℕ} [CharP k p] {x : (ι → ℤ) → k → K}

theorem isElemAbelian_card_of_isParametrization (hx : IsParametrization (Φ := Φ) X x)
    {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) :
    IsElemAbelian p (X γ) ∧ Nat.card (X γ) = Nat.card k := by
  obtain ⟨hmem, hadd, hinj⟩ := hx γ hγ
  have hx0 : x γ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := (hmem a).1 a.2
    obtain ⟨d, hd⟩ := (hmem b).1 b.2
    apply Subtype.ext
    change (a : K) * b = b * a
    rw [← hc, ← hd, ← hadd, ← hadd, add_comm]
  · obtain ⟨c, rfl⟩ := (hmem g).1 hg
    have : ∀ n : ℕ, x γ c ^ n = x γ (n • c) := by
      intro n
      induction n with
      | zero => simp [hx0]
      | succ n ih => rw [pow_succ, ih, succ_nsmul, hadd]
    rw [this p, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, hx0]
  · refine (Nat.card_congr (Equiv.ofBijective (fun c : k => (⟨x γ c, (hmem _).2 ⟨c, rfl⟩⟩ : X γ))
      ⟨fun c d h => hinj (congrArg Subtype.val h), fun g => ?_⟩)).symm
    obtain ⟨c, hc⟩ := (hmem g).1 g.2
    exact ⟨c, Subtype.ext hc⟩

end Param

section Transfer

variable {G L : Type*} [Group G] [Finite G] [Group L] [Finite L]

theorem pRank_le_pRank_map {p : ℕ} (hp : p.Prime) (f : G →* L) {P : Subgroup G}
    (hinj : ∀ x ∈ P, f x = 1 → x = 1) {R : Subgroup G} (hRP : R ≤ P) :
    Open.pRank p R ≤ Open.pRank p (R.map f) := by
  obtain ⟨E, hER, hE, hcard⟩ := pRank_attained p hp R
  have hEP : E ≤ P := hER.trans hRP
  have hinjE : Function.Injective (f.comp E.subtype) := by
    intro x y hxy
    have h1 : f ((x : G) * (y : G)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.2 hxy
    have h2 := hinj _ (hEP (E.mul_mem x.2 (E.inv_mem y.2))) h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  have hmap : E.map f = (f.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardmap : Nat.card (E.map f) = Nat.card E := by
    rw [hmap]
    exact Nat.card_range_of_injective hinjE
  have hE' : IsElemAbelian p (E.map f) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      have hxy : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      apply Subtype.ext
      change (a : L) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  exact le_pRank_of_elemAbelian hp (Subgroup.map_mono hER) hE'
    (by rw [hcardmap, hcard])

theorem weakCore_le_comap_map {p : ℕ} (hp : p.Prime) (f : G →* L) {P : Subgroup G}
    (hinj : ∀ x ∈ P, f x = 1 → x = 1) :
    GLBWeakCore p P ≤ (GLBWeakCore p (P.map f)).comap f := by
  rw [weakCore_le_iff]
  intro Q hQP hQ2 hQ3 g hg
  have hQ2' : 2 ≤ Open.pRank p (Q.map f) := hQ2.trans (pRank_le_pRank_map hp f hinj hQP)
  have hQ3' : 3 ≤ Open.pRank p (Q.map f ⊔ (P.map f ⊓ Subgroup.centralizer (Q.map f : Set L))) := by
    refine hQ3.trans ((pRank_le_pRank_map hp f hinj
      (R := Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) (sup_le hQP inf_le_left)).trans
      (pRank_mono p hp ?_))
    rw [Subgroup.map_sup]
    refine sup_le_sup_left ?_ _
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    show f x ∈ Subgroup.centralizer ((Q.map f : Subgroup L) : Set L)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx.2 q hq
    rw [← map_mul, ← map_mul, this]
  exact normalizer_le_weakCore p (Subgroup.map_mono hQP) hQ2' hQ3'
    (Subgroup.le_normalizer_map f ⟨g, hg, rfl⟩)

theorem weakCore_map_eq_top {p : ℕ} (hp : p.Prime) (f : G →* L) (hf : Function.Surjective f)
    {P : Subgroup G} (hinj : ∀ x ∈ P, f x = 1 → x = 1) (hcore : GLBWeakCore p P = ⊤) :
    GLBWeakCore p (P.map f) = ⊤ := by
  have hle := weakCore_le_comap_map hp f hinj
  rw [eq_top_iff]
  intro l _
  obtain ⟨g, rfl⟩ := hf l
  exact hle (hcore ▸ Subgroup.mem_top g)

theorem weakCore_eq_top_of_pGroup {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P)
    (hcore : GLBWeakCore p P = ⊤) (T : Sylow p G) : GLBWeakCore p (T : Subgroup G) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S T
  have hS : GLBWeakCore p (S : Subgroup G) = ⊤ :=
    top_le_iff.mp (hcore ▸ weakCore_mono p hp hPS)
  have h := weakCore_map_eq_top hp (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective
    (P := (S : Subgroup G)) (fun x _ hx => (MulAut.conj g).injective (by simpa using hx)) hS
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact h

end Transfer

section Cover

variable {K X : Type*} [Group K] [Finite K] [Group X] [Finite X] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

omit [Finite K] in
theorem eq_one_of_mem_center_of_pow_prime_pow {p : ℕ}
    (hcen : ∀ z ∈ Subgroup.center K, z ^ p = 1 → z = 1) {x : K} {k : ℕ} :
    x ∈ Subgroup.center K → x ^ p ^ k = 1 → x = 1 := by
  induction k generalizing x with
  | zero => intro _ h; simpa using h
  | succ k ih =>
    intro hx hk
    refine hcen x hx (ih (pow_mem hx p) ?_)
    rw [← pow_mul, ← pow_succ']
    exact hk

theorem exists_pGroup_weakCore_of_central_cover {p : ℕ} (hp : p.Prime)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hcen : ∀ z ∈ Subgroup.center K, z ^ p = 1 → z = 1) (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K)
    (h3 : ∀ i, 3 ≤ Open.pRank p (posUnipotentExcept D i)) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  have hU : IsPGroup p (posUnipotent D) := isPGroup_iSup_pos hext hX
  have hinj : ∀ x ∈ posUnipotent D, ψ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_center_of_pow_prime_pow hcen (hker (MonoidHom.mem_ker.2 hx1))
      (congrArg Subtype.val hk)
  exact ⟨(posUnipotent D).map ψ, hU.map ψ,
    weakCore_map_eq_top hp ψ hψ hinj
      (weakCore_posUnipotent_eq_top hct hp hrank (fun i => (by omega : 2 ≤ 3).trans (h3 i))
        (fun i => (h3 i).trans (pRank_mono p hp le_sup_left)))⟩

end Cover

section Gen2

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

omit [Finite K] in
theorem CommRoots.symm {γ δ : Fin D.rank → ℤ} (h : CommRoots D γ δ) : CommRoots D δ γ := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · have := h.1 b a (by rwa [add_comm])
    exact ⟨this.2, this.1⟩
  · ext ε
    have h2 := Set.ext_iff.1 h.2 ε
    simp only [openCone, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false] at h2 ⊢
    rintro ⟨hε, a, b, ha, hb, rfl⟩
    exact h2 ⟨hε, b, a, hb, ha, add_comm _ _⟩

omit [Finite K] in
theorem openCone_eq_empty_of_support {ι : Type*} (T : (Fin D.rank → ℤ) →+ (ι → ℤ))
    (hsupp : ∀ ε ∈ D.roots, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      ¬ (T ε i ≠ 0 ∧ T ε j ≠ 0 ∧ T ε k ≠ 0))
    {γ δ : Fin D.rank → ℤ} {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h3 : ∀ a b : ℕ, 0 < a → 0 < b →
      (a : ℤ) * T γ i + b * T δ i ≠ 0 ∧ (a : ℤ) * T γ j + b * T δ j ≠ 0 ∧
        (a : ℤ) * T γ k + b * T δ k ≠ 0) :
    openCone D.roots γ δ = ∅ := by
  ext ε
  simp only [openCone, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hε, a, b, ha, hb, rfl⟩
  have hT : T (a • γ + b • δ) = a • T γ + b • T δ := by rw [map_add, map_nsmul, map_nsmul]
  refine hsupp _ hε i j k hij hik hjk ?_
  obtain ⟨h1, h2, h3'⟩ := h3 a b ha hb
  rw [hT]
  simp only [Pi.add_apply, nsmul_eq_mul]
  exact ⟨h1, h2, h3'⟩

theorem exists_elemAbelian_of_pGroup_ne_bot {p : ℕ} (hp : p.Prime) {X : Subgroup K}
    (hX : IsPGroup p X) (hne : X ≠ ⊥) : ∃ E ≤ X, IsElemAbelian p E ∧ p ^ 1 ≤ Nat.card E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hne)
  have hxp : IsPGroup p X := hX
  have hdvd : p ∣ Nat.card X := by
    rcases hxp.card_eq_or_dvd with h | h
    · exfalso
      have : Subsingleton X := Finite.card_le_one_iff_subsingleton.1 (by omega)
      exact hx1 (Subsingleton.elim _ _)
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) p hdvd
  refine ⟨Subgroup.map X.subtype (Subgroup.zpowers y), Subgroup.map_subtype_le _, ?_, ?_⟩
  · refine ⟨inferInstance, ?_⟩
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    change ((y ^ k : X) : K) ^ p = 1
    rw [← Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : y ^ p = 1 := hy ▸ pow_orderOf_eq_one y
    rw [this, one_zpow, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hy, pow_one]

theorem three_le_pRank_of_triple (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    {γ₁ γ₂ γ₃ : Fin D.rank → ℤ}
    (hr : ∀ γ ∈ ({γ₁, γ₂, γ₃} : Finset (Fin D.rank → ℤ)), γ ∈ D.roots ∧
      (∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃) (h23 : γ₂ ≠ γ₃)
    (c12 : CommRoots D γ₁ γ₂) (c13 : CommRoots D γ₁ γ₃) (c23 : CommRoots D γ₂ γ₃) (i : Fin D.rank) :
    3 ≤ Open.pRank p (posUnipotentExcept D i) := by
  classical
  have hroot : ∀ γ ∈ D.roots, ∃ E ≤ D.rootGroup γ, IsElemAbelian p E ∧
      p ^ (fun _ => 1) γ ≤ Nat.card E :=
    fun γ hγ => exists_elemAbelian_of_pGroup_ne_bot hp (hX γ hγ) (hext.ne_bot γ hγ)
  have key := sum_le_pRank_posUnipotentExcept hext hp (fun _ => 1) hroot (i := i)
    ({γ₁, γ₂, γ₃} : Finset (Fin D.rank → ℤ))
    (fun γ hγ => by
      obtain ⟨hγR, ⟨j₁, j₂, hj, h1, h2⟩, hnd⟩ := hr γ hγ
      refine ⟨?_, hnd⟩
      by_cases h : j₁ = i
      · exact (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos hγR
          (fun e => hj (h.trans e.symm)) h2
      · exact (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos hγR h h1)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro γ (rfl | rfl | rfl) δ (rfl | rfl | rfl) hne
      · exact absurd rfl hne
      · exact c12
      · exact c13
      · exact c12.symm
      · exact absurd rfl hne
      · exact c23
      · exact c13.symm
      · exact c23.symm
      · exact absurd rfl hne)
  have hcard : ({γ₁, γ₂, γ₃} : Finset (Fin D.rank → ℤ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_insert_of_notMem
      (by simp [h23]), Finset.card_singleton]
  simpa [hcard] using key


omit [Finite K] in
theorem mem_posExcept_of_two_pos {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {j₁ j₂ : Fin D.rank}
    (hj : j₁ ≠ j₂) (h1 : 0 < γ j₁) (h2 : 0 < γ j₂) (i : Fin D.rank) :
    γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i := by
  by_cases h : j₁ = i
  · exact (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos hγ
      (fun e => hj (h.trans e.symm)) h2
  · exact (RootSystem.ofCartan D.isFiniteType D.divisible).mem_posExcept_of_pos hγ h h1

omit [Finite K] in
theorem ne_two_smul_of_divisible_eq_empty (hD : D.divisible = ∅) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : ∀ δ ∈ D.roots, γ ≠ 2 • δ := fun _ hδ e =>
  two_smul_notMem_roots D.isFiniteType hD hδ (e ▸ hγ)

omit [Finite K] in
theorem linIndepPair_of_nonneg_image {ι : Type*} (T : (Fin D.rank → ℤ) →+ (ι → ℤ))
    (hD : D.divisible = ∅) {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (hne : γ ≠ δ) (hγ0 : ∀ i, 0 ≤ T γ i) (hδ0 : ∀ i, 0 ≤ T δ i) (hnz : ∃ i, T γ i ≠ 0) :
    LinIndepPair γ δ := by
  by_contra h
  rcases eq_or_eq_neg_of_not_linIndepPair D.isFiniteType hD hγ hδ h with h1 | h1
  · exact hne h1.symm
  · obtain ⟨i, hi⟩ := hnz
    have h2 : T δ i = -T γ i := by rw [h1, map_neg]; rfl
    have := hγ0 i
    have := hδ0 i
    omega

omit [Finite K] in
theorem commRoots_of_images {ι : Type*} (T : (Fin D.rank → ℤ) →+ (ι → ℤ)) (hD : D.divisible = ∅)
    (hsupp : ∀ ε ∈ D.roots, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      ¬ (T ε i ≠ 0 ∧ T ε j ≠ 0 ∧ T ε k ≠ 0))
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hne : γ ≠ δ)
    (hγ0 : ∀ i, 0 ≤ T γ i) (hδ0 : ∀ i, 0 ≤ T δ i) (hnz : ∃ i, T γ i ≠ 0)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h3 : ∀ a b : ℕ, 0 < a → 0 < b →
      (a : ℤ) * T γ i + b * T δ i ≠ 0 ∧ (a : ℤ) * T γ j + b * T δ j ≠ 0 ∧
        (a : ℤ) * T γ k + b * T δ k ≠ 0) :
    CommRoots D γ δ :=
  ⟨linIndepPair_of_nonneg_image T hD hγ hδ hne hγ0 hδ0 hnz,
    openCone_eq_empty_of_support T hsupp hij hik hjk h3⟩

theorem weakCore_posUnipotent_eq_top_of_triple
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    {γ₁ γ₂ γ₃ : Fin D.rank → ℤ}
    (hr : ∀ γ ∈ ({γ₁, γ₂, γ₃} : Finset (Fin D.rank → ℤ)), γ ∈ D.roots ∧
      (∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃) (h23 : γ₂ ≠ γ₃)
    (c12 : CommRoots D γ₁ γ₂) (c13 : CommRoots D γ₁ γ₃) (c23 : CommRoots D γ₂ γ₃) :
    GLBWeakCore p (posUnipotent D) = ⊤ := by
  have h3 := three_le_pRank_of_triple hext hp hX hr h12 h13 h23 c12 c13 c23
  exact weakCore_posUnipotent_eq_top hct hp hrank (fun i => (by omega : 2 ≤ 3).trans (h3 i))
    (fun i => (h3 i).trans (pRank_mono p hp le_sup_left))

theorem weakCore_posUnipotent_eq_top_of_pair {F : Type} [Field F] {x : (Fin D.rank → ℤ) → F → K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p f : ℕ} [CharP F p] (hp : p.Prime) (hrank : 2 ≤ D.rank)
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    (hF : Nat.card F = p ^ f) (hf : 2 ≤ f)
    {γ₁ γ₂ : Fin D.rank → ℤ}
    (hr : ∀ γ ∈ ({γ₁, γ₂} : Finset (Fin D.rank → ℤ)), γ ∈ D.roots ∧
      (∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (h12 : γ₁ ≠ γ₂) (c12 : CommRoots D γ₁ γ₂) :
    GLBWeakCore p (posUnipotent D) = ⊤ := by
  classical
  refine weakCore_posUnipotent_eq_top_of_commuting hct hext hp hrank (fun _ => f) ?_ ?_
  · intro γ hγ
    obtain ⟨hE, hcard⟩ := isElemAbelian_card_of_isParametrization (p := p) hx hγ
    exact ⟨_, le_rfl, hE, by rw [hcard, hF]⟩
  · intro i
    refine ⟨({γ₁, γ₂} : Finset (Fin D.rank → ℤ)), ?_, ?_, ?_⟩
    · intro γ hγ
      obtain ⟨hγR, ⟨j₁, j₂, hj, h1, h2⟩, hnd⟩ := hr γ hγ
      exact ⟨mem_posExcept_of_two_pos hγR hj h1 h2 i, hnd⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro γ (rfl | rfl) δ (rfl | rfl) hne
      · exact absurd rfl hne
      · exact c12
      · exact c12.symm
      · exact absurd rfl hne
    · rw [Finset.sum_const, Finset.card_pair h12, smul_eq_mul]
      omega

theorem weakCore_posUnipotent_eq_top_of_weighted_pair
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime) (hrank : 2 ≤ D.rank)
    {γ₁ γ₂ : Fin D.rank → ℤ} (w₁ w₂ : ℕ)
    (h₁ : ∃ E ≤ D.rootGroup γ₁, IsElemAbelian p E ∧ p ^ w₁ ≤ Nat.card E)
    (h₂ : ∃ E ≤ D.rootGroup γ₂, IsElemAbelian p E ∧ p ^ w₂ ≤ Nat.card E)
    (hr : ∀ γ ∈ ({γ₁, γ₂} : Finset (Fin D.rank → ℤ)), γ ∈ D.roots ∧
      (∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (h12 : γ₁ ≠ γ₂) (c12 : CommRoots D γ₁ γ₂) (hw : 3 ≤ w₁ + w₂) :
    GLBWeakCore p (posUnipotent D) = ⊤ := by
  classical
  refine weakCore_posUnipotent_eq_top_of_commuting hct hext hp hrank
    (fun γ => if γ = γ₁ then w₁ else if γ = γ₂ then w₂ else 0) ?_ ?_
  · intro γ hγ
    by_cases e1 : γ = γ₁
    · subst e1
      simpa using h₁
    · by_cases e2 : γ = γ₂
      · subst e2
        simpa [e1] using h₂
      · refine ⟨⊥, bot_le, ⟨inferInstance, fun g hg => ?_⟩, ?_⟩
        · rw [Subgroup.mem_bot] at hg
          rw [hg, one_pow]
        · simp [e1, e2]
  · intro i
    refine ⟨({γ₁, γ₂} : Finset (Fin D.rank → ℤ)), ?_, ?_, ?_⟩
    · intro γ hγ
      obtain ⟨hγR, ⟨j₁, j₂, hj, h1, h2⟩, hnd⟩ := hr γ hγ
      exact ⟨mem_posExcept_of_two_pos hγR hj h1 h2 i, hnd⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro γ (rfl | rfl) δ (rfl | rfl) hne
      · exact absurd rfl hne
      · exact c12
      · exact c12.symm
      · exact absurd rfl hne
    · rw [Finset.sum_pair h12]
      simp [h12.symm]
      omega

omit [Finite K] in
theorem openCone_eq_empty_of_bound {ι : Type*} (T : (Fin D.rank → ℤ) →+ (ι → ℤ)) {i : ι} {M : ℤ}
    (hbd : ∀ ε ∈ D.roots, T ε i ≤ M) {γ δ : Fin D.rank → ℤ}
    (h : ∀ a b : ℕ, 0 < a → 0 < b → M < (a : ℤ) * T γ i + b * T δ i) :
    openCone D.roots γ δ = ∅ := by
  ext ε
  simp only [openCone, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hε, a, b, ha, hb, rfl⟩
  have hT : T (a • γ + b • δ) = a • T γ + b • T δ := by rw [map_add, map_nsmul, map_nsmul]
  have h1 := hbd _ hε
  have h2 := h a b ha hb
  have h3 : (a • T γ + b • T δ) i = (a : ℤ) * T γ i + b * T δ i := by simp
  rw [hT, h3] at h1
  omega

omit [Finite K] in
theorem commRoots_of_bound {ι : Type*} (T : (Fin D.rank → ℤ) →+ (ι → ℤ)) (hD : D.divisible = ∅)
    {i : ι} {M : ℤ} (hbd : ∀ ε ∈ D.roots, T ε i ≤ M)
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hne : γ ≠ δ)
    (hγ0 : ∀ i, 0 ≤ T γ i) (hδ0 : ∀ i, 0 ≤ T δ i) (hnz : ∃ i, T γ i ≠ 0)
    (h : ∀ a b : ℕ, 0 < a → 0 < b → M < (a : ℤ) * T γ i + b * T δ i) :
    CommRoots D γ δ :=
  ⟨linIndepPair_of_nonneg_image T hD hγ hδ hne hγ0 hδ0 hnz,
    openCone_eq_empty_of_bound T hbd h⟩

omit [Finite K] in
theorem exists_two_pos_of_two_le_ht (hD : D.divisible = ∅) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (h2 : 2 ≤ ht γ) :
    ∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂ := by
  have h0 : 0 ≤ γ := by
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ with h | h
    · exact h
    · exfalso
      have : ht γ ≤ 0 := Finset.sum_nonpos fun i _ => h i
      omega
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ : ∃ j, 0 < γ j := by
    by_contra h
    push Not at h
    have : ht γ ≤ 0 := Finset.sum_nonpos fun i _ => h i
    omega
  have hγj : γ = γ j • Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · have h1 := hcon j i (Ne.symm hi) hj
      have h2 : 0 ≤ γ i := h0 i
      simp only [Pi.smul_apply, Pi.single_apply, hi, ite_false, smul_zero]
      omega
  have hsingle : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hdep : ¬ LinIndepPair γ (Pi.single j 1 : Fin D.rank → ℤ) := by
    intro h
    have := (h 1 (-γ j) (by
      funext i
      have := congrFun hγj i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      rw [this]; ring)).2
    omega
  rcases eq_or_eq_neg_of_not_linIndepPair D.isFiniteType hD hγ hsingle hdep with e | e
  · have : ht γ = 1 := by rw [← e]; simp [ht]
    omega
  · have := congrFun e j
    simp only [Pi.single_eq_same, Pi.neg_apply] at this
    omega

omit [Finite K] in
theorem posData_of_two_le_ht (hD : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (h2 : 2 ≤ ht γ) :
    γ ∈ D.roots ∧ (∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧
      ∀ δ ∈ D.roots, γ ≠ 2 • δ :=
  ⟨hγ, exists_two_pos_of_two_le_ht hD hγ h2, ne_two_smul_of_divisible_eq_empty hD hγ⟩

theorem weakCore_posUnipotent_eq_top_of_image_triple
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) (hD : D.divisible = ∅)
    {ι : Type*} [DecidableEq ι] (T : (Fin D.rank → ℤ) →+ (ι → ℤ))
    (hsupp : ∀ ε ∈ D.roots, ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      ¬ (T ε i ≠ 0 ∧ T ε j ≠ 0 ∧ T ε k ≠ 0))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {γ₁ γ₂ γ₃ : Fin D.rank → ℤ} (h₁ : γ₁ ∈ D.roots) (h₂ : γ₂ ∈ D.roots) (h₃ : γ₃ ∈ D.roots)
    (e₁ : T γ₁ = Pi.single i 1 + Pi.single j 1) (e₂ : T γ₂ = Pi.single i 1 + Pi.single k 1)
    (e₃ : T γ₃ = Pi.single j 1 + Pi.single k 1)
    (ht₁ : 2 ≤ ht γ₁) (ht₂ : 2 ≤ ht γ₂) (ht₃ : 2 ≤ ht γ₃) :
    GLBWeakCore p (posUnipotent D) = ⊤ := by
  have nn : ∀ (u v l : ι), 0 ≤ (Pi.single u 1 + Pi.single v 1 : ι → ℤ) l := by
    intro u v l
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  have v1 : T γ₁ i = 1 ∧ T γ₁ j = 1 ∧ T γ₁ k = 0 := by
    rw [e₁]; simp [hij, hij.symm, hik.symm, hjk.symm]
  have v2 : T γ₂ i = 1 ∧ T γ₂ j = 0 ∧ T γ₂ k = 1 := by
    rw [e₂]; simp [hij.symm, hik, hik.symm, hjk]
  have v3 : T γ₃ i = 0 ∧ T γ₃ j = 1 ∧ T γ₃ k = 1 := by
    rw [e₃]; simp [hij, hik, hjk, hjk.symm]
  have h12 : γ₁ ≠ γ₂ := fun h => by
    have := congrArg (fun v => T v j) h
    simp only [v1.2.1, v2.2.1] at this
    omega
  have h13 : γ₁ ≠ γ₃ := fun h => by
    have := congrArg (fun v => T v i) h
    simp only [v1.1, v3.1] at this
    omega
  have h23 : γ₂ ≠ γ₃ := fun h => by
    have := congrArg (fun v => T v i) h
    simp only [v2.1, v3.1] at this
    omega
  have n1 : ∀ l, 0 ≤ T γ₁ l := fun l => by rw [e₁]; exact nn i j l
  have n2 : ∀ l, 0 ≤ T γ₂ l := fun l => by rw [e₂]; exact nn i k l
  have n3 : ∀ l, 0 ≤ T γ₃ l := fun l => by rw [e₃]; exact nn j k l
  have c12 : CommRoots D γ₁ γ₂ :=
    commRoots_of_images T hD hsupp h₁ h₂ h12 n1 n2 ⟨i, by rw [v1.1]; exact one_ne_zero⟩ hij hik hjk
      fun a b ha hb => by
        simp only [v1.1, v1.2.1, v1.2.2, v2.1, v2.2.1, v2.2.2]
        refine ⟨?_, ?_, ?_⟩ <;> omega
  have c13 : CommRoots D γ₁ γ₃ :=
    commRoots_of_images T hD hsupp h₁ h₃ h13 n1 n3 ⟨i, by rw [v1.1]; exact one_ne_zero⟩ hij hik hjk
      fun a b ha hb => by
        simp only [v1.1, v1.2.1, v1.2.2, v3.1, v3.2.1, v3.2.2]
        refine ⟨?_, ?_, ?_⟩ <;> omega
  have c23 : CommRoots D γ₂ γ₃ :=
    commRoots_of_images T hD hsupp h₂ h₃ h23 n2 n3 ⟨i, by rw [v2.1]; exact one_ne_zero⟩ hij hik hjk
      fun a b ha hb => by
        simp only [v2.1, v2.2.1, v2.2.2, v3.1, v3.2.1, v3.2.2]
        refine ⟨?_, ?_, ?_⟩ <;> omega
  refine weakCore_posUnipotent_eq_top_of_triple hct hext hp hrank hX (fun γ hγ => ?_) h12 h13 h23
    c12 c13 c23
  simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl
  · exact posData_of_two_le_ht hD h₁ ht₁
  · exact posData_of_two_le_ht hD h₂ ht₂
  · exact posData_of_two_le_ht hD h₃ ht₃

@[expose] def htHom (m : ℕ) : (Fin m → ℤ) →+ (Unit → ℤ) :=
  AddMonoidHom.mk' (fun v _ => ht v) fun v w => by
    funext _
    simp [ht, Finset.sum_add_distrib]

omit [Finite K] in
theorem commRoots_of_ht (hD : D.divisible = ∅) {M : ℤ} (hM : ∀ ε ∈ D.roots, ht ε ≤ M)
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hne : γ ≠ δ)
    (hγ1 : 1 ≤ ht γ) (hδ1 : 1 ≤ ht δ) (hMs : M < ht γ + ht δ) : CommRoots D γ δ := by
  have hnn : ∀ ε ∈ D.roots, 1 ≤ ht ε → ∀ l, 0 ≤ ε l := by
    intro ε hε hpos l
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hε with h | h
    · exact h l
    · exfalso
      have : ht ε ≤ 0 := Finset.sum_nonpos fun i _ => h i
      omega
  refine commRoots_of_bound (D := D) (htHom D.rank) hD (i := ()) (M := M) hM hγ hδ hne
    (fun _ => ?_) (fun _ => ?_) ⟨(), ?_⟩ fun a b ha hb => ?_
  · change 0 ≤ ht γ; omega
  · change 0 ≤ ht δ; omega
  · change ht γ ≠ 0; omega
  · change M < (a : ℤ) * ht γ + b * ht δ
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith

theorem weakCore_posUnipotent_eq_top_of_heights
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) (hD : D.divisible = ∅)
    {M k : ℤ} (hk : 2 ≤ k) (hMk : M < 2 * k) (hM : ∀ ε ∈ D.roots, ht ε ≤ M)
    (h3 : ∃ γ₁ ∈ D.roots, ∃ γ₂ ∈ D.roots, ∃ γ₃ ∈ D.roots, γ₁ ≠ γ₂ ∧ γ₁ ≠ γ₃ ∧ γ₂ ≠ γ₃ ∧
      k ≤ ht γ₁ ∧ k ≤ ht γ₂ ∧ k ≤ ht γ₃) :
    GLBWeakCore p (posUnipotent D) = ⊤ := by
  obtain ⟨γ₁, h₁, γ₂, h₂, γ₃, h₃, h12, h13, h23, k1, k2, k3⟩ := h3
  refine weakCore_posUnipotent_eq_top_of_triple hct hext hp hrank hX (fun γ hγ => ?_) h12 h13 h23
    (commRoots_of_ht hD hM h₁ h₂ h12 (by omega) (by omega) (by omega))
    (commRoots_of_ht hD hM h₁ h₃ h13 (by omega) (by omega) (by omega))
    (commRoots_of_ht hD hM h₂ h₃ h23 (by omega) (by omega) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl
  · exact posData_of_two_le_ht hD h₁ (by omega)
  · exact posData_of_two_le_ht hD h₂ (by omega)
  · exact posData_of_two_le_ht hD h₃ (by omega)

omit [Finite K] in
theorem two_le_ht_of_two_pos {m : ℕ} {v : Fin m → ℤ} (h0 : ∀ k, 0 ≤ v k) {i j : Fin m}
    (hij : i ≠ j) (hi : 0 < v i) (hj : 0 < v j) : 2 ≤ ht v := by
  calc (2 : ℤ) ≤ v i + v j := by omega
    _ = ∑ k ∈ ({i, j} : Finset (Fin m)), v k := (Finset.sum_pair hij).symm
    _ ≤ ∑ k, v k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => h0 k

end Gen2

end CFSG.AGLEmbedding.P1Lie
