module

public import CFSG.LieType.TitsSimplicity.LeviDatum

public section

namespace CFSG.LieType.TitsSimplicity.Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem.Restrict
open scoped commutatorElement

variable {G : Type*} [Group G] {D : UniversalRootDatum G} {m : ℕ} {e : Fin m → Fin D.rank}
  (he : Function.Injective e) {n : Fin D.rank → G} {H : Fin D.rank → Subgroup G}
  (hdiv : D.divisible = ∅)

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

namespace SE

section Lists

variable {α : Type*}

theorem list_exists_sorted_extension [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (htrans : ∀ a b c, r a b → r b c → r a c) (htotal : ∀ a b, r a b ∨ r b a) {c : List α}
    (hc : c.Nodup) (hcr : c.Pairwise r) (S : Finset α) (hcS : ∀ x ∈ c, x ∈ S) :
    ∃ L : List α, L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ S) ∧ L.Pairwise r ∧ List.Sublist c L := by
  haveI : Std.Total r := ⟨htotal⟩
  haveI : IsTrans α r := ⟨htrans⟩
  refine ⟨(c ++ (S.filter (· ∉ c)).toList).insertionSort r, ?_, ?_,
    List.pairwise_insertionSort r _,
    List.sublist_insertionSort hcr (List.sublist_append_left _ _)⟩
  · refine ((List.perm_insertionSort r _).nodup_iff).mpr ?_
    refine List.nodup_append.mpr ⟨hc, (S.filter (· ∉ c)).nodup_toList, ?_⟩
    intro a ha b hb hab
    subst hab
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hb)).2 ha
  · intro x
    rw [List.mem_insertionSort, List.mem_append, Finset.mem_toList, Finset.mem_filter]
    by_cases hxc : x ∈ c
    · exact ⟨fun _ => hcS x hxc, fun _ => Or.inl hxc⟩
    · exact ⟨fun h => (h.resolve_left hxc).1, fun h => Or.inr ⟨h, hxc⟩⟩

theorem list_prod_map_eq_of_sublist {M : Type*} [Monoid M] {c l : List α}
    (h : List.Sublist c l) (F : α → M) :
    l.Nodup → (∀ x ∈ l, x ∉ c → F x = 1) → (l.map F).prod = (c.map F).prod := by
  induction h with
  | slnil => intro _ _; rfl
  | cons a h ih =>
    rename_i l₁ l₂
    intro hl hF
    have ha : a ∉ l₁ := fun hmem => (List.nodup_cons.mp hl).1 (h.subset hmem)
    rw [List.map_cons, List.prod_cons, hF a List.mem_cons_self ha, one_mul]
    exact ih (List.nodup_cons.mp hl).2 fun x hx hxc => hF x (List.mem_cons_of_mem a hx) hxc
  | cons_cons a h ih =>
    rename_i l₁ l₂
    intro hl hF
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    congr 1
    refine ih (List.nodup_cons.mp hl).2 fun x hx hxc => hF x (List.mem_cons_of_mem a hx) ?_
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact (List.nodup_cons.mp hl).1 hx
    · exact hxc hmem

end Lists

section Products

variable {ι : Type*} {K : Type*} [Group K]

theorem prodInjectiveFor_of_sublist {X : (ι → ℤ) → Subgroup K} {c l : List (ι → ℤ)}
    (h : List.Sublist c l) (hl : l.Nodup) (hinj : ProdInjectiveFor X l) :
    ProdInjectiveFor X c := by
  classical
  intro f g hf hg hfg γ hγ
  have hext : ∀ f : (ι → ℤ) → K, (∀ γ ∈ c, f γ ∈ X γ) →
      (∀ γ ∈ l, (if γ ∈ c then f γ else 1) ∈ X γ) ∧
        (l.map fun γ => if γ ∈ c then f γ else 1).prod = (c.map f).prod := by
    intro f hf
    refine ⟨fun γ _ => ?_, ?_⟩
    · by_cases hγ : γ ∈ c
      · rw [if_pos hγ]
        exact hf γ hγ
      · rw [if_neg hγ]
        exact one_mem _
    · rw [list_prod_map_eq_of_sublist h _ hl fun x _ hx => if_neg hx]
      exact congrArg List.prod (List.map_congr_left fun x hx => if_pos hx)
  obtain ⟨hf1, hf2⟩ := hext f hf
  obtain ⟨hg1, hg2⟩ := hext g hg
  have key := hinj _ _ hf1 hg1 (hf2.trans (hfg.trans hg2.symm)) γ (h.subset hγ)
  simpa [hγ] using key

end Products

include hdiv in
theorem ne_two_smul_of_mem_roots {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) :
    γ ≠ 2 • δ := by
  have hD : D.roots = roots D.isFiniteType ∅ := by rw [UniversalRootDatum.roots, hdiv]
  rw [hD] at hγ hδ
  have hroot : ∀ {v : Fin D.rank → ℤ}, v ∈ roots D.isFiniteType ∅ →
      ∃ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
        v = weylAction D.isFiniteType w (Pi.single i 1) := by
    rintro v (h | ⟨w, i, hi, -⟩)
    · exact h
    · exact (Set.notMem_empty i hi).elim
  obtain ⟨w, i, rfl⟩ := hroot hγ
  obtain ⟨w', j, rfl⟩ := hroot hδ
  intro h
  have h1 := congrArg (weylAction D.isFiniteType w⁻¹) h
  rw [weylAction_inv_apply_apply, map_nsmul] at h1
  have h2 := congrFun h1 i
  simp only [Pi.single_eq_same, Pi.smul_apply, nsmul_eq_mul] at h2
  omega

theorem mem_HC {i : Fin m} {x : ↥(leviC D e)} : x ∈ HC D H e i ↔ (x : G) ∈ H (e i) :=
  Iff.rfl

theorem rootGroup_single_le (i : Fin m) : D.rootGroup (Pi.single (e i) 1) ≤ leviC D e :=
  le_sup_left.trans (rankOne_le_levi D.rootGroup (Finset.mem_image_of_mem e (Finset.mem_univ i)))

theorem rootGroup_neg_single_le (i : Fin m) : D.rootGroup (-Pi.single (e i) 1) ≤ leviC D e :=
  le_sup_right.trans (rankOne_le_levi D.rootGroup (Finset.mem_image_of_mem e (Finset.mem_univ i)))

section Ext

include he

theorem mem_restrict_rootGroup {γ : Fin m → ℤ} {x : ↥(leviC D e)} :
    x ∈ (restrict D he).rootGroup γ ↔ (x : G) ∈ D.rootGroup (ext e γ) :=
  Iff.rfl

theorem restrict_ext_nsmul (a : ℕ) (γ : Fin m → ℤ) : ext e (a • γ) = a • ext e γ := by
  simpa [natCast_zsmul] using ext_smul he (a : ℤ) γ

theorem restrict_ext_neg (γ : Fin m → ℤ) : ext e (-γ) = -ext e γ := by
  simpa using ext_smul he (-1) γ

theorem restrict_ext_zero : ext e (0 : Fin m → ℤ) = 0 := by
  simpa using ext_smul he 0 (0 : Fin m → ℤ)

theorem restrict_ht_ext (γ : Fin m → ℤ) : ht (ext e γ) = ht γ :=
  sum_ext he γ

theorem mem_restrict_rootGroup_single {i : Fin m} {x : ↥(leviC D e)} :
    x ∈ (restrict D he).rootGroup (Pi.single i 1) ↔
      (x : G) ∈ D.rootGroup (Pi.single (e i) 1) := by
  rw [← ext_single he]
  exact Iff.rfl

theorem mem_restrict_rootGroup_neg_single {i : Fin m} {x : ↥(leviC D e)} :
    x ∈ (restrict D he).rootGroup (-Pi.single i 1) ↔
      (x : G) ∈ D.rootGroup (-Pi.single (e i) 1) := by
  rw [← ext_single he, ← restrict_ext_neg he]
  exact Iff.rfl

theorem map_iSup_restrict_rootGroup_le {S' : Set (Fin m → ℤ)} {S : Set (Fin D.rank → ℤ)}
    (h : ∀ γ ∈ S', ext e γ ∈ S) :
    (⨆ γ ∈ S', (restrict D he).rootGroup γ).map (leviC D e).subtype ≤ ⨆ γ ∈ S, D.rootGroup γ := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun γ hγ => ?_
  exact Subgroup.comap_mono
    (le_iSup₂_of_le (f := fun γ' (_ : γ' ∈ S) => D.rootGroup γ') (ext e γ) (h γ hγ) le_rfl)

end Ext

section Fields

include he

include hct hdiv in
theorem restrict_ne_bot (hext : SteinbergExtras D n H) :
    ∀ γ : Fin m → ℤ, γ ∈ (restrict D he).roots → (restrict D he).rootGroup γ ≠ ⊥ := by
  intro γ hγ hbot
  have hγ' := (restrict_roots he hdiv γ).mp hγ
  apply hext.ne_bot _ hγ'
  rw [← Subgroup.map_subgroupOf_eq_of_le (rootGroup_ext_le_leviC hdiv hct hγ')]
  have h1 : (D.rootGroup (ext e γ)).subgroupOf (leviC D e) = ⊥ := hbot
  rw [h1, Subgroup.map_bot]

include hdiv in
theorem restrict_two_smul_le (hext : SteinbergExtras D n H) :
    ∀ γ : Fin m → ℤ, γ ∈ (restrict D he).roots → 2 • γ ∈ (restrict D he).roots →
      (restrict D he).rootGroup (2 • γ) ≤ (restrict D he).rootGroup γ := by
  intro γ hγ h2 x hx
  have hγ' := (restrict_roots he hdiv γ).mp hγ
  have h2' : ext e (2 • γ) ∈ D.roots := (restrict_roots he hdiv (2 • γ)).mp h2
  have hx' : (x : G) ∈ D.rootGroup (ext e (2 • γ)) := (mem_restrict_rootGroup he).mp hx
  rw [restrict_ext_nsmul he] at h2' hx'
  exact (mem_restrict_rootGroup he).mpr (hext.two_smul_le _ hγ' h2' hx')

include hct hdiv in
theorem restrict_commutator_mem (hext : SteinbergExtras D n H) :
    ∀ γ : Fin m → ℤ, γ ∈ (restrict D he).roots → ∀ δ : Fin m → ℤ, δ ∈ (restrict D he).roots →
      LinIndepPair γ δ → ∀ x ∈ (restrict D he).rootGroup γ, ∀ y ∈ (restrict D he).rootGroup δ,
        ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (restrict D he).roots γ δ, (restrict D he).rootGroup ε := by
  intro γ hγ δ hδ hli x hx y hy
  have hγ' := (restrict_roots he hdiv γ).mp hγ
  have hδ' := (restrict_roots he hdiv δ).mp hδ
  have hli' : LinIndepPair (ext e γ) (ext e δ) := by
    intro a b hab
    refine hli a b (ext_injective he ?_)
    rw [ext_add he, ext_smul he, ext_smul he, hab, restrict_ext_zero he]
  have h := hext.commutator_mem _ hγ' _ hδ' hli' (x : G) ((mem_restrict_rootGroup he).mp hx)
    (y : G) ((mem_restrict_rootGroup he).mp hy)
  have hsub : (⨆ ε ∈ openCone D.roots (ext e γ) (ext e δ), D.rootGroup ε) ≤
      (⨆ ε ∈ openCone (restrict D he).roots γ δ, (restrict D he).rootGroup ε).map
        (leviC D e).subtype := by
    refine iSup₂_le fun ε' hε' => ?_
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε'
    have hεe : a • ext e γ + b • ext e δ = ext e (a • γ + b • δ) := by
      rw [ext_add he, restrict_ext_nsmul he, restrict_ext_nsmul he]
    have hεr' : ext e (a • γ + b • δ) ∈ D.roots := by
      rw [← hεe]
      exact hεr
    have hε : a • γ + b • δ ∈ openCone (restrict D he).roots γ δ :=
      ⟨(restrict_roots he hdiv _).mpr hεr', a, b, ha, hb, rfl⟩
    rw [hεe, ← Subgroup.map_subgroupOf_eq_of_le (rootGroup_ext_le_leviC hdiv hct hεr')]
    exact Subgroup.map_mono (le_iSup₂_of_le (f := fun ε
      (_ : ε ∈ openCone (restrict D he).roots γ δ) => (restrict D he).rootGroup ε)
      (a • γ + b • δ) hε le_rfl)
  have hc : (leviC D e).subtype ⁅x, y⁆ = ⁅(x : G), (y : G)⁆ := map_commutatorElement _ x y
  have h2 : (leviC D e).subtype ⁅x, y⁆ ∈ (⨆ ε ∈ openCone (restrict D he).roots γ δ,
      (restrict D he).rootGroup ε).map (leviC D e).subtype := by
    rw [hc]
    exact hsub h
  exact (Subgroup.mem_map_iff_mem (leviC D e).subtype_injective).mp h2

theorem prodInjectiveFor_restrict {L : List (Fin m → ℤ)}
    (hinj : ProdInjectiveFor D.rootGroup (L.map (ext e))) :
    ProdInjectiveFor (restrict D he).rootGroup L := by
  show ProdInjectiveFor (ι := Fin m) (restrict D he).rootGroup L
  have hcomp : ∀ γ : Fin m → ℤ, ext e γ ∘ e = γ := fun γ => funext (ext_apply he γ)
  have hext : ∀ f : (Fin m → ℤ) → ↥(leviC D e),
      (∀ γ ∈ L, f γ ∈ (restrict D he).rootGroup γ) →
      (∀ γ' ∈ L.map (ext e), ((f (γ' ∘ e) : ↥(leviC D e)) : G) ∈ D.rootGroup γ') ∧
        ((L.map (ext e)).map fun γ' => ((f (γ' ∘ e) : ↥(leviC D e)) : G)).prod =
          (((L.map f).prod : ↥(leviC D e)) : G) := by
    intro f hf
    refine ⟨fun γ' hγ' => ?_, ?_⟩
    · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hγ'
      rw [hcomp]
      exact hf γ hγ
    · rw [List.map_map]
      have h1 : ((fun γ' => ((f (γ' ∘ e) : ↥(leviC D e)) : G)) ∘ ext e) =
          fun γ => ((f γ : ↥(leviC D e)) : G) := by
        funext γ
        simp only [Function.comp_apply, hcomp]
      rw [h1]
      have := map_list_prod (leviC D e).subtype (L.map f)
      rw [List.map_map] at this
      exact this.symm
  intro f g hf hg hfg γ hγ
  obtain ⟨hf1, hf2⟩ := hext f hf
  obtain ⟨hg1, hg2⟩ := hext g hg
  have key := hinj _ _ hf1 hg1 (by rw [hf2, hg2, hfg]) (ext e γ) (List.mem_map_of_mem hγ)
  rw [hcomp] at key
  exact Subtype.ext key

include hdiv in
theorem exists_rootList_restrict (P : ℤ → Prop) (R : ℤ → ℤ → Prop) [DecidableRel R]
    (htrans : ∀ a b c, R a b → R b c → R a c) (htotal : ∀ a b, R a b ∨ R b a)
    {L : List (Fin m → ℤ)} (hnd : L.Nodup)
    (hmem : ∀ γ ∈ L, γ ∈ (restrict D he).roots ∧ P (ht γ))
    (hsort : L.Pairwise fun γ δ => R (ht γ) (ht δ)) :
    ∃ L' : List (Fin D.rank → ℤ), L'.Nodup ∧
      (∀ γ, γ ∈ L' ↔ γ ∈ D.roots ∧ P (ht γ) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ) ∧
      L'.Pairwise (fun γ δ => R (ht γ) (ht δ)) ∧ List.Sublist (L.map (ext e)) L' := by
  classical
  have hfin : {γ : Fin D.rank → ℤ | γ ∈ D.roots ∧ P (ht γ) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ}.Finite :=
    (finite_roots D.isFiniteType D.divisible).subset fun γ hγ => hγ.1
  have hsort0 : (L.map (ext e)).Pairwise (fun γ δ => R (ht γ) (ht δ)) := by
    rw [List.pairwise_map]
    refine hsort.imp fun {a b} h => ?_
    rwa [restrict_ht_ext he, restrict_ht_ext he]
  have hS : ∀ x ∈ L.map (ext e), x ∈ hfin.toFinset := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hr, hP⟩ := hmem γ hγ
    have hr' := (restrict_roots he hdiv γ).mp hr
    rw [Set.Finite.mem_toFinset]
    exact ⟨hr', by rwa [restrict_ht_ext he], fun δ hδ => ne_two_smul_of_mem_roots hdiv hr' hδ⟩
  obtain ⟨L', hnd', hmem', hsort', hsub'⟩ := list_exists_sorted_extension
    (fun γ δ : Fin D.rank → ℤ => R (ht γ) (ht δ)) (fun a b c => htrans _ _ _)
    (fun a b => htotal _ _) (hnd.map (ext_injective he)) hsort0 hfin.toFinset hS
  exact ⟨L', hnd', fun γ => (hmem' γ).trans hfin.mem_toFinset, hsort', hsub'⟩

include hdiv in
theorem restrict_prodInjective_pos (hext : SteinbergExtras D n H) :
    ∀ L : List (Fin (restrict D he).rank → ℤ), L.Nodup →
      (∀ γ, γ ∈ L ↔ γ ∈ (restrict D he).roots ∧ 0 < ht γ ∧
        ∀ δ ∈ (restrict D he).roots, γ ≠ 2 • δ) →
      L.Pairwise (fun γ δ => ht γ ≤ ht δ) → ProdInjectiveFor (restrict D he).rootGroup L := by
  intro L hnd hmem hsort
  obtain ⟨L', hnd', hmem', hsort', hsub⟩ := exists_rootList_restrict he hdiv (0 < ·) (· ≤ ·)
    (fun a b c => le_trans) le_total hnd
    (fun γ hγ => ⟨((hmem γ).mp hγ).1, ((hmem γ).mp hγ).2.1⟩) hsort
  exact prodInjectiveFor_restrict he
    (prodInjectiveFor_of_sublist hsub hnd' (hext.prodInjective_pos L' hnd' hmem' hsort'))

include hdiv in
theorem restrict_prodInjective_neg (hext : SteinbergExtras D n H) :
    ∀ L : List (Fin (restrict D he).rank → ℤ), L.Nodup →
      (∀ γ, γ ∈ L ↔ γ ∈ (restrict D he).roots ∧ ht γ < 0 ∧
        ∀ δ ∈ (restrict D he).roots, γ ≠ 2 • δ) →
      L.Pairwise (fun γ δ => ht δ ≤ ht γ) → ProdInjectiveFor (restrict D he).rootGroup L := by
  intro L hnd hmem hsort
  obtain ⟨L', hnd', hmem', hsort', hsub⟩ := exists_rootList_restrict he hdiv (· < 0)
    (fun a b => b ≤ a) (fun a b c hab hbc => le_trans hbc hab) (fun a b => le_total b a) hnd
    (fun γ hγ => ⟨((hmem γ).mp hγ).1, ((hmem γ).mp hγ).2.1⟩) hsort
  exact prodInjectiveFor_restrict he
    (prodInjectiveFor_of_sublist hsub hnd' (hext.prodInjective_neg L' hnd' hmem' hsort'))

include hdiv in
theorem restrict_posPart_inf_negPart (hext : SteinbergExtras D n H) :
    (⨆ γ ∈ {γ | γ ∈ (restrict D he).roots ∧ 0 < ht γ}, (restrict D he).rootGroup γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ (restrict D he).roots ∧ ht γ < 0}, (restrict D he).rootGroup γ) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hp := map_iSup_restrict_rootGroup_le he (S := {γ | γ ∈ D.roots ∧ 0 < ht γ})
    (fun γ hγ => ⟨(restrict_roots he hdiv γ).mp hγ.1, by rw [restrict_ht_ext he]; exact hγ.2⟩)
    (Subgroup.mem_map_of_mem (leviC D e).subtype hx.1)
  have hn := map_iSup_restrict_rootGroup_le he (S := {γ | γ ∈ D.roots ∧ ht γ < 0})
    (fun γ hγ => ⟨(restrict_roots he hdiv γ).mp hγ.1, by rw [restrict_ht_ext he]; exact hγ.2⟩)
    (Subgroup.mem_map_of_mem (leviC D e).subtype hx.2)
  have h1 : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← hext.posPart_inf_negPart]
    exact ⟨hp, hn⟩
  exact Subtype.ext (Subgroup.mem_bot.mp h1)

include hct in
theorem restrict_rankOne_bruhat (hext : SteinbergExtras D n H) :
    ∀ i : Fin m, ∀ g ∈ rankOne (restrict D he).rootGroup i,
      (∃ h ∈ HC D H e i, ∃ u ∈ (restrict D he).rootGroup (Pi.single i 1), g = h * u) ∨
        ∃ u ∈ (restrict D he).rootGroup (Pi.single i 1), ∃ h ∈ HC D H e i,
          ∃ v ∈ (restrict D he).rootGroup (Pi.single i 1), g = u * nC D n e i * h * v := by
  intro i g hg
  have hX1 := rootGroup_single_le (D := D) (e := e) i
  have hn : n (e i) ∈ leviC D e := by
    have h1 := (nC D n e i).2
    rwa [coe_nC hct i] at h1
  have hg' : (g : G) ∈ rankOne D.rootGroup (e i) := by
    refine (sup_le (a := (restrict D he).rootGroup (Pi.single i 1))
      (b := (restrict D he).rootGroup (-Pi.single i 1))
      (c := (rankOne D.rootGroup (e i)).comap (leviC D e).subtype) (fun x hx => ?_)
      (fun x hx => ?_)) hg
    · exact Subgroup.mem_sup_left ((mem_restrict_rootGroup_single he).mp hx)
    · exact Subgroup.mem_sup_right ((mem_restrict_rootGroup_neg_single he).mp hx)
  rcases hext.rankOne_bruhat (e i) g hg' with ⟨h, hh, u, hu, hgu⟩ |
    ⟨u, hu, h, hh, v, hv, hguhv⟩
  · left
    have huL : u ∈ leviC D e := hX1 hu
    have hhL : h ∈ leviC D e := by
      have h1 : h = (g : G) * u⁻¹ := by rw [hgu]; group
      rw [h1]
      exact mul_mem g.2 (inv_mem huL)
    exact ⟨⟨h, hhL⟩, mem_HC.mpr hh, ⟨u, huL⟩, (mem_restrict_rootGroup_single he).mpr hu,
      Subtype.ext hgu⟩
  · right
    have huL : u ∈ leviC D e := hX1 hu
    have hvL : v ∈ leviC D e := hX1 hv
    have hhL : h ∈ leviC D e := by
      have h1 : h = (n (e i))⁻¹ * (u⁻¹ * (g : G) * v⁻¹) := by rw [hguhv]; group
      rw [h1]
      exact mul_mem (inv_mem hn) (mul_mem (mul_mem (inv_mem huL) g.2) (inv_mem hvL))
    refine ⟨⟨u, huL⟩, (mem_restrict_rootGroup_single he).mpr hu, ⟨h, hhL⟩, mem_HC.mpr hh,
      ⟨v, hvL⟩, (mem_restrict_rootGroup_single he).mpr hv, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, coe_nC hct]
    exact hguhv

theorem restrict_eq_one_of_mem_normalizer (hext : SteinbergExtras D n H) :
    ∀ i : Fin m, ∀ u ∈ (restrict D he).rootGroup (Pi.single i 1),
      u ∈ Subgroup.normalizer ((restrict D he).rootGroup (-Pi.single i 1) : Set ↥(leviC D e)) →
        u = 1 := by
  intro i u hu hnorm
  have hX2 := rootGroup_neg_single_le (D := D) (e := e) i
  have hnorm' : (u : G) ∈ Subgroup.normalizer (D.rootGroup (-Pi.single (e i) 1) : Set G) := by
    intro x
    by_cases hxL : x ∈ leviC D e
    · have h1 := Subgroup.mem_set_normalizer_iff.mp hnorm ⟨x, hxL⟩
      exact ((mem_restrict_rootGroup_neg_single he (x := ⟨x, hxL⟩)).symm.trans
        (h1.trans (mem_restrict_rootGroup_neg_single he)))
    · constructor
      · intro hx
        exact absurd (hX2 hx) hxL
      · intro hx
        refine absurd ?_ hxL
        have h1 := mul_mem (mul_mem (inv_mem u.2) (hX2 hx)) u.2
        simpa [mul_assoc] using h1
  exact Subtype.ext (hext.eq_one_of_mem_normalizer (e i) u
    ((mem_restrict_rootGroup_single he).mp hu) hnorm')

theorem restrict_torus_commute (hext : SteinbergExtras D n H) :
    ∀ i j, ∀ h ∈ HC D H e i, ∀ h' ∈ HC D H e j, Commute h h' := by
  intro i j h hh h' hh'
  exact Subtype.ext (hext.torus_commute (e i) (e j) h (mem_HC.mp hh) h' (mem_HC.mp hh'))

theorem restrict_torus_iSupIndep (hext : SteinbergExtras D n H) : iSupIndep (HC D H e) := by
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  have h1 : (x : G) ∈ H (e i) := mem_HC.mp hx
  have hle : (⨆ j, ⨆ (_ : j ≠ i), HC D H e j).map (leviC D e).subtype ≤
      ⨆ j', ⨆ (_ : j' ≠ e i), H j' := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun j hj => ?_
    exact Subgroup.comap_mono (le_iSup₂_of_le (f := fun j' (_ : j' ≠ e i) => H j') (e j)
      (fun h => hj (he h)) le_rfl)
  have h2 : (x : G) ∈ ⨆ j', ⨆ (_ : j' ≠ e i), H j' := hle (Subgroup.mem_map_of_mem _ hx')
  exact Subtype.ext (Subgroup.disjoint_def.mp (hext.torus_iSupIndep (e i)) h1 h2)

include hdiv in
theorem restrict_torus_inf_posPart (hext : SteinbergExtras D n H) :
    (⨆ i, HC D H e i) ⊓
      (⨆ γ ∈ {γ | γ ∈ (restrict D he).roots ∧ 0 < ht γ}, (restrict D he).rootGroup γ) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hT : (x : G) ∈ ⨆ i, H i := by
    have hle : (⨆ i, HC D H e i).map (leviC D e).subtype ≤ ⨆ i, H i := by
      rw [Subgroup.map_le_iff_le_comap]
      exact iSup_le fun i => Subgroup.comap_mono (le_iSup H (e i))
    exact hle (Subgroup.mem_map_of_mem _ hx.1)
  have hU := map_iSup_restrict_rootGroup_le he (S := {γ | γ ∈ D.roots ∧ 0 < ht γ})
    (fun γ hγ => ⟨(restrict_roots he hdiv γ).mp hγ.1, by rw [restrict_ht_ext he]; exact hγ.2⟩)
    (Subgroup.mem_map_of_mem (leviC D e).subtype hx.2)
  have h1 : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← hext.torus_inf_posPart]
    exact ⟨hT, hU⟩
  exact Subtype.ext (Subgroup.mem_bot.mp h1)

end Fields

end SE

include hct hdiv in
theorem restrict_steinbergExtras (hext : SteinbergExtras D n H) :
    SteinbergExtras (restrict D he) (nC D n e) (HC D H e) where
  ne_bot := SE.restrict_ne_bot he hdiv hct hext
  two_smul_le := SE.restrict_two_smul_le he hdiv hext
  commutator_mem := SE.restrict_commutator_mem he hdiv hct hext
  prodInjective_pos := SE.restrict_prodInjective_pos he hdiv hext
  prodInjective_neg := SE.restrict_prodInjective_neg he hdiv hext
  posPart_inf_negPart := SE.restrict_posPart_inf_negPart he hdiv hext
  rankOne_bruhat := SE.restrict_rankOne_bruhat he hct hext
  eq_one_of_mem_normalizer := SE.restrict_eq_one_of_mem_normalizer he hext
  torus_commute := SE.restrict_torus_commute he hext
  torus_iSupIndep := SE.restrict_torus_iSupIndep he hext
  torus_inf_posPart := SE.restrict_torus_inf_posPart he hdiv hext

end CFSG.LieType.TitsSimplicity.Levi
