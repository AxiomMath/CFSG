module

public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Steinberg.Extras

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

universe u w

theorem isNegMultiple_iff {ι : Type*} (α β : ι → ℤ) :
    Steinberg.IsNegMultiple α β ↔ Universal.IsNegMultiple α β := by
  constructor
  · rintro ⟨c, hc, h⟩
    by_cases hα : α = 0
    · subst hα
      refine ⟨1, 1, one_pos, one_pos, funext fun j => ?_⟩
      have := h j
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, Int.cast_eq_zero] at this
      simp [this]
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hα (funext hcon)
    have key : ∀ k, α j * β k = β j * α k := fun k => by
      have : (α j : ℝ) * β k = β j * α k := by
        rw [h k, h j]
        ring
      exact_mod_cast this
    rcases lt_or_gt_of_ne hj with hneg | hpos
    · have hβ : 0 < β j := by
        have : (0 : ℝ) < β j := by
          rw [h j]
          exact mul_pos_of_neg_of_neg hc (by exact_mod_cast hneg)
        exact_mod_cast this
      refine ⟨(-α j).toNat, (β j).toNat, by omega, by omega, funext fun k => ?_⟩
      simp only [Pi.smul_apply, Pi.neg_apply]
      simp only [nsmul_eq_mul, Int.natCast_toNat_eq_self.mpr hβ.le,
        Int.natCast_toNat_eq_self.mpr (by omega : 0 ≤ -α j)]
      linear_combination -key k
    · have hβ : β j < 0 := by
        have : (β j : ℝ) < 0 := by
          rw [h j]
          exact mul_neg_of_neg_of_pos hc (by exact_mod_cast hpos)
        exact_mod_cast this
      refine ⟨(α j).toNat, (-β j).toNat, by omega, by omega, funext fun k => ?_⟩
      simp only [Pi.smul_apply, Pi.neg_apply]
      simp only [nsmul_eq_mul, Int.natCast_toNat_eq_self.mpr hpos.le,
        Int.natCast_toNat_eq_self.mpr (by omega : 0 ≤ -β j)]
      linear_combination key k
  · rintro ⟨a, b, ha, hb, h⟩
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    refine ⟨-(b : ℝ) / a, div_neg_of_neg_of_pos (neg_neg_of_pos hb') ha', fun j => ?_⟩
    have hj := congrFun h j
    simp only [Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul] at hj
    have hj' : (a : ℝ) * β j = -((b : ℝ) * α j) := by exact_mod_cast hj
    field_simp
    linarith

section Relations

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Group K] (Φ : RootSystem ι)
  {X : (ι → ℤ) → Subgroup K} {G : Type*} [Group G] (ψ : ∀ γ, X γ → G)

@[expose] def symbolMap : Symbol Φ X → G := fun s => ψ s.1.1 ⟨s.1.2, s.2.2⟩

variable {Φ ψ}

theorem exists_list_of_mem_freeSub {S : Set (ι → ℤ)}
    (hinv : ∀ γ ∈ S, ∀ x : X γ, ψ γ x⁻¹ = (ψ γ x)⁻¹) {v : FreeSt Φ X}
    (hv : v ∈ freeSub Φ X S) :
    ∃ l : List (Σ γ : ι → ℤ, X γ), (∀ p ∈ l, p.1 ∈ S) ∧
      piF Φ X v = (l.map fun p => (p.2 : K)).prod ∧
      FreeGroup.lift (symbolMap Φ ψ) v = (l.map fun p => ψ p.1 p.2).prod := by
  induction hv using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨s, hs, rfl⟩ := hv
    exact ⟨[⟨s.1.1, ⟨s.1.2, s.2.2⟩⟩], by simpa using hs, by simp [piF], by simp [symbolMap]⟩
  | one => exact ⟨[], by simp, by simp, by simp⟩
  | mul v v' _ _ ih ih' =>
    obtain ⟨l, hl, h1, h2⟩ := ih
    obtain ⟨l', hl', h1', h2'⟩ := ih'
    refine ⟨l ++ l', fun p hp => ?_, by simp [h1, h1'], by simp [h2, h2']⟩
    rcases List.mem_append.mp hp with hp | hp
    exacts [hl p hp, hl' p hp]
  | inv v _ ih =>
    obtain ⟨l, hl, h1, h2⟩ := ih
    refine ⟨(l.map fun p => ⟨p.1, p.2⁻¹⟩).reverse, fun p hp => ?_, ?_, ?_⟩
    · simp only [List.mem_reverse, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hl q hq
    · rw [map_inv, h1, List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
      rfl
    · rw [map_inv, h2, List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
      congr 2
      exact List.map_congr_left fun p hp => (hinv p.1 (hl p hp) p.2).symm

theorem relationsHold_iff {S : Set (ι → ℤ)} (hS : S ⊆ Φ.roots) :
    RelationsHold X S ψ ↔
      ∀ v ∈ freeSub Φ X S, piF Φ X v = 1 → FreeGroup.lift (symbolMap Φ ψ) v = 1 := by
  constructor
  · intro h v hv h1
    have hinv : ∀ γ ∈ S, ∀ x : X γ, ψ γ x⁻¹ = (ψ γ x)⁻¹ := fun γ hγ x => by
      have := h [⟨γ, x⟩, ⟨γ, x⁻¹⟩] (by simp [hγ]) (by simp)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
      exact eq_inv_of_mul_eq_one_right this
    obtain ⟨l, hl, hπ, hψ⟩ := exists_list_of_mem_freeSub hinv hv
    rw [hψ]
    exact h l hl (hπ ▸ h1)
  · intro h l hl h1
    set v : FreeSt Φ X := (l.attach.map fun p =>
      FreeGroup.of (⟨(p.1.1, (p.1.2 : K)), hS (hl p.1 p.2), p.1.2.2⟩ : Symbol Φ X)).prod
    have hv : v ∈ freeSub Φ X S := Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
      exact Subgroup.subset_closure ⟨_, hl p.1 p.2, rfl⟩
    have hπ : piF Φ X v = (l.map fun p => (p.2 : K)).prod := by
      rw [map_list_prod, List.map_map]
      conv_rhs => rw [← List.attach_map_subtype_val l, List.map_map]
      congr 1
      exact List.map_congr_left fun p _ => by simp [piF]
    have hψ : FreeGroup.lift (symbolMap Φ ψ) v = (l.map fun p => ψ p.1 p.2).prod := by
      rw [map_list_prod, List.map_map]
      conv_rhs => rw [← List.attach_map_subtype_val l, List.map_map]
      congr 1
      exact List.map_congr_left fun p _ => by simp [symbolMap]
    rw [← hψ]
    exact h v hv (hπ.trans h1)

end Relations

variable {K : Type u} [Group K]

@[expose] def toRootGroupData (D : UniversalRootDatum K) (n : Fin D.rank → K) :
    RootGroupData (RootSystem.ofCartan D.isFiniteType D.divisible) K :=
  ⟨D.rootGroup, n⟩

@[simp] theorem toRootGroupData_X (D : UniversalRootDatum K) (n : Fin D.rank → K) :
    (toRootGroupData D n).X = D.rootGroup := rfl

@[simp] theorem toRootGroupData_n (D : UniversalRootDatum K) (n : Fin D.rank → K) :
    (toRootGroupData D n).n = n := rfl

private theorem exists_nodup_sorted {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℤ) :
    ∃ L : List α, L.Nodup ∧ (∀ a, a ∈ L ↔ a ∈ s) ∧ L.Pairwise (fun a b => f a ≤ f b) := by
  refine ⟨hs.toFinset.toList.mergeSort (fun a b => decide (f a ≤ f b)), ?_, fun a => ?_, ?_⟩
  · exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  · rw [(List.mergeSort_perm _ _).mem_iff, Finset.mem_toList, hs.mem_toFinset]
  · refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp ?_
    · simp only [decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc
    · simpa using le_total (f a) (f b)
    · intro a b h
      simpa using h

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

section IsSteinberg

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)

include hct in
theorem mem_normalizer_rootGroup {k : Fin D.rank} {h : K} (hh : h ∈ H k)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    h ∈ Subgroup.normalizer (D.rootGroup γ : Set K) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => hct.H_conj_mem k γ hγ h hh x hx, fun hx => ?_⟩
  have := hct.H_conj_mem k γ hγ h⁻¹ (inv_mem hh) _ hx
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e] at this

include hct in
theorem map_conj_rootGroup (i : Fin D.rank) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    (D.rootGroup γ).map (MulAut.conj (n i)).toMonoidHom =
      D.rootGroup ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hs : ∀ v, weylAction D.isFiniteType
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) v = Φ.refl i v := fun v => by
    rw [weylAction_simple]
    rfl
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have := hct.conj_mem i γ hγ x hx
    rw [hs] at this
    simpa using this
  · intro y hy
    have h1 := hct.conj_mem i _ (Φ.refl_mem i γ hγ) y hy
    rw [hs, Φ.refl_refl] at h1
    have h2 := hct.H_conj_mem i γ hγ _ (inv_mem (hct.sq_mem i)) _ h1
    refine ⟨(n i)⁻¹ * y * n i, ?_, ?_⟩
    · have e : (n i)⁻¹ * y * n i = (n i ^ 2)⁻¹ * (n i * y * (n i)⁻¹) * ((n i ^ 2)⁻¹)⁻¹ := by
        group
      rw [e]
      exact h2
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

variable (hext : SteinbergExtras D n H)

include hct hext in
theorem torus_toRootGroupData_apply (i : Fin D.rank) : (toRootGroupData D n).torus i = H i := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hα : Pi.single i 1 ∈ D.roots := hΦ.single_mem i
  have hα' : -Pi.single i 1 ∈ D.roots := by
    have := hΦ.smul_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) _ hα
    rwa [hΦ.simple_single] at this
  apply le_antisymm
  · intro g hg
    simp only [RootGroupData.torus, Subgroup.mem_inf] at hg
    obtain ⟨⟨hgL, hgN⟩, hgN'⟩ := hg
    rcases hext.rankOne_bruhat i g hgL with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    ·
      have hu' : u ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
        have e : u = h⁻¹ * (h * u) := by group
        rw [e]
        exact mul_mem (inv_mem (mem_normalizer_rootGroup hct hh hα')) hgN'
      rw [hext.eq_one_of_mem_normalizer i u hu hu', mul_one]
      exact hh
    ·
      exfalso
      set g := u * n i * h * v with hg
      have hle : D.rootGroup (Pi.single i 1) ≤ D.rootGroup (-Pi.single i 1) := by
        intro x hx
        have hy : u * x * u⁻¹ ∈ D.rootGroup (Pi.single i 1) :=
          mul_mem (mul_mem hu hx) (inv_mem hu)
        have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hgN) _).mp hy
        have h2 : v * (g⁻¹ * (u * x * u⁻¹) * g⁻¹⁻¹) * v⁻¹ ∈ D.rootGroup (Pi.single i 1) :=
          mul_mem (mul_mem hv h1) (inv_mem hv)
        have h3 := hct.H_conj_mem i _ hα h hh _ h2
        have h4 := hct.conj_mem i _ hα _ h3
        rw [weylAction_simple_single] at h4
        have e : n i * (h * (v * (g⁻¹ * (u * x * u⁻¹) * g⁻¹⁻¹) * v⁻¹) * h⁻¹) * (n i)⁻¹ = x := by
          rw [hg]
          group
        rwa [e] at h4
      apply hext.ne_bot _ hα
      rw [eq_bot_iff, ← hext.posPart_inf_negPart]
      refine le_inf ?_ (hle.trans ?_)
      · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}) => D.rootGroup γ)
          (Pi.single i 1) ⟨hα, by simp [ht]⟩ le_rfl
      · exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}) => D.rootGroup γ)
          (-Pi.single i 1) ⟨hα', by simp [ht]⟩ le_rfl
  · intro h hh
    simp only [RootGroupData.torus, Subgroup.mem_inf]
    exact ⟨⟨hct.H_le i hh, mem_normalizer_rootGroup hct hh hα⟩,
      mem_normalizer_rootGroup hct hh hα'⟩

include hct hext in
theorem torus_toRootGroupData : (toRootGroupData D n).torus = H :=
  funext (torus_toRootGroupData_apply hct hext)

include hct hext in
theorem isSteinberg_of : (toRootGroupData D n).IsSteinberg where
  ne_bot := hext.ne_bot
  two_smul_le := hext.two_smul_le
  commutator_mem := hext.commutator_mem
  exists_posList := by
    obtain ⟨L, hnd, hmem, hsort⟩ := exists_nodup_sorted
      ((finite_roots D.isFiniteType D.divisible).subset
        (fun γ (h : γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ) => h.1)) ht
    exact ⟨L, hnd, fun γ => (hmem γ).trans and_assoc.symm, hsort,
      hext.prodInjective_pos L hnd hmem hsort⟩
  exists_negList := by
    obtain ⟨L, hnd, hmem, hsort⟩ := exists_nodup_sorted
      ((finite_roots D.isFiniteType D.divisible).subset
        (fun γ (h : γ ∈ D.roots ∧ ht γ < 0 ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ) => h.1)) (fun γ => -ht γ)
    have hsort' : L.Pairwise (fun γ δ => ht δ ≤ ht γ) := hsort.imp fun h => neg_le_neg_iff.mp h
    exact ⟨L, hnd, fun γ => (hmem γ).trans and_assoc.symm, hsort',
      hext.prodInjective_neg L hnd hmem hsort'⟩
  posPart_inf_negPart := hext.posPart_inf_negPart
  n_mem := hct.n_mem
  map_conj_n i _ hγ := map_conj_rootGroup hct i hγ
  torus_le_normalizer i _ hγ := by
    rw [torus_toRootGroupData_apply hct hext]
    exact fun h hh => mem_normalizer_rootGroup hct hh hγ
  rankOne_bruhat i g hg := by
    rw [torus_toRootGroupData_apply hct hext]
    exact hext.rankOne_bruhat i g hg
  eq_one_of_mem_normalizer := hext.eq_one_of_mem_normalizer
  torus_commute i j h hh h' hh' := by
    rw [torus_toRootGroupData_apply hct hext] at hh hh'
    exact hext.torus_commute i j h hh h' hh'
  torus_iSupIndep := by
    rw [torus_toRootGroupData hct hext]
    exact hext.torus_iSupIndep
  torusPart_inf_posPart := by
    rw [RootGroupData.torusPart, torus_toRootGroupData hct hext]
    exact hext.torus_inf_posPart

end IsSteinberg

theorem steinbergPresentation_of (hgen : ⨆ γ ∈ D.roots, D.rootGroup γ = ⊤)
    (hbij : Function.Bijective
      (stPi (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup)) :
    D.SteinbergPresentation.{u, w} := by
  refine ⟨hgen, fun G _ ψ hψ => ?_⟩
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hR1 : ∀ S ∈ D.relsR1 ∪ D.relsR2, S ⊆ Φ.roots := by
    rintro S (⟨α, -, β, -, -, rfl⟩ | ⟨i, rfl⟩)
    · exact fun γ hγ => hγ.1
    · have hΦ := isCTRootSystem D.isFiniteType D.divisible
      rintro γ (rfl | rfl)
      · exact hΦ.single_mem i
      · have := hΦ.smul_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) _
          (hΦ.single_mem i)
        rwa [hΦ.simple_single] at this
  have hker : relN Φ D.rootGroup ≤ (FreeGroup.lift (symbolMap Φ ψ)).ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro x (⟨α, hα, β, hβ, hneg, hx, h1⟩ | ⟨i, hx, h1⟩)
    · have hS : D.cone α β ∈ D.relsR1 ∪ D.relsR2 :=
        Or.inl ⟨α, hα, β, hβ, fun h => hneg ((isNegMultiple_iff α β).mpr h), rfl⟩
      exact MonoidHom.mem_ker.mpr (((relationsHold_iff (hR1 _ hS)).mp (hψ _ hS)) x hx h1)
    · have hS : ({Pi.single i 1, -Pi.single i 1} : Set (Fin D.rank → ℤ)) ∈
          D.relsR1 ∪ D.relsR2 := Or.inr ⟨i, rfl⟩
      exact MonoidHom.mem_ker.mpr (((relationsHold_iff (hR1 _ hS)).mp (hψ _ hS)) x hx h1)
  let e := MulEquiv.ofBijective (stPi Φ D.rootGroup) hbij
  refine ⟨(QuotientGroup.lift _ _ hker).comp e.symm.toMonoidHom, fun γ hγ x => ?_⟩
  have hx : e.symm x = (FreeGroup.of (⟨(γ, (x : K)), hγ, x.2⟩ : Symbol Φ D.rootGroup) :
      StGroup Φ D.rootGroup) := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, MulEquiv.ofBijective_apply]
    simp [stPi, piF]
  simp [hx, symbolMap]

end CFSG.LieType.Steinberg
