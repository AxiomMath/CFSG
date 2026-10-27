module

public import CFSG.LieType.Steinberg.Collection
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

theorem prod_map_eq_prod_filter_mul {G V : Type*} [Group G] (f : V → G) (p : V → Bool)
    (hcen : ∀ v, p v = false → f v ∈ Subgroup.center G) (L : List V) :
    (L.map f).prod = ((L.filter p).map f).prod * ((L.filter (fun v => !p v)).map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : p a = true
    · simp [ha, ih, mul_assoc]
    · have hfa : p a = false := by simpa using ha
      simp only [List.map_cons, List.prod_cons, List.filter_cons, hfa, Bool.not_false,
        ite_true, Bool.false_eq_true, ite_false, ih]
      rw [← mul_assoc, ← (Subgroup.mem_center_iff.1 (hcen a hfa) _), mul_assoc]

universe u v

theorem le_center_of_height_max {G : Type u} [Group G] {ι : Type v} (h : ι → ℤ)
    (A : ι → Subgroup G) (hab : ∀ i, IsMulCommutative (A i)) (hgen : ⨆ i, A i = ⊤)
    (hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ ≤ ⨆ (k) (_ : max (h i) (h j) < h k), A k) {m : ℤ}
    (hle : ∀ i, h i ≤ m) {k : ι} (hk : h k = m) : A k ≤ Subgroup.center G := by
  have hj : ∀ j, A j ≤ Subgroup.centralizer (A k : Set G) := fun j => by
    by_cases hjk : j = k
    · subst hjk
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := (hab j).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
      exact congrArg Subtype.val this
    · have hbot : ⁅A j, A k⁆ = ⊥ := by
        refine eq_bot_iff.2 ((hc j k hjk).trans (iSup₂_le fun l hl => ?_))
        exact absurd (lt_of_le_of_lt (le_max_right _ _) hl) (by rw [hk]; exact not_lt.2 (hle l))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ Subgroup.centralizer (A k : Set G) := by
    have : (⊤ : Subgroup G) ≤ Subgroup.centralizer (A k : Set G) := hgen ▸ iSup_le hj
    exact this (Subgroup.mem_top y)
  exact (Subgroup.mem_centralizer_iff.1 hy x hx).symm

theorem prod_map_filterMap_subtype {G ι : Type*} [Group G] (P : ι → Prop) [DecidablePred P]
    (F : {i // P i} → G) (f : ι → G) (hf : ∀ i (hi : P i), f i = F ⟨i, hi⟩) (L : List ι) :
    ((L.filterMap fun i => if hi : P i then some ⟨i, hi⟩ else none).map F).prod =
      ((L.filter fun i => decide (P i)).map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : P a
    · simp [ha, ih, hf a ha]
    · simp [ha, ih]

theorem height_commutator_collection_aux (n : ℕ) :
    ∀ {G : Type u} [Group G] {ι : Type v} [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (h : ι → ℤ) (A : ι → Subgroup G), (∀ i, IsMulCommutative (A i)) → ⨆ i, A i = ⊤ →
    (∀ i j, i ≠ j → ⁅A i, A j⁆ ≤ ⨆ (k) (_ : max (h i) (h j) < h k), A k) →
    ∀ L : List ι, L.Nodup → (∀ i, i ∈ L) →
      ∀ g : G, ∃ f : ι → G, (∀ i, f i ∈ A i) ∧ g = (L.map f).prod := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ ι _ _ hn h A hab hgen hc L hnd hall g
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have htop : (⊤ : Subgroup G) = ⊥ := by rw [← hgen]; simp
    have hg : g = 1 := by
      have := Subgroup.mem_top g
      rwa [htop, Subgroup.mem_bot] at this
    have hL : L = [] := List.eq_nil_iff_forall_not_mem.2 fun i => isEmptyElim i
    exact ⟨1, fun i => isEmptyElim i, by simp [hL, hg]⟩
  · classical
    set m := Finset.univ.sup' ⟨i₀, Finset.mem_univ _⟩ h with hm
    have hle : ∀ i, h i ≤ m := fun i => Finset.le_sup' h (Finset.mem_univ i)
    obtain ⟨imax, -, himax⟩ := Finset.exists_mem_eq_sup' ⟨i₀, Finset.mem_univ _⟩ h
    have hcen : ∀ k, h k = m → A k ≤ Subgroup.center G := fun k hk =>
      le_center_of_height_max h A hab hgen hc hle hk
    set Z : Subgroup G := ⨆ (k) (_ : h k = m), A k with hZdef
    have hZ : Z ≤ Subgroup.center G := iSup₂_le fun k hk => hcen k hk
    have hZn : Z.Normal := Subgroup.normal_of_le_center hZ
    have hAZ : ∀ k, h k = m → A k ≤ Z := fun k hk => le_iSup₂ (f := fun k (_ : h k = m) => A k) k hk
    have hcard : Fintype.card {i : ι // h i < m} < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := imax) (by rw [← himax]; exact lt_irrefl _)
    set q := QuotientGroup.mk' Z
    let A' : {i : ι // h i < m} → Subgroup (G ⧸ Z) := fun i => (A i.1).map q
    have hab' : ∀ i, IsMulCommutative (A' i) := fun i => by
      refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      have := (hab i.1).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      change (x : G ⧸ Z) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      exact congrArg (fun t : A i.1 => q (t : G)) this
    have hmapbot : ∀ k, ¬ h k < m → (A k).map q = ⊥ := fun k hk => by
      have hk' : h k = m := le_antisymm (hle k) (not_lt.1 hk)
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hAZ k hk'
    have hgen' : ⨆ i, A' i = ⊤ := by
      refine eq_top_iff.2 ?_
      have htop : (⊤ : Subgroup (G ⧸ Z)) = (⨆ i, A i).map q := by
        rw [hgen, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
      rw [htop, Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      by_cases hk : h k < m
      · exact le_iSup A' ⟨k, hk⟩
      · rw [hmapbot k hk]; exact bot_le
    have hc' : ∀ i j, i ≠ j →
        ⁅A' i, A' j⁆ ≤ ⨆ (k) (_ : max (h i.1) (h j.1) < h k.1), A' k := fun i j hij => by
      have hij' : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
      change ⁅(A i.1).map q, (A j.1).map q⁆ ≤ _
      rw [← Subgroup.map_commutator]
      refine (Subgroup.map_mono (hc i.1 j.1 hij')).trans ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hk => ?_
      by_cases hkm : h k < m
      · exact le_iSup₂_of_le (f := fun (k : {i : ι // h i < m})
          (_ : max (h i.1) (h j.1) < h k.1) => A' k) ⟨k, hkm⟩ hk le_rfl
      · rw [hmapbot k hkm]; exact bot_le
    set L' : List {i : ι // h i < m} :=
      L.filterMap fun i => if hi : h i < m then some ⟨i, hi⟩ else none with hL'
    have hnd' : L'.Nodup := by
      refine hnd.filterMap fun a a' b hb hb' => ?_
      by_cases ha : h a < m
      · by_cases ha' : h a' < m
        · simp only [ha, ha', ↓reduceDIte, Option.mem_def, Option.some.injEq] at hb hb'
          rw [← hb] at hb'
          exact (congrArg Subtype.val hb').symm
        · simp [ha'] at hb'
      · simp [ha] at hb
    have hall' : ∀ i, i ∈ L' := fun i => by
      rw [hL', List.mem_filterMap]
      exact ⟨i.1, hall i.1, by simp [i.2]⟩
    obtain ⟨f', hf', hg'⟩ := ih _ hcard rfl (fun i => h i.1) A' hab' hgen' hc' L' hnd' hall' (q g)
    have hlift : ∀ i : {i : ι // h i < m}, ∃ x ∈ A i.1, q x = f' i := fun i => hf' i
    choose f₁ hf₁ hqf₁ using hlift
    set w := (L'.map f₁).prod
    have hqw : q w = q g := by
      rw [hg', map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => hqf₁ i
    have hz : w⁻¹ * g ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, hqw, inv_mul_cancel]
    set LM := L.filter fun i => decide (h i = m)
    have hZLM : Z ≤ ⨆ v ∈ LM, A v := iSup₂_le fun k hk =>
      le_iSup₂_of_le (f := fun v (_ : v ∈ LM) => A v) k
        (List.mem_filter.2 ⟨hall k, by simpa using hk⟩) le_rfl
    obtain ⟨fz, hfz, hzprod⟩ := exists_prod_eq_of_commutator_mem A (fun _ => (0 : ℤ))
      (hnd.filter _) (List.Pairwise.imp (fun _ => le_rfl) (List.pairwise_of_forall fun _ _ => trivial))
      (fun a ha b hb _ x hx y hy => by
        have hxc := hcen a (by simpa using (List.mem_filter.1 ha).2) hx
        rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hxc y).symm]
        exact one_mem _)
      (w⁻¹ * g) (hZLM hz)
    let f : ι → G := fun i => if hi : h i < m then f₁ ⟨i, hi⟩ else fz i
    have hfcen : ∀ v, decide (h v < m) = false → f v ∈ Subgroup.center G := fun v hv => by
      have hv' : ¬ h v < m := by simpa using hv
      have hvm : h v = m := le_antisymm (hle v) (not_lt.1 hv')
      simp only [f, hv', ↓reduceDIte]
      exact hcen v hvm (hfz v (List.mem_filter.2 ⟨hall v, by simpa using hvm⟩))
    refine ⟨f, fun i => ?_, ?_⟩
    · by_cases hi : h i < m
      · simp only [f, hi, ↓reduceDIte]; exact hf₁ ⟨i, hi⟩
      · have him : h i = m := le_antisymm (hle i) (not_lt.1 hi)
        simp only [f, hi, ↓reduceDIte]
        exact hfz i (List.mem_filter.2 ⟨hall i, by simpa using him⟩)
    · rw [prod_map_eq_prod_filter_mul f (fun i => decide (h i < m)) hfcen L]
      have h1 : ((L.filter fun i => decide (h i < m)).map f).prod = w := by
        rw [← prod_map_filterMap_subtype (fun i => h i < m) f₁ f
          (fun i hi => by simp only [f, hi, ↓reduceDIte])]
      have h2 : ((L.filter fun i => !decide (h i < m)).map f).prod = w⁻¹ * g := by
        have hfil : (L.filter fun i => !decide (h i < m)) = LM := by
          refine List.filter_congr fun i _ => ?_
          by_cases hi : h i < m
          · simp [hi, ne_of_lt hi]
          · simp [le_antisymm (hle i) (not_lt.1 hi)]
        rw [hfil, hzprod]
        refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
        have him : h i = m := by simpa using (List.mem_filter.1 hi).2
        have hi' : ¬ h i < m := by rw [him]; exact lt_irrefl _
        simp only [f, hi', ↓reduceDIte]
      rw [h1, h2, mul_inv_cancel_left]

theorem height_commutator_collection {G : Type u} [Group G] {ι : Type v} [Fintype ι]
    [DecidableEq ι] (h : ι → ℤ) (A : ι → Subgroup G) (hab : ∀ i, IsMulCommutative (A i))
    (hgen : ⨆ i, A i = ⊤)
    (hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ ≤ ⨆ (k) (_ : max (h i) (h j) < h k), A k)
    (L : List ι) (hnd : L.Nodup) (hall : ∀ i, i ∈ L) (g : G) :
    ∃ f : ι → G, (∀ i, f i ∈ A i) ∧ g = (L.map f).prod :=
  height_commutator_collection_aux _ rfl h A hab hgen hc L hnd hall g

end CFSG.LieType.Steinberg
