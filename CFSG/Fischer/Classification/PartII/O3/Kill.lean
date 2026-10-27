module

public import CFSG.Fischer.Classification.PartII.O3.Rho
public import CFSG.Fischer.Classification.PartII.O3.Count

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

@[expose] def ySet (E : Set X) (φ : Pt → X) : Set X :=
  {y | y ∈ E ∧ ¬ Cent E φ y ∧ ∀ m, Cent E φ m → y * m = m * y}

theorem IsPlane.mem_ySet {φ : Pt → X} (hπ : IsPlane E φ) (p : Pt) : φ p ∈ ySet E φ :=
  ⟨hπ.mem p, fun h => IsPlane.ne_of_cent h p rfl, fun _ hm => (hm.2 p).2.2⟩

theorem mem_localClass_of_mem_ySet {φ : Pt → X} {y m : X} (hy : y ∈ ySet E φ)
    (hm : Cent E φ m) : m ∈ LocalClass E y :=
  ⟨hm.1, fun h => hy.2.1 (h ▸ hm), (hy.2.2 m hm).symm⟩

theorem eq_of_sub_eq_zero_pt : ∀ p q : Pt, q - p = 0 → q = p := by decide

theorem neg_add_sub_ne_pt : ∀ p s : Pt, s ≠ 0 → -(p + s) - p ≠ p := by decide

namespace ConfAt

variable {φ : Pt → X} {w₁ w₂ : X} {r₁ r₂ : Pt} (hc : ConfAt E φ w₁ w₂ r₁ r₂) (hS : Setting X E)
include hc hS

theorem muSet_eq {p q : Pt} (hpq : p ≠ q) : muSet E (φ p) (φ q) = {e | Cent E φ e} := by
  ext e
  exact ⟨fun he => hc.cent_of_mem_muSet hS hpq he,
    fun he => ⟨mem_localClass_symm he.1 (he.2 p), mem_localClass_symm he.1 (he.2 q)⟩⟩

theorem inter_subset_cent {w : X} (hw : Cent E φ w) {p₀ s : Pt} (hs : s ≠ 0)
    (hst : s ∈ typ E φ w) : LocalClass E w ∩ LocalClass E (φ p₀) ⊆ {e | Cent E φ e} := by
  rintro c ⟨hcw, hcx⟩
  have hP := hS.pair
  have hf : φ (p₀ + s) ∈ fib E w (φ p₀) :=
    (hc.plane.fib_iff hP hw p₀ (p₀ + s)).2 (by rw [add_sub_cancel_left_pt]; exact hst)
  have hcs : c * φ (p₀ + s) = φ (p₀ + s) * c :=
    Pair.commute_of_mem_fib hP hcw (hw.2 p₀) hcx.2.1 hcx.2.2 hf
  have hne : p₀ ≠ p₀ + s := fun h => hs (eq_zero_of_add_eq_pt p₀ s h.symm)
  refine hc.cent_of_mem_muSet hS hne ⟨hcx, hcx.1, fun h => ?_, hcs⟩
  rw [h] at hcx
  exact hc.plane.ncomm (p₀ + s) p₀ (Ne.symm hne) hcx.2.2

theorem ncard_inter_lt {a b : X} (ha : a ∈ E) (hb : b ∈ LocalClass E a) :
    (muSet E a b).ncard < {e | Cent E φ e}.ncard := by
  have hP := hS.pair
  have := Pair.finite hP
  have hx : φ 0 ∈ LocalClass E w₁ := hc.cent₁.2 0
  rw [hS.ncard_inter_eq hc.cent₁.1 hx ha hb]
  have hsub : muSet E w₁ (φ 0) ⊆ {e | Cent E φ e} :=
    hc.inter_subset_cent hS hc.cent₁ hc.ne₁ (by rw [hc.typ₁]; exact Or.inr (Or.inl rfl))
  exact Set.ncard_lt_ncard (hsub.ssubset_of_not_subset fun h => (h hc.cent₁).1.2.1 rfl)

theorem ySet_pairwise {p q : X} (hp : p ∈ ySet E φ) (hq : q ∈ ySet E φ) (hpq : p ≠ q) :
    p * q ≠ q * p ∧ LocalClass E p ∩ LocalClass E q ⊆ {e | Cent E φ e} := by
  have hP := hS.pair
  have := Pair.finite hP
  have hsub : {e | Cent E φ e} ⊆ muSet E p q := fun m hm =>
    ⟨mem_localClass_of_mem_ySet hp hm, mem_localClass_of_mem_ySet hq hm⟩
  have hnc : p * q ≠ q * p := by
    intro h
    have h1 := hc.ncard_inter_lt hS hp.1 ⟨hq.1, Ne.symm hpq, h.symm⟩
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  refine ⟨hnc, ?_⟩
  have h1 := hS.ncard_muSet_eq (hc.plane.mem 0) (hc.plane.mem r₁)
    (hc.plane.ncomm 0 r₁ (Ne.symm hc.ne₁)) hp.1 hq.1 hnc
  rw [hc.muSet_eq hS (Ne.symm hc.ne₁)] at h1
  have heq : {e | Cent E φ e} = muSet E p q :=
    Set.eq_of_subset_of_ncard_le hsub h1.le (Set.toFinite _)
  intro e he
  rw [heq]
  exact he

theorem not_commute_of_not_cent {z : X} {p₀ : Pt} (hz : z ∈ LocalClass E (φ p₀))
    (hzM : ¬ Cent E φ z) {m : X} (hm : Cent E φ m) {s : Pt} (hs : s ≠ 0)
    (hst : s ∈ typ E φ m) : z * m ≠ m * z := by
  intro h
  have hP := hS.pair
  have hzπ : ∀ q, z ≠ φ q := by
    intro q hq
    rw [hq] at hz
    exact hc.plane.ncomm q p₀ (fun h' => hz.2.1 (by rw [h'])) hz.2.2
  have hzm : z ∈ LocalClass E m := ⟨hz.1, fun h' => hzM (h' ▸ hm), h⟩
  have hzs := hc.plane.commute_add hP hm hzm hzπ (q := p₀ + s) hz.2.2
    (by rw [add_sub_cancel_left_pt]; exact hst)
  have hne : p₀ ≠ p₀ + s := fun h' => hs (eq_zero_of_add_eq_pt p₀ s h'.symm)
  exact hzM (hc.cent_of_mem_muSet hS hne ⟨hz, hz.1, hzπ _, hzs⟩)

theorem exists_big : ∃ U : Set X, (∀ m ∈ U, Cent E φ m ∧ ∃ s ≠ 0, s ∈ typ E φ m) ∧
    {e | IsWit E e (φ 0) (φ r₁)}.ncard < U.ncard := by
  have hP := hS.pair
  have := Pair.finite hP
  obtain ⟨s₁, s₂, s₃, h1, h2, h3, h1r, h2r, h3r, h21, h31, h32⟩ :=
    exists_three_other_dirs r₁ hc.ne₁
  refine ⟨part E φ r₁ ∪ (part E φ s₁ ∪ (part E φ s₂ ∪ (part E φ s₃ ∪ top E φ))), ?_, ?_⟩
  · have hl : ∀ {r : Pt} {m : X}, r ≠ 0 → m ∈ part E φ r →
        Cent E φ m ∧ ∃ s ≠ 0, s ∈ typ E φ m := fun hr hm =>
      ⟨hm.1, _, hr, by rw [hm.2]; exact Or.inr (Or.inl rfl)⟩
    rintro m (hm | hm | hm | hm | hm)
    · exact hl hc.ne₁ hm
    · exact hl h1 hm
    · exact hl h2 hm
    · exact hl h3 hm
    · exact ⟨hm.1, r₁, hc.ne₁, by rw [hm.2]; exact Set.mem_univ _⟩
  · rw [hc.ncard_wit_eq_add hP hc.ne₁,
      Set.ncard_union_eq (Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h1r,
        Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h2r, Set.disjoint_union_right.2
          ⟨disjoint_part_part E φ h3r, disjoint_part_top E φ r₁⟩⟩⟩),
      Set.ncard_union_eq (Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h21,
        Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h31, disjoint_part_top E φ s₁⟩⟩),
      Set.ncard_union_eq (Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h32,
        disjoint_part_top E φ s₂⟩),
      Set.ncard_union_eq (disjoint_part_top E φ s₃), hc.ncard_part_eq hS hc.ne₁ h1,
      hc.ncard_part_eq hS hc.ne₁ h2, hc.ncard_part_eq hS hc.ne₁ h3]
    have := (Set.ncard_pos (Set.toFinite _)).2 (hc.part_nonempty hS hc.ne₁)
    omega

theorem commute_of_mem_fib_of_ne_zero {w : X} (hw : Cent E φ w) {p₀ s : Pt} (hs : s ≠ 0)
    (hst : s ∈ typ E φ w) {y : X} (hy : y ∈ fib E w (φ p₀)) (hyx : y ≠ φ p₀) {m : X}
    (hm : Cent E φ m) : y * m = m * y := by
  have hP := hS.pair
  have := Pair.finite hP
  have hxw : φ p₀ ∈ LocalClass E w := hw.2 p₀
  have hyw : y ∈ LocalClass E w := Pair.mem_localClass_of_mem_fib hP hxw hy
  have hxy : φ p₀ * y ≠ y * φ p₀ := Pair.not_commute_of_mem_fib hP (hc.plane.mem p₀) hy hyx
  by_contra hym
  set M := {e | Cent E φ e}
  set Λ := LocalClass E w ∩ LocalClass E (φ p₀)
  have hΛM : Λ ⊆ M := hc.inter_subset_cent hS hw hs hst
  have hwmu : w ∈ muSet E (φ p₀) y :=
    ⟨mem_localClass_symm hw.1 hxw, mem_localClass_symm hw.1 hyw⟩
  have hwW : IsWit E w (φ p₀) y := ⟨hwmu, hy.2⟩
  have hΛmu : Λ ⊆ muSet E (φ p₀) y := by
    rintro c ⟨hcw, hcx⟩
    have hcy : c * y = y * c := Pair.commute_of_mem_fib hP hcw hxw hcx.2.1 hcx.2.2 hy
    refine ⟨hcx, hcx.1, fun h => ?_, hcy⟩
    rw [h] at hcx
    exact hxy hcx.2.2.symm
  have hmuM : (muSet E (φ p₀) y).ncard = M.ncard := by
    rw [hS.ncard_muSet_eq (hc.plane.mem 0) (hc.plane.mem r₁)
      (hc.plane.ncomm 0 r₁ (Ne.symm hc.ne₁)) (hc.plane.mem p₀) hy.1 hxy,
      hc.muSet_eq hS (Ne.symm hc.ne₁)]
  obtain ⟨z, hzmu, hzM⟩ : ∃ z ∈ muSet E (φ p₀) y, z ∉ M := by
    by_contra! hall
    have heq := Set.eq_of_subset_of_ncard_le (fun z hz => hall z hz) hmuM.ge (Set.toFinite M)
    have hmmu : m ∈ muSet E (φ p₀) y := heq ▸ hm
    exact hym hmmu.2.2.2.symm
  have hzw : w * z ≠ z * w := fun h =>
    hzM (hΛM ⟨⟨hzmu.1.1, fun h' => hzM (h' ▸ hw), h.symm⟩, hzmu.1⟩)
  have hzW : IsWit E z (φ p₀) y := Pair.isWit_of_not_commute hP hwW hzmu hzw
  obtain ⟨U, hU, hUW⟩ := hc.exists_big hS
  have hUw : ∀ u ∈ U, u ∈ LocalClass E w → IsWit E u (φ p₀) y := by
    intro u hu huw
    obtain ⟨hcu, s', hs', hs't⟩ := hU u hu
    have hzu := hc.not_commute_of_not_cent hS hzmu.1 hzM hcu hs' hs't
    exact Pair.isWit_of_not_commute hP hzW (hΛmu ⟨huw, mem_localClass_symm hcu.1 (hcu.2 p₀)⟩)
      hzu
  set I := insert w Λ
  have hIM : I ⊆ M := Set.insert_subset hw hΛM
  have hImu : I ⊆ muSet E (φ p₀) y := Set.insert_subset hwmu hΛmu
  have hTW : ∀ c ∈ muSet E (φ p₀) y \ I, IsWit E c (φ p₀) y := by
    rintro c ⟨hc1, hc2⟩
    refine Pair.isWit_of_not_commute hP hwW hc1 fun h => hc2 (Or.inr ⟨⟨hc1.1.1,
      fun h' => hc2 (Or.inl h'), h.symm⟩, hc1.1⟩)
  have hW := hS.ncard_wit_eq (hc.plane.mem 0) (hc.plane.mem r₁)
    (hc.plane.ncomm 0 r₁ (Ne.symm hc.ne₁)) (hc.plane.mem p₀) hy.1 hxy
  have hsub : insert w ((muSet E (φ p₀) y \ I) ∪ (U ∩ LocalClass E w)) ⊆
      {e | IsWit E e (φ p₀) y} := by
    rintro c (rfl | hc1 | ⟨hcU, hcw⟩)
    · exact hwW
    · exact hTW c hc1
    · exact hUw c hcU hcw
  have hcard1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hwT : w ∉ (muSet E (φ p₀) y \ I) ∪ (U ∩ LocalClass E w) := by
    rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact h (Set.mem_insert w Λ)
    · exact h.2.1 rfl
  have hdisj : Disjoint (muSet E (φ p₀) y \ I) (U ∩ LocalClass E w) := by
    rw [Set.disjoint_left]
    rintro c ⟨hc1, hc2⟩ ⟨-, hcw⟩
    exact hc2 (Or.inr ⟨hcw, hc1.1⟩)
  rw [Set.ncard_insert_of_notMem hwT, Set.ncard_union_eq hdisj, Set.ncard_sdiff hImu,
    hmuM] at hcard1
  have hUsub : U ⊆ insert w ((M \ I) ∪ (U ∩ LocalClass E w)) := by
    intro u hu
    by_cases huw : u = w
    · exact Or.inl huw
    by_cases huΛ : u ∈ LocalClass E w
    · exact Or.inr (Or.inr ⟨hu, huΛ⟩)
    · refine Or.inr (Or.inl ⟨(hU u hu).1, ?_⟩)
      rintro (h | h)
      · exact huw h
      · exact huΛ h.1
  have hcard2 := Set.ncard_le_ncard hUsub (Set.toFinite _)
  have hcard3 := Set.ncard_insert_le w ((M \ I) ∪ (U ∩ LocalClass E w))
  have hcard4 := Set.ncard_union_le (M \ I) (U ∩ LocalClass E w)
  rw [Set.ncard_sdiff hIM] at hcard4
  omega

theorem commute_of_mem_fib_of_typ_zero {w : X} (hw : Cent E φ w) (hw0 : typ E φ w = {0})
    {p₀ : Pt} {y : X} (hy : y ∈ fib E w (φ p₀)) (hyx : y ≠ φ p₀) {m : X}
    (hm : Cent E φ m) : y * m = m * y := by
  have hP := hS.pair
  have := Pair.finite hP
  have hxw : φ p₀ ∈ LocalClass E w := hw.2 p₀
  have hyw : y ∈ LocalClass E w := Pair.mem_localClass_of_mem_fib hP hxw hy
  have hxy : φ p₀ * y ≠ y * φ p₀ := Pair.not_commute_of_mem_fib hP (hc.plane.mem p₀) hy hyx
  have hqy : ∀ q, q ≠ p₀ → φ q * y ≠ y * φ q := by
    intro q hq h
    have hqne : φ q ≠ y := by
      intro h'
      have h1 : q - p₀ ∈ typ E φ w := (hc.plane.fib_iff hP hw p₀ q).1 (h' ▸ hy)
      rw [hw0] at h1
      exact hq (eq_of_sub_eq_zero_pt p₀ q h1)
    exact hc.plane.ncomm q p₀ hq (Pair.commute_of_mem_fib hP (hw.2 q) hyw hqne h
      (Pair.fib_symm hP (hc.plane.mem p₀) hy))
  obtain ⟨U, hU, hUW⟩ := hc.exists_big hS
  have hUmu : ∀ u ∈ U, u ∈ muSet E (φ p₀) y := by
    intro u hu
    obtain ⟨hcu, s, hs, hst⟩ := hU u hu
    have huw : u ∈ LocalClass E w := hc.mem_localClass_of_typ_ne hS hcu hw fun h => by
      rw [h, hw0] at hst
      exact hs hst
    have hux : u ∈ LocalClass E (φ p₀) := mem_localClass_symm hcu.1 (hcu.2 p₀)
    refine ⟨hux, hux.1, fun h => hxy (by rw [← h]; exact hux.2.2.symm),
      Pair.commute_of_mem_fib hP huw hxw hux.2.1 hux.2.2 hy⟩
  obtain ⟨u, hu, hnu⟩ : ∃ u ∈ U, ¬ IsWit E u (φ p₀) y := by
    by_contra! hall
    have hsub : U ⊆ {e | IsWit E e (φ p₀) y} := fun u hu => hall u hu
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hW := hS.ncard_wit_eq (hc.plane.mem 0) (hc.plane.mem r₁)
      (hc.plane.ncomm 0 r₁ (Ne.symm hc.ne₁)) (hc.plane.mem p₀) hy.1 hxy
    omega
  have hyu : y ∉ fib E u (φ p₀) := fun h => hnu ⟨hUmu u hu, h.2⟩
  obtain ⟨hcu, s, hs, hst⟩ := hU u hu
  have hne1 : p₀ + s ≠ p₀ := fun h => hs (eq_zero_of_add_eq_pt p₀ s h)
  have hxx₁ : φ p₀ * φ (p₀ + s) ≠ φ (p₀ + s) * φ p₀ := hc.plane.ncomm p₀ _ (Ne.symm hne1)
  have hx₁y : φ (p₀ + s) * y ≠ y * φ (p₀ + s) := hqy _ hne1
  have hyl : y * (φ p₀ * φ (p₀ + s) * φ p₀) ≠ φ p₀ * φ (p₀ + s) * φ p₀ * y := by
    rw [hc.plane.tau (p₀ + s) p₀]
    exact fun h => hqy _ (neg_add_sub_ne_pt p₀ s hs) h.symm
  have hx := hc.plane.mem p₀
  have hx₁ := hc.plane.mem (p₀ + s)
  have hπ := isPlane_planePt hP hx hx₁ hy.1 hxx₁ hxy hx₁y hyl
  have h0 : planePt (φ p₀) (φ (p₀ + s)) y 0 = φ p₀ := planePt_zero
  have h10 : planePt (φ p₀) (φ (p₀ + s)) y (1, 0) = φ (p₀ + s) :=
    planePt_one_zero hP hx hx₁ hxx₁
  have h01 : planePt (φ p₀) (φ (p₀ + s)) y (0, 1) = y := planePt_zero_one hP hx hy.1 hxy
  have hcw : Cent E (planePt (φ p₀) (φ (p₀ + s)) y) w := hπ.cent_of_commute hw.1
    (commute_planePt hP hx hx₁ hy.1 hxx₁ hxy hx₁y hyl (hw.2 p₀).2.2.symm
      (hw.2 (p₀ + s)).2.2.symm hyw.2.2.symm)
  have hcu' : Cent E (planePt (φ p₀) (φ (p₀ + s)) y) u := hπ.cent_of_commute hcu.1
    (commute_planePt hP hx hx₁ hy.1 hxx₁ hxy hx₁y hyl (hcu.2 p₀).2.2.symm
      (hcu.2 (p₀ + s)).2.2.symm (hUmu u hu).2.2.2)
  have htw : typ E (planePt (φ p₀) (φ (p₀ + s)) y) w = lineSet (0, 1) := by
    refine hπ.typ_eq_line hP hcw (s := (1, 0)) (by decide) ?_ ?_
    · change planePt (φ p₀) (φ (p₀ + s)) y (0, 1) ∈
        fib E w (planePt (φ p₀) (φ (p₀ + s)) y 0)
      rw [h01, h0]
      exact hy
    · intro h
      change planePt (φ p₀) (φ (p₀ + s)) y (1, 0) ∈
        fib E w (planePt (φ p₀) (φ (p₀ + s)) y 0) at h
      rw [h10, h0] at h
      have h1 : p₀ + s - p₀ ∈ typ E φ w := (hc.plane.fib_iff hP hw p₀ (p₀ + s)).1 h
      rw [add_sub_cancel_left_pt, hw0] at h1
      exact hs h1
  have htu : typ E (planePt (φ p₀) (φ (p₀ + s)) y) u = lineSet (1, 0) := by
    refine hπ.typ_eq_line hP hcu' (s := (0, 1)) (by decide) ?_ ?_
    · change planePt (φ p₀) (φ (p₀ + s)) y (1, 0) ∈
        fib E u (planePt (φ p₀) (φ (p₀ + s)) y 0)
      rw [h10, h0]
      exact (hc.plane.fib_iff hP hcu p₀ (p₀ + s)).2 (by rw [add_sub_cancel_left_pt]; exact hst)
    · intro h
      change planePt (φ p₀) (φ (p₀ + s)) y (0, 1) ∈
        fib E u (planePt (φ p₀) (φ (p₀ + s)) y 0) at h
      rw [h01, h0] at h
      exact hyu h
  have hconf : ConfAt E (planePt (φ p₀) (φ (p₀ + s)) y) u w (1, 0) (0, 1) :=
    ⟨hπ, hcu', hcw, by decide, by decide, htu, htw, by
      change ¬ (((0, 1) : Pt) = 0 ∨ ((0, 1) : Pt) = (1, 0) ∨ ((0, 1) : Pt) = (1, 0) + (1, 0))
      decide⟩
  have hmmu : m ∈ muSet E (planePt (φ p₀) (φ (p₀ + s)) y 0)
      (planePt (φ p₀) (φ (p₀ + s)) y (1, 0)) := by
    rw [h0, h10]
    exact ⟨mem_localClass_symm hm.1 (hm.2 p₀), mem_localClass_symm hm.1 (hm.2 (p₀ + s))⟩
  have hcm := hconf.cent_of_mem_muSet hS (p := 0) (q := (1, 0)) (by decide) hmmu
  have h1 := (hcm.2 (0, 1)).2.2
  rw [h01] at h1
  exact h1

theorem fib_subset_ySet {w : X} (hw : Cent E φ w) (p₀ : Pt) : fib E w (φ p₀) ⊆ ySet E φ := by
  intro y hy
  by_cases hyx : y = φ p₀
  · rw [hyx]
    exact hc.plane.mem_ySet p₀
  have hP := hS.pair
  have hxy : φ p₀ * y ≠ y * φ p₀ := Pair.not_commute_of_mem_fib hP (hc.plane.mem p₀) hy hyx
  refine ⟨hy.1, fun h => hxy (h.2 p₀).2.2, fun m hm => ?_⟩
  rcases hc.plane.typ_cases hP hw with h0 | h1 | ⟨r, hr, hl⟩
  · exact hc.commute_of_mem_fib_of_typ_zero hS hw h0 hy hyx hm
  · exact hc.commute_of_mem_fib_of_ne_zero hS hw hc.ne₁ (by rw [h1]; exact Set.mem_univ _) hy
      hyx hm
  · exact hc.commute_of_mem_fib_of_ne_zero hS hw hr (by rw [hl]; exact Or.inr (Or.inl rfl)) hy
      hyx hm

theorem false : False := by
  have hP := hS.pair
  have := Pair.finite hP
  refine hS.false_of_ySet (M := {e | Cent E φ e}) (hc.plane.mem_ySet 0) (hc.plane.mem_ySet r₁)
    (fun h => hc.ne₁ (hc.plane.inj h).symm)
    (fun p hp => ⟨hp.1, fun m hm => mem_localClass_of_mem_ySet hp hm⟩)
    (fun p hp q hq hpq => hc.ySet_pairwise hS hp hq hpq) (fun w hw => hc.fib_subset_ySet hS hw 0)
    ((Set.one_lt_ncard_iff (Set.toFinite _)).2 ⟨w₁, w₂, hc.cent₁, hc.cent₂, fun h => ?_⟩)
  have h1 := hc.typ₂
  rw [← h, hc.typ₁] at h1
  have h2 : r₂ ∈ lineSet r₂ := Or.inr (Or.inl rfl)
  rw [← h1] at h2
  exact hc.dist h2

end ConfAt

end O3

end CFSG.Fischer.Classification
