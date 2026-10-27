module

public import CFSG.Fischer.Classification.PartII.O3.Conf
public import CFSG.Fischer.Classification.PartII.O3.Trans

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

theorem ne_add_one_zero_pt : ∀ p : Pt, p ≠ p + (1, 0) := by decide

namespace IsPlane

variable {φ : Pt → X} (hπ : IsPlane E φ) (hP : Pair X E)
include hπ hP

omit hP in
theorem cent_of_commute {v : X} (hv : v ∈ E) (hc : ∀ p, v * φ p = φ p * v) : Cent E φ v := by
  refine ⟨hv, fun p => ⟨hπ.mem p, fun h => ?_, (hc p).symm⟩⟩
  apply hπ.ncomm p (p + (1, 0)) (ne_add_one_zero_pt p)
  rw [h]
  exact hc _

theorem typ_eq_line {v : X} (hv : Cent E φ v) {r s : Pt} (hr : r ≠ 0) (hrin : r ∈ typ E φ v)
    (hs : s ∉ typ E φ v) : typ E φ v = lineSet r := by
  rcases hπ.typ_cases hP hv with h | h | ⟨r', hr', h⟩
  · rw [h] at hrin
    exact absurd hrin hr
  · rw [h] at hs
    exact absurd (Set.mem_univ s) hs
  · rw [h] at hrin ⊢
    ext x
    exact line_eq_pt r r' x hr hrin

end IsPlane

theorem commute_planePt (hP : Pair X E) {d e z v : X} (hd : d ∈ E) (he : e ∈ E) (hz : z ∈ E)
    (hde : d * e ≠ e * d) (hdz : d * z ≠ z * d) (hez : e * z ≠ z * e)
    (hzl : z * (d * e * d) ≠ d * e * d * z) (hvd : v * d = d * v) (hve : v * e = e * v)
    (hvz : v * z = z * v) (p : Pt) : v * planePt d e z p = planePt d e z p * v := by
  have hmem : planePt d e z p ∈ (Subgroup.closure ({d, e, z} : Set X) : Set X) :=
    ((range_planePt hP hd he hz hde hdz hez hzl) ▸ Set.mem_range_self p).2
  have hle : Subgroup.closure ({d, e, z} : Set X) ≤ Subgroup.centralizer ({v} : Set X) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hvd.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hve.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hvz.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)).symm

theorem exists_two_other_dirs : ∀ r : Pt, r ≠ 0 → ∃ r' r'' : Pt, r' ≠ 0 ∧ r'' ≠ 0 ∧
    ¬ (r' = 0 ∨ r' = r ∨ r' = r + r) ∧ ¬ (r'' = 0 ∨ r'' = r ∨ r'' = r + r) ∧
    ¬ (r'' = 0 ∨ r'' = r' ∨ r'' = r' + r') := by
  decide

theorem noncollinear_pt : ∀ p r' r'' : Pt, r' ≠ 0 → ¬ (r'' = 0 ∨ r'' = r' ∨ r'' = r' + r') →
    p + r' ≠ p ∧ p + r'' ≠ p ∧ p + r'' ≠ p + r' ∧ p + r'' ≠ -p - (p + r') := by
  decide +kernel

theorem line_ne_univ_pt : ∀ r : Pt, ∃ x : Pt, ¬ (x = 0 ∨ x = r ∨ x = r + r) := by decide

namespace Setting

variable (hS : Setting X E)
include hS

theorem exists_confAt_of_nonwit {a b w v : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b ≠ b * a)
    (hw : IsWit E w a b) (hv : v ∈ muSet E a b) (hnv : ¬ IsWit E v a b) :
    ∃ y, y ∈ fib E v a ∧ y ∉ fib E w a ∧ a * y ≠ y * a ∧ b * y ≠ y * b ∧
      y * (a * b * a) ≠ a * b * a * y ∧ ConfAt E (planePt a b y) w v (1, 0) (0, 1) := by
  have hP := hS.pair
  obtain ⟨y, hy, hyw, hyW, hay, hby, hyl⟩ := hS.exists_affine ha hb hw hv hnv
  have hπ := isPlane_planePt hP ha hb hy.1 hab hay hby hyl
  have h0 : planePt a b y 0 = a := planePt_zero
  have h10 : planePt a b y (1, 0) = b := planePt_one_zero hP ha hb hab
  have h01 : planePt a b y (0, 1) = y := planePt_zero_one hP ha hy.1 hay
  have hyV : y ∈ LocalClass E v := Pair.mem_localClass_of_mem_fib hP
    (mem_localClass_symm ha hv.1) hy
  have hcw : Cent E (planePt a b y) w := hπ.cent_of_commute hw.1.1.1
    (commute_planePt hP ha hb hy.1 hab hay hby hyl hw.1.1.2.2 hw.1.2.2.2 hyW.2.2.symm)
  have hcv : Cent E (planePt a b y) v := hπ.cent_of_commute hv.1.1
    (commute_planePt hP ha hb hy.1 hab hay hby hyl hv.1.2.2 hv.2.2.2 hyV.2.2.symm)
  refine ⟨y, hy, hyw, hay, hby, hyl, hπ, hcw, hcv, by decide, by decide, ?_, ?_, ?_⟩
  · refine hπ.typ_eq_line hP hcw (s := (0, 1)) (by decide) ?_ ?_
    · change planePt a b y (1, 0) ∈ fib E w (planePt a b y 0)
      rw [h10, h0]
      exact ⟨hb, hw.2⟩
    · intro h
      change planePt a b y (0, 1) ∈ fib E w (planePt a b y 0) at h
      rw [h01, h0] at h
      exact hyw h
  · refine hπ.typ_eq_line hP hcv (s := (1, 0)) (by decide) ?_ ?_
    · change planePt a b y (0, 1) ∈ fib E v (planePt a b y 0)
      rw [h01, h0]
      exact hy
    · intro h
      change planePt a b y (1, 0) ∈ fib E v (planePt a b y 0) at h
      rw [h10, h0] at h
      exact hnv ⟨hv, h.2⟩
  · change ¬ (((0, 1) : Pt) = 0 ∨ ((0, 1) : Pt) = (1, 0) ∨ ((0, 1) : Pt) = (1, 0) + (1, 0))
    decide

end Setting

namespace ConfAt

variable {φ : Pt → X} {w₁ w₂ : X} {r₁ r₂ : Pt} (hc : ConfAt E φ w₁ w₂ r₁ r₂) (hS : Setting X E)
include hc hS

theorem mem_localClass_of_typ_ne {e e' : X} (he : Cent E φ e) (he' : Cent E φ e')
    (h : typ E φ e ≠ typ E φ e') : e ∈ LocalClass E e' := by
  have hP := hS.pair
  refine ⟨he.1, fun h' => h (h' ▸ rfl), ?_⟩
  by_contra hne
  exact h (hc.plane.typ_eq_of_not_commute hP he he' hne)

omit hc hS in
theorem typ_ne_of_not_mem {e e' : X} {r r' : Pt} (he : e ∈ part E φ r) (he' : e' ∈ part E φ r')
    (h : r' ∉ lineSet r) : typ E φ e ≠ typ E φ e' := by
  rw [he.2, he'.2]
  intro heq
  have : r' ∈ lineSet r' := Or.inr (Or.inl rfl)
  rw [← heq] at this
  exact h this

theorem fib_subset_part {p₀ r : Pt} (hr : r ≠ 0) {e : X} (he : e ∈ part E φ r) :
    fib E (φ p₀) e ⊆ part E φ r := by
  intro y hy
  have hP := hS.pair
  obtain ⟨r', r'', hr', hr'', h1, h2, h3⟩ := exists_two_other_dirs r hr
  obtain ⟨e', he'⟩ := hc.part_nonempty hS hr'
  obtain ⟨e'', he''⟩ := hc.part_nonempty hS hr''
  have hee' := hc.mem_localClass_of_typ_ne hS he.1 he'.1 (typ_ne_of_not_mem he he' h1)
  have hee'' := hc.mem_localClass_of_typ_ne hS he.1 he''.1 (typ_ne_of_not_mem he he'' h2)
  have hxe : e ∈ LocalClass E (φ p₀) := mem_localClass_symm he.1.1 (he.1.2 p₀)
  have hxe' : e' ∈ LocalClass E (φ p₀) := mem_localClass_symm he'.1.1 (he'.1.2 p₀)
  have hxe'' : e'' ∈ LocalClass E (φ p₀) := mem_localClass_symm he''.1.1 (he''.1.2 p₀)
  have hyD : y ∈ LocalClass E (φ p₀) := Pair.mem_localClass_of_mem_fib hP hxe hy
  have hy' : y ∈ LocalClass E e' := Pair.mem_localClass_of_mem_fib_of_mem hP hxe' hxe hee' hy
  have hy'' : y ∈ LocalClass E e'' :=
    Pair.mem_localClass_of_mem_fib_of_mem hP hxe'' hxe hee'' hy
  have hyπ : ∀ q, y ≠ φ q := by
    intro q hq
    rw [hq] at hyD
    exact hc.plane.ncomm q p₀ (fun h => hyD.2.1 (by rw [h])) hyD.2.2
  have hyp : y * φ p₀ = φ p₀ * y := hyD.2.2
  have hm' : p₀ + r' - p₀ ∈ typ E φ e' := by
    rw [add_sub_cancel_left_pt, he'.2]
    exact Or.inr (Or.inl rfl)
  have hm'' : p₀ + r'' - p₀ ∈ typ E φ e'' := by
    rw [add_sub_cancel_left_pt, he''.2]
    exact Or.inr (Or.inl rfl)
  have hya : y * φ (p₀ + r') = φ (p₀ + r') * y :=
    hc.plane.commute_add hP he'.1 hy' hyπ hyp hm'
  have hyb : y * φ (p₀ + r'') = φ (p₀ + r'') * y :=
    hc.plane.commute_add hP he''.1 hy'' hyπ hyp hm''
  obtain ⟨n1, n2, n3, n4⟩ := noncollinear_pt p₀ r' r'' hr' h3
  have huniv := hc.plane.isTauClosed_commute.eq_univ_of_not_collinear hyp hya hyb n1 n2 n3 n4
  have hcy : Cent E φ y := hc.plane.cent_of_commute hy.1 fun q =>
    (huniv ▸ Set.mem_univ q : q ∈ {q | y * φ q = φ q * y})
  refine ⟨hcy, ?_⟩
  by_cases hye : y = e
  · rw [hye]
    exact he.2
  · rw [hc.plane.typ_eq_of_not_commute hP hcy he.1
      fun h => Pair.not_commute_of_mem_fib hP he.1.1 hy hye h.symm]
    exact he.2

theorem fib_eq_fib {p₀ p₁ r : Pt} (hr : r ≠ 0) {e : X} (he : e ∈ part E φ r) :
    fib E (φ p₁) e = fib E (φ p₀) e := by
  have hP := hS.pair
  have := Pair.finite hP
  by_cases hp : p₀ = p₁
  · rw [hp]
  have hsub : fib E (φ p₀) e ⊆ fib E (φ p₁) e :=
    Pair.fib_subset_of_commute hP (hc.plane.mem p₀) (hc.plane.mem p₁) (hc.plane.ncomm p₀ p₁ hp)
      (fun y hy => ((hc.fib_subset_part hS hr he hy).1.2 p₁).2.2.symm) he.1.1
  have hxe : e ∈ LocalClass E (φ p₀) := mem_localClass_symm he.1.1 (he.1.2 p₀)
  have hxe1 : e ∈ LocalClass E (φ p₁) := mem_localClass_symm he.1.1 (he.1.2 p₁)
  exact (Set.eq_of_subset_of_ncard_le hsub (Pair.ncard_fib_eq hP hS.hyp.center hS.hyp.simple
    (hc.plane.mem p₀) hxe (hc.plane.mem p₁) hxe1).le).symm

theorem isWit_of_mem_fib {p₀ r : Pt} (hr : r ≠ 0) {e e' : X} (he : e ∈ part E φ r)
    (he' : e' ∈ fib E (φ p₀) e) (p : Pt) : IsWit E (φ p) e e' := by
  have he'' := hc.fib_subset_part hS hr he he'
  refine ⟨⟨he.1.2 p, he''.1.2 p⟩, ?_⟩
  have h := hc.fib_eq_fib hS (p₀ := p₀) (p₁ := p) hr he
  exact (h ▸ he' : e' ∈ fib E (φ p) e).2

end ConfAt

omit [Group X] in
theorem ncard_range_pt {φ : Pt → X} (hinj : Function.Injective φ) : (Set.range φ).ncard = 9 := by
  rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  rfl

namespace ConfAt

variable {φ : Pt → X} {w₁ w₂ : X} {r₁ r₂ : Pt} (hc : ConfAt E φ w₁ w₂ r₁ r₂) (hS : Setting X E)
include hc hS

theorem mem_localClass_of_part {r r' : Pt} (hrr : r' ∉ lineSet r) {e u : X}
    (he : e ∈ part E φ r) (hu : u ∈ part E φ r' ∪ top E φ) : u ∈ LocalClass E e := by
  rcases hu with hu | hu
  · exact hc.mem_localClass_of_typ_ne hS hu.1 he.1 (typ_ne_of_not_mem he hu hrr).symm
  · refine hc.mem_localClass_of_typ_ne hS hu.1 he.1 ?_
    rw [hu.2, he.2]
    intro h
    obtain ⟨x, hx⟩ := line_ne_univ_pt r
    have hxr : x ∈ lineSet r := by
      rw [← h]
      exact Set.mem_univ x
    exact hx hxr

theorem exists_nonwit_part {p₀ r r' : Pt} (hr : r ≠ 0) (hr' : r' ≠ 0) (hrr : r' ∉ lineSet r)
    {e e' : X} (he : e ∈ part E φ r) (he' : e' ∈ fib E (φ p₀) e) (hee : e' ≠ e) :
    ∃ u ∈ part E φ r' ∪ top E φ, u ∈ muSet E e e' ∧ ¬ IsWit E u e e' := by
  have hP := hS.pair
  have := Pair.finite hP
  have he'P := hc.fib_subset_part hS hr he he'
  have hsub : part E φ r' ∪ top E φ ⊆ muSet E e e' := fun u hu =>
    ⟨hc.mem_localClass_of_part hS hrr he hu, hc.mem_localClass_of_part hS hrr he'P hu⟩
  by_contra! hall
  set W := {u | IsWit E u e e'}
  have hW1 : Set.range φ ⊆ W := by
    rintro _ ⟨p, rfl⟩
    exact hc.isWit_of_mem_fib hS hr he he' p
  have hW2 : part E φ r' ∪ top E φ ⊆ W := fun u hu => hall u hu (hsub hu)
  have hdisj : Disjoint (Set.range φ) (part E φ r' ∪ top E φ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ hu
    have hcu : Cent E φ (φ p) := by
      rcases hu with hu | hu
      · exact hu.1
      · exact hu.1
    exact IsPlane.ne_of_cent hcu p rfl
  have hle := Set.ncard_le_ncard (Set.union_subset hW1 hW2) (Set.toFinite W)
  rw [Set.ncard_union_eq hdisj, ncard_range_pt hc.plane.inj,
    Set.ncard_union_eq (disjoint_part_top E φ r')] at hle
  have hee' : e * e' ≠ e' * e := Pair.not_commute_of_mem_fib hP he.1.1 he' hee
  have h1 : W.ncard = (part E φ r').ncard + (top E φ).ncard := by
    rw [← hc.ncard_wit_eq_add hS.pair hr']
    exact hS.ncard_wit_eq (hc.plane.mem 0) (hc.plane.mem r')
      (hc.plane.ncomm 0 r' (Ne.symm hr')) he.1.1 he'.1 hee'
  omega

theorem exists_ne_mem_fib {p₀ : Pt} {e : X} (he : Cent E φ e) :
    ∃ e' ∈ fib E (φ p₀) e, e' ≠ e := by
  have hP := hS.pair
  have := Pair.finite hP
  obtain ⟨d, hd, -⟩ := hS.move
  obtain ⟨x, hx, y, hy, hyx⟩ := hS.exists_fib_pair hd
  have hxe : e ∈ LocalClass E (φ p₀) := mem_localClass_symm he.1 (he.2 p₀)
  have h2 : 1 < (fib E (φ p₀) e).ncard := by
    rw [Pair.ncard_fib_eq hP hS.hyp.center hS.hyp.simple hd hx (hc.plane.mem p₀) hxe]
    have hsub : ({x, y} : Set X) ⊆ fib E d x := by
      rintro z (rfl | rfl)
      · exact Pair.mem_fib_self hP hx.1
      · exact hy
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm hyx)] at this
    omega
  exact Set.exists_ne_of_one_lt_ncard h2 e

theorem exists_dual {p₀ r r' : Pt} (hr : r ≠ 0) (hr' : r' ≠ 0) (hrr : r' ∉ lineSet r) {e : X}
    (he : e ∈ part E φ r) :
    ∃ ψ : Pt → X, ∃ u ∈ part E φ r' ∪ top E φ, ConfAt E ψ (φ p₀) u (1, 0) (0, 1) ∧
      ∀ q, ψ q ∈ part E φ r := by
  have hP := hS.pair
  obtain ⟨e', he', hee⟩ := hc.exists_ne_mem_fib hS (p₀ := p₀) he.1
  have he'P := hc.fib_subset_part hS hr he he'
  obtain ⟨u, hu, humu, hnu⟩ := hc.exists_nonwit_part hS hr hr' hrr he he' hee
  have hee' : e * e' ≠ e' * e := Pair.not_commute_of_mem_fib hP he.1.1 he' hee
  have hw : IsWit E (φ p₀) e e' := hc.isWit_of_mem_fib hS hr he he' p₀
  obtain ⟨y', hy'u, -, hey', he'y', hyl, hconf⟩ :=
    hS.exists_confAt_of_nonwit he.1.1 he'.1 hee' hw humu hnu
  have hcu : Cent E φ u := by
    rcases hu with hu | hu
    · exact hu.1
    · exact hu.1
  have heu : e ∈ LocalClass E u :=
    mem_localClass_symm he.1.1 (hc.mem_localClass_of_part hS hrr he hu)
  refine ⟨planePt e e' y', u, hu, hconf, fun q' => ?_⟩
  have hcomm : ∀ q, planePt e e' y' q' * φ q = φ q * planePt e e' y' q' := by
    intro q
    have hy'q : y' ∈ LocalClass E (φ q) := Pair.mem_localClass_of_mem_fib_of_mem hP (hcu.2 q)
      heu (mem_localClass_symm he.1.1 (he.1.2 q)) hy'u
    exact (commute_planePt hP he.1.1 he'.1 hy'u.1 hee' hey' he'y' hyl (he.1.2 q).2.2
      (he'P.1.2 q).2.2 hy'q.2.2.symm q').symm
  have hcq : Cent E φ (planePt e e' y' q') := hc.plane.cent_of_commute (hconf.plane.mem q') hcomm
  refine ⟨hcq, ?_⟩
  by_cases hq : q' = 0
  · rw [hq, planePt_zero]
    exact he.2
  · have h0 : planePt e e' y' 0 = e := planePt_zero
    have hne := hconf.plane.ncomm q' 0 hq
    rw [h0] at hne
    rw [hc.plane.typ_eq_of_not_commute hP hcq he.1 hne]
    exact he.2

end ConfAt

end O3

end CFSG.Fischer.Classification
