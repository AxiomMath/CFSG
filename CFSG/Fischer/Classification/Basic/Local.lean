module

public import CFSG.Fischer.Classification.Basic.Transitivity
public import CFSG.Fischer.Classification.Uniqueness.Star

public section

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace CFSG.Fischer.Classification

variable {X : Type} [Group X] {E : Set X}

section LocalPair

theorem centralizerClass_eq {x : X} (hx : x ∈ E) :
    {w | w ∈ E ∧ w * x = x * w} = insert x (LocalClass E x) := by
  ext w
  constructor
  · rintro ⟨hw, hwx⟩
    by_cases h : w = x
    · exact Or.inl h
    · exact Or.inr ⟨hw, h, hwx⟩
  · rintro (rfl | hw)
    · exact ⟨hx, rfl⟩
    · exact ⟨hw.1, hw.2.2⟩

theorem Pair.exists_not_commute_of_mem_localClass (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d f : X} (hd : d ∈ E) (hf : f ∈ LocalClass E d) :
    ∃ g ∈ LocalClass E d, g * f ≠ f * g := by
  by_contra! hall
  have := Pair.finite hP
  have hfE := hf.1
  have hsub : {w | w ∈ E ∧ w * d = d * w} ⊆ {w | w ∈ E ∧ w * f = f * w} := by
    rw [centralizerClass_eq hd]
    rintro w (rfl | hw)
    · exact ⟨hd, hf.2.2.symm⟩
    · exact ⟨hw.1, hall w hw⟩
  have hcard : {w | w ∈ E ∧ w * f = f * w}.ncard ≤ {w | w ∈ E ∧ w * d = d * w}.ncard := by
    rw [centralizerClass_eq hd, centralizerClass_eq hfE,
      Set.ncard_insert_of_notMem (fun h => h.2.1 rfl) (Set.toFinite _),
      Set.ncard_insert_of_notMem (fun h => h.2.1 rfl) (Set.toFinite _),
      Pair.ncard_localClass_eq hP hfE hd]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  apply hf.2.1
  refine Pair.eq_of_forall_commute_iff hP hZ hS hfE hd fun w hw => ?_
  have h1 : w ∈ {w | w ∈ E ∧ w * d = d * w} ↔ w ∈ {w | w ∈ E ∧ w * f = f * w} := by rw [heq]
  exact ⟨fun h => (h1.2 ⟨hw, h⟩).2, fun h => (h1.1 ⟨hw, h⟩).2⟩

theorem Pair.starImage_injective_of_simple (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d : X} (hd : d ∈ E) :
    Function.Injective (starImage E d) :=
  Pair.starImage_injective hP fun _ hf => Pair.exists_not_commute_of_mem_localClass hP hZ hS hd hf

theorem Pair.starImage_ne_one (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d : X} (hd : d ∈ E) (f : LocalClass E d) :
    starImage E d f ≠ 1 := by
  rw [Ne, starImage_eq_one_iff]
  intro h
  obtain ⟨g, hg, hgf⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hd f.2
  exact hgf (h g hg)

theorem commute_of_mem_localGroup' {d h : X} (hh : h ∈ LocalGroup E d) : h * d = d * h :=
  commute_of_mem_localGroup (fun _ hg => hg.2.2) hh

theorem Pair.conj_mem_localClass_of_mem (hP : Pair X E) {d h f : X} (hh : h ∈ LocalGroup E d)
    (hf : f ∈ LocalClass E d) : h * f * h⁻¹ ∈ LocalClass E d := by
  have := (Pair.conj_mem_localClass_iff hP h).2 hf
  rwa [commute_of_mem_localGroup' hh, mul_inv_cancel_right] at this

theorem Pair.localClass_nonempty (hP : Pair X E) (hS : IsSimpleGroup (commutator X))
    (hna : ∃ a b : commutator X, a * b ≠ b * a) {d : X} (hd : d ∈ E) :
    (LocalClass E d).Nonempty := by
  obtain ⟨a, ha, b, hb, hab, habc⟩ := Pair.exists_ne_commute hP hS (not_forall_commute hna)
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd ha)
  refine ⟨g⁻¹ * b * g, ?_⟩
  rw [← Pair.conj_mem_localClass_iff hP g, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
  exact ⟨hb, fun h => hab h.symm, habc.symm⟩

theorem Pair.pair_localQuotient (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a) {d : X}
    (hd : d ∈ E) : Pair (LocalQuotient E d) (LocalImages E d) := by
  have := Pair.finite hP
  obtain ⟨f₀, hf₀⟩ := Pair.localClass_nonempty hP hS hna hd
  refine ⟨inferInstance, ⟨starImage E d ⟨f₀, hf₀⟩, ?_⟩, ?_, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨h, hh, hhf⟩ := Pair.exists_localGroup_conj hP hZ hS hd hf₀ hf
      refine isConj_iff.2 ⟨QuotientGroup.mk ⟨h, hh⟩, ?_⟩
      rw [starImage, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hhf
    · intro hq
      obtain ⟨c, rfl⟩ := isConj_iff.1 hq
      obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective c
      have hmem := Pair.conj_mem_localClass_of_mem hP hh hf₀
      refine ⟨⟨h * f₀ * h⁻¹, mem_localGroup hmem⟩, hmem, ?_⟩
      rw [starImage, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
  · rintro q ⟨f, hf, rfl⟩
    apply orderOf_eq_prime
    · rw [sq, ← QuotientGroup.mk_mul]
      have : f * f = 1 := Subtype.ext (Pair.mul_self hP hf.1)
      rw [this, QuotientGroup.mk_one]
    · have := Pair.starImage_ne_one hP hZ hS hd ⟨f, hf⟩
      exact this
  · rintro q₁ ⟨f, hf, rfl⟩ q₂ ⟨g, hg, rfl⟩
    have hmem := Pair.orderOf_mul_mem hP hf.1 hg.1
    have hdvd : orderOf (QuotientGroup.mk (s := Subgroup.center (LocalGroup E d)) f *
        QuotientGroup.mk g) ∣ orderOf ((f : X) * g) := by
      rw [← QuotientGroup.mk_mul, ← Subgroup.coe_mul, Subgroup.orderOf_coe]
      exact orderOf_map_dvd (QuotientGroup.mk' _) (f * g)
    have hpos : 0 < orderOf ((f : X) * g) := by
      rcases hmem with h | h | h <;> rw [h] <;> norm_num
    have hle : orderOf ((f : X) * g) ≤ 3 := by
      rcases hmem with h | h | h <;> rw [h] <;> norm_num
    have h1 := Nat.le_of_dvd hpos hdvd
    have h2 := Nat.pos_of_dvd_of_pos hdvd hpos
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · have hS' : LocalImages E d = (QuotientGroup.mk' (Subgroup.center (LocalGroup E d))) ''
        ((LocalGroup E d).subtype ⁻¹' LocalClass E d) := by
      ext q
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact ⟨f, hf, rfl⟩
      · rintro ⟨f, hf, rfl⟩
        exact ⟨f, hf, rfl⟩
    have htop : Subgroup.closure ((LocalGroup E d).subtype ⁻¹' LocalClass E d) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [hS', ← MonoidHom.map_closure, htop, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']

theorem Pair.center_localQuotient (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d : X} (hd : d ∈ E) :
    Subgroup.center (LocalQuotient E d) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have key : ∀ f ∈ LocalClass E d, f * (y : X) = (y : X) * f := by
    intro f hf
    have hfL := mem_localGroup hf
    have hfE := hf.1
    have hc := (Subgroup.mem_center_iff.1 hq) (QuotientGroup.mk ⟨f, hfL⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    have hzc : ∀ l ∈ LocalGroup E d, l * ((y : X)⁻¹ * f * y * f) = (y : X)⁻¹ * f * y * f * l := by
      intro l hl
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨l, hl⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev] at this
      rw [Pair.inv_eq hP hfE] at this
      simpa only [mul_assoc] using this
    have hw : (y : X)⁻¹ * f * y ∈ LocalClass E d := by
      have := Pair.conj_mem_localClass_of_mem hP (inv_mem y.2) hf
      rwa [inv_inv] at this
    by_contra hne
    have hz1 : (y : X)⁻¹ * f * y * f ≠ 1 := by
      intro h1
      apply hne
      have hwf : (y : X)⁻¹ * f * y = f := by
        rw [← mul_one ((y : X)⁻¹ * f * y), ← Pair.mul_self hP hfE, ← mul_assoc, h1, one_mul]
      calc f * (y : X) = y * ((y : X)⁻¹ * f * y) := by group
        _ = y * f := by rw [hwf]
    have hzf := hzc f hfL
    have hfw : f * ((y : X)⁻¹ * f * y) = (y : X)⁻¹ * f * y * f := by
      calc f * ((y : X)⁻¹ * f * y) = f * ((y : X)⁻¹ * f * y * f) * f := by
            simp only [mul_assoc, Pair.mul_self hP hfE, mul_one]
        _ = (y : X)⁻¹ * f * y * f * f * f := by rw [hzf]
        _ = (y : X)⁻¹ * f * y * f := by
            simp only [mul_assoc, Pair.mul_self hP hfE, mul_one]
    have hz2 : (y : X)⁻¹ * f * y * f * ((y : X)⁻¹ * f * y * f) = 1 := by
      calc (y : X)⁻¹ * f * y * f * ((y : X)⁻¹ * f * y * f)
          = (y : X)⁻¹ * f * y * (f * ((y : X)⁻¹ * f * y)) * f := by simp only [mul_assoc]
        _ = (y : X)⁻¹ * f * y * ((y : X)⁻¹ * f * y) * (f * f) := by
            rw [hfw]; simp only [mul_assoc]
        _ = 1 := by rw [Pair.mul_self hP hw.1, Pair.mul_self hP hfE, one_mul]
    have hzo : orderOf ((y : X)⁻¹ * f * y * f) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    obtain ⟨g, hg, hgf⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hd hf
    have h3 := Pair.orderOf_mul_eq_three hP hg.1 hfE hgf
    have hcomm : Commute ((y : X)⁻¹ * f * y * f) (g * f) :=
      Commute.mul_right (hzc g (mem_localGroup hg)).symm hzf.symm
    have h6 := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hzo, h3]; norm_num)
    have hgw : (y : X)⁻¹ * f * y * f * (g * f) = g * ((y : X)⁻¹ * f * y) := by
      calc (y : X)⁻¹ * f * y * f * (g * f) = ((y : X)⁻¹ * f * y * f * g) * f := by
            simp only [mul_assoc]
        _ = g * ((y : X)⁻¹ * f * y * f) * f := by rw [← hzc g (mem_localGroup hg)]
        _ = g * ((y : X)⁻¹ * f * y) := by
            rw [mul_assoc g, mul_assoc _ f f, Pair.mul_self hP hfE, mul_one]
    rw [hzo, h3, hgw] at h6
    have hmem := Pair.orderOf_mul_mem hP hg.1 hw.1
    rw [h6] at hmem
    simp at hmem
  exact Subgroup.mem_center_iff.2 fun l =>
    Subtype.ext (commute_of_mem_localGroup (fun g hg => key g hg) l.2)

theorem Pair.bijective_starImage (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {d : X} (hd : d ∈ E) :
    Function.Bijective fun f : LocalClass E d =>
      (⟨starImage E d f, range_starImage (E := E) d ▸ ⟨f, rfl⟩⟩ : LocalImages E d) := by
  refine ⟨fun f g h => Pair.starImage_injective_of_simple hP hZ hS hd (congrArg Subtype.val h),
    fun q => ?_⟩
  have hq : (q : LocalQuotient E d) ∈ Set.range (starImage E d) := by
    rw [range_starImage]
    exact q.2
  obtain ⟨f, hf⟩ := hq
  exact ⟨f, Subtype.ext hf⟩

theorem Pair.card_localQuotient_lt (hP : Pair X E) (hZ : Subgroup.center X = ⊥) {d : X}
    (hd : d ∈ E) : Nat.card (LocalQuotient E d) < Nat.card X := by
  have := Pair.finite hP
  have h1 : Nat.card (LocalQuotient E d) ≤ Nat.card (LocalGroup E d) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hlt : LocalGroup E d < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    have hdZ : d ∈ Subgroup.center X := by
      refine (Pair.mem_center_iff hP).2 fun e he => ?_
      have : e ∈ LocalGroup E d := h ▸ Subgroup.mem_top e
      exact (commute_of_mem_localGroup' this)
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [Subgroup.card_top] at h2
  omega

end LocalPair

section Centralizer

theorem commute_of_mem_localGroupD' {d y h : X} (hyd : y * d = d * y)
    (hyD : ∀ f ∈ LocalClass E d, y * f = f * y) (hh : h ∈ localGroupD E d) : y * h = h * y := by
  have hle : localGroupD E d ≤ Subgroup.centralizer ({y} : Set X) := by
    rw [Subgroup.closure_le]
    rintro s (rfl | hs)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hyd.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hyD s hs).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hh)).symm

theorem Pair.eq_one_of_centralizes_of_fix (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    {d y c : X} (hd : d ∈ E) (hyd : y * d = d * y) (hyD : ∀ f ∈ LocalClass E d, y * f = f * y)
    (hc : c ∈ farClass E d) (hyc : y * c * y⁻¹ = c) : y = 1 := by
  apply Pair.eq_one_of_forall_conj_eq hP hZ
  intro e he
  by_cases hed : e = d
  · rw [hed, hyd, mul_inv_cancel_right]
  by_cases hec : e * d = d * e
  · rw [hyD e ⟨he, hed, hec⟩, mul_inv_cancel_right]
  obtain ⟨h, hh, rfl⟩ := Pair.exists_conj_far hP hZ hS hna hd hc.1 hc.2 e he hec
  have hyh := commute_of_mem_localGroupD' hyd hyD hh
  calc y * (h * c * h⁻¹) * y⁻¹ = h * (y * c * y⁻¹) * h⁻¹ := by
        rw [show y * (h * c * h⁻¹) * y⁻¹ = y * h * c * h⁻¹ * y⁻¹ by group, hyh]
        have hyh' : h⁻¹ * y⁻¹ = y⁻¹ * h⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hyh]
        rw [mul_assoc (h * y * c), hyh']
        group
    _ = h * c * h⁻¹ := by rw [hyc]

theorem Pair.eq_one_or_eq_of_centralizes (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hT : TripleProperty E) {d y : X} (hd : d ∈ E) (hyd : y * d = d * y)
    (hyD : ∀ f ∈ LocalClass E d, y * f = f * y) : y = 1 ∨ y = d := by
  obtain ⟨c, hc, hcd⟩ : ∃ c ∈ E, c * d ≠ d * c := by
    by_contra! hall
    have hdZ : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 hall
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  have hcA : c ∈ farClass E d := ⟨hc, hcd⟩
  have hconjA : y * c * y⁻¹ ∈ farClass E d := Pair.conj_mem_farClass hP hyd hcA
  have hmem : y * c * y⁻¹ ∈ ySet E d c := by
    refine ⟨hconjA.1, fun s hs => ⟨hs.1.1, fun e => hconjA.2 ?_, ?_⟩⟩
    · rw [← e]
      exact hs.1.2.2
    · have hys : y * s * y⁻¹ = s := by rw [hyD s hs.1, mul_inv_cancel_right]
      rw [← hys]
      exact (conj_commute_iff y s c).2 hs.2.2.2
  rcases hT d c hd hc (fun h => hcd h.symm) hmem with h | h | h
  · exact absurd (h ▸ hconjA).2 (fun h' => h' rfl)
  · exact Or.inl (Pair.eq_one_of_centralizes_of_fix hP hZ hS hna hd hyd hyD hcA h)
  · right
    have hdy := Pair.eq_one_of_centralizes_of_fix hP hZ hS hna (y := d * y) hd
      (by rw [mul_assoc, hyd, ← mul_assoc]) (fun f hf => by
        rw [mul_assoc, hyD f hf, ← mul_assoc, hf.2.2.symm, mul_assoc]) hcA (by
        rw [mul_inv_rev, Pair.inv_eq hP hd, show d * y * c * (y⁻¹ * d) = d * (y * c * y⁻¹) * d by
          group, h, Pair.mul_mul_mul_mul hP hd])
    rw [← Pair.inv_eq hP hd]
    exact eq_inv_of_mul_eq_one_right hdy

theorem Pair.centralizer_insert_localClass (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hT : TripleProperty E) {d : X} (hd : d ∈ E) :
    Subgroup.centralizer (insert d (LocalClass E d)) = Subgroup.zpowers d := by
  apply le_antisymm
  · intro y hy
    have hyd : y * d = d * y := (Subgroup.mem_centralizer_iff.1 hy d (Or.inl rfl)).symm
    have hyD : ∀ f ∈ LocalClass E d, y * f = f * y := fun f hf =>
      (Subgroup.mem_centralizer_iff.1 hy f (Or.inr hf)).symm
    rcases Pair.eq_one_or_eq_of_centralizes hP hZ hS hna hT hd hyd hyD with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    rintro f (rfl | hf)
    · rfl
    · exact hf.2.2

theorem Pair.center_localGroup_le (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hT : TripleProperty E) {d : X} (hd : d ∈ E) :
    (Subgroup.center (LocalGroup E d)).map (LocalGroup E d).subtype ≤ Subgroup.zpowers d := by
  rintro _ ⟨z, hz, rfl⟩
  have hzD : ∀ f ∈ LocalClass E d, (z : X) * f = f * z := fun f hf =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨f, mem_localGroup hf⟩)).symm
  rcases Pair.eq_one_or_eq_of_centralizes hP hZ hS hna hT hd (commute_of_mem_localGroup' z.2)
    hzD with h | h
  · rw [Subgroup.coe_subtype, h]
    exact one_mem _
  · rw [Subgroup.coe_subtype, h]
    exact Subgroup.mem_zpowers d

end Centralizer

section Weiss

theorem Pair.connected_commGraph_localClass (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a) {d : X}
    (hd : d ∈ E) (hedge : ∃ u ∈ LocalClass E d, ∃ v ∈ LocalClass E d, u ≠ v ∧ u * v = v * u)
    (hV : ∀ u ∈ LocalClass E d, ∀ v ∈ LocalClass E d,
      (∀ w ∈ LocalClass E d, w * u = u * w ↔ w * v = v * w) → u = v) :
    (commGraph (LocalClass E d)).Connected := by
  obtain ⟨u, hu, v, hv, w, hw, huv, huvc, hwv, hwu⟩ : ∃ u ∈ LocalClass E d,
      ∃ v ∈ LocalClass E d, ∃ w ∈ LocalClass E d,
        u ≠ v ∧ u * v = v * u ∧ w * v = v * w ∧ w * u ≠ u * w := by
    obtain ⟨u, hu, v, hv, huv, huvc⟩ := hedge
    by_contra! hall
    exact huv (hV u hu v hv fun w hw =>
      ⟨fun h => hall v hv u hu w hw (Ne.symm huv) huvc.symm h,
        fun h => hall u hu v hv w hw huv huvc h⟩)
  refine (SimpleGraph.connected_iff _).2 ⟨fun a b => ?_, ⟨⟨u, hu⟩⟩⟩
  by_contra hab
  obtain ⟨x, hx⟩ := a
  obtain ⟨y, hy⟩ := b
  have hxy : x * y ≠ y * x := fun h => hab (commGraph_reachable_of_commute h)
  have hcommon : ∀ z ∈ LocalClass E d, z * x = x * z → z * y = y * z → False := by
    intro z hz hzx hzy
    by_cases hzx' : z = x
    · exact hxy (by rw [← hzx']; exact hzy)
    by_cases hzy' : z = y
    · exact hxy (by rw [← hzy']; exact hzx.symm)
    apply hab
    have h1 : (commGraph (LocalClass E d)).Adj ⟨x, hx⟩ ⟨z, hz⟩ :=
      commGraph_adj_iff.2 ⟨Ne.symm hzx', hzx.symm⟩
    have h2 : (commGraph (LocalClass E d)).Adj ⟨z, hz⟩ ⟨y, hy⟩ :=
      commGraph_adj_iff.2 ⟨hzy', hzy⟩
    exact h1.reachable.trans h2.reachable
  obtain ⟨g, hgx, hgy⟩ := Pair.exists_conj_pair_of_not_commute hP hZ hS hna hu.1 hw.1 hx.1 hy.1
    (fun h => hwu h.symm) hxy
  have hpE : g * d * g⁻¹ ∈ E := Pair.conj_mem hP hd g
  have hqE : g * v * g⁻¹ ∈ E := Pair.conj_mem hP hv.1 g
  have hpx : g * d * g⁻¹ * x = x * (g * d * g⁻¹) := by
    rw [← hgx, conj_commute_iff]
    exact hu.2.2.symm
  have hpy : g * d * g⁻¹ * y = y * (g * d * g⁻¹) := by
    rw [← hgy, conj_commute_iff]
    exact hw.2.2.symm
  have hqx : g * v * g⁻¹ * x = x * (g * v * g⁻¹) := by
    rw [← hgx, conj_commute_iff]
    exact huvc.symm
  have hqy : g * v * g⁻¹ * y = y * (g * v * g⁻¹) := by
    rw [← hgy, conj_commute_iff]
    exact hwv.symm
  have hpq : g * d * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * d * g⁻¹) :=
    (conj_commute_iff g d v).2 hv.2.2.symm
  have hpq' : g * d * g⁻¹ ≠ g * v * g⁻¹ := (conj_injective g).ne hv.2.1.symm
  by_cases hpd : g * d * g⁻¹ * d = d * (g * d * g⁻¹)
  · by_cases hpd' : g * d * g⁻¹ = d
    · refine hcommon _ ⟨hqE, fun h => hpq' (hpd'.trans h.symm), ?_⟩ hqx hqy
      have h := hpq
      rw [hpd'] at h
      exact h.symm
    · exact hcommon _ ⟨hpE, hpd', hpd⟩ hpx hpy
  by_cases hqd : g * v * g⁻¹ * d = d * (g * v * g⁻¹)
  · by_cases hqd' : g * v * g⁻¹ = d
    · refine hcommon _ ⟨hpE, fun h => hpq' (h.trans hqd'.symm), ?_⟩ hpx hpy
      have h := hpq
      rw [hqd'] at h
      exact h
    · exact hcommon _ ⟨hqE, hqd', hqd⟩ hqx hqy
  have hz := Pair.triality_adj hP hpE hqE hd hpq hpq' (fun h => hpd h.symm) fun h => hqd h.symm
  have hcomm : ∀ t : X, t * (g * d * g⁻¹) = g * d * g⁻¹ * t →
      t * (g * v * g⁻¹) = g * v * g⁻¹ * t → t * d = d * t →
      g * d * g⁻¹ * (g * v * g⁻¹) * d * (g * d * g⁻¹ * (g * v * g⁻¹))⁻¹ * t =
        t * (g * d * g⁻¹ * (g * v * g⁻¹) * d * (g * d * g⁻¹ * (g * v * g⁻¹))⁻¹) := by
    intro t h1 h2 h3
    have hc : Commute t (g * d * g⁻¹ * (g * v * g⁻¹) * d * (g * d * g⁻¹ * (g * v * g⁻¹))⁻¹) :=
      ((Commute.mul_right h1 h2).mul_right h3).mul_right (Commute.mul_right h1 h2).inv_right
    exact hc.eq.symm
  exact hcommon _ hz (hcomm x hpx.symm hqx.symm hx.2.2)
    (hcomm y hpy.symm hqy.symm hy.2.2)

end Weiss

end CFSG.Fischer.Classification
