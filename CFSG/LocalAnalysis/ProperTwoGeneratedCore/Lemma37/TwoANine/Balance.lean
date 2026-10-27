module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Signalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

section OddQuotient

variable {K : Type*} [Group K] {N : Subgroup K} [N.Normal]

theorem eq_one_of_mem_of_isPGroup_of_odd {P M : Subgroup K} (hP : IsPGroup 2 P)
    (hM : Odd (Nat.card M)) {x : K} (hxP : x ∈ P) (hxM : x ∈ M) : x = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ n := by
    rw [← Subgroup.orderOf_mk x hxP]
    exact orderOf_dvd_of_pow_eq_one hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf x ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hxM
  rcases k with _ | k
  · rwa [pow_zero, orderOf_eq_one_iff] at hk
  · rw [hk, pow_succ] at h2
    exact absurd (even_iff_two_dvd.mpr ((Dvd.intro_left _ rfl).trans h2))
      (Nat.not_even_iff_odd.mpr hM)

theorem eq_of_mk_eq_of_isPGroup (hN : Odd (Nat.card N)) {P : Subgroup K} (hP : IsPGroup 2 P)
    {x y : K} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : QuotientGroup.mk' N x = QuotientGroup.mk' N y) : x = y := by
  have h := eq_one_of_mem_of_isPGroup_of_odd hP hN (P.mul_mem (P.inv_mem hx) hy)
    (QuotientGroup.eq.mp hxy)
  rwa [inv_mul_eq_one] at h

theorem card_map_mk_of_isPGroup (hN : Odd (Nat.card N)) {P : Subgroup K} (hP : IsPGroup 2 P) :
    Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card P := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := fun x y hxy =>
    Subtype.ext (eq_of_mk_eq_of_isPGroup hN hP x.2 y.2 hxy)
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, MonoidHom.range_comp,
    Subgroup.range_subtype]

end OddQuotient

variable {X : Type} [Group X] [Finite X]

@[expose] def oddCentralizer (a : X) : Subgroup X :=
  (CFSG.pPrimeCore 2 (centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype

omit [Finite X] in
theorem oddCentralizer_le (a : X) : oddCentralizer a ≤ centralizer {a} :=
  Subgroup.map_subtype_le _

omit [Finite X] in
theorem coe_mem_oddCentralizer_iff {a : X} {c : centralizer ({a} : Set X)} :
    (c : X) ∈ oddCentralizer a ↔ escapingMk a c = 1 := by
  change (centralizer ({a} : Set X)).subtype c ∈ oddCentralizer a ↔ _
  rw [oddCentralizer, Subgroup.mem_map_iff_mem (centralizer ({a} : Set X)).subtype_injective,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem odd_card_oddCentralizer (a : X) : Odd (Nat.card (oddCentralizer a)) := by
  rw [oddCentralizer, Subgroup.card_map_of_injective (centralizer ({a} : Set X)).subtype_injective]
  exact escaping_oddCore_odd a

omit [Finite X] in
theorem centralizer_le_normalizer_oddCentralizer (a : X) :
    centralizer {a} ≤ normalizer (oddCentralizer a : Set X) := by
  calc centralizer {a} = (⊤ : Subgroup (centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (normalizer (CFSG.pPrimeCore 2 (centralizer ({a} : Set X)) :
          Set (centralizer ({a} : Set X)))).map (centralizer ({a} : Set X)).subtype := by
        rw [Subgroup.normalizer_eq_top]
    _ ≤ _ := Subgroup.le_normalizer_map _

omit [Finite X] in
theorem inf_centralizer_le_oddCentralizer_of_map_eq_bot {a : X} {Y : Subgroup X}
    (h : escapingImage Y a = ⊥) : Y ⊓ centralizer {a} ≤ oddCentralizer a := by
  intro x hx
  have hmem : (⟨x, hx.2⟩ : centralizer ({a} : Set X)) ∈
      Y.subgroupOf (centralizer ({a} : Set X)) := Subgroup.mem_subgroupOf.mpr hx.1
  have h1 : escapingMk a ⟨x, hx.2⟩ = 1 := by
    have := Subgroup.mem_map_of_mem (escapingMk a) hmem
    rw [escapingImage] at h
    rwa [h, Subgroup.mem_bot] at this
  exact coe_mem_oddCentralizer_iff.mpr h1

omit [Finite X] in
theorem mem_normalizer_subgroupOf {a : X} {Y : Subgroup X} {c : centralizer ({a} : Set X)}
    (hc : (c : X) ∈ normalizer (Y : Set X)) :
    c ∈ normalizer (Y.subgroupOf (centralizer ({a} : Set X)) : Set (centralizer ({a} : Set X))) :=
  Subgroup.mem_normalizer_iff.mpr fun d => by
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hc d

theorem IsTwoANine.zbar_eq_escapingBar {b : X} (hJ : IsTwoANine (EscapingQuotient b))
    (hb : orderOf b = 2) : zbar (EscapingQuotient b) = escapingBar b := by
  refine (hJ.eq_zbar_of_mem_center ?_ ?_).symm
  · refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ y
    change escapingMk b c * escapingMk b (escapingSelf b) =
      escapingMk b (escapingSelf b) * escapingMk b c
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2))
  · have h2 : orderOf (escapingSelf b) = 2 := by rw [Subgroup.orderOf_mk, hb]
    intro h1
    have h3 := escaping_orderOf_mk b h2
    rw [show escapingMk b (escapingSelf b) = 1 from h1, orderOf_one] at h3
    exact absurd h3 (by norm_num)

theorem IsTwoANine.eq_of_escapingMk_eq_zbar {b : X} (hJ : IsTwoANine (EscapingQuotient b))
    (hb : orderOf b = 2) {x : centralizer ({b} : Set X)} (hx : x ^ 2 = 1)
    (hxb : escapingMk b x = zbar (EscapingQuotient b)) : (x : X) = b := by
  have hbb : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  exact escaping_eq_of_mk_eq_bar hbb (by rw [← sq, hx]) (hxb.trans (hJ.zbar_eq_escapingBar hb))

theorem card_escapingImage_of_isPGroup {b : X} {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPb : P ≤ centralizer {b}) : Nat.card (escapingImage P b) = Nat.card P :=
  (card_map_mk_of_isPGroup (escaping_oddCore_odd b) hP.comap_subtype).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPb).toEquiv)

theorem eq_of_escapingMk_eq_of_isPGroup {b : X} {P : Subgroup X} (hP : IsPGroup 2 P)
    {x y : centralizer ({b} : Set X)} (hx : (x : X) ∈ P) (hy : (y : X) ∈ P)
    (hxy : escapingMk b x = escapingMk b y) : x = y :=
  eq_of_mk_eq_of_isPGroup (escaping_oddCore_odd b) (P := P.subgroupOf (centralizer {b}))
    hP.comap_subtype (Subgroup.mem_subgroupOf.mpr hx) (Subgroup.mem_subgroupOf.mpr hy) hxy

omit [Finite X] in
theorem sq_eq_one_of_mem_escapingImage {b : X} {P : Subgroup X} (hP2 : ∀ x ∈ P, x ^ 2 = 1)
    {y : EscapingQuotient b} (hy : y ∈ escapingImage P b) : y ^ 2 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by
    rw [Subgroup.coe_pow, hP2 _ (Subgroup.mem_subgroupOf.mp hx), OneMemClass.coe_one]), map_one]

theorem isPGroup_of_sq_eq_one {G : Type*} [Group G] {P : Subgroup G} (hP2 : ∀ x ∈ P, x ^ 2 = 1) :
    IsPGroup 2 P := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hP2 x x.2)⟩

theorem commute_of_sq_eq_one_of_mem {G : Type*} [Group G] {P : Subgroup G}
    (hP2 : ∀ x ∈ P, x ^ 2 = 1) {x y : G} (hx : x ∈ P) (hy : y ∈ P) : Commute x y :=
  commute_of_sq_eq_one_of_mul_sq_eq_one (hP2 x hx) (hP2 y hy) (hP2 _ (P.mul_mem hx hy))

theorem le_centralizer_of_sq_eq_one {G : Type*} [Group G] {P : Subgroup G}
    (hP2 : ∀ x ∈ P, x ^ 2 = 1) {a : G} (ha : a ∈ P) : P ≤ centralizer {a} := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_sq_eq_one_of_mem hP2 hx ha).eq

omit [Finite X] in
theorem centralizer_conj (g a : X) :
    centralizer ({g * a * g⁻¹} : Set X) =
      (centralizer ({a} : Set X)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [hx]
      _ = a * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group

@[expose] noncomputable def centralizerConj (g a : X) :
    centralizer ({a} : Set X) ≃* centralizer ({g * a * g⁻¹} : Set X) :=
  ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_conj g a).symm)

omit [Finite X] in
@[simp] theorem coe_centralizerConj_apply (g a : X) (c : centralizer ({a} : Set X)) :
    (centralizerConj g a c : X) = g * c * g⁻¹ :=
  rfl

@[expose] noncomputable def escapingQuotientConj (g a : X) :
    EscapingQuotient a ≃* EscapingQuotient (g * a * g⁻¹) :=
  QuotientGroup.congr _ _ (centralizerConj g a) (CFSG.pPrimeCore_map_iso 2 (centralizerConj g a))

omit [Finite X] in
theorem IsTwoANine.escapingQuotient_conj {a : X} (hJ : IsTwoANine (EscapingQuotient a)) (g : X) :
    IsTwoANine (EscapingQuotient (g * a * g⁻¹)) :=
  hJ.of_mulEquiv (escapingQuotientConj g a)

omit [Finite X] in
theorem IsTwoANine.of_isConj_escapingQuotient {a b : X} (hJ : IsTwoANine (EscapingQuotient a))
    (hab : IsConj a b) : IsTwoANine (EscapingQuotient b) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  exact hJ.escapingQuotient_conj g

omit [Finite X] in
theorem map_conj_oddCentralizer (g a : X) :
    (oddCentralizer a).map (MulAut.conj g).toMonoidHom = oddCentralizer (g * a * g⁻¹) := by
  rw [oddCentralizer, oddCentralizer, ← CFSG.pPrimeCore_map_iso 2 (centralizerConj g a),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem oddCentralizer_inf_centralizer_le {a b : X} (ha : orderOf a = 2) (hab : Commute a b)
    (hb : IsTwoANine (EscapingQuotient b)) :
    oddCentralizer a ⊓ centralizer {b} ≤ oddCentralizer b := by
  have haC : a ∈ centralizer ({b} : Set X) := Subgroup.mem_centralizer_singleton_iff.mpr hab.eq
  set a' : centralizer ({b} : Set X) := ⟨a, haC⟩ with ha'_def
  have ha' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk, ha]
  apply inf_centralizer_le_oddCentralizer_of_map_eq_bot
  refine hb.eq_bot_of_odd_of_centralizer_le_normalizer (escaping_orderOf_mk b ha') ?_ ?_
  · exact (odd_card_oddCentralizer a).of_dvd_nat ((Subgroup.card_map_dvd _ _).trans
      (Subgroup.card_comap_dvd_of_injective _ _ (centralizer ({b} : Set X)).subtype_injective))
  · rw [← escaping_map_centralizer b ha']
    refine (Subgroup.map_mono fun c hc => ?_).trans (Subgroup.le_normalizer_map _)
    refine mem_normalizer_subgroupOf (centralizer_le_normalizer_oddCentralizer a ?_)
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact congrArg Subtype.val hc

theorem inf_centralizer_le_oddCentralizer {A Y : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA : Nat.card A = 16) {a : X} (haA : a ∈ A) (hJ : IsTwoANine (EscapingQuotient a))
    (hY : Odd (Nat.card Y)) (hAY : A ≤ normalizer (Y : Set X)) :
    Y ⊓ centralizer {a} ≤ oddCentralizer a := by
  have hAC := le_centralizer_of_sq_eq_one hA2 haA
  apply inf_centralizer_le_oddCentralizer_of_map_eq_bot
  refine hJ.eq_bot_of_odd_of_le_normalizer (E := escapingImage A a)
    (fun y hy => sq_eq_one_of_mem_escapingImage hA2 hy)
    (by rw [card_escapingImage_of_isPGroup (isPGroup_of_sq_eq_one hA2) hAC, hA]) ?_ ?_
  · exact hY.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans
      (Subgroup.card_comap_dvd_of_injective _ _ (centralizer ({a} : Set X)).subtype_injective))
  · refine (Subgroup.map_mono fun c hc => ?_).trans (Subgroup.le_normalizer_map _)
    exact mem_normalizer_subgroupOf (hAY (Subgroup.mem_subgroupOf.mp hc))

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
