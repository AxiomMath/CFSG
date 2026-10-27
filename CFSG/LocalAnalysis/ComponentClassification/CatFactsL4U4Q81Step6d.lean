module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Q81

theorem mem_closure_pair_cases {G : Type*} [Group G] {a c : G} (ha : a * a = 1)
    (hc : c * c = 1) (hac : a * c = c * a) {x : G} (hx : x ∈ closure {a, c}) :
    x = 1 ∨ x = a ∨ x = c ∨ x = a * c := by
  have h16 : a * c * (a * c) = 1 := by
    rw [mul_assoc, ← mul_assoc c, ← hac, mul_assoc, hc, mul_one, ha]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
  | one => exact .inl rfl
  | mul y y' _ _ hy hy' =>
    rcases hy with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> rw [h, h']
    · exact .inl (mul_one 1)
    · exact .inr (.inl (one_mul a))
    · exact .inr (.inr (.inl (one_mul c)))
    · exact .inr (.inr (.inr (one_mul _)))
    · exact .inr (.inl (mul_one a))
    · exact .inl ha
    · exact .inr (.inr (.inr rfl))
    · exact .inr (.inr (.inl (by rw [← mul_assoc, ha, one_mul])))
    · exact .inr (.inr (.inl (mul_one c)))
    · exact .inr (.inr (.inr hac.symm))
    · exact .inl hc
    · exact .inr (.inl (by rw [← mul_assoc, ← hac, mul_assoc, hc, mul_one]))
    · exact .inr (.inr (.inr (mul_one _)))
    · exact .inr (.inr (.inl (by rw [mul_assoc, ← hac, ← mul_assoc, ha, one_mul])))
    · exact .inr (.inl (by rw [mul_assoc, hc, mul_one]))
    · exact .inl h16
  | inv y _ hy =>
    rcases hy with h | h | h | h <;> rw [h]
    · exact .inl inv_one
    · exact .inr (.inl (inv_eq_of_mul_eq_one_left ha))
    · exact .inr (.inr (.inl (inv_eq_of_mul_eq_one_left hc)))
    · exact .inr (.inr (.inr (inv_eq_of_mul_eq_one_left h16)))

theorem card_le_four {G : Type*} [Group G] [Finite G] {E Y : Subgroup G} (hEY : E ≤ Y)
    (hY : Nat.card Y = 8) {y : G} (hy : y ∈ Y) (hyE : y ∉ E) : Nat.card E ≤ 4 := by
  have hdvd : Nat.card E ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hY]
    exact Subgroup.card_dvd_of_le hEY
  have hne : Nat.card E ≠ 8 := by
    intro h8
    have hEq : E = Y := Subgroup.eq_of_le_of_card_ge hEY (by rw [h8, hY])
    exact hyE (hEq ▸ hy)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk3 : k ≠ 3 := fun h => hne (by rw [hk', h]; norm_num)
  have hk2 : k ≤ 2 := by omega
  rw [hk']
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem two_dvd_card_of_pPrimeCore_eq_bot {Y : Type*} [Group Y] [Finite Y] [Nontrivial Y]
    (h : pPrimeCore 2 Y = ⊥) : 2 ∣ Nat.card Y := by
  by_contra h2
  have hodd : Odd (Nat.card Y) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have htop : pPrimeCore 2 Y = ⊤ :=
    eq_top_iff.mpr (le_sSup ⟨inferInstance, by rw [card_top]; exact Nat.coprime_two_left.mpr hodd⟩)
  rw [h] at htop
  exact bot_ne_top htop

theorem le_normalizer_inf {G : Type*} [Group G] {P N : Subgroup G} (hN : N.Normal) :
    P ≤ normalizer ((P ⊓ N : Subgroup G) : Set G) := by
  intro r hr
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact mem_inf.mpr ⟨mul_mem (mul_mem hr (mem_inf.mp hh).1) (inv_mem hr),
      hN.conj_mem _ (mem_inf.mp hh).2 r⟩
  · intro hh
    have h1 : h = r⁻¹ * (r * h * r⁻¹) * r := by group
    rw [h1]
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hr) (mem_inf.mp hh).1) hr, ?_⟩
    have h2 := hN.conj_mem _ (mem_inf.mp hh).2 r⁻¹
    rwa [inv_inv] at h2

theorem centralizer_inf_mul {G : Type*} [Group G] (z a : G) :
    centralizer ({z} : Set G) ⊓ centralizer {z * a} = centralizer {z} ⊓ centralizer {a} := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc x * a = z⁻¹ * (z * x) * a := by group
      _ = z⁻¹ * (x * z) * a := by rw [h1]
      _ = z⁻¹ * (x * (z * a)) := by group
      _ = z⁻¹ * (z * a * x) := by rw [h2]
      _ = a * x := by group
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc x * (z * a) = x * z * a := by group
      _ = z * x * a := by rw [h1]
      _ = z * (x * a) := by group
      _ = z * (a * x) := by rw [h2]
      _ = z * a * x := by group

theorem isPComponent_subgroupOf {G : Type*} [Group G] [Finite G] {K H : Subgroup G}
    (hKH : K ≤ H) (h : IsPComponent 2 K) : IsPComponent 2 (K.subgroupOf H) := by
  rw [← isTwoComponent_iff_isPComponent] at h ⊢
  exact ⟨h.1.subgroupOf, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKH).symm h.2⟩

variable {X : Type} [Group X] [Finite X]

abbrev liftIn (R : Subgroup X) (z : X) (U : Subgroup (MBar z)) : Subgroup X :=
  ((R.subgroupOf (centralizer {z})) ⊓
      U.comap (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))).map
    (centralizer ({z} : Set X)).subtype

omit [Finite X] in
theorem mem_liftIn {R : Subgroup X} {z : X} {U : Subgroup (MBar z)} {x : X} :
    x ∈ liftIn R z U ↔ ∃ hx : x ∈ centralizer ({z} : Set X), x ∈ R ∧
      (QuotientGroup.mk ⟨x, hx⟩ : MBar z) ∈ U := by
  constructor
  · rintro ⟨y, ⟨hyR, hyU⟩, rfl⟩
    exact ⟨y.2, hyR, hyU⟩
  · rintro ⟨hx, hxR, hxU⟩
    exact ⟨⟨x, hx⟩, ⟨hxR, hxU⟩, rfl⟩

omit [Finite X] in
theorem liftIn_le {R : Subgroup X} {z : X} {U : Subgroup (MBar z)} : liftIn R z U ≤ R := by
  rintro _ ⟨y, ⟨hyR, -⟩, rfl⟩
  exact hyR

omit [Finite X] in
theorem exists_mem_liftIn {R : Subgroup X} {z : X} {U : Subgroup (MBar z)}
    (hU : U ≤ (R.subgroupOf (centralizer {z})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))) {u : MBar z}
    (hu : u ∈ U) : ∃ x ∈ liftIn R z U, ∃ hx : x ∈ centralizer ({z} : Set X),
      (QuotientGroup.mk ⟨x, hx⟩ : MBar z) = u := by
  obtain ⟨y, hyR, rfl⟩ := hU hu
  exact ⟨y, ⟨y, ⟨hyR, hu⟩, rfl⟩, y.2, rfl⟩

theorem eq_of_mk_eq {R : Subgroup X} {z : X} (hR : IsPGroup 2 R)
    (hRz : R ≤ centralizer ({z} : Set X)) {x y : X} (hx : x ∈ R) (hy : y ∈ R)
    (h : (QuotientGroup.mk ⟨x, hRz hx⟩ : MBar z) = QuotientGroup.mk ⟨y, hRz hy⟩) : x = y := by
  have hRp : IsPGroup 2 (R.subgroupOf (centralizer ({z} : Set X))) :=
    hR.of_equiv (subgroupOfEquivOfLe hRz).symm
  exact congrArg Subtype.val (GSThmB.OddQuot.injOn_of_isPGroup hRp
    (show (⟨x, hRz hx⟩ : ↥(centralizer ({z} : Set X))) ∈ R.subgroupOf (centralizer {z}) from hx)
    (show (⟨y, hRz hy⟩ : ↥(centralizer ({z} : Set X))) ∈ R.subgroupOf (centralizer {z}) from hy)
    h)

omit [Finite X] in
theorem conj_mem_liftIn {R : Subgroup X} {z : X} {U : Subgroup (MBar z)}
    (hRz : R ≤ centralizer ({z} : Set X)) (hUn : U.Normal) {r e : X} (hr : r ∈ R)
    (he : e ∈ liftIn R z U) : r * e * r⁻¹ ∈ liftIn R z U := by
  obtain ⟨hez, heR, heU⟩ := mem_liftIn.mp he
  have hrz := hRz hr
  refine mem_liftIn.mpr ⟨mul_mem (mul_mem hrz hez) (inv_mem hrz),
    mul_mem (mul_mem hr heR) (inv_mem hr), ?_⟩
  have h1 : (⟨r * e * r⁻¹, mul_mem (mul_mem hrz hez) (inv_mem hrz)⟩ :
      ↥(centralizer ({z} : Set X))) = ⟨r, hrz⟩ * ⟨e, hez⟩ * (⟨r, hrz⟩)⁻¹ := rfl
  rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact hUn.conj_mem _ heU _

theorem mul_self_eq_one_of_mem_liftIn {R : Subgroup X} {z : X} {U : Subgroup (MBar z)}
    (hR : IsPGroup 2 R) (hRz : R ≤ centralizer ({z} : Set X)) (hU2 : ∀ u ∈ U, u * u = 1)
    {e : X} (he : e ∈ liftIn R z U) : e * e = 1 := by
  obtain ⟨hez, heR, heU⟩ := mem_liftIn.mp he
  refine eq_of_mk_eq hR hRz (mul_mem heR heR) (one_mem R) ?_
  have h1 : (⟨e * e, hRz (mul_mem heR heR)⟩ : ↥(centralizer ({z} : Set X))) =
      ⟨e, hez⟩ * ⟨e, hez⟩ := rfl
  have h2 : (⟨1, hRz (one_mem R)⟩ : ↥(centralizer ({z} : Set X))) = 1 := rfl
  rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_one]
  exact hU2 _ heU

theorem comm_of_mem_liftIn {R : Subgroup X} {z : X} {U : Subgroup (MBar z)}
    (hR : IsPGroup 2 R) (hRz : R ≤ centralizer ({z} : Set X)) {t : X} (htR : t ∈ R)
    (hUt : U ≤ centralizer {(QuotientGroup.mk ⟨t, hRz htR⟩ : MBar z)}) {e : X}
    (he : e ∈ liftIn R z U) : e * t = t * e := by
  obtain ⟨hez, heR, heU⟩ := mem_liftIn.mp he
  refine eq_of_mk_eq hR hRz (mul_mem heR htR) (mul_mem htR heR) ?_
  have h1 : (⟨e * t, hRz (mul_mem heR htR)⟩ : ↥(centralizer ({z} : Set X))) =
      ⟨e, hez⟩ * ⟨t, hRz htR⟩ := rfl
  have h2 : (⟨t * e, hRz (mul_mem htR heR)⟩ : ↥(centralizer ({z} : Set X))) =
      ⟨t, hRz htR⟩ * ⟨e, hez⟩ := rfl
  rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
  exact mem_centralizer_singleton_iff.mp (hUt heU)

end Q81

end CFSG.ComponentClassification.HarrisLit
