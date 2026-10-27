module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Inner

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups

namespace F3D4

variable {Q : Type} [Group Q] [Finite Q]

theorem eq_of_involutions {M : Subgroup Q} (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3))
    {i j : Q} (hi : i ∈ M) (hj : j ∈ M) (hi2 : orderOf i = 2) (hj2 : orderOf j = 2) {n : ℕ}
    (hij : (i * j) ^ 2 ^ n = 1) : i = j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hei := F3A75.e_mk_eq_neg_one e hi hi2
  have hej := F3A75.e_mk_eq_neg_one e hj hj2
  have h1 : (⟨i, hi⟩ : ↥M)⁻¹ * ⟨j, hj⟩ ∈ pPrimeCore 2 ↥M :=
    QuotientGroup.eq.mp (e.injective (hei.trans hej.symm))
  have hii : i * i = 1 := by rw [← sq, ← hi2, pow_orderOf_eq_one]
  have hinv : i⁻¹ = i := inv_eq_of_mul_eq_one_right hii
  have h2 : (⟨⟨i, hi⟩⁻¹ * ⟨j, hj⟩, h1⟩ : ↥(pPrimeCore 2 ↥M)) ^ 2 ^ n = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [hinv]
    exact hij
  have h3 := orderOf_dvd_natCard (⟨⟨i, hi⟩⁻¹ * ⟨j, hj⟩, h1⟩ : ↥(pPrimeCore 2 ↥M))
  have h4 := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_card_pPrimeCore_two ↥M))
  have h5 := Nat.eq_one_of_dvd_coprimes hcop h4 h3
  rw [orderOf_eq_one_iff] at h5
  have h6 : i⁻¹ * j = 1 := by
    have h7 := congrArg (fun w : ↥(pPrimeCore 2 ↥M) => ((w : ↥M) : Q)) h5
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] using h7
  calc i = i * (i⁻¹ * j) := by rw [h6, mul_one]
    _ = j := by group

omit [Finite Q] in
theorem conj_mem_map_of_characteristic {X : Subgroup Q} {D : Subgroup X} [hD : D.Characteristic]
    {g : Q} (hg : g ∈ normalizer (X : Set Q)) {x : Q} (hx : x ∈ D.map X.subtype) :
    g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rfl

omit [Finite Q] in
theorem map_pCore_le_of_le_normalizer {p : ℕ} {X Y : Subgroup Q} (hXY : X ≤ Y)
    (hYN : Y ≤ normalizer (X : Set Q)) :
    (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
  have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
  have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
    apply le_sSup
    refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hl ⊢
      simpa using conj_mem_map_of_characteristic (hYN y.2) hl
    · exact ((CFSG.pCore_isPGroup).map X.subtype).of_equiv
        (Subgroup.subgroupOfEquivOfLe hLY).symm
  calc (CFSG.pCore p X).map X.subtype
      = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hLY).symm
    _ ≤ (CFSG.pCore p Y).map Y.subtype := Subgroup.map_mono hle

omit [Finite Q] in
theorem map_pCore_le_pCore_of_isSubnormal {p : ℕ} {X : Subgroup Q} (hX : X.IsSubnormal) :
    (CFSG.pCore p X).map X.subtype ≤ CFSG.pCore p Q := by
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => conj_mem_map_of_characteristic ?_ hl⟩,
      (CFSG.pCore_isPGroup).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Y hXY hY hN ih =>
    exact (map_pCore_le_of_le_normalizer hXY
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

omit [Finite Q] in
theorem le_pCore_of_isSubnormal {p : ℕ} {P : Subgroup Q} (hP : P.IsSubnormal)
    (hp : IsPGroup p P) : P ≤ CFSG.pCore p Q := by
  have htop : CFSG.pCore p (P : Subgroup Q) = ⊤ := by
    apply le_antisymm le_top
    exact le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩
  have h := map_pCore_le_pCore_of_isSubnormal (p := p) hP
  rwa [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

omit [Finite Q] in
theorem mem_klein {Z : Subgroup Q} (hZ4 : Nat.card Z = 4) (hZ2 : ∀ c ∈ Z, c * c = 1) {a b : Q}
    (ha : a ∈ Z) (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {c : Q} (hc : c ∈ Z) :
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype Z := Fintype.ofFinite Z
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hZ2 a ha)
  have hab1 : a * b ≠ 1 := fun h => hab (by rw [eq_inv_of_mul_eq_one_right h, hainv])
  have haab : a ≠ a * b := fun h => hb1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [← h, inv_mul_cancel])
  have hbab : b ≠ a * b := fun h => ha1 (by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel])
  let T : Finset ↥Z := {1, ⟨a, ha⟩, ⟨b, hb⟩, ⟨a * b, mul_mem ha hb⟩, ⟨c, hc⟩}
  have hT : T.card = 5 := by
    simp only [T]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Subtype.mk.injEq]
      exact fun h => h4 h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨hbab, fun h => h3 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨hab, haab, fun h => h2 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm, fun h => hab1 (congrArg Subtype.val h).symm,
        fun h => h1 (congrArg Subtype.val h).symm⟩
  have h5 := Finset.card_le_univ T
  rw [hT, ← Nat.card_eq_fintype_card, hZ4] at h5
  omega

section Chain

variable {L : Subgroup Q} {t : Q} (htL : t ∈ L) {S : Type} [Group S] {θ : S →* ↥L}

omit [Finite Q] in
include htL in
theorem centralizer_normal_comap (hker : θ.ker ≤ center S) {x : S} (hx : θ x = ⟨t, htL⟩) :
    ((centralizer ({x} : Set S)).subgroupOf
      ((centralizer ({(⟨t, htL⟩ : ↥L)} : Set ↥L)).comap θ)).Normal := by
  constructor
  intro g hg y
  rw [mem_subgroupOf, mem_centralizer_singleton_iff] at hg ⊢
  have hy : θ (y : S) * ⟨t, htL⟩ = ⟨t, htL⟩ * θ (y : S) :=
    mem_centralizer_singleton_iff.mp (mem_comap.mp y.2)
  have hc : x⁻¹ * ((y : S) * x * (y : S)⁻¹) ∈ center S := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hx]
    calc (⟨t, htL⟩ : ↥L)⁻¹ * (θ (y : S) * ⟨t, htL⟩ * (θ (y : S))⁻¹)
        = (⟨t, htL⟩ : ↥L)⁻¹ * (⟨t, htL⟩ * θ (y : S) * (θ (y : S))⁻¹) := by rw [hy]
      _ = 1 := by group)
  have hcc := mem_center_iff.mp hc
  set c := x⁻¹ * ((y : S) * x * (y : S)⁻¹) with hcdef
  have hyx : (y : S) * x * (y : S)⁻¹ = x * c := by rw [hcdef]; group
  have hg' : (g : S) * x = x * (g : S) := hg
  show (y : S) * (g : S) * (y : S)⁻¹ * x = x * ((y : S) * (g : S) * (y : S)⁻¹)
  have h1 : ((y : S) * (g : S) * (y : S)⁻¹) * (x * c) = (x * c) * ((y : S) * (g : S) * (y : S)⁻¹) :=
    by
    rw [← hyx]
    calc (y : S) * (g : S) * (y : S)⁻¹ * ((y : S) * x * (y : S)⁻¹)
        = (y : S) * ((g : S) * x) * (y : S)⁻¹ := by group
      _ = (y : S) * (x * (g : S)) * (y : S)⁻¹ := by rw [hg']
      _ = (y : S) * x * (y : S)⁻¹ * ((y : S) * (g : S) * (y : S)⁻¹) := by group
  have h2 := hcc ((y : S) * (g : S) * (y : S)⁻¹)
  calc (y : S) * (g : S) * (y : S)⁻¹ * x
      = (y : S) * (g : S) * (y : S)⁻¹ * (x * c) * c⁻¹ := by group
    _ = x * c * ((y : S) * (g : S) * (y : S)⁻¹) * c⁻¹ := by rw [h1]
    _ = x * ((y : S) * (g : S) * (y : S)⁻¹ * c) * c⁻¹ := by rw [h2]; group
    _ = x * ((y : S) * (g : S) * (y : S)⁻¹) := by group

omit [Finite Q] in
include htL in
theorem isSubnormal_map_of_centralizer (hθ : Function.Surjective θ) (hker : θ.ker ≤ center S)
    {x : S} (hx : θ x = ⟨t, htL⟩) {H : Subgroup S} (hHx : H ≤ centralizer ({x} : Set S))
    (hHs : (H.subgroupOf (centralizer ({x} : Set S))).IsSubnormal) :
    ((H.map (L.subtype.comp θ)).subgroupOf
      (normalizer (L : Set Q) ⊓ centralizer ({t} : Set Q))).IsSubnormal := by
  set C' := (centralizer ({(⟨t, htL⟩ : ↥L)} : Set ↥L)).comap θ with hC'
  have hCx : centralizer ({x} : Set S) ≤ C' := by
    intro s hs
    rw [hC', mem_comap, mem_centralizer_singleton_iff, ← hx]
    rw [mem_centralizer_singleton_iff] at hs
    rw [← map_mul, ← map_mul, hs]
  have h1 : (H.subgroupOf C').IsSubnormal :=
    GroupTheory.isSubnormal_subgroupOf_trans hHx hCx hHs
      (centralizer_normal_comap htL hker hx).isSubnormal
  set Cq := L ⊓ centralizer ({t} : Set Q) with hCq
  have hmemCq : ∀ s ∈ C', ((θ s : ↥L) : Q) ∈ Cq := by
    intro s hs
    refine mem_inf.mpr ⟨(θ s).2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h := mem_centralizer_singleton_iff.mp (mem_comap.mp hs)
    exact congrArg Subtype.val h
  let φ : ↥C' →* ↥Cq :=
    { toFun := fun s => ⟨((θ s : ↥L) : Q), hmemCq s s.2⟩
      map_one' := by
        apply Subtype.ext
        show ((θ 1 : ↥L) : Q) = 1
        rw [map_one, OneMemClass.coe_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((θ ((a : S) * b) : ↥L) : Q) = ((θ a : ↥L) : Q) * ((θ b : ↥L) : Q)
        rw [map_mul, Subgroup.coe_mul] }
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨hqL, hqt⟩ := mem_inf.mp hq
    obtain ⟨s, hs⟩ := hθ ⟨q, hqL⟩
    have hsC : s ∈ C' := by
      rw [hC', mem_comap, hs, mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp hqt
    refine ⟨⟨s, hsC⟩, Subtype.ext ?_⟩
    show ((θ s : ↥L) : Q) = q
    rw [hs]
  have h2 := h1.map hφs
  have h3 : (H.subgroupOf C').map φ = (H.map (L.subtype.comp θ)).subgroupOf Cq := by
    ext ⟨q, hq⟩
    constructor
    · rintro ⟨s, hs, hsq⟩
      rw [mem_subgroupOf]
      refine ⟨(s : S), hs, ?_⟩
      exact congrArg Subtype.val hsq
    · intro h
      rw [mem_subgroupOf] at h
      obtain ⟨s, hs, hsq⟩ := h
      refine ⟨⟨s, hCx (hHx hs)⟩, hs, Subtype.ext ?_⟩
      exact hsq
  rw [h3] at h2
  have h4 : H.map (L.subtype.comp θ) ≤ Cq := by
    rintro _ ⟨s, hs, rfl⟩
    exact hmemCq s (hCx (hHx hs))
  have h5 : Cq ≤ normalizer (L : Set Q) ⊓ centralizer ({t} : Set Q) :=
    le_inf (inf_le_left.trans le_normalizer) inf_le_right
  have h6 : (Cq.subgroupOf (normalizer (L : Set Q) ⊓ centralizer ({t} : Set Q))).Normal := by
    constructor
    intro c hc a
    rw [mem_subgroupOf] at hc ⊢
    obtain ⟨hcL, hct⟩ := mem_inf.mp hc
    obtain ⟨haN, hat⟩ := mem_inf.mp a.2
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (mem_normalizer_iff.mp haN (c : Q)).mp hcL
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (mul_mem hat hct) (inv_mem hat)
  exact GroupTheory.isSubnormal_subgroupOf_trans h4 h5 h2 h6.isSubnormal

end Chain

end F3D4

end CFSG.ComponentClassification.HarrisLit.T1
