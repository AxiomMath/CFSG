module

public import CFSG.GH74.Uniqueness.SU.SU8Stmts
public import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4
open scoped commutatorElement

namespace Setup

abbrev Hz {G : Type} [Group G] (z : G) : Subgroup G := centralizer ({z} : Set G)

theorem eq_one_of_pow_odd {M : Type*} [Monoid M] {u : M} {k m : ℕ} (hk : u ^ (2 ^ k) = 1)
    (hm : u ^ m = 1) (hodd : Odd m) : u = 1 := by
  have h1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf u ∣ m := orderOf_dvd_of_pow_eq_one hm
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf u = 1 := Nat.Coprime.eq_one_of_dvd (hc.coprime_dvd_left h1) h2
  exact orderOf_eq_one_iff.mp h3

theorem mem_of_mul_odd {X : Type*} [Group X] {O L : Subgroup X} [O.Normal] [L.Normal]
    [Finite X] (hO : Odd (Nat.card O)) {x l o : X} (hl : l ∈ L) (ho : o ∈ O) (hx : x = l * o)
    {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x ∈ L := by
  have hq : (QuotientGroup.mk x : X ⧸ L) = QuotientGroup.mk o := by
    rw [hx, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
  have h1 : (QuotientGroup.mk x : X ⧸ L) ^ (2 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk x : X ⧸ L) ^ (Nat.card O) = 1 := by
    rw [hq, ← QuotientGroup.mk_pow]
    have h3 : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard _ ho
    rw [orderOf_dvd_iff_pow_eq_one.mp h3, QuotientGroup.mk_one]
  exact (QuotientGroup.eq_one_iff x).mp (eq_one_of_pow_odd h1 h2 hO)

section Abstract

variable {X : Type*} [Group X] [Finite X] {O : Subgroup X} [O.Normal]

omit [Finite X] [O.Normal] in
theorem eq_one_of_mem_odd (hO : Odd (Nat.card O)) {x : X} (hx : x ∈ O) {k : ℕ}
    (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  refine eq_one_of_pow_odd hk (m := Nat.card O) ?_ hO
  exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hx)

omit [Finite X] in
theorem mk_inj_of_exp_two (hO : Odd (Nat.card O)) {A : Subgroup X} (hA : ∀ a ∈ A, a * a = 1)
    {a b : X} (ha : a ∈ A) (hb : b ∈ A)
    (h : (QuotientGroup.mk' O) a = (QuotientGroup.mk' O) b) : a = b := by
  have h1 : a⁻¹ * b ∈ O := QuotientGroup.eq.mp h
  have h2 : (a⁻¹ * b) ^ (2 ^ 1) = 1 := by
    have := hA _ (A.mul_mem (A.inv_mem ha) hb)
    simpa [pow_one, sq] using this
  exact inv_mul_eq_one.mp (eq_one_of_mem_odd hO h1 h2)

theorem mem_of_mk_mem_map {L : Subgroup X} [L.Normal] (hO : Odd (Nat.card O)) {x : X} {k : ℕ}
    (hk : x ^ (2 ^ k) = 1) (hx : (QuotientGroup.mk' O) x ∈ L.map (QuotientGroup.mk' O)) :
    x ∈ L := by
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hx
  have ho : l⁻¹ * x ∈ O := QuotientGroup.eq.mp hlx
  exact mem_of_mul_odd (O := O) hO hl ho (by simp) hk

end Abstract

theorem mem_normalizer_of_conj_le {X : Type*} [Group X] [Finite X] {A : Subgroup X} {g : X}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ normalizer (A : Set X) := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact h a
  · intro ha
    rw [← heq] at ha
    obtain ⟨a', ha', h'⟩ := Subgroup.mem_map.mp ha
    have h'' : g * a' * g⁻¹ = g * a * g⁻¹ := by simpa [MulAut.conj_apply] using h'
    have : a' = a := mul_left_cancel (mul_right_cancel h'')
    rw [← this]; exact ha'

theorem mem_sylow_smul_iff {K : Type*} [Group K] [Finite K] (g : K) (S : Sylow 2 K) (x : K) :
    x ∈ ((g • S : Sylow 2 K) : Subgroup K) ↔ g⁻¹ * x * g ∈ (S : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_mul_mem_normalizer {X : Type*} [Group X] [Finite X] {O L A : Subgroup X}
    [O.Normal] [L.Normal] (hO : Odd (Nat.card O)) (hA : ∀ a ∈ A, a * a = 1)
    (hdec : ∀ a ∈ A, ∃ l ∈ A ⊓ L, ∃ c ∈ A, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c)
    {m : X} (hm : m ∈ L) (hmA : ∀ a ∈ A, m⁻¹ * a * m ∈ A ⊔ O) :
    ∃ r ∈ L ⊓ O, m * r ∈ normalizer (A : Set X) := by
  set R : Subgroup X := L ⊓ O with hR
  have hRn : R.Normal := Subgroup.normal_inf_normal L O
  have hRodd : Odd (Nat.card R) := by
    have hdvd : Nat.card R ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_right
    exact Odd.of_dvd_nat hO hdvd
  have hstep : ∀ a ∈ A, m⁻¹ * a * m ∈ R ⊔ A := by
    intro a ha
    obtain ⟨l, hlAL, c, hcA, hc, rfl⟩ := hdec a ha
    have hlA : l ∈ A := hlAL.1
    have hlL : l ∈ L := hlAL.2
    have h1 : m⁻¹ * l * m ∈ R ⊔ A := by
      have hmem : m⁻¹ * l * m ∈ A ⊔ O := hmA l hlA
      obtain ⟨a', ha', o, ho, hao⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
      have hL1 : m⁻¹ * l * m ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hm) hlL) hm
      have ha'L : a' ∈ L := by
        refine mem_of_mul_odd (O := O) hO (l := m⁻¹ * l * m) hL1 (o := o⁻¹) (O.inv_mem ho) ?_
          (k := 1) ?_
        · rw [← hao]; group
        · have := hA a' ha'
          simpa [pow_one, sq] using this
      have hoL : o ∈ L := by
        have : o = a'⁻¹ * (m⁻¹ * l * m) := by rw [← hao]; group
        rw [this]
        exact L.mul_mem (L.inv_mem ha'L) hL1
      rw [← hao]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha')
        (Subgroup.mem_sup_left (show o ∈ R from ⟨hoL, ho⟩))
    have h2 : m⁻¹ * c * m ∈ R ⊔ A := by
      have hr : ⁅c, m⁻¹⁆ ∈ R := by
        refine ⟨?_, hc m⁻¹ (L.inv_mem hm)⟩
        have : ⁅c, m⁻¹⁆ = (c * m⁻¹ * c⁻¹) * m := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact L.mul_mem ((inferInstance : L.Normal).conj_mem _ (L.inv_mem hm) c) hm
      have : m⁻¹ * c * m = ⁅c, m⁻¹⁆⁻¹ * c := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (R.inv_mem hr)) (Subgroup.mem_sup_right hcA)
    have h3 : m⁻¹ * (l * c) * m = (m⁻¹ * l * m) * (m⁻¹ * c * m) := by group
    rw [h3]
    exact Subgroup.mul_mem _ h1 h2
  have hAR : A ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxL, hxO⟩ : x ∈ A ∧ x ∈ L ∧ x ∈ O := ⟨hx.1, hx.2.1, hx.2.2⟩
    have h1 : x ^ (2 ^ 1) = 1 := by simpa [pow_one, sq] using hA x hxA
    have h2 : x ^ (Nat.card O) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hxO)
    exact eq_one_of_pow_odd h1 h2 hO
  have hcard : Nat.card ↥(R ⊔ A) = Nat.card R * Nat.card A :=
    CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer (A := R) (B := A)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) (by rw [inf_comm]; exact hAR)
  set AR : Subgroup X := R ⊔ A with hARdef
  have hA_le : A ≤ AR := le_sup_right
  have hR_le : R ≤ AR := le_sup_left
  set B : Subgroup X := A.map (MulAut.conj m⁻¹).toMonoidHom with hB
  have hB_mem : ∀ x, x ∈ B ↔ ∃ a ∈ A, m⁻¹ * a * m = x := by
    intro x
    simp [hB, Subgroup.mem_map]
  have hB_le : B ≤ AR := fun x hx => by
    obtain ⟨a, ha, rfl⟩ := (hB_mem x).mp hx
    exact hstep a ha
  have hBexp : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hB_mem x).mp hx
    calc m⁻¹ * a * m * (m⁻¹ * a * m) = m⁻¹ * (a * a) * m := by group
      _ = 1 := by rw [hA a ha]; group
  have hpg : ∀ C : Subgroup X, (∀ x ∈ C, x * x = 1) → C ≤ AR →
      IsPGroup 2 ↥(C.subgroupOf AR) := by
    intro C hC hCAR x
    refine ⟨1, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    have := hC (x : X) (Subgroup.mem_subgroupOf.mp x.2)
    simpa [sq] using this
  have hindex : ∀ C : Subgroup X, Nat.card C = Nat.card A → C ≤ AR →
      ¬ 2 ∣ (C.subgroupOf AR).index := by
    intro C hCA hCAR
    have h1 := Subgroup.card_mul_index (C.subgroupOf AR)
    have h2 : Nat.card ↥(C.subgroupOf AR) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCAR).toEquiv
    rw [h2, hCA, hcard] at h1
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h3 : (C.subgroupOf AR).index = Nat.card R := by
      have : Nat.card A * (C.subgroupOf AR).index = Nat.card A * Nat.card R := by
        rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hApos this
    rw [h3]
    have := Nat.odd_iff.mp hRodd
    omega
  have hBcard : Nat.card B = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective
  let P₁ : Sylow 2 ↥AR := (hpg A hA hA_le).toSylow (hindex A rfl hA_le)
  let P₂ : Sylow 2 ↥AR := (hpg B hBexp hB_le).toSylow (hindex B hBcard hB_le)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥AR) P₁ P₂
  have hP2 : ∀ x : ↥AR, (x : X) ∈ B ↔ g⁻¹ * x * g ∈ A.subgroupOf AR := by
    intro x
    have h1 : x ∈ ((P₂ : Sylow 2 ↥AR) : Subgroup ↥AR) ↔ (x : X) ∈ B := Subgroup.mem_subgroupOf
    rw [← h1, ← hg, mem_sylow_smul_iff]
    rfl
  obtain ⟨r, hr, a, ha, hra⟩ := Subgroup.mem_sup_of_normal_left.mp g.2
  refine ⟨r, hr, mem_normalizer_of_conj_le fun a₀ ha₀ => ?_⟩
  have hmem : r * a₀ * r⁻¹ ∈ AR :=
    AR.mul_mem (AR.mul_mem (hR_le hr) (hA_le ha₀)) (AR.inv_mem (hR_le hr))
  have hx := (hP2 ⟨r * a₀ * r⁻¹, hmem⟩).mpr (by
    rw [Subgroup.mem_subgroupOf]
    have : (g⁻¹ * (⟨r * a₀ * r⁻¹, hmem⟩ : ↥AR) * g : ↥AR) = ⟨a⁻¹ * a₀ * a, by
        exact AR.mul_mem (AR.mul_mem (AR.inv_mem (hA_le ha)) (hA_le ha₀)) (hA_le ha)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hra]; group
    rw [this]
    exact A.mul_mem (A.mul_mem (A.inv_mem ha) ha₀) ha)
  obtain ⟨a₁, ha₁, h₁⟩ := (hB_mem _).mp hx
  have h₁' : r * a₀ * r⁻¹ = m⁻¹ * a₁ * m := h₁.symm
  have : m * r * a₀ * (m * r)⁻¹ = a₁ := by
    calc m * r * a₀ * (m * r)⁻¹ = m * (r * a₀ * r⁻¹) * m⁻¹ := by group
      _ = a₁ := by rw [h₁']; group
  rw [this]
  exact ha₁

section Bar

variable {G : Type} [Group G] [Finite G]

abbrev bar (H : Subgroup G) : ↥H →* Hbar H := QuotientGroup.mk' (pPrimeCore 2 ↥H)

theorem odd_card_core (H : Subgroup G) : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := 2))

theorem pPrimeCore_hbar (H : Subgroup G) : pPrimeCore 2 (Hbar H) = ⊥ :=
  CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) 2

omit [Finite G] in
theorem bar_eq_one_iff {H : Subgroup G} {x : ↥H} : bar H x = 1 ↔ x ∈ pPrimeCore 2 ↥H :=
  QuotientGroup.eq_one_iff x

omit [Finite G] in
theorem bar_eq_bar_iff {H : Subgroup G} {x y : ↥H} :
    bar H x = bar H y ↔ x⁻¹ * y ∈ pPrimeCore 2 ↥H :=
  QuotientGroup.eq

omit [Finite G] in
theorem mem_hbarImage {H X : Subgroup G} {y : Hbar H} :
    y ∈ hbarImage H X ↔ ∃ x : ↥H, (x : G) ∈ X ∧ bar H x = y := by
  unfold hbarImage
  simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem bar_mem_hbarImage {H X : Subgroup G} {x : ↥H} (hx : (x : G) ∈ X) :
    bar H x ∈ hbarImage H X :=
  mem_hbarImage.mpr ⟨x, hx, rfl⟩

omit [Finite G] in
theorem hbarImage_normal {H L : Subgroup G} (hLH : L ≤ H) (hL : H ≤ normalizer (L : Set G)) :
    (hbarImage H L).Normal := by
  have : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hL
  exact Subgroup.Normal.map this (bar H) (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem mem_centralizerBar {H L : Subgroup G} {g : G} :
    g ∈ centralizerBar H L ↔ ∃ hg : g ∈ H, ∀ l : ↥H, (l : G) ∈ L →
      bar H l * bar H ⟨g, hg⟩ = bar H ⟨g, hg⟩ * bar H l := by
  unfold centralizerBar
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe, Subgroup.coe_subtype]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, fun l hl => ?_⟩
    exact hh _ (bar_mem_hbarImage hl)
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, fun y hy => ?_, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_hbarImage.mp hy
    exact hc l hl

omit [Finite G] in
theorem centralizerBar_le (H L : Subgroup G) : centralizerBar H L ≤ H := fun _ hg =>
  (mem_centralizerBar.mp hg).1

omit [Finite G] in
theorem bar_commutator_mem_iff {H : Subgroup G} {c l : ↥H} :
    ⁅c, l⁆ ∈ pPrimeCore 2 ↥H ↔ bar H c * bar H l = bar H l * bar H c := by
  rw [← bar_eq_one_iff, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]

end Bar

end Setup

end CFSG.GH74.Uniqueness.SU.SU8
