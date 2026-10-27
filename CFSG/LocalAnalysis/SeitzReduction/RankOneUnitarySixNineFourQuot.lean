module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineFourBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryClosureBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStartBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

namespace SixNineFour

theorem card_inf_centralizer_mul_le {D : Type*} [Group D] [Finite D] {A : Subgroup D} {w : D}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hwA : w ∈ normalizer (A : Set D))
    (hfree : ∀ e ∈ A, e * w = w * e → ∃ a ∈ A, e = a * w * a⁻¹ * w⁻¹) :
    Nat.card (A ⊓ centralizer {w} : Subgroup D) * Nat.card (A ⊓ centralizer {w} : Subgroup D) ≤
      Nat.card A := by
  have hconj : ∀ a ∈ A, w * a⁻¹ * w⁻¹ ∈ A := fun a ha =>
    (mem_normalizer_iff.mp hwA _).mp (inv_mem ha)
  let φ : A →* A :=
    { toFun := fun a => ⟨a * (w * (a : D)⁻¹ * w⁻¹), mul_mem a.2 (hconj a a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [coe_mul, mul_inv_rev]
        have h1 := hAc _ (mul_mem b.2 (hconj b b.2)) _ (hconj a a.2)
        calc (a : D) * b * (w * ((b : D)⁻¹ * (a : D)⁻¹) * w⁻¹) =
            a * ((b * (w * (b : D)⁻¹ * w⁻¹)) * (w * (a : D)⁻¹ * w⁻¹)) := by group
          _ = a * ((w * (a : D)⁻¹ * w⁻¹) * (b * (w * (b : D)⁻¹ * w⁻¹))) := by rw [h1]
          _ = (a : D) * (w * (a : D)⁻¹ * w⁻¹) * (b * (w * (b : D)⁻¹ * w⁻¹)) := by group) }
  have hφ : ∀ a : A, ((φ a : A) : D) = a * w * (a : D)⁻¹ * w⁻¹ := fun a => by
    show (a : D) * (w * (a : D)⁻¹ * w⁻¹) = _
    group
  have hmemA : ∀ k : (A ⊓ centralizer {w} : Subgroup D), (k : D) ∈ A := fun k => (mem_inf.mp k.2).1
  have hker : ∀ k : (A ⊓ centralizer {w} : Subgroup D), (⟨k, hmemA k⟩ : A) ∈ φ.ker := by
    intro k
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    rw [hφ]
    have hkw : (k : D) * w = w * k := mem_centralizer_singleton_iff.mp (mem_inf.mp k.2).2
    simp only [coe_one]
    rw [hkw]
    group
  have hrange : ∀ k : (A ⊓ centralizer {w} : Subgroup D), (⟨k, hmemA k⟩ : A) ∈ φ.range := by
    intro k
    obtain ⟨a, ha, hae⟩ := hfree k (hmemA k) (mem_centralizer_singleton_iff.mp (mem_inf.mp k.2).2)
    exact ⟨⟨a, ha⟩, Subtype.ext (by rw [hφ]; exact hae.symm)⟩
  have h1 : Nat.card (A ⊓ centralizer {w} : Subgroup D) ≤ Nat.card φ.ker :=
    Nat.card_le_card_of_injective (fun k => (⟨⟨k, hmemA k⟩, hker k⟩ : φ.ker))
      fun k k' h => Subtype.ext (by simpa using congrArg (fun x : φ.ker => ((x : A) : D)) h)
  have h2 : Nat.card (A ⊓ centralizer {w} : Subgroup D) ≤ Nat.card φ.range :=
    Nat.card_le_card_of_injective (fun k => (⟨⟨k, hmemA k⟩, hrange k⟩ : φ.range))
      fun k k' h => Subtype.ext (by simpa using congrArg (fun x : φ.range => ((x : A) : D)) h)
  have h3 : Nat.card φ.ker * Nat.card φ.range = Nat.card A := by
    rw [← index_ker, card_mul_index]
  calc _ ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul h1 h2
    _ = Nat.card A := h3

theorem le_two_pow_of_mul_self_le {c f : ℕ} (h : c * c ≤ 2 ^ (4 * f)) : c ≤ 2 ^ (2 * f) := by
  by_contra hc
  push Not at hc
  have h1 : 2 ^ (2 * f) * 2 ^ (2 * f) < c * c := Nat.mul_self_lt_mul_self hc
  rw [← pow_add, show 2 * f + 2 * f = 4 * f by ring] at h1
  omega

variable {G : Type} [Group G] [Finite G]

structure FourData (R U S : Subgroup G) (t v : G) (f : ℕ) : Prop where
  sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = S
  le : R ≤ U
  le_S : U ≤ S
  normR : S ≤ normalizer (R : Set G)
  normU : S ≤ normalizer (U : Set G)
  comm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ R
  sq : ∀ x ∈ U, x ^ 2 ∈ R
  card : Nat.card U = 2 ^ (4 * f) * Nat.card R
  commS : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ U
  t_mem : t ∈ S
  v_mem : v ∈ S
  t_sq : t ^ 2 = 1
  v_sq : v ^ 2 = 1
  tv_comm : t * v = v * t
  t_not_mem : t ∉ U
  v_not_mem : v ∉ U
  tv_not_mem : t * v ∉ U
  cases : ∀ s ∈ S, s ∈ U ∨ t⁻¹ * s ∈ U ∨ v⁻¹ * s ∈ U ∨ (t * v)⁻¹ * s ∈ U
  free : ∀ w : G, (w = t ∨ w = v ∨ w = t * v) → ∀ x ∈ U, w * x * w⁻¹ * x⁻¹ ∈ R →
    ∃ y ∈ U, (y * w * y⁻¹ * w⁻¹)⁻¹ * x ∈ R

namespace FourData

variable {R U S : Subgroup G} {t v : G} {f : ℕ}

omit [Finite G] in
theorem mem_of_cases (h : FourData R U S t v f) {w : G} (hw : w = t ∨ w = v ∨ w = t * v) :
    w ∈ S ∧ w ^ 2 = 1 ∧ w ∉ U := by
  rcases hw with rfl | rfl | rfl
  · exact ⟨h.t_mem, h.t_sq, h.t_not_mem⟩
  · exact ⟨h.v_mem, h.v_sq, h.v_not_mem⟩
  · exact ⟨mul_mem h.t_mem h.v_mem, by rw [(Commute.mul_pow h.tv_comm 2), h.t_sq, h.v_sq,
      one_mul], h.tv_not_mem⟩

omit [Finite G] in
theorem exists_of_not_mem (h : FourData R U S t v f) {x : G} (hxS : x ∈ S) (hxU : x ∉ U) :
    ∃ w : G, (w = t ∨ w = v ∨ w = t * v) ∧ w⁻¹ * x ∈ U := by
  rcases h.cases _ hxS with h1 | h1 | h1 | h1
  · exact absurd h1 hxU
  · exact ⟨t, Or.inl rfl, h1⟩
  · exact ⟨v, Or.inr (Or.inl rfl), h1⟩
  · exact ⟨t * v, Or.inr (Or.inr rfl), h1⟩

theorem exists_mem_normalizer (hG : Goldschmidt1974) (h : FourData R U S t v f) (hf : 2 ≤ f)
    {g : G} (hg : g ∈ normalizer (R : Set G)) (hgt : g⁻¹ * t * g = v) :
    ∃ n ∈ normalizer (R : Set G) ⊓ normalizer (U : Set G), v⁻¹ * (n⁻¹ * t * n) ∈ R := by
  classical
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := h.sylow
  set X := normalizer (R : Set G) with hXdef
  set N := R.subgroupOf X with hNdef
  set π := QuotientGroup.mk' N with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hRS : R ≤ S := h.le.trans h.le_S
  have hSX : S ≤ X := h.normR
  have hUX : U ≤ X := h.le_S.trans hSX
  set Sb := (S.subgroupOf X).map π with hSb
  set Ab := (U.subgroupOf X).map π with hAb
  have memS : ∀ x : X, π x ∈ Sb ↔ (x : G) ∈ S := StrongClosureMod.mem_map_mk_iff hRS
  have memU : ∀ x : X, π x ∈ Ab ↔ (x : G) ∈ U := StrongClosureMod.mem_map_mk_iff h.le
  have hone : ∀ x : X, π x = 1 ↔ (x : G) ∈ R := fun x =>
    (QuotientGroup.eq_one_iff x).trans mem_subgroupOf
  have hAbcomm : ∀ a ∈ Ab, ∀ b ∈ Ab, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    replace hx : (x : G) ∈ U := mem_subgroupOf.mp hx
    replace hy : (y : G) ∈ U := mem_subgroupOf.mp hy
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)
    have h1 := h.comm _ (inv_mem hy) _ (inv_mem hx)
    have e : (((x * y)⁻¹ * (y * x) : X) : G) =
        (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹⁻¹ * (x : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact h1
  have hAbsq : ∀ a ∈ Ab, a ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hone]
    simpa using h.sq _ (mem_subgroupOf.mp hx)
  have hAbel : IsElementaryAbelian 2 Ab :=
    { toIsMulCommutative := ⟨⟨fun u w => Subtype.ext (hAbcomm _ u.2 _ w.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hAbsq _ u.2) }
  have hAbo : CFSG.Open.IsElemAbelian 2 Ab :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 Ab).mp hAbel
  have hAbcard : Nat.card Ab = 2 ^ (4 * f) := by
    rw [hAb, StrongClosureMod.card_map_mk hUX]
    have h1 := StrongClosureMod.relIndex_mul_card_of_le h.le
    rw [h.card] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hAbrank : CFSG.pRank 2 Ab = 4 * f :=
    CFSG.LocalAnalysis.GorensteinLyons.pRank_eq_of_elementary one_lt_two hAbo hAbcard
  have hSbN : Sb ≤ normalizer (Ab : Set (X ⧸ N)) := by
    refine le_trans (map_mono fun s hs => ?_) (le_normalizer_map π)
    refine mem_normalizer_iff.mpr fun y => ?_
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp (h.normU (mem_subgroupOf.mp hs)) y
  have hAbSb : Ab ≤ Sb :=
    map_mono fun x hx => mem_subgroupOf.mpr (h.le_S (mem_subgroupOf.mp hx))
  have hAbn : (Ab.subgroupOf Sb).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAbSb).mpr hSbN
  have hS2 : IsPGroup 2 S := by rw [← hS₀]; exact S₀.isPGroup'
  have hSb2 : IsPGroup 2 Sb := (hS2.of_equiv (subgroupOfEquivOfLe hSX).symm).map π
  have hS₀X : (S₀ : Subgroup G) ≤ X := by rw [hS₀]; exact hSX
  set P : Sylow 2 (X ⧸ N) := (S₀.subtype hS₀X).mapSurjective hπs with hPdef
  have hP : (P : Subgroup (X ⧸ N)) = Sb := by
    rw [hPdef, Sylow.coe_mapSurjective, Sylow.coe_subtype, hS₀]
  set tX : X := ⟨t, hSX h.t_mem⟩ with htX
  set vX : X := ⟨v, hSX h.v_mem⟩ with hvX
  have hcls : ∀ (c x : X) (hc : π c ∈ Sb) (hx : π x ∈ Sb), (c : G)⁻¹ * x ∈ U →
      (QuotientGroup.mk (⟨π c, hc⟩ : Sb) : Sb ⧸ Ab.subgroupOf Sb) = QuotientGroup.mk ⟨π x, hx⟩ := by
    intro c x hc hx hcx
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)
    show (π c)⁻¹ * π x ∈ Ab
    rw [← map_inv, ← map_mul, memU]
    simpa using hcx
  have hQcard : Nat.card (Sb ⧸ Ab.subgroupOf Sb) ≤ 4 := by
    have htb : π tX ∈ Sb := (memS tX).mpr h.t_mem
    have hvb : π vX ∈ Sb := (memS vX).mpr h.v_mem
    have htvb : π (tX * vX) ∈ Sb := (memS _).mpr (mul_mem h.t_mem h.v_mem)
    let F : Fin 4 → Sb ⧸ Ab.subgroupOf Sb := ![QuotientGroup.mk ⟨π 1, (memS 1).mpr (one_mem _)⟩,
      QuotientGroup.mk ⟨π tX, htb⟩, QuotientGroup.mk ⟨π vX, hvb⟩,
      QuotientGroup.mk ⟨π (tX * vX), htvb⟩]
    have hF : Function.Surjective F := by
      intro q
      obtain ⟨⟨_, ⟨x, hx, rfl⟩⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hxS : (x : G) ∈ S := mem_subgroupOf.mp hx
      rcases h.cases _ hxS with h1 | h1 | h1 | h1
      · exact ⟨0, hcls 1 x _ _ (by simpa using h1)⟩
      · exact ⟨1, hcls tX x _ _ h1⟩
      · exact ⟨2, hcls vX x _ _ h1⟩
      · exact ⟨3, hcls (tX * vX) x _ _ h1⟩
    calc Nat.card (Sb ⧸ Ab.subgroupOf Sb) ≤ Nat.card (Fin 4) := Nat.card_le_card_of_surjective F hF
      _ = 4 := by simp
  have hcent : ∀ xb ∈ Sb, xb ∉ Ab →
      Nat.card (Ab ⊓ centralizer {xb} : Subgroup (X ⧸ N)) ≤ 2 ^ (2 * f) := by
    rintro _ ⟨x, hx, rfl⟩ hxA
    have hxS : (x : G) ∈ S := mem_subgroupOf.mp hx
    obtain ⟨w, hw, hwx⟩ := h.exists_of_not_mem hxS fun h1 => hxA ((memU x).mpr h1)
    obtain ⟨hwS, -, -⟩ := h.mem_of_cases hw
    set wX : X := ⟨w, hSX hwS⟩ with hwX
    have hux : π (wX⁻¹ * x) ∈ Ab := (memU _).mpr (by simpa [hwX] using hwx)
    have hle : Ab ⊓ centralizer {π x} ≤ Ab ⊓ centralizer {π wX} := by
      intro e he
      obtain ⟨heA, hec⟩ := mem_inf.mp he
      refine mem_inf.mpr ⟨heA, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : e * π x = π x * e := mem_centralizer_singleton_iff.mp hec
      have h2 : e * π (wX⁻¹ * x) = π (wX⁻¹ * x) * e := hAbcomm _ heA _ hux
      have e3 : π x = π wX * π (wX⁻¹ * x) := by rw [← map_mul, mul_inv_cancel_left]
      rw [e3] at h1
      have h4 : e * π wX * π (wX⁻¹ * x) = π wX * e * π (wX⁻¹ * x) := by
        calc e * π wX * π (wX⁻¹ * x) = e * (π wX * π (wX⁻¹ * x)) := by group
          _ = π wX * π (wX⁻¹ * x) * e := h1
          _ = π wX * (π (wX⁻¹ * x) * e) := by group
          _ = π wX * (e * π (wX⁻¹ * x)) := by rw [h2]
          _ = π wX * e * π (wX⁻¹ * x) := by group
      exact mul_right_cancel h4
    refine (card_le_of_le hle).trans (le_two_pow_of_mul_self_le ?_)
    rw [← hAbcard]
    refine card_inf_centralizer_mul_le hAbcomm (hSbN ((memS wX).mpr hwS)) ?_
    rintro _ ⟨y, hy, rfl⟩ hyw
    have hyU : (y : G) ∈ U := mem_subgroupOf.mp hy
    have h1 : w * y * w⁻¹ * (y : G)⁻¹ ∈ R := by
      have h2 : π (wX * y * wX⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hyw]; group
      simpa [hwX] using (hone _).mp h2
    obtain ⟨z, hz, hzy⟩ := h.free w hw _ hyU h1
    set zX : X := ⟨z, hUX hz⟩ with hzX
    refine ⟨π zX, (memU zX).mpr hz, ?_⟩
    have h2 : π ((zX * wX * zX⁻¹ * wX⁻¹)⁻¹ * y) = 1 := (hone _).mpr (by simpa [hzX, hwX] using hzy)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [← h2]
    simp only [map_mul, map_inv]
  have hrank : ∀ xb ∈ Sb, xb ∉ Ab → CFSG.pRank 2 (Sb ⧸ Ab.subgroupOf Sb) +
      CFSG.pRank 2 ↥(Ab ⊓ centralizer {xb}) < CFSG.pRank 2 Ab := by
    intro xb hxb hxbA
    have h1 : CFSG.pRank 2 (Sb ⧸ Ab.subgroupOf Sb) ≤ 2 :=
      CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun B _ =>
        (card_le_card_group B).trans (hQcard.trans (by norm_num))
    have h2 : CFSG.pRank 2 ↥(Ab ⊓ centralizer {xb}) ≤ 2 * f :=
      CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun B _ =>
        (card_le_card_group B).trans (hcent xb hxb hxbA)
    rw [hAbrank]
    omega
  have hsc := (CFSG.LocalAnalysis.GorensteinLyons.elementary_strict_rank_strong_closure_criterion
    hSb2 hAbSb hAbel hrank).2.2 ⟨P, hP⟩
  set M := normalClosure (Ab : Set (X ⧸ N)) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hAbM : Ab ≤ M := fun a ha => subset_normalClosure ha
  have hinv : ∀ z ∈ Sb, z ∈ M → z ^ 2 = 1 → z ∈ Ab := by
    intro z hz hzM hz2
    refine mem_of_sq_eq_one_of_mem_normalClosure hG P (by rw [hP]; exact hAbSb)
      ⟨⟨fun a b => Subtype.ext (hAbcomm _ a.2 _ b.2)⟩⟩ hAbsq
      (fun a ha g hga => hsc.2 a ha g (by rwa [← hP])) (by rw [hP]; exact hz) hzM hz2
  have hinf : Sb ⊓ M = Ab := by
    refine le_antisymm (fun z hz => ?_) (le_inf hAbSb hAbM)
    obtain ⟨⟨x, hx, rfl⟩, hzM⟩ := mem_inf.mp hz
    have hxS : (x : G) ∈ S := mem_subgroupOf.mp hx
    by_contra hxA
    obtain ⟨w, hw, hwx⟩ := h.exists_of_not_mem hxS fun h1 => hxA ((memU x).mpr h1)
    obtain ⟨hwS, hw2, hwU⟩ := h.mem_of_cases hw
    set wX : X := ⟨w, hSX hwS⟩ with hwX
    have hux : π (wX⁻¹ * x) ∈ Ab := (memU _).mpr (by simpa [hwX] using hwx)
    have hwM : π wX ∈ M := by
      have e : π wX = π x * (π (wX⁻¹ * x))⁻¹ := by rw [map_mul, map_inv]; group
      rw [e]
      exact mul_mem hzM (inv_mem (hAbM hux))
    have hw2' : π wX ^ 2 = 1 := by
      rw [← map_pow, hone]
      simp [hwX, hw2]
    exact hwU ((memU wX).mp (hinv _ ((memS wX).mpr hwS) hwM hw2'))
  have hcommSb : ∀ a ∈ (P : Subgroup (X ⧸ N)), ∀ b ∈ (P : Subgroup (X ⧸ N)),
      a * b * a⁻¹ * b⁻¹ ∈ Ab := by
    rw [hP]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, memU]
    simpa using h.commS _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy)
  have htt : t * t = 1 := by rw [← pow_two, h.t_sq]
  have ht2 : π tX * π tX = 1 := by
    rw [← map_mul, hone]
    simp [htX, htt]
  have ht2' : π tX ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hfreet : ∀ a ∈ Ab, (a * π tX) ^ 2 = 1 → ∃ b ∈ Ab, b⁻¹ * π tX * b = a * π tX := by
    rintro _ ⟨u, hu, rfl⟩ hut
    have huU : (u : G) ∈ U := mem_subgroupOf.mp hu
    have hu2 : π u * π u = 1 := by rw [← pow_two]; exact hAbsq _ ⟨u, hu, rfl⟩
    have h1 : π (tX * u * tX⁻¹ * u⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, inv_eq_of_mul_eq_one_right ht2,
        inv_eq_of_mul_eq_one_right hu2]
      rw [pow_two] at hut
      calc π tX * π u * π tX * π u = (π u)⁻¹ * (π u * π tX * (π u * π tX)) * π u := by group
        _ = 1 := by rw [hut, mul_one, inv_mul_cancel]
    have h2 : t * u * t⁻¹ * (u : G)⁻¹ ∈ R := by simpa [htX] using (hone _).mp h1
    obtain ⟨y, hy, hyu⟩ := h.free t (Or.inl rfl) _ huU h2
    set yX : X := ⟨y, hUX hy⟩ with hyX
    refine ⟨(π yX)⁻¹, inv_mem ((memU yX).mpr hy), ?_⟩
    have h3 : π ((yX * tX * yX⁻¹ * tX⁻¹)⁻¹ * u) = 1 :=
      (hone _).mpr (by simpa [hyX, htX] using hyu)
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    rw [← h3]
    simp only [map_mul, map_inv]
    group
  have hgv : (π ⟨g, hg⟩)⁻¹ * π tX * π ⟨g, hg⟩ = π vX := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa [htX, hvX] using hgt)
  have hvN : π vX ∈ normalizer (Ab : Set (X ⧸ N)) := hSbN ((memS vX).mpr h.v_mem)
  obtain ⟨nb, hnb, hnbt⟩ := exists_mem_normalizer_conj_of_inf_eq P hMn (by rw [hP]; exact hinf)
    hcommSb (by rw [hP]; exact (memS tX).mpr h.t_mem) ht2' hfreet
    (x := π ⟨g, hg⟩) (by rw [hgv]; exact hvN)
  obtain ⟨n, rfl⟩ := hπs nb
  refine ⟨n, mem_inf.mpr ⟨n.2, ?_⟩, ?_⟩
  · refine mem_normalizer_of_forall_inv_mul_mul_mem fun u hu => ?_
    have h1 : (π n)⁻¹ * π ⟨u, hUX hu⟩ * π n ∈ Ab :=
      (mem_normalizer_iff''.mp hnb _).mp ((memU _).mpr hu)
    rw [← map_inv, ← map_mul, ← map_mul, memU] at h1
    simpa using h1
  · have h1 : π (vX⁻¹ * (n⁻¹ * tX * n)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hnbt, hgv, inv_mul_cancel]
    simpa [hvX, htX] using (hone _).mp h1

end FourData

end SixNineFour

end CFSG.SeitzReduction.RankOne
