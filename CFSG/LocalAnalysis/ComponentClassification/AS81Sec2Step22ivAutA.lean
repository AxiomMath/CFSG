module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivAut
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2F0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open LinearFlag CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mem_sup_of_pow_two {X : Type*} [Group X] {H N : Subgroup X} [N.Normal]
    (hodd : Odd (Nat.card N)) (hNH : N ≤ centralizer (H : Set X)) {x : X} (hx : x ∈ H ⊔ N)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ H := by
  obtain ⟨h, hh, n, hn, rfl⟩ := mem_sup_of_normal_right.mp hx
  have hc : Commute h n := (mem_centralizer_iff.mp (hNH hn)) h hh
  have h1 : n ^ 2 ^ k = (h ^ 2 ^ k)⁻¹ := by
    rw [hc.mul_pow] at hk
    exact eq_inv_of_mul_eq_one_right hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf n) := by
    refine Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2 => ?_)
    have : Odd (orderOf n) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hnH : n ∈ H := by
    rw [← hj, h1]
    exact pow_mem (inv_mem (pow_mem hh _)) j
  exact mul_mem hh hnH

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_cover_projRad_zero (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ c : L34Cover ↥A, ∃ φ : ↥A →* projectiveSL 3 c.k, Function.Surjective φ ∧
      φ.ker = center ↥A ∧ ((E ⊓ A).subgroupOf A).map φ = projRad c.k 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hF.quasisimple
  obtain ⟨cv⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have : CharP cv.k 2 := charP_two_of_card cv.card_k
  have hO := oddCore_le_center hq.1 hq.2
  have hU : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  have hU16 : Nat.card (E ⊓ A : Subgroup G) = 16 := card_inf_left hF hodd
  have hH₀ : IsPGroup 2 ((E ⊓ A).subgroupOf A) :=
    (isPGroup_two_of_isElemAbelian hU).comap_subtype
  obtain ⟨T, hT⟩ := hH₀.exists_le_sylow
  obtain ⟨φ, hφs, hφk, hφT⟩ := cv.exists_std hO T
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hH₀2 : ∀ x ∈ ((E ⊓ A).subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hU.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card (((E ⊓ A).subgroupOf A).map φ) = 16 := by
    rw [card_map_of_isPGroup φ hkerodd hH₀, ← hU16]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hH₀U : ((E ⊓ A).subgroupOf A).map φ ≤ projUnip cv.k := hφT ▸ map_mono hT
  rcases eq_projRad_of_le_projUnip cv.card_k hH₀U hH₀2 hH₀16 with h0 | h1
  · exact ⟨cv, φ, hφs, hφk, h0⟩
  · refine ⟨cv, Sec2Aut.radSwap.toMonoidHom.comp φ,
      Sec2Aut.radSwap.surjective.comp hφs, ?_, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφk]
    · rw [← Subgroup.map_map, h1, Sec2Aut.map_projRad_one_radSwap]


omit [Finite G] in
theorem descendAut_pow_apply {A : Subgroup G} {k : Type} [Field k] {φ : ↥A →* projectiveSL 3 k}
    (hφs : Function.Surjective φ) (hφk : φ.ker = center ↥A) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (n : ℕ) (a : ↥A) :
    (descendAut φ hφs (normalizerConj hxA) (by rw [hφk]; exact Subgroup.map_center_eq _) ^ n)
      (φ a) = φ ⟨x ^ n * a * (x ^ n)⁻¹, by
        have := (mem_normalizer_iff.mp (pow_mem hxA n) a).mp a.2
        exact this⟩ := by
  induction n generalizing a with
  | zero =>
    simp only [pow_zero, MulAut.one_apply, one_mul, inv_one, mul_one]
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, descendAut_apply, ih]
    congr 1
    apply Subtype.ext
    show x ^ n * ((normalizerConj hxA a : ↥A) : G) * (x ^ n)⁻¹ = x ^ (n + 1) * a * (x ^ (n + 1))⁻¹
    rw [coe_normalizerConj_apply, pow_succ]
    group

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

omit [Finite G] in
theorem descendAut_mem_projRad {k : Type} [Field k] {φ : ↥A →* projectiveSL 3 k}
    (hφs : Function.Surjective φ) (hφk : φ.ker = center ↥A)
    (hφU : ((E ⊓ A).subgroupOf A).map φ = projRad k 0) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxU : x ∈ normalizer ((E ⊓ A : Subgroup G) : Set G))
    {y : projectiveSL 3 k} (hy : y ∈ projRad k 0) :
    descendAut φ hφs (normalizerConj hxA) (by rw [hφk]; exact Subgroup.map_center_eq _) y ∈
      projRad k 0 := by
  rw [← hφU] at hy ⊢
  obtain ⟨u, hu, rfl⟩ := hy
  rw [descendAut_apply]
  refine ⟨normalizerConj hxA u, ?_, rfl⟩
  have hu' : (u : G) ∈ E ⊓ A := hu
  show ((normalizerConj hxA u : ↥A) : G) ∈ E ⊓ A
  rw [coe_normalizerConj_apply]
  exact (mem_normalizer_iff.mp hxU _).mp hu'

theorem exists_mem_inv_mul_mem_centralizer_of_fix (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {k : Type} [Field k]
    {φ : ↥A →* projectiveSL 3 k} (hφs : Function.Surjective φ) (hφk : φ.ker = center ↥A)
    (hφU : ((E ⊓ A).subgroupOf A).map φ = projRad k 0) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxU : x ∈ normalizer ((E ⊓ A : Subgroup G) : Set G))
    (hall : ∀ y ∈ projRad k 0, descendAut φ hφs (normalizerConj hxA)
      (by rw [hφk]; exact Subgroup.map_center_eq _) y = y) :
    ∃ u ∈ E ⊓ A, u⁻¹ * x ∈ centralizer (A : Set G) := by
  have hU : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  have hH₀ : IsPGroup 2 ((E ⊓ A).subgroupOf A) :=
    (isPGroup_two_of_isElemAbelian hU).comap_subtype
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  refine exists_mem_inv_mul_mem_centralizer hF.quasisimple hL hodd inf_le_right hU
    (card_inf_left hF hodd) hxA fun h hh => ?_
  have h1 : φ (normalizerConj hxA ⟨h, hh.2⟩) = φ ⟨h, hh.2⟩ := by
    rw [← descendAut_apply φ hφs (normalizerConj hxA)
      (by rw [hφk]; exact Subgroup.map_center_eq _)]
    exact hall _ (by rw [← hφU]; exact ⟨_, mem_subgroupOf.mpr hh, rfl⟩)
  have h2 := eq_of_map_eq_of_isPGroup φ hkerodd hH₀
    (mem_subgroupOf.mpr ((mem_normalizer_iff.mp hxU h).mp hh)) (mem_subgroupOf.mpr hh) h1
  exact congrArg Subtype.val h2

theorem exists_mem_inv_mul_mem_centralizer_of_card_le (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxU : x ∈ normalizer ((E ⊓ A : Subgroup G) : Set G))
    (h8 : 8 ≤ Nat.card ((E ⊓ A) ⊓ centralizer ({x} : Set G) : Subgroup G)) :
    ∃ u ∈ E ⊓ A, u⁻¹ * x ∈ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  have hH₀ : IsPGroup 2 ((E ⊓ A).subgroupOf A) :=
    (isPGroup_two_of_isElemAbelian hU).comap_subtype
  obtain ⟨c, φ, hφs, hφk, hφU⟩ := exists_cover_projRad_zero hF hL hodd
  have : CharP c.k 2 := charP_two_of_card c.card_k
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  set α := descendAut φ hφs (normalizerConj hxA) (by rw [hφk]; exact Subgroup.map_center_eq _)
    with hα
  have hαφ : ∀ a : ↥A, α (φ a) = φ (normalizerConj hxA a) := descendAut_apply _ _ _ _
  have hcoord : ∀ w : ↥((E ⊓ A) ⊓ centralizer ({x} : Set G)), ∃ v : c.k × c.k,
      proj 3 c.k (unipU c.k v.1 0 v.2) = φ ⟨w, w.2.1.2⟩ := fun w => by
    have hw : φ ⟨w, w.2.1.2⟩ ∈ projRad c.k 0 := by
      rw [← hφU]
      exact ⟨_, mem_subgroupOf.mpr w.2.1, rfl⟩
    obtain ⟨a, c', h⟩ := mem_projRad_zero.1 hw
    exact ⟨(a, c'), h⟩
  choose v hv using hcoord
  have hfix : ∀ w, α (proj 3 c.k (unipU c.k (v w).1 0 (v w).2)) =
      proj 3 c.k (unipU c.k (v w).1 0 (v w).2) := fun w => by
    rw [hv, hαφ]
    congr 1
    apply Subtype.ext
    rw [coe_normalizerConj_apply]
    have hc := mem_centralizer_iff.mp w.2.2 x (Set.mem_singleton x)
    rw [hc, mul_inv_cancel_right]
  have hinj : Function.Injective (fun w => (⟨v w, hfix w⟩ : {v : c.k × c.k //
      α (proj 3 c.k (unipU c.k v.1 0 v.2)) = proj 3 c.k (unipU c.k v.1 0 v.2)})) := by
    intro w w' h
    have h1 : v w = v w' := congrArg Subtype.val h
    have h2 : φ ⟨w, w.2.1.2⟩ = φ ⟨w', w'.2.1.2⟩ := by rw [← hv, ← hv, h1]
    have h3 := eq_of_map_eq_of_isPGroup φ hkerodd hH₀ (mem_subgroupOf.mpr w.2.1)
      (mem_subgroupOf.mpr w'.2.1) h2
    have h4 := congrArg Subtype.val h3
    exact Subtype.ext h4
  exact exists_mem_inv_mul_mem_centralizer_of_fix hF hL hodd hφs hφk hφU hxA hxU
    (Sec2Aut.fix_projRad_zero_of_card_le c.card_k
      (fun y hy => descendAut_mem_projRad hφs hφk hφU hxA hxU hy)
      (h8.trans (Nat.card_le_card_of_injective _ hinj)))

theorem mem_normalizer_of_map_mem (hF : Frame G A A R g E F) (hodd : Odd (Nat.card (center ↥A)))
    {k : Type} [Field k] {φ : ↥A →* projectiveSL 3 k} (hφk : φ.ker = center ↥A)
    (hφU : ((E ⊓ A).subgroupOf A).map φ = projRad k 0) {a : ↥A}
    (ha : φ a ∈ normalizer (projRad k 0 : Set (projectiveSL 3 k))) :
    (a : G) ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
  have hU : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hkerU : φ.ker ≤ centralizer (((E ⊓ A).subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    fun z hz => by
      rw [hφk] at hz
      exact mem_centralizer_iff.mpr fun u _ => (mem_center_iff.mp hz u)
  have hmaps : ∀ b : ↥A, φ b ∈ normalizer (projRad k 0 : Set (projectiveSL 3 k)) →
      ∀ x ∈ E ⊓ A, b * x * (b : G)⁻¹ ∈ E ⊓ A := by
    intro b hb x hx
    set u : ↥A := ⟨x, hx.2⟩
    have hu : u ∈ (E ⊓ A).subgroupOf A := mem_subgroupOf.mpr hx
    have h1 : b * u * b⁻¹ ∈ (E ⊓ A).subgroupOf A ⊔ φ.ker := by
      rw [← comap_map_eq, hφU, mem_comap, map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hb _).mp (hφU ▸ mem_map_of_mem φ hu)
    have hu2 : u * u = 1 := Subtype.ext (by
      simpa [sq] using hU.2 _ (mem_subgroupOf.mp hu))
    have h2 : (b * u * b⁻¹) ^ 2 ^ 1 = 1 := by
      calc (b * u * b⁻¹) ^ 2 ^ 1 = (b * u * b⁻¹) * (b * u * b⁻¹) := by rw [pow_one, sq]
        _ = b * (u * u) * b⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    exact mem_subgroupOf.mp (mem_of_mem_sup_of_pow_two hkerodd hkerU h1 h2)
  refine ⟨a.2, mem_normalizer_of_conj_mem (hmaps a ha) fun x hx => ?_⟩
  simpa using hmaps a⁻¹ (by rw [map_inv]; exact inv_mem ha) x hx

theorem exists_mem_commutator_eq_levi (hF : Frame G A A R g E F) (hodd : Odd (Nat.card (center ↥A)))
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4) {φ : ↥A →* projectiveSL 3 k}
    (hφs : Function.Surjective φ) (hφk : φ.ker = center ↥A)
    (hφU : ((E ⊓ A).subgroupOf A).map φ = projRad k 0) (B : SL2 k) :
    ∃ l : ↥A, (l : G) ∈ ⁅A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)⁆ ∧ φ l = proj 3 k (leviOne k B) := by
  set N := A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) with hNdef
  set N₀ := N.subgroupOf A with hN₀
  have hrange : (leviProj k 0).range ≤ N₀.map φ := by
    rintro _ ⟨B', rfl⟩
    obtain ⟨a, ha⟩ := hφs (leviProj k 0 B')
    refine ⟨a, mem_subgroupOf.mpr (mem_normalizer_of_map_mem hF hodd hφk hφU ?_), ha⟩
    rw [ha, leviProj, MonoidHom.comp_apply, levi_zero]
    exact leviOne_mem_normalizer B'
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k (by omega)
  have hcomm : (leviProj k 0).range = ⁅(leviProj k 0).range, (leviProj k 0).range⁆ := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def,
      hperf.commutator_eq_top]
  have hmem : proj 3 k (leviOne k B) ∈ ⁅N₀, N₀⁆.map φ := by
    rw [map_commutator]
    refine commutator_mono hrange hrange ?_
    rw [← hcomm]
    exact ⟨B, by rw [leviProj, MonoidHom.comp_apply, levi_zero]⟩
  obtain ⟨l, hl, hφl⟩ := hmem
  refine ⟨l, ?_, hφl⟩
  have h1 : (l : G) ∈ ⁅N₀, N₀⁆.map A.subtype := mem_map_of_mem _ hl
  rwa [map_commutator, hN₀, subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at h1

theorem exists_mem_inv_mul_mem_centralizer_of_levi (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {x : G}
    (hxA : x ∈ normalizer (A : Set G)) (hxU : x ∈ normalizer ((E ⊓ A : Subgroup G) : Set G))
    (h2 : ∃ n : ℕ, x ^ 2 ^ n = 1)
    (hLx : ∀ l ∈ ⁅A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)⁆, x * l * x⁻¹ * l⁻¹ ∈ E ⊓ A) :
    ∃ u ∈ E ⊓ A, u⁻¹ * x ∈ centralizer (A : Set G) := by
  obtain ⟨c, φ, hφs, hφk, hφU⟩ := exists_cover_projRad_zero hF hL hodd
  have : CharP c.k 2 := charP_two_of_card c.card_k
  set α := descendAut φ hφs (normalizerConj hxA) (by rw [hφk]; exact Subgroup.map_center_eq _)
    with hα
  refine exists_mem_inv_mul_mem_centralizer_of_fix hF hL hodd hφs hφk hφU hxA hxU
    (Sec2Aut.fix_projRad_zero_of_levi c.card_k
      (fun y hy => descendAut_mem_projRad hφs hφk hφU hxA hxU hy) (fun B => ?_) ?_)
  · obtain ⟨l, hl, hφl⟩ := exists_mem_commutator_eq_levi hF hodd c.card_k hφs hφk hφU B
    rw [← hφl, descendAut_apply, ← map_inv, ← map_mul, ← hφU]
    refine ⟨_, mem_subgroupOf.mpr ?_, rfl⟩
    show ((normalizerConj hxA l : ↥A) : G) * (l : G)⁻¹ ∈ E ⊓ A
    rw [coe_normalizerConj_apply]
    exact hLx l hl
  · obtain ⟨n, hn⟩ := h2
    refine ⟨n, MulEquiv.ext fun y => ?_⟩
    obtain ⟨a, rfl⟩ := hφs y
    rw [descendAut_pow_apply hφs hφk hxA, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only [hn, one_mul, inv_one, mul_one]

end Frame

end CFSG.ComponentClassification.AS81
