module

public import CFSG.LocalAnalysis.GH72.Coprime
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.OddInversion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GH72

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped Pointwise

universe u

section Defs

variable {A₀ G : Type*} [Group A₀] [Group G]

@[expose] def xySupOf (X₀ Y₀ : Subgroup A₀) (f : A₀ → A₀ → Subgroup G) : Subgroup G :=
  ⨆ (x : A₀) (_ : x ∈ X₀) (_ : x ≠ 1) (y : A₀) (_ : y ∈ Y₀) (_ : y ≠ 1), f x y

@[expose] def IsKxyGen (X₀ Y₀ : Subgroup A₀) (Kxy : A₀ → A₀ → Subgroup G) (F : Subgroup G) :
    Prop :=
  F ≤ xySupOf X₀ Y₀ fun x y => F ⊓ Kxy x y

structure Prop22Hyp (X₀ Y₀ : Subgroup A₀) (ι : A₀ →* G) (K : Subgroup G)
    (Kxy : A₀ → A₀ → Subgroup G) : Prop where
  kleinX : IsKleinFour X₀
  kleinY : IsKleinFour Y₀
  inf_eq : X₀ ⊓ Y₀ = ⊥
  comm : Y₀ ≤ centralizer (X₀ : Set A₀)
  sup_eq : X₀ ⊔ Y₀ = ⊤
  inj : Function.Injective ι
  odd : Odd (Nat.card K)
  normalizes : ι.range ≤ normalizer (K : Set G)
  le : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → Kxy x y ≤ K ⊓ C (ι x) ⊓ C (ι y)
  normal : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 →
    ((Kxy x y).subgroupOf (K ⊓ C (ι x) ⊓ C (ι y))).Normal
  inv : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → ι.range ≤ normalizer (Kxy x y : Set G)
  gen : K ≤ xySupOf X₀ Y₀ Kxy
  a : ∀ x ∈ X₀, x ≠ 1 → ∀ x' ∈ X₀, x' ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → ∀ y' ∈ Y₀, y' ≠ 1 →
    Kxy x y ⊓ C (ι x') ≤ Kxy x' y ∧ Kxy x y ⊓ C (ι y') ≤ Kxy x y'
  b : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → ∀ u ∈ K ⊓ C (ι x) ⊓ C (ι y),
    (∀ x' ∈ X₀, x' ∉ zpowers x → ι x' * u * (ι x')⁻¹ = u⁻¹) →
    (∀ y' ∈ Y₀, y' ∉ zpowers y → ι y' * u * (ι y')⁻¹ = u⁻¹) → u ∈ Kxy x y
  c : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 →
    (∀ u ∈ ⁅⁅K ⊓ C (ι x), Y₀.map ι⁆, ⁅K ⊓ C (ι x), Y₀.map ι⁆⁆ ⊓ C (ι y),
      (∀ y' ∈ Y₀, y' ∉ zpowers y → ι y' * u * (ι y')⁻¹ = u⁻¹) → u ∈ Kxy x y) ∧
    (∀ u ∈ ⁅⁅K ⊓ C (ι y), X₀.map ι⁆, ⁅K ⊓ C (ι y), X₀.map ι⁆⁆ ⊓ C (ι x),
      (∀ x' ∈ X₀, x' ∉ zpowers x → ι x' * u * (ι x')⁻¹ = u⁻¹) → u ∈ Kxy x y)
  d : ∀ (p : ℕ) (P : Subgroup G), p.Prime → IsPGroup p P → P ≤ K →
    ι.range ≤ normalizer (P : Set G) → IsKxyGen X₀ Y₀ Kxy P →
    ∀ Q ≤ P, ι.range ≤ normalizer (Q : Set G) → IsKxyGen X₀ Y₀ Kxy Q

@[expose] def Prop22Concl (X₀ Y₀ : Subgroup A₀) (ι : A₀ →* G) (K : Subgroup G)
    (Kxy : A₀ → A₀ → Subgroup G) : Prop :=
  ∀ F ≤ K, ι.range ≤ normalizer (F : Set G) → IsKxyGen X₀ Y₀ Kxy F

end Defs

@[expose] def Prop22Step (A₀ : Type*) [Group A₀] (X₀ Y₀ : Subgroup A₀) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (ι : A₀ →* G) (K : Subgroup G)
    (Kxy : A₀ → A₀ → Subgroup G), Prop22Hyp X₀ Y₀ ι K Kxy → (∀ p : ℕ, p.Prime → ¬ IsPGroup p K) →
    (∀ (G' : Type u) [Group G'] [Finite G'] (ι' : A₀ →* G') (K' : Subgroup G')
      (Kxy' : A₀ → A₀ → Subgroup G'), Prop22Hyp X₀ Y₀ ι' K' Kxy' →
        Nat.card K' < Nat.card K → Prop22Concl X₀ Y₀ ι' K' Kxy') →
    ∃ (H : Subgroup G) (r : ℕ), r.Prime ∧ IsPGroup r H ∧ H ≠ ⊥ ∧ H ≤ K ∧
      (H.subgroupOf K).Normal ∧ ι.range ≤ normalizer (H : Set G) ∧ IsKxyGen X₀ Y₀ Kxy H

section XySupOf

variable {A₀ G : Type*} [Group A₀] [Group G] {X₀ Y₀ : Subgroup A₀}

theorem le_xySupOf {f : A₀ → A₀ → Subgroup G} {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1)
    (hy : y ∈ Y₀) (hy1 : y ≠ 1) : f x y ≤ xySupOf X₀ Y₀ f :=
  le_iSup₂_of_le x hx <| le_iSup_of_le hx1 <| le_iSup₂_of_le y hy <| le_iSup_of_le hy1 le_rfl

theorem xySupOf_le {f : A₀ → A₀ → Subgroup G} {N : Subgroup G}
    (h : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → f x y ≤ N) : xySupOf X₀ Y₀ f ≤ N :=
  iSup₂_le fun x hx => iSup_le fun hx1 => iSup₂_le fun y hy => iSup_le fun hy1 => h x hx hx1 y hy hy1

theorem xySupOf_mono {f g : A₀ → A₀ → Subgroup G}
    (h : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → f x y ≤ g x y) : xySupOf X₀ Y₀ f ≤ xySupOf X₀ Y₀ g :=
  xySupOf_le fun x hx hx1 y hy hy1 => (h x hx hx1 y hy hy1).trans (le_xySupOf hx hx1 hy hy1)

theorem map_xySupOf {G' : Type*} [Group G'] (φ : G →* G') (f : A₀ → A₀ → Subgroup G) :
    (xySupOf X₀ Y₀ f).map φ = xySupOf X₀ Y₀ fun x y => (f x y).map φ := by
  simp only [xySupOf, Subgroup.map_iSup]

theorem mem_normalizer_xySupOf {f : A₀ → A₀ → Subgroup G} {g : G}
    (h : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → g ∈ normalizer (f x y : Set G)) :
    g ∈ normalizer (xySupOf X₀ Y₀ f : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, map_xySupOf]
  refine le_antisymm (xySupOf_mono fun x hx hx1 y hy hy1 => ?_)
    (xySupOf_mono fun x hx hx1 y hy hy1 => ?_)
  · exact (mem_normalizer_iff_map_conj_eq.mp (h x hx hx1 y hy hy1)).le
  · exact (mem_normalizer_iff_map_conj_eq.mp (h x hx hx1 y hy hy1)).ge

theorem xySupOf_sup_le (S : A₀ → A₀ → Subgroup G) (H : Subgroup G) :
    xySupOf X₀ Y₀ (fun x y => S x y ⊔ H) ≤ xySupOf X₀ Y₀ S ⊔ H :=
  xySupOf_le fun _ hx hx1 _ hy hy1 => sup_le_sup_right (le_xySupOf hx hx1 hy hy1) H

end XySupOf

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_commutator' {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [map_commutator, hA, hB]

theorem exists_fixed_mem_coset {O : Subgroup G} (hO : Odd (Nat.card O)) {t k : G}
    (ht : t * t = 1) (htO : t ∈ normalizer (O : Set G)) (hk : k⁻¹ * (t * k * t⁻¹) ∈ O) :
    ∃ o ∈ O, t * (k * o) * t⁻¹ = k * o := by
  classical
  have : Finite O := OddInversion.finite_of_odd_card hO
  letI : Fintype O := Fintype.ofFinite O
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hOt : ∀ o ∈ O, t * o * t⁻¹ ∈ O := fun o ho => (mem_normalizer_iff.mp htO o).mp ho
  have hmem : ∀ o ∈ O, k⁻¹ * (t * (k * o) * t⁻¹) ∈ O := by
    intro o ho
    have e : k⁻¹ * (t * (k * o) * t⁻¹) = (k⁻¹ * (t * k * t⁻¹)) * (t * o * t⁻¹) := by group
    rw [e]
    exact mul_mem hk (hOt o ho)
  let f : O → O := fun o => ⟨k⁻¹ * (t * (k * o) * t⁻¹), hmem o o.2⟩
  have hf : Function.Involutive f := by
    intro o
    apply Subtype.ext
    change k⁻¹ * (t * (k * (k⁻¹ * (t * (k * (o : G)) * t⁻¹))) * t⁻¹) = o
    have e : k⁻¹ * (t * (k * (k⁻¹ * (t * (k * (o : G)) * t⁻¹))) * t⁻¹) =
        k⁻¹ * ((t * t) * (k * o) * (t⁻¹ * t⁻¹)) := by group
    rw [e, ht, htinv, ht]
    group
  have hcard : ¬ 2 ∣ Fintype.card O := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hO)
  obtain ⟨o, ho⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) (σ := hf.toPerm f)
    (hp := ⟨Nat.prime_two⟩) hcard (by
      ext a
      simp [sq, Equiv.Perm.mul_apply, hf a])
  refine ⟨o, o.2, ?_⟩
  have hfo : k⁻¹ * (t * (k * (o : G)) * t⁻¹) = o := congrArg Subtype.val ho
  exact inv_mul_eq_iff_eq_mul.mp hfo

variable [Finite G]

theorem le_sup_of_isSylowOf_of_relIndex {p : ℕ} [Fact p.Prime] {T L H : Subgroup G}
    (hT : IsSylowOf p T L) {k : ℕ} (hk : H.relIndex L = p ^ k) : L ≤ T ⊔ H := by
  have hpp : p.Prime := Fact.out
  have h1 : (T ⊔ (H ⊓ L)).relIndex L ∣ (H ⊓ L).relIndex L := relIndex_dvd_of_le_left L le_sup_right
  have h2 : (T ⊔ (H ⊓ L)).relIndex L ∣ T.relIndex L := relIndex_dvd_of_le_left L le_sup_left
  rw [inf_relIndex_right, hk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpp).mp h1
  have hT' := (isSylowOf_iff.mp hT).2.2
  have hj0 : j = 0 := by
    by_contra hj0
    apply hT'
    rw [hj] at h2
    exact (dvd_pow_self p hj0).trans h2
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact hj.trans (sup_le_sup_left inf_le_left T)

theorem relIndex_dvd_of_le_normalizer' {H L J : Subgroup G} (hL : L ≤ normalizer (H : Set G))
    (hLJ : L ≤ J) (hHJ : H ≤ J) : H.relIndex L ∣ H.relIndex J := by
  rw [← ABGTheoremB.relIndex_sup_right_of_le_normalizer hL]
  exact Dvd.intro _ (relIndex_mul_relIndex H (L ⊔ H) J le_sup_right (sup_le hLJ hHJ))

end Generic

section KleinFour

variable {A₀ : Type*} [Group A₀] {X : Subgroup A₀}

theorem mul_self_eq_one_of_isKleinFour (hX : IsKleinFour X) {x : A₀} (hx : x ∈ X) :
    x * x = 1 := by
  haveI := hX
  exact congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : X))

theorem orderOf_eq_two_of_isKleinFour (hX : IsKleinFour X) {x : A₀} (hx : x ∈ X)
    (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq]; exact mul_self_eq_one_of_isKleinFour hX hx) hx1

theorem exists_mem_not_mem_zpowers_of_isKleinFour (hX : IsKleinFour X) {x : A₀} (hx : x ∈ X)
    (hx1 : x ≠ 1) : ∃ x' ∈ X, x' ∉ zpowers x := by
  classical
  by_contra h
  push Not at h
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX.card_four]; norm_num)
  letI := Fintype.ofFinite X
  have hsub : (Finset.univ : Finset X) ⊆ {1, ⟨x, hx⟩} := by
    intro z _
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_eq_two_of_isKleinFour hX hx hx1) (h z z.2) with
      h1 | h1
    · simp [Subtype.ext_iff, h1]
    · simp [Subtype.ext_iff, h1]
  have h4 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hX.card_four] at h4
  have h2 := Finset.card_le_two (a := (1 : X)) (b := ⟨x, hx⟩)
  omega

theorem eq_or_eq_mul_of_not_mem_zpowers (hX : IsKleinFour X) {x x' z : A₀} (hx : x ∈ X)
    (hx1 : x ≠ 1) (hx' : x' ∈ X) (hx'z : x' ∉ zpowers x) (hz : z ∈ X) (hzz : z ∉ zpowers x) :
    z = x' ∨ z = x * x' := by
  haveI := hX
  by_contra h
  push Not at h
  have hx'1 : x' ≠ 1 := fun h1 => hx'z (h1 ▸ one_mem _)
  have hz1 : z ≠ 1 := fun h1 => hzz (h1 ▸ one_mem _)
  have hxx' : x ≠ x' := fun h1 => hx'z (h1 ▸ mem_zpowers x)
  have hzx : z ≠ x := fun h1 => hzz (h1 ▸ mem_zpowers x)
  have hmul := IsKleinFour.eq_mul_of_ne_all (x := (⟨x, hx⟩ : X)) (y := ⟨x', hx'⟩) (z := ⟨z, hz⟩)
    (by simpa [Subtype.ext_iff] using hx1) (by simpa [Subtype.ext_iff] using hx'1)
    (by simpa [Subtype.ext_iff] using hxx') (by simpa [Subtype.ext_iff] using hz1)
    (by simpa [Subtype.ext_iff] using hzx) (by simpa [Subtype.ext_iff] using h.1)
  exact h.2 (congrArg Subtype.val hmul)

theorem inverts_of_isKleinFour {G : Type*} [Group G] (hX : IsKleinFour X) (ι : A₀ →* G)
    {x x' : A₀} {u : G} (hx : x ∈ X) (hx1 : x ≠ 1) (hx' : x' ∈ X) (hx'z : x' ∉ zpowers x)
    (hxu : ι x * u * (ι x)⁻¹ = u) (hx'u : ι x' * u * (ι x')⁻¹ = u⁻¹) :
    ∀ z ∈ X, z ∉ zpowers x → ι z * u * (ι z)⁻¹ = u⁻¹ := by
  intro z hz hzz
  rcases eq_or_eq_mul_of_not_mem_zpowers hX hx hx1 hx' hx'z hz hzz with rfl | rfl
  · exact hx'u
  · rw [map_mul]
    calc ι x * ι x' * u * (ι x * ι x')⁻¹ = ι x * (ι x' * u * (ι x')⁻¹) * (ι x)⁻¹ := by group
      _ = ι x * u⁻¹ * (ι x)⁻¹ := by rw [hx'u]
      _ = (ι x * u * (ι x)⁻¹)⁻¹ := by group
      _ = u⁻¹ := by rw [hxu]

end KleinFour

namespace Prop22Hyp

variable {A₀ G : Type*} [Group A₀] [Group G] {X₀ Y₀ : Subgroup A₀} {ι : A₀ →* G}
  {K : Subgroup G} {Kxy : A₀ → A₀ → Subgroup G}

theorem isPGroup_two (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) : IsPGroup 2 A₀ := by
  have hX : IsPGroup 2 X₀ := IsPGroup.of_card (n := 2) (by rw [hyp.kleinX.card_four]; norm_num)
  have hY : IsPGroup 2 Y₀ := IsPGroup.of_card (n := 2) (by rw [hyp.kleinY.card_four]; norm_num)
  have hXY : X₀ ≤ normalizer (Y₀ : Set A₀) :=
    (le_centralizer_iff.mp hyp.comm).trans (centralizer_le_normalizer _)
  have h := IsPGroup.to_sup_of_normal_right' hX hY hXY
  rw [hyp.sup_eq] at h
  exact h.of_equiv Subgroup.topEquiv

theorem isPGroup_range (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) : IsPGroup 2 ι.range := by
  rw [MonoidHom.range_eq_map]
  exact (hyp.isPGroup_two.of_equiv Subgroup.topEquiv.symm).map ι

theorem le_normalizer_of_normal {H : Subgroup G} (hHK : H ≤ K) (hHn : (H.subgroupOf K).Normal) :
    K ≤ normalizer (H : Set G) :=
  (normal_subgroupOf_iff_le_normalizer hHK).mp hHn

theorem le_normalizer_Kxy (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1)
    (hy : y ∈ Y₀) (hy1 : y ≠ 1) : K ⊓ C (ι x) ⊓ C (ι y) ≤ normalizer (Kxy x y : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (hyp.le x hx hx1 y hy hy1)).mp (hyp.normal x hx hx1 y hy hy1)

theorem mul_comm' (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (a b : A₀) : a * b = b * a := by
  have hX : ∀ x ∈ X₀, ∀ x' ∈ X₀, x * x' = x' * x := by
    haveI := hyp.kleinX
    intro x hx x' hx'
    have h := (IsKleinFour.isMulCommutative (G := X₀)).is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩
    exact congrArg Subtype.val h
  have hY : ∀ y ∈ Y₀, ∀ y' ∈ Y₀, y * y' = y' * y := by
    haveI := hyp.kleinY
    intro y hy y' hy'
    have h := (IsKleinFour.isMulCommutative (G := Y₀)).is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩
    exact congrArg Subtype.val h
  have hXY : ∀ x ∈ X₀, ∀ y ∈ Y₀, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (hyp.comm hy)) x hx
  have hcen : X₀ ⊔ Y₀ ≤ center A₀ := by
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · rw [← centralizer_univ, ← coe_top, ← hyp.sup_eq]
      refine (le_centralizer_iff.mp (sup_le ?_ ?_)) hx
      · exact fun x' hx' => mem_centralizer_iff.mpr fun x'' hx'' => (hX x' hx' x'' hx'').symm
      · exact fun y hy => mem_centralizer_iff.mpr fun x'' hx'' => hXY x'' hx'' y hy
    · rw [← centralizer_univ, ← coe_top, ← hyp.sup_eq]
      refine (le_centralizer_iff.mp (sup_le ?_ ?_)) hy
      · exact fun x hx => mem_centralizer_iff.mpr fun y' hy' => (hXY x hx y' hy').symm
      · exact fun y' hy' => mem_centralizer_iff.mpr fun y'' hy'' => (hY y' hy' y'' hy'').symm
  rw [hyp.sup_eq] at hcen
  exact mem_center_iff.mp (hcen (mem_top b)) a

theorem commute_range (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (a b : A₀) : ι a * ι b = ι b * ι a := by
  rw [← map_mul, ← map_mul, hyp.mul_comm' a b]

theorem mul_self (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (a : A₀) : a * a = 1 := by
  let E : Subgroup A₀ :=
    { carrier := {a | a * a = 1}
      mul_mem' := fun {a b} ha hb => by
        change a * b * (a * b) = 1
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hyp.mul_comm' b a]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [show a * a = 1 from ha, show b * b = 1 from hb, one_mul]
      one_mem' := by change (1 : A₀) * 1 = 1; rw [one_mul]
      inv_mem' := fun {a} ha => by
        change a⁻¹ * a⁻¹ = 1
        rw [← mul_inv_rev, show a * a = 1 from ha, inv_one] }
  have h : X₀ ⊔ Y₀ ≤ E := sup_le (fun x hx => mul_self_eq_one_of_isKleinFour hyp.kleinX hx)
    (fun y hy => mul_self_eq_one_of_isKleinFour hyp.kleinY hy)
  rw [hyp.sup_eq] at h
  exact h (mem_top a)

theorem ι_mul_self (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (a : A₀) : ι a * ι a = 1 := by
  rw [← map_mul, hyp.mul_self a, map_one]

theorem ι_mem_normalizer_C (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (a b : A₀) :
    ι a ∈ normalizer ((C (ι b) : Subgroup G) : Set G) :=
  mem_normalizer_C_of_commute (hyp.commute_range a b)

end Prop22Hyp

section Lifting

variable {G : Type*} [Group G]

theorem exists_mem_coset_commute_list (ts : List G) {O : Subgroup G} (hO : Odd (Nat.card O))
    (h1 : ∀ t ∈ ts, t * t = 1) (hN : ∀ t ∈ ts, t ∈ normalizer (O : Set G))
    (hc : ∀ t ∈ ts, ∀ s ∈ ts, t * s = s * t) {k : G}
    (hk : ∀ t ∈ ts, k⁻¹ * (t * k * t⁻¹) ∈ O) :
    ∃ o ∈ O, ∀ t ∈ ts, k * o * t = t * (k * o) := by
  induction ts generalizing O k with
  | nil => exact ⟨1, one_mem _, fun _ ht => absurd ht List.not_mem_nil⟩
  | cons t ts ih =>
    have htt : t ∈ t :: ts := List.mem_cons_self
    have hts : ∀ s ∈ ts, s ∈ t :: ts := fun s hs => List.mem_cons_of_mem t hs
    obtain ⟨o₁, ho₁, hfix⟩ := exists_fixed_mem_coset hO (h1 t htt) (hN t htt) (hk t htt)
    have hk₁t : k * o₁ ∈ C t := by
      rw [mem_centralizer_singleton_iff]
      calc k * o₁ * t = t * (k * o₁) * t⁻¹ * t := by rw [hfix]
        _ = t * (k * o₁) := by group
    have hsC : ∀ s ∈ ts, s ∈ C t := fun s hs =>
      mem_centralizer_singleton_iff.mpr (hc s (hts s hs) t htt)
    obtain ⟨o₂, ho₂, hcomm⟩ := ih (O := O ⊓ C t) (hO.of_dvd_nat (card_dvd_of_le inf_le_left))
      (fun s hs => h1 s (hts s hs))
      (fun s hs => inf_normalizer_le_normalizer_inf ⟨hN s (hts s hs), le_normalizer (hsC s hs)⟩)
      (fun s hs s' hs' => hc s (hts s hs) s' (hts s' hs')) (k := k * o₁) (fun s hs => by
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have e : (k * o₁)⁻¹ * (s * (k * o₁) * s⁻¹) =
              o₁⁻¹ * (k⁻¹ * (s * k * s⁻¹)) * (s * o₁ * s⁻¹) := by group
          rw [e]
          exact mul_mem (mul_mem (inv_mem ho₁) (hk s (hts s hs)))
            ((mem_normalizer_iff.mp (hN s (hts s hs)) o₁).mp ho₁)
        · exact mul_mem (inv_mem hk₁t) (mul_mem (mul_mem (hsC s hs) hk₁t) (inv_mem (hsC s hs))))
    obtain ⟨ho₂O, ho₂C⟩ := mem_inf.mp ho₂
    refine ⟨o₁ * o₂, mul_mem ho₁ ho₂O, ?_⟩
    intro s hs
    have e : k * (o₁ * o₂) = k * o₁ * o₂ := (mul_assoc _ _ _).symm
    rw [e]
    rcases List.mem_cons.mp hs with rfl | hs
    · exact mem_centralizer_singleton_iff.mp (mul_mem hk₁t ho₂C)
    · exact hcomm s hs

theorem commute_of_conj_eq {g u : G} (h : g * u * g⁻¹ = u) : u * g = g * u := by
  calc u * g = g * u * g⁻¹ * g := by rw [h]
    _ = g * u := by group

theorem conj_eq_of_mem_C {t u : G} (h : u ∈ C t) : t * u * t⁻¹ = u := by
  rw [← mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right]

theorem conj_mul_eq_of_conj_eq_inv {s t u : G} (hs : s * u * s⁻¹ = u⁻¹)
    (ht : t * u * t⁻¹ = u⁻¹) : s * t * u * (s * t)⁻¹ = u := by
  calc s * t * u * (s * t)⁻¹ = s * (t * u * t⁻¹) * s⁻¹ := by group
    _ = s * u⁻¹ * s⁻¹ := by rw [ht]
    _ = (s * u * s⁻¹)⁻¹ := by group
    _ = u := by rw [hs, inv_inv]

end Lifting

section QuotientH

variable {G : Type*} [Group G] {H : Subgroup G}

private abbrev QH (H : Subgroup G) : Type _ :=
  ↥(normalizer (H : Set G)) ⧸ H.subgroupOf (normalizer (H : Set G))

private abbrev πH (H : Subgroup G) : ↥(normalizer (H : Set G)) →* QH H :=
  QuotientGroup.mk' (H.subgroupOf (normalizer (H : Set G)))

private def imgH (H S : Subgroup G) : Subgroup (QH H) :=
  (S.subgroupOf (normalizer (H : Set G))).map (πH H)

private def preH (H : Subgroup G) (R : Subgroup (QH H)) : Subgroup G :=
  (R.comap (πH H)).map (normalizer (H : Set G)).subtype

private theorem finite_QH [Finite G] : Finite (QH H) :=
  Finite.of_surjective (πH H) (QuotientGroup.mk'_surjective _)

private theorem mem_imgH {S : Subgroup G} {z : QH H} :
    z ∈ imgH H S ↔ ∃ g : normalizer (H : Set G), (g : G) ∈ S ∧ πH H g = z := by
  simp only [imgH, mem_map, mem_subgroupOf]

private theorem πH_mem_imgH {S : Subgroup G} {g : normalizer (H : Set G)} (hg : (g : G) ∈ S) :
    πH H g ∈ imgH H S := by
  unfold imgH
  exact mem_map_of_mem _ hg

private theorem imgH_mono {S T : Subgroup G} (h : S ≤ T) : imgH H S ≤ imgH H T := by
  unfold imgH
  exact map_mono fun _ hx => h hx

private theorem card_imgH_dvd {S : Subgroup G} (hSJ : S ≤ normalizer (H : Set G)) :
    Nat.card (imgH H S) ∣ Nat.card S := by
  unfold imgH
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv]

private theorem πH_eq_one {g : normalizer (H : Set G)} (hg : (g : G) ∈ H) : πH H g = 1 :=
  (QuotientGroup.eq_one_iff g).mpr hg

private theorem mem_of_πH_eq {a b : normalizer (H : Set G)} (h : πH H a = πH H b) :
    (a : G)⁻¹ * b ∈ H := by
  have h' : ((a : QH H) = b) := h
  have h'' := QuotientGroup.eq.mp h'
  simpa [mem_subgroupOf] using h''

private theorem mem_of_πH_commute {a t : normalizer (H : Set G)}
    (h : πH H a * πH H t = πH H t * πH H a) : (a : G)⁻¹ * ((t : G) * a * (t : G)⁻¹) ∈ H := by
  have h1 : πH H (a⁻¹ * (t * a * t⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
    group
  have h2 : ((a⁻¹ * (t * a * t⁻¹) : normalizer (H : Set G)) : QH H) = 1 := h1
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
  simpa using h2

private theorem mem_of_πH_inv {a t : normalizer (H : Set G)}
    (h : πH H t * πH H a * (πH H t)⁻¹ = (πH H a)⁻¹) : (a : G) * ((t : G) * a * (t : G)⁻¹) ∈ H := by
  have h1 : πH H (a * (t * a * t⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, h, mul_inv_cancel]
  have h2 : ((a * (t * a * t⁻¹) : normalizer (H : Set G)) : QH H) = 1 := h1
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
  simpa using h2

private theorem πH_commute_of_commute {a t : normalizer (H : Set G)} (h : (a : G) * t = t * a) :
    πH H a * πH H t = πH H t * πH H a := by
  rw [← map_mul, ← map_mul]
  exact congrArg (πH H) (Subtype.ext h)

private theorem πH_mem_normalizer_imgH {S : Subgroup G} {g : normalizer (H : Set G)}
    (hg : (g : G) ∈ normalizer (S : Set G)) : πH H g ∈ normalizer (imgH H S : Set (QH H)) := by
  have hg' : g ∈ normalizer ((S.subgroupOf (normalizer (H : Set G)) : Subgroup _) : Set _) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv]
    exact mem_normalizer_iff.mp hg h
  unfold imgH
  exact le_normalizer_map (πH H) (mem_map_of_mem _ hg')

private theorem commutator_imgH_le (S T : Subgroup G) :
    ⁅imgH H S, imgH H T⁆ ≤ imgH H ⁅S, T⁆ := by
  unfold imgH
  rw [← map_commutator]
  refine map_mono ?_
  rw [commutator_le]
  intro s hs t ht
  exact commutator_mem_commutator hs ht

private theorem imgH_xySupOf_le {A₀ : Type*} [Group A₀] {X₀ Y₀ : Subgroup A₀}
    {f : A₀ → A₀ → Subgroup G}
    (hf : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → f x y ≤ normalizer (H : Set G)) :
    imgH H (xySupOf X₀ Y₀ f) ≤ xySupOf X₀ Y₀ fun x y => imgH H (f x y) := by
  unfold imgH
  set T : Subgroup (normalizer (H : Set G)) :=
    xySupOf X₀ Y₀ fun x y => (f x y).subgroupOf (normalizer (H : Set G)) with hT
  have h1 : xySupOf X₀ Y₀ f ≤ T.map (normalizer (H : Set G)).subtype := by
    refine xySupOf_le fun x hx hx1 y hy hy1 => ?_
    rw [← map_subgroupOf_eq_of_le (hf x hx hx1 y hy hy1)]
    exact map_mono (le_xySupOf (f := fun x y => (f x y).subgroupOf (normalizer (H : Set G)))
      hx hx1 hy hy1)
  have h2 : (xySupOf X₀ Y₀ f).subgroupOf (normalizer (H : Set G)) ≤ T := by
    intro g hg
    obtain ⟨g', hg', hgg'⟩ := mem_map.mp (h1 hg)
    rwa [Subtype.ext hgg'] at hg'
  exact (map_mono h2).trans (map_xySupOf _ _).le

private theorem card_imgH_mul {S : Subgroup G} (hHS : H ≤ S)
    (hSJ : S ≤ normalizer (H : Set G)) : Nat.card (imgH H S) * Nat.card H = Nat.card S := by
  unfold imgH
  have h1 := relIndex_ker (K := S.subgroupOf (normalizer (H : Set G))) (πH H)
  rw [QuotientGroup.ker_mk'] at h1
  have h2 := relIndex_mul_card (H.subgroupOf (normalizer (H : Set G)))
    (S.subgroupOf (normalizer (H : Set G)))
  rw [inf_eq_left.mpr (fun x hx => hHS hx), h1,
    Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : H ≤ normalizer (H : Set G))).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv] at h2
  exact h2

private theorem card_imgH_lt [Finite G] {S : Subgroup G} (hH1 : H ≠ ⊥) (hHS : H ≤ S)
    (hSJ : S ≤ normalizer (H : Set G)) : Nat.card (imgH H S) < Nat.card S := by
  have h := card_imgH_mul hHS hSJ
  have hH : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot H).mpr hH1
  rw [← h]
  exact lt_mul_of_one_lt_right Nat.card_pos hH

private theorem le_sup_of_imgH_le {F W : Subgroup G} (hFJ : F ≤ normalizer (H : Set G))
    (h : imgH H F ≤ imgH H W) : F ≤ W ⊔ H := by
  intro f hf
  obtain ⟨w, hw, hwf⟩ := mem_imgH.mp (h (πH_mem_imgH (g := ⟨f, hFJ hf⟩) hf))
  have h1 := mem_of_πH_eq hwf
  have e : f = w * ((w : G)⁻¹ * f) := by group
  rw [e]
  exact mul_mem (mem_sup_left hw) (mem_sup_right h1)

private theorem imgH_inf_le_imgH_sup_inf {F T : Subgroup G} :
    imgH H F ⊓ imgH H T ≤ imgH H ((F ⊔ H) ⊓ T) := by
  rintro z ⟨hzF, hzT⟩
  obtain ⟨f, hf, rfl⟩ := mem_imgH.mp hzF
  obtain ⟨t, ht, htf⟩ := mem_imgH.mp hzT
  have h1 := mem_of_πH_eq htf.symm
  refine mem_imgH.mpr ⟨t, ⟨?_, ht⟩, htf⟩
  have e : (t : G) = f * ((f : G)⁻¹ * t) := by group
  rw [e]
  exact mul_mem (mem_sup_left hf) (mem_sup_right h1)

private theorem mem_preH {R : Subgroup (QH H)} {g : G} :
    g ∈ preH H R ↔ ∃ hg : g ∈ normalizer (H : Set G), πH H ⟨g, hg⟩ ∈ R := by
  unfold preH
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

private theorem imgH_preH_le {R : Subgroup (QH H)} : imgH H (preH H R) ≤ R := by
  intro z hz
  obtain ⟨g, hg, rfl⟩ := mem_imgH.mp hz
  obtain ⟨_, h⟩ := mem_preH.mp hg
  exact h

end QuotientH

namespace Prop22Hyp

variable {A₀ G : Type*} [Group A₀] [Group G] {X₀ Y₀ : Subgroup A₀} {ι : A₀ →* G}
  {K : Subgroup G} {Kxy : A₀ → A₀ → Subgroup G} {H : Subgroup G}

private def ιH (H : Subgroup G) (hHA : ι.range ≤ normalizer (H : Set G)) : A₀ →* QH H :=
  (πH H).comp (ι.codRestrict (normalizer (H : Set G)) fun a => hHA ⟨a, rfl⟩)

private theorem ιH_range_le_normalizer_imgH (hHA : ι.range ≤ normalizer (H : Set G))
    {F : Subgroup G} (hF : ι.range ≤ normalizer (F : Set G)) :
    (ιH H hHA).range ≤ normalizer (imgH H F : Set (QH H)) := by
  rintro _ ⟨a, rfl⟩
  exact πH_mem_normalizer_imgH (g := ⟨ι a, hHA ⟨a, rfl⟩⟩) (hF ⟨a, rfl⟩)

private theorem conj_mem_preH (hHA : ι.range ≤ normalizer (H : Set G)) {R : Subgroup (QH H)}
    (hR : (ιH H hHA).range ≤ normalizer (R : Set (QH H))) (a : A₀) {g : G}
    (hg : g ∈ preH H R) : ι a * g * (ι a)⁻¹ ∈ preH H R := by
  obtain ⟨hgJ, hgR⟩ := mem_preH.mp hg
  have hJ : ι a * g * (ι a)⁻¹ ∈ normalizer (H : Set G) :=
    mul_mem (mul_mem (hHA ⟨a, rfl⟩) hgJ) (inv_mem (hHA ⟨a, rfl⟩))
  refine mem_preH.mpr ⟨hJ, ?_⟩
  have e₀ : (⟨ι a * g * (ι a)⁻¹, hJ⟩ : normalizer (H : Set G)) =
      ⟨ι a, hHA ⟨a, rfl⟩⟩ * ⟨g, hgJ⟩ * (⟨ι a, hHA ⟨a, rfl⟩⟩ : normalizer (H : Set G))⁻¹ := rfl
  have e : πH H ⟨ι a * g * (ι a)⁻¹, hJ⟩ = ιH H hHA a * πH H ⟨g, hgJ⟩ * (ιH H hHA a)⁻¹ := by
    rw [e₀, map_mul, map_mul, map_inv]
    rfl
  rw [e]
  exact (mem_normalizer_iff.mp (hR ⟨a, rfl⟩) _).mp hgR

private theorem range_le_normalizer_preH (hHA : ι.range ≤ normalizer (H : Set G))
    {R : Subgroup (QH H)} (hR : (ιH H hHA).range ≤ normalizer (R : Set (QH H))) :
    ι.range ≤ normalizer (preH H R : Set G) := by
  rintro _ ⟨a, rfl⟩
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_preH hHA hR a, fun hg => ?_⟩
  have h := conj_mem_preH hHA hR a⁻¹ hg
  rwa [map_inv, inv_inv, show (ι a)⁻¹ * (ι a * g * (ι a)⁻¹) * ι a = g by group] at h

variable [Finite G]

private theorem lift_commute (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) {S : Subgroup G} (as : List A₀)
    (hS : ∀ a ∈ as, ι a ∈ normalizer (S : Set G)) {z : QH H} (hz : z ∈ imgH H S)
    (hzc : ∀ a ∈ as, z * ιH H hHA a = ιH H hHA a * z) :
    ∃ g : normalizer (H : Set G), (g : G) ∈ S ∧ πH H g = z ∧
      ∀ a ∈ as, (g : G) * ι a = ι a * g := by
  obtain ⟨g₀, hg₀S, rfl⟩ := mem_imgH.mp hz
  have hO : Odd (Nat.card (H ⊓ S : Subgroup G)) :=
    (hyp.odd.of_dvd_nat (card_dvd_of_le hHK)).of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨o, ho, hcomm⟩ := exists_mem_coset_commute_list (as.map ι) hO
    (by
      intro t ht
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht
      exact hyp.ι_mul_self a)
    (by
      intro t ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      exact inf_normalizer_le_normalizer_inf ⟨hHA ⟨a, rfl⟩, hS a ha⟩)
    (by
      intro t ht s hs
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
      exact hyp.commute_range a b)
    (k := (g₀ : G)) (by
      intro t ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      refine mem_inf.mpr ⟨mem_of_πH_commute (t := ⟨ι a, hHA ⟨a, rfl⟩⟩) (hzc a ha), ?_⟩
      exact mul_mem (inv_mem hg₀S) ((mem_normalizer_iff.mp (hS a ha) _).mp hg₀S))
  obtain ⟨hoH, hoS⟩ := mem_inf.mp ho
  refine ⟨g₀ * ⟨o, le_normalizer hoH⟩, mul_mem hg₀S hoS, ?_, ?_⟩
  · rw [map_mul, πH_eq_one (g := ⟨o, le_normalizer hoH⟩) hoH, mul_one]
  · intro a ha
    exact hcomm (ι a) (List.mem_map.mpr ⟨a, ha, rfl⟩)

private theorem lift_inv (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) {S : Subgroup G} {b : A₀}
    (hbS : ι b ∈ normalizer (S : Set G)) {g : normalizer (H : Set G)} (hgS : (g : G) ∈ S)
    (hgN : (g : G) ∈ normalizer (S : Set G))
    (h : ιH H hHA b * πH H g * (ιH H hHA b)⁻¹ = (πH H g)⁻¹) :
    ∃ g' : normalizer (H : Set G), (g' : G) ∈ S ∧ πH H g' = πH H g ∧
      ι b * g' * (ι b)⁻¹ = (g' : G)⁻¹ := by
  have hO : Odd (Nat.card (H ⊓ S : Subgroup G)) :=
    (hyp.odd.of_dvd_nat (card_dvd_of_le hHK)).of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨o, ho, hinv⟩ := exists_inverted_mem_coset hO (hyp.ι_mul_self b)
    (inf_normalizer_le_normalizer_inf ⟨hHA ⟨b, rfl⟩, hbS⟩)
    (inf_normalizer_le_normalizer_inf ⟨g.2, hgN⟩)
    (mem_inf.mpr ⟨mem_of_πH_inv (t := ⟨ι b, hHA ⟨b, rfl⟩⟩) h,
      mul_mem hgS ((mem_normalizer_iff.mp hbS _).mp hgS)⟩)
  obtain ⟨hoH, hoS⟩ := mem_inf.mp ho
  exact ⟨g * ⟨o, le_normalizer hoH⟩, mul_mem hgS hoS,
    by rw [map_mul, πH_eq_one (g := ⟨o, le_normalizer hoH⟩) hoH, mul_one], hinv⟩

private theorem mem_C_ιH {g : normalizer (H : Set G)} {hHA : ι.range ≤ normalizer (H : Set G)}
    {a : A₀} (h : (g : G) * ι a = ι a * g) : πH H g ∈ C (ιH H hHA a) :=
  mem_centralizer_singleton_iff.mpr (πH_commute_of_commute (t := ⟨ι a, hHA ⟨a, rfl⟩⟩) h)

private theorem ιH_injective (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) : Function.Injective (ιH H hHA) := by
  intro a b hab
  have h1 : ι (a⁻¹ * b) ∈ H := by
    have h := mem_of_πH_eq (a := ⟨ι a, hHA ⟨a, rfl⟩⟩) (b := ⟨ι b, hHA ⟨b, rfl⟩⟩) hab
    simpa [map_mul, map_inv] using h
  have hodd : Odd (Nat.card H) := hyp.odd.of_dvd_nat (card_dvd_of_le hHK)
  have h2 : orderOf (ι (a⁻¹ * b)) = 1 := by
    have hd1 : orderOf (ι (a⁻¹ * b)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hyp.ι_mul_self _)
    have hd2 : orderOf (ι (a⁻¹ * b)) ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H h1
    exact Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) hd1 hd2
  rw [orderOf_eq_one_iff, ← map_one ι] at h2
  have h3 := hyp.inj h2
  rw [inv_mul_eq_one] at h3
  exact h3

private theorem quot_le (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHA : ι.range ≤ normalizer (H : Set G))
    {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1) (hy : y ∈ Y₀) (hy1 : y ≠ 1) :
    imgH H (Kxy x y) ≤ imgH H K ⊓ C (ιH H hHA x) ⊓ C (ιH H hHA y) := by
  intro z hz
  obtain ⟨g, hg, rfl⟩ := mem_imgH.mp hz
  obtain ⟨⟨hgK, hgx⟩, hgy⟩ := hyp.le x hx hx1 y hy hy1 hg
  exact ⟨⟨πH_mem_imgH hgK, mem_C_ιH (mem_centralizer_singleton_iff.mp hgx)⟩,
    mem_C_ιH (mem_centralizer_singleton_iff.mp hgy)⟩

private theorem quot_normal (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) {x y : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1)
    (hy : y ∈ Y₀) (hy1 : y ≠ 1) :
    ((imgH H (Kxy x y)).subgroupOf (imgH H K ⊓ C (ιH H hHA x) ⊓ C (ιH H hHA y))).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (quot_le hyp hHA hx hx1 hy hy1)]
  rintro z ⟨⟨hzK, hzx⟩, hzy⟩
  obtain ⟨g, hgK, rfl, hgc⟩ := lift_commute hyp hHK hHA [x, y] (S := K)
    (fun a _ => hyp.normalizes ⟨a, rfl⟩) hzK (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mem_centralizer_singleton_iff.mp hzx
      · exact mem_centralizer_singleton_iff.mp hzy)
  exact πH_mem_normalizer_imgH (hyp.le_normalizer_Kxy hx hx1 hy hy1
    ⟨⟨hgK, mem_centralizer_singleton_iff.mpr (hgc x (by simp))⟩,
      mem_centralizer_singleton_iff.mpr (hgc y (by simp))⟩)

private theorem quot_a (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) {x x' y y' : A₀} (hx : x ∈ X₀) (hx1 : x ≠ 1)
    (hx' : x' ∈ X₀) (hx'1 : x' ≠ 1) (hy : y ∈ Y₀) (hy1 : y ≠ 1) (hy' : y' ∈ Y₀) (hy'1 : y' ≠ 1) :
    imgH H (Kxy x y) ⊓ C (ιH H hHA x') ≤ imgH H (Kxy x' y) ∧
      imgH H (Kxy x y) ⊓ C (ιH H hHA y') ≤ imgH H (Kxy x y') := by
  have ha := hyp.a x hx hx1 x' hx' hx'1 y hy hy1 y' hy' hy'1
  constructor
  · rintro z ⟨hz, hzc⟩
    obtain ⟨g, hg, rfl, hgc⟩ := lift_commute hyp hHK hHA [x'] (S := Kxy x y)
      (fun a _ => hyp.inv x hx hx1 y hy hy1 ⟨a, rfl⟩) hz (by
        intro a ha
        rw [List.mem_singleton] at ha
        rw [ha]
        exact mem_centralizer_singleton_iff.mp hzc)
    exact πH_mem_imgH (ha.1 ⟨hg, mem_centralizer_singleton_iff.mpr (hgc x' (by simp))⟩)
  · rintro z ⟨hz, hzc⟩
    obtain ⟨g, hg, rfl, hgc⟩ := lift_commute hyp hHK hHA [y'] (S := Kxy x y)
      (fun a _ => hyp.inv x hx hx1 y hy hy1 ⟨a, rfl⟩) hz (by
        intro a ha
        rw [List.mem_singleton] at ha
        rw [ha]
        exact mem_centralizer_singleton_iff.mp hzc)
    exact πH_mem_imgH (ha.2 ⟨hg, mem_centralizer_singleton_iff.mpr (hgc y' (by simp))⟩)

private theorem quot_b (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) :
    ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → ∀ u ∈ imgH H K ⊓ C (ιH H hHA x) ⊓ C (ιH H hHA y),
      (∀ x' ∈ X₀, x' ∉ zpowers x → ιH H hHA x' * u * (ιH H hHA x')⁻¹ = u⁻¹) →
      (∀ y' ∈ Y₀, y' ∉ zpowers y → ιH H hHA y' * u * (ιH H hHA y')⁻¹ = u⁻¹) →
        u ∈ imgH H (Kxy x y) := by
  intro x hx hx1 y hy hy1 u ⟨⟨huK, hux⟩, huy⟩ hX hY
  obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hyp.kleinX hx hx1
  obtain ⟨y', hy', hy'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hyp.kleinY hy hy1
  have hu₃ : u * ιH H hHA (x' * y') = ιH H hHA (x' * y') * u := by
    rw [map_mul]
    exact commute_of_conj_eq (conj_mul_eq_of_conj_eq_inv (hX x' hx' hx'z) (hY y' hy' hy'z))
  obtain ⟨g₀, hg₀K, rfl, hg₀c⟩ := lift_commute hyp hHK hHA [x, y, x' * y'] (S := K)
    (fun a _ => hyp.normalizes ⟨a, rfl⟩) huK (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact mem_centralizer_singleton_iff.mp hux
      · exact mem_centralizer_singleton_iff.mp huy
      · exact hu₃)
  have hg₀x := mem_centralizer_singleton_iff.mpr (hg₀c x (by simp))
  have hg₀y := mem_centralizer_singleton_iff.mpr (hg₀c y (by simp))
  have hg₀xy := mem_centralizer_singleton_iff.mpr (hg₀c (x' * y') (by simp))
  obtain ⟨g, ⟨hgS, hgxy⟩, hgπ, hginv⟩ := lift_inv hyp hHK hHA
    (S := K ⊓ C (ι x) ⊓ C (ι y) ⊓ C (ι (x' * y'))) (b := x')
    (inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨hyp.normalizes ⟨x', rfl⟩, hyp.ι_mem_normalizer_C x' x⟩,
        hyp.ι_mem_normalizer_C x' y⟩, hyp.ι_mem_normalizer_C x' (x' * y')⟩)
    ⟨⟨⟨hg₀K, hg₀x⟩, hg₀y⟩, hg₀xy⟩
    (inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨le_normalizer hg₀K, mem_normalizer_C_of_commute
        (hg₀c x (by simp))⟩, mem_normalizer_C_of_commute (hg₀c y (by simp))⟩,
        mem_normalizer_C_of_commute (hg₀c (x' * y') (by simp))⟩)
    (hX x' hx' hx'z)
  rw [← hgπ]
  refine πH_mem_imgH (hyp.b x hx hx1 y hy hy1 g hgS ?_ ?_)
  · exact inverts_of_isKleinFour hyp.kleinX ι hx hx1 hx' hx'z (conj_eq_of_mem_C hgS.1.2) hginv
  · have hy'u : ι y' * g * (ι y')⁻¹ = (g : G)⁻¹ := by
      have e : ι y' = ι x' * ι (x' * y') := by
        rw [map_mul, ← mul_assoc, hyp.ι_mul_self x', one_mul]
      rw [e]
      calc ι x' * ι (x' * y') * g * (ι x' * ι (x' * y'))⁻¹ =
          ι x' * (ι (x' * y') * g * (ι (x' * y'))⁻¹) * (ι x')⁻¹ := by group
        _ = ι x' * g * (ι x')⁻¹ := by rw [conj_eq_of_mem_C hgxy]
        _ = (g : G)⁻¹ := hginv
    exact inverts_of_isKleinFour hyp.kleinY ι hy hy1 hy' hy'z (conj_eq_of_mem_C hgS.2) hy'u

private theorem quot_c_aux (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) {a b : A₀} {Z₀ : Subgroup A₀}
    (hZ : IsKleinFour Z₀) (hb : b ∈ Z₀) (hb1 : b ≠ 1) {u : QH H}
    (hu : u ∈ ⁅⁅imgH H K ⊓ C (ιH H hHA a), Z₀.map (ιH H hHA)⁆,
      ⁅imgH H K ⊓ C (ιH H hHA a), Z₀.map (ιH H hHA)⁆⁆ ⊓ C (ιH H hHA b))
    (hinv : ∀ b' ∈ Z₀, b' ∉ zpowers b → ιH H hHA b' * u * (ιH H hHA b')⁻¹ = u⁻¹) :
    ∃ g : normalizer (H : Set G),
      (g : G) ∈ ⁅⁅K ⊓ C (ι a), Z₀.map ι⁆, ⁅K ⊓ C (ι a), Z₀.map ι⁆⁆ ⊓ C (ι b) ∧ πH H g = u ∧
        ∀ b' ∈ Z₀, b' ∉ zpowers b → ι b' * g * (ι b')⁻¹ = (g : G)⁻¹ := by
  set L₁ : Subgroup G := ⁅K ⊓ C (ι a), Z₀.map ι⁆ with hL₁
  set L : Subgroup G := ⁅L₁, L₁⁆ with hL
  have h1 : imgH H K ⊓ C (ιH H hHA a) ≤ imgH H (K ⊓ C (ι a)) := by
    rintro z ⟨hzK, hza⟩
    obtain ⟨g, hgK, rfl, hgc⟩ := lift_commute hyp hHK hHA [a] (S := K)
      (fun c _ => hyp.normalizes ⟨c, rfl⟩) hzK (by
        intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]
        exact mem_centralizer_singleton_iff.mp hza)
    exact πH_mem_imgH ⟨hgK, mem_centralizer_singleton_iff.mpr (hgc a (by simp))⟩
  have h2 : Z₀.map (ιH H hHA) ≤ imgH H (Z₀.map ι) := by
    rintro _ ⟨c, hc, rfl⟩
    exact πH_mem_imgH (g := ⟨ι c, hHA ⟨c, rfl⟩⟩) (mem_map_of_mem ι hc)
  have h3 : ⁅⁅imgH H K ⊓ C (ιH H hHA a), Z₀.map (ιH H hHA)⁆,
      ⁅imgH H K ⊓ C (ιH H hHA a), Z₀.map (ιH H hHA)⁆⁆ ≤ imgH H L :=
    (commutator_mono ((commutator_mono h1 h2).trans (commutator_imgH_le _ _))
      ((commutator_mono h1 h2).trans (commutator_imgH_le _ _))).trans (commutator_imgH_le _ _)
  have hLn : ∀ c ∈ Z₀, ι c ∈ normalizer (L : Set G) := by
    intro c hc
    have hL₁n : ι c ∈ normalizer (L₁ : Set G) := mem_normalizer_commutator'
      (inf_normalizer_le_normalizer_inf ⟨hyp.normalizes ⟨c, rfl⟩, hyp.ι_mem_normalizer_C c a⟩)
      (le_normalizer (mem_map_of_mem ι hc))
    exact mem_normalizer_commutator' hL₁n hL₁n
  obtain ⟨g₀, hg₀L, rfl, hg₀c⟩ := lift_commute hyp hHK hHA [b] (S := L)
    (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact hLn b hb) (h3 hu.1) (by
      intro c hc
      rw [List.mem_singleton] at hc
      rw [hc]
      exact mem_centralizer_singleton_iff.mp hu.2)
  obtain ⟨b', hb', hb'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hZ hb hb1
  obtain ⟨g, hgS, hgπ, hginv⟩ := lift_inv hyp hHK hHA (S := L ⊓ C (ι b)) (b := b')
    (inf_normalizer_le_normalizer_inf ⟨hLn b' hb', hyp.ι_mem_normalizer_C b' b⟩)
    ⟨hg₀L, mem_centralizer_singleton_iff.mpr (hg₀c b (by simp))⟩
    (inf_normalizer_le_normalizer_inf ⟨le_normalizer hg₀L,
      mem_normalizer_C_of_commute (hg₀c b (by simp))⟩)
    (hinv b' hb' hb'z)
  exact ⟨g, hgS, hgπ,
    inverts_of_isKleinFour hZ ι hb hb1 hb' hb'z (conj_eq_of_mem_C hgS.2) hginv⟩

private theorem quot_c (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHA : ι.range ≤ normalizer (H : Set G)) :
    ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 →
      (∀ u ∈ ⁅⁅imgH H K ⊓ C (ιH H hHA x), Y₀.map (ιH H hHA)⁆,
          ⁅imgH H K ⊓ C (ιH H hHA x), Y₀.map (ιH H hHA)⁆⁆ ⊓ C (ιH H hHA y),
        (∀ y' ∈ Y₀, y' ∉ zpowers y → ιH H hHA y' * u * (ιH H hHA y')⁻¹ = u⁻¹) →
          u ∈ imgH H (Kxy x y)) ∧
      (∀ u ∈ ⁅⁅imgH H K ⊓ C (ιH H hHA y), X₀.map (ιH H hHA)⁆,
          ⁅imgH H K ⊓ C (ιH H hHA y), X₀.map (ιH H hHA)⁆⁆ ⊓ C (ιH H hHA x),
        (∀ x' ∈ X₀, x' ∉ zpowers x → ιH H hHA x' * u * (ιH H hHA x')⁻¹ = u⁻¹) →
          u ∈ imgH H (Kxy x y)) := by
  intro x hx hx1 y hy hy1
  constructor
  · intro u hu hinv
    obtain ⟨g, hgS, rfl, hginv⟩ := quot_c_aux hyp hHK hHA (a := x) hyp.kleinY hy hy1 hu hinv
    exact πH_mem_imgH ((hyp.c x hx hx1 y hy hy1).1 g hgS hginv)
  · intro u hu hinv
    obtain ⟨g, hgS, rfl, hginv⟩ := quot_c_aux hyp hHK hHA (a := y) hyp.kleinX hx hx1 hu hinv
    exact πH_mem_imgH ((hyp.c x hx hx1 y hy hy1).2 g hgS hginv)

private theorem isSylowOf_map' {G' H' : Type*} [Group G'] [Group H'] [Finite G'] {p : ℕ}
    [Fact p.Prime] {P S : Subgroup G'} (h : IsSylowOf p P S) (f : G' →* H') :
    IsSylowOf p (P.map f) (S.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective S), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem quot_d (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHn : (H.subgroupOf K).Normal) (hHA : ι.range ≤ normalizer (H : Set G)) :
    ∀ (p : ℕ) (P : Subgroup (QH H)), p.Prime → IsPGroup p P → P ≤ imgH H K →
      (ιH H hHA).range ≤ normalizer (P : Set (QH H)) →
      IsKxyGen X₀ Y₀ (fun x y => imgH H (Kxy x y)) P →
      ∀ Q ≤ P, (ιH H hHA).range ≤ normalizer (Q : Set (QH H)) →
        IsKxyGen X₀ Y₀ (fun x y => imgH H (Kxy x y)) Q := by
  intro p P hp hPp hPK hPA hPgen Q hQP hQA
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (QH H) := finite_QH
  have hKJ := le_normalizer_of_normal hHK hHn
  have hA := hyp.isPGroup_range
  set M : Subgroup G := K ⊓ preH H P with hMdef
  have hMK : M ≤ K := inf_le_left
  have hModd : Odd (Nat.card M) := hyp.odd.of_dvd_nat (card_dvd_of_le hMK)
  have hMA : ι.range ≤ normalizer (M : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hyp.normalizes hg, range_le_normalizer_preH hHA hPA hg⟩
  have hMimg : imgH H M = P := by
    refine le_antisymm ((imgH_mono inf_le_right).trans imgH_preH_le) ?_
    intro z hz
    obtain ⟨g, hgK, rfl⟩ := mem_imgH.mp (hPK hz)
    exact πH_mem_imgH ⟨hgK, mem_preH.mpr ⟨g.2, hz⟩⟩
  obtain ⟨Ps, hPs, hPsA⟩ := ABGTheoremB.exists_isSylowOf_normalized_of_odd hp hA hMA hModd
  have himgSyl : ∀ {T S : Subgroup G}, IsSylowOf p T S → S ≤ normalizer (H : Set G) →
      IsSylowOf p (imgH H T) (imgH H S) := by
    intro T S hTS hSJ
    have h1 : IsSylowOf p (T.subgroupOf (normalizer (H : Set G)))
        (S.subgroupOf (normalizer (H : Set G))) := by
      rw [← ABGLocalTools.isSylowOf_map_subtype_iff (normalizer (H : Set G)),
        map_subgroupOf_eq_of_le (hTS.le.trans hSJ), map_subgroupOf_eq_of_le hSJ]
      exact hTS
    exact isSylowOf_map' h1 (πH H)
  have hF3 : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → IsSylowOf p (Ps ⊓ Kxy x y) (M ⊓ Kxy x y) := by
    intro x hx hx1 y hy hy1
    have hMKA : ι.range ≤ normalizer ((M ⊓ Kxy x y : Subgroup G) : Set G) := fun g hg =>
      inf_normalizer_le_normalizer_inf ⟨hMA hg, hyp.inv x hx hx1 y hy hy1 hg⟩
    have hMKodd : Odd (Nat.card (M ⊓ Kxy x y : Subgroup G)) :=
      hModd.of_dvd_nat (card_dvd_of_le inf_le_left)
    obtain ⟨R, hR, hRA⟩ := ABGTheoremB.exists_isSylowOf_normalized_of_odd hp hA hMKA hMKodd
    obtain ⟨Rs, hRs, hRRs, hRsA⟩ := ABGTheoremB.exists_isSylowOf_normalized_ge_of_odd hp hA hMA
      hModd (hR.le.trans inf_le_left) hR.isPGroup hRA
    obtain ⟨c, ⟨hcM, hcA⟩, hc⟩ :=
      ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_odd hp hA hMA hModd hRs hPs hRsA hPsA
    have hcx : c ∈ C (ι x) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hcA) (ι x) ⟨x, rfl⟩).symm
    have hcy : c ∈ C (ι y) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hcA) (ι y) ⟨y, rfl⟩).symm
    have hcN : c ∈ normalizer (Kxy x y : Set G) :=
      hyp.le_normalizer_Kxy hx hx1 hy hy1 ⟨⟨hcM.1, hcx⟩, hcy⟩
    have hcMK : c ∈ normalizer ((M ⊓ Kxy x y : Subgroup G) : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨le_normalizer hcM, hcN⟩
    set R' : Subgroup G := R.map (MulAut.conj c).toMonoidHom with hR'
    have hR'le : R' ≤ Ps ⊓ Kxy x y := by
      refine le_inf ?_ ?_
      · rw [← hc]
        exact map_mono hRRs
      · rw [← mem_normalizer_iff_map_conj_eq.mp hcN]
        exact map_mono (hR.le.trans inf_le_right)
    have hR'syl : IsSylowOf p R' (M ⊓ Kxy x y) := by
      refine ABGLocalTools.isSylowOf_of_card ?_ ?_
      · rw [← mem_normalizer_iff_map_conj_eq.mp hcMK]
        exact map_mono hR.le
      · rw [hR', card_map_of_injective (MulAut.conj c).injective]
        exact hR.card_eq
    have heq := hR'syl.eq_of_le hR'le (inf_le_inf_right _ hPs.le)
      (hPs.isPGroup.to_le inf_le_left)
    rw [heq]
    exact hR'syl
  have hF2 : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 →
      P ⊓ imgH H (Kxy x y) ≤ imgH H (Ps ⊓ Kxy x y) := by
    intro x hx hx1 y hy hy1
    have hsyl := himgSyl (hF3 x hx hx1 y hy hy1) (inf_le_left.trans (hMK.trans hKJ))
    have hp' : IsPGroup p (imgH H (M ⊓ Kxy x y)) :=
      hPp.to_le ((imgH_mono inf_le_left).trans hMimg.le)
    rw [← hsyl.eq_of_le hsyl.le le_rfl hp']
    rintro z ⟨hzP, hzK⟩
    obtain ⟨g, hg, rfl⟩ := mem_imgH.mp hzK
    exact πH_mem_imgH ⟨⟨(hyp.le x hx hx1 y hy hy1 hg).1.1, mem_preH.mpr ⟨g.2, hzP⟩⟩, hg⟩
  set fP : A₀ → A₀ → Subgroup G := fun x y => Ps ⊓ Kxy x y with hfP
  set P₁ : Subgroup G := xySupOf X₀ Y₀ fP with hP₁
  have hP₁Ps : P₁ ≤ Ps := xySupOf_le (f := fP) fun _ _ _ _ _ _ => inf_le_left
  have hP₁A : ι.range ≤ normalizer (P₁ : Set G) := fun g hg =>
    mem_normalizer_xySupOf (f := fP) fun x hx hx1 y hy hy1 =>
      inf_normalizer_le_normalizer_inf ⟨hPsA hg, hyp.inv x hx hx1 y hy hy1 hg⟩
  have hP₁gen : IsKxyGen X₀ Y₀ Kxy P₁ :=
    xySupOf_mono (f := fP) (g := fun x y => P₁ ⊓ Kxy x y) fun x hx hx1 y hy hy1 =>
      le_inf (le_xySupOf (f := fP) hx hx1 hy hy1) inf_le_right
  have hP₁K : P₁ ≤ K := hP₁Ps.trans (hPs.le.trans hMK)
  have hPP₁ : P ≤ imgH H P₁ := by
    refine hPgen.trans (xySupOf_le (f := fun x y => P ⊓ imgH H (Kxy x y)) ?_)
    intro x hx hx1 y hy hy1
    exact (hF2 x hx hx1 y hy hy1).trans (imgH_mono (le_xySupOf (f := fP) hx hx1 hy hy1))
  set Q₁ : Subgroup G := P₁ ⊓ preH H Q with hQ₁
  have hQ₁A : ι.range ≤ normalizer (Q₁ : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hP₁A hg, range_le_normalizer_preH hHA hQA hg⟩
  have hQ₁gen : IsKxyGen X₀ Y₀ Kxy Q₁ :=
    hyp.d p P₁ hp (hPs.isPGroup.to_le hP₁Ps) hP₁K hP₁A hP₁gen Q₁ inf_le_left hQ₁A
  have hQQ₁ : Q ≤ imgH H Q₁ := by
    intro z hz
    obtain ⟨g, hgP₁, rfl⟩ := mem_imgH.mp (hPP₁ (hQP hz))
    exact πH_mem_imgH ⟨hgP₁, mem_preH.mpr ⟨g.2, hz⟩⟩
  have hQ₁Q : imgH H Q₁ ≤ Q := (imgH_mono inf_le_right).trans imgH_preH_le
  have h1 : imgH H (xySupOf X₀ Y₀ fun x y => Q₁ ⊓ Kxy x y) ≤
      xySupOf X₀ Y₀ fun x y => imgH H (Q₁ ⊓ Kxy x y) :=
    imgH_xySupOf_le (f := fun x y => Q₁ ⊓ Kxy x y) fun x hx hx1 y hy hy1 =>
      inf_le_right.trans ((hyp.le x hx hx1 y hy hy1).trans (inf_le_left.trans
        (inf_le_left.trans hKJ)))
  have h2 : (xySupOf X₀ Y₀ fun x y => imgH H (Q₁ ⊓ Kxy x y)) ≤
      xySupOf X₀ Y₀ fun x y => Q ⊓ imgH H (Kxy x y) :=
    xySupOf_mono (f := fun x y => imgH H (Q₁ ⊓ Kxy x y))
      (g := fun x y => Q ⊓ imgH H (Kxy x y)) fun x _ _ y _ _ =>
        le_inf ((imgH_mono inf_le_left).trans hQ₁Q) (imgH_mono inf_le_right)
  exact hQQ₁.trans ((imgH_mono hQ₁gen).trans (h1.trans h2))

private theorem quot_hyp (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) (hHK : H ≤ K)
    (hHn : (H.subgroupOf K).Normal) (hHA : ι.range ≤ normalizer (H : Set G)) :
    Prop22Hyp X₀ Y₀ (ιH H hHA) (imgH H K) fun x y => imgH H (Kxy x y) where
  kleinX := hyp.kleinX
  kleinY := hyp.kleinY
  inf_eq := hyp.inf_eq
  comm := hyp.comm
  sup_eq := hyp.sup_eq
  inj := ιH_injective hyp hHK hHA
  odd := hyp.odd.of_dvd_nat (card_imgH_dvd (le_normalizer_of_normal hHK hHn))
  normalizes := ιH_range_le_normalizer_imgH hHA hyp.normalizes
  le := fun x hx hx1 y hy hy1 => quot_le hyp hHA hx hx1 hy hy1
  normal := fun x hx hx1 y hy hy1 => quot_normal hyp hHK hHA hx hx1 hy hy1
  inv := fun x hx hx1 y hy hy1 => ιH_range_le_normalizer_imgH hHA (hyp.inv x hx hx1 y hy hy1)
  gen := (imgH_mono hyp.gen).trans (imgH_xySupOf_le fun x hx hx1 y hy hy1 =>
    (hyp.le x hx hx1 y hy hy1).trans (inf_le_left.trans (inf_le_left.trans
      (le_normalizer_of_normal hHK hHn))))
  a := fun x hx hx1 x' hx' hx'1 y hy hy1 y' hy' hy'1 =>
    quot_a hyp hHK hHA hx hx1 hx' hx'1 hy hy1 hy' hy'1
  b := quot_b hyp hHK hHA
  c := quot_c hyp hHK hHA
  d := quot_d hyp hHK hHn hHA

end Prop22Hyp

namespace Prop22Hyp

variable {A₀ : Type*} [Group A₀] {X₀ Y₀ : Subgroup A₀}

theorem le_xySupOf_sup {G : Type u} [Group G] [Finite G] {ι : A₀ →* G} {K : Subgroup G}
    {Kxy : A₀ → A₀ → Subgroup G} (hyp : Prop22Hyp X₀ Y₀ ι K Kxy)
    (ih : ∀ (G' : Type u) [Group G'] [Finite G'] (ι' : A₀ →* G') (K' : Subgroup G')
      (Kxy' : A₀ → A₀ → Subgroup G'), Prop22Hyp X₀ Y₀ ι' K' Kxy' →
        Nat.card K' < Nat.card K → Prop22Concl X₀ Y₀ ι' K' Kxy')
    {H : Subgroup G} (hH1 : H ≠ ⊥) (hHK : H ≤ K) (hHn : (H.subgroupOf K).Normal)
    (hHA : ι.range ≤ normalizer (H : Set G)) {F : Subgroup G} (hFK : F ≤ K)
    (hFA : ι.range ≤ normalizer (F : Set G)) :
    F ≤ xySupOf X₀ Y₀ (fun x y => (F ⊔ H) ⊓ Kxy x y) ⊔ H := by
  haveI : Finite (QH H) := finite_QH
  have hKJ := le_normalizer_of_normal hHK hHn
  have hconc := ih (QH H) (ιH H hHA) (imgH H K) _ (quot_hyp hyp hHK hHn hHA)
    (card_imgH_lt hH1 hHK hKJ)
  have hF : imgH H F ≤ xySupOf X₀ Y₀ (fun x y => imgH H F ⊓ imgH H (Kxy x y)) :=
    hconc (imgH H F) (imgH_mono hFK) (ιH_range_le_normalizer_imgH hHA hFA)
  have h1 : ∀ x y : A₀, imgH H F ⊓ imgH H (Kxy x y) ≤ imgH H ((F ⊔ H) ⊓ Kxy x y) :=
    fun x y => imgH_inf_le_imgH_sup_inf (H := H) (F := F) (T := Kxy x y)
  have h2 : xySupOf X₀ Y₀ (fun x y => imgH H F ⊓ imgH H (Kxy x y)) ≤
      imgH H (xySupOf X₀ Y₀ fun x y => (F ⊔ H) ⊓ Kxy x y) :=
    xySupOf_le fun x hx hx1 y hy hy1 => (h1 x y).trans
      (imgH_mono (le_xySupOf (f := fun x y => (F ⊔ H) ⊓ Kxy x y) hx hx1 hy hy1))
  exact le_sup_of_imgH_le (hFK.trans hKJ) (hF.trans h2)

variable {G : Type*} [Group G] [Finite G] {ι : A₀ →* G} {K : Subgroup G}
  {Kxy : A₀ → A₀ → Subgroup G}

theorem isKxyGen_of_coprime (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) {H : Subgroup G} {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hHr : IsPGroup r H) (hHK : H ≤ K)
    (hHn : (H.subgroupOf K).Normal) (hHA : ι.range ≤ normalizer (H : Set G)) {F : Subgroup G}
    (hFp : IsPGroup p F) (hFK : F ≤ K) (hFA : ι.range ≤ normalizer (F : Set G))
    (hQ : F ≤ xySupOf X₀ Y₀ (fun x y => (F ⊔ H) ⊓ Kxy x y) ⊔ H) :
    IsKxyGen X₀ Y₀ Kxy F := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hKH := le_normalizer_of_normal hHK hHn
  have hFH : F ≤ normalizer (H : Set G) := hFK.trans hKH
  have hA := hyp.isPGroup_range
  have hdisj : F ⊓ H = ⊥ := by
    obtain ⟨m, hm⟩ := hFp.exists_card_eq
    obtain ⟨n, hn⟩ := hHr.exists_card_eq
    refine (disjoint_of_coprime_natCard ?_).eq_bot
    rw [hm, hn]
    exact ((Nat.coprime_primes hp hr).mpr hpr).pow m n
  have hFHK : F ⊔ H ≤ K := sup_le hFK hHK
  have hFHodd : Odd (Nat.card (F ⊔ H : Subgroup G)) := hyp.odd.of_dvd_nat (card_dvd_of_le hFHK)
  have hFHA : ι.range ≤ normalizer ((F ⊔ H : Subgroup G) : Set G) := fun g hg =>
    ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup F H ⟨hFA hg, hHA hg⟩
  have hFsyl : IsSylowOf p F (F ⊔ H) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_left, hFp, fun hdvd => ?_⟩
    have h1 : F.relIndex (H ⊔ F) = F.relIndex H :=
      ABGTheoremB.relIndex_sup_eq_relIndex_of_le_normalizer hFH
    rw [sup_comm, h1] at hdvd
    obtain ⟨n, hn⟩ := hHr.exists_card_eq
    have h2 : p ∣ r ^ n := hn ▸ hdvd.trans (relIndex_dvd_card F H)
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h2))
  have h3 : ∀ x ∈ X₀, x ≠ 1 → ∀ y ∈ Y₀, y ≠ 1 → (F ⊔ H) ⊓ Kxy x y ≤ (F ⊓ Kxy x y) ⊔ H := by
    intro x hx hx1 y hy hy1
    have hMA : ι.range ≤ normalizer (((F ⊔ H) ⊓ Kxy x y : Subgroup G) : Set G) := fun g hg =>
      inf_normalizer_le_normalizer_inf ⟨hFHA hg, hyp.inv x hx hx1 y hy hy1 hg⟩
    have hModd : Odd (Nat.card ((F ⊔ H) ⊓ Kxy x y : Subgroup G)) :=
      hFHodd.of_dvd_nat (card_dvd_of_le inf_le_left)
    obtain ⟨P, hP, hPA⟩ := ABGTheoremB.exists_isSylowOf_normalized_of_odd hp hA hMA hModd
    have hMPH : (F ⊔ H) ⊓ Kxy x y ≤ P ⊔ H := by
      have hdvd : H.relIndex ((F ⊔ H) ⊓ Kxy x y) ∣ Nat.card F := by
        have h1 := relIndex_dvd_of_le_normalizer' (H := H) (L := (F ⊔ H) ⊓ Kxy x y)
          (J := F ⊔ H) (inf_le_left.trans (hFHK.trans hKH)) inf_le_left le_sup_right
        rw [ABGTheoremB.relIndex_sup_right_of_le_normalizer hFH] at h1
        exact h1.trans (relIndex_dvd_card H F)
      obtain ⟨a, ha⟩ := hFp.exists_card_eq
      rw [ha] at hdvd
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      exact le_sup_of_isSylowOf_of_relIndex hP hk
    obtain ⟨R, hR, hPR, hRA⟩ := ABGTheoremB.exists_isSylowOf_normalized_ge_of_odd hp hA hFHA
      hFHodd (hP.le.trans inf_le_left) hP.isPGroup hPA
    obtain ⟨c, ⟨hcFH, hcA⟩, hc⟩ :=
      ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_odd hp hA hFHA hFHodd hR hFsyl hRA hFA
    have hcmem : c ∈ ((F : Set G) * (H : Set G)) := by
      rw [← coe_mul_of_left_le_normalizer_right F H hFH]
      exact hcFH
    obtain ⟨f, hf, h, hh, rfl⟩ := hcmem
    have hfA : ∀ g ∈ ι.range, g * f * g⁻¹ = f := by
      intro g hg
      have hcg : g * (f * h) * g⁻¹ = f * h := by
        rw [(mem_centralizer_iff.mp hcA) g hg, mul_inv_cancel_right]
      have h1 : f⁻¹ * (g * f * g⁻¹) ∈ F :=
        mul_mem (inv_mem hf) ((mem_normalizer_iff.mp (hFA hg) f).mp hf)
      have h2 : f⁻¹ * (g * f * g⁻¹) ∈ H := by
        have e : f⁻¹ * (g * f * g⁻¹) = h * (g * h * g⁻¹)⁻¹ := by
          calc f⁻¹ * (g * f * g⁻¹) = f⁻¹ * (g * (f * h) * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
            _ = f⁻¹ * (f * h) * (g * h * g⁻¹)⁻¹ := by rw [hcg]
            _ = h * (g * h * g⁻¹)⁻¹ := by group
        rw [e]
        exact mul_mem hh (inv_mem ((mem_normalizer_iff.mp (hHA hg) h).mp hh))
      have h3 : f⁻¹ * (g * f * g⁻¹) = 1 := by
        have hmem : f⁻¹ * (g * f * g⁻¹) ∈ F ⊓ H := ⟨h1, h2⟩
        rwa [hdisj, mem_bot] at hmem
      calc g * f * g⁻¹ = f * (f⁻¹ * (g * f * g⁻¹)) := by group
        _ = f := by rw [h3, mul_one]
    have hhA : ∀ g ∈ ι.range, g * h = h * g := by
      intro g hg
      have hcg : g * (f * h) = f * h * g := (mem_centralizer_iff.mp hcA) g hg
      have hfg : g * f = f * g := commute_of_conj_eq (hfA g hg) |>.symm
      have e : f * (g * h) = f * (h * g) := by
        calc f * (g * h) = (f * g) * h := by group
          _ = (g * f) * h := by rw [hfg]
          _ = g * (f * h) := by group
          _ = f * h * g := hcg
          _ = f * (h * g) := by group
      exact mul_left_cancel e
    have hhN : h ∈ normalizer (Kxy x y : Set G) := hyp.le_normalizer_Kxy hx hx1 hy hy1
      ⟨⟨hHK hh, mem_centralizer_singleton_iff.mpr (hhA (ι x) ⟨x, rfl⟩).symm⟩,
        mem_centralizer_singleton_iff.mpr (hhA (ι y) ⟨y, rfl⟩).symm⟩
    have hPle : P ≤ (F ⊓ Kxy x y) ⊔ H := by
      intro q hq
      have hcq : f * h * q * (f * h)⁻¹ ∈ F := by
        rw [← hc]
        exact mem_map_of_mem (MulAut.conj (f * h)).toMonoidHom (hPR hq)
      have hhq : h * q * h⁻¹ ∈ F := by
        have e : h * q * h⁻¹ = f⁻¹ * (f * h * q * (f * h)⁻¹) * f := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hf) hcq) hf
      have hhqK : h * q * h⁻¹ ∈ Kxy x y := (mem_normalizer_iff.mp hhN q).mp (hP.le hq).2
      have e : q = h⁻¹ * (h * q * h⁻¹) * h := by group
      rw [e]
      exact mul_mem (mul_mem (mem_sup_right (inv_mem hh)) (mem_sup_left ⟨hhq, hhqK⟩))
        (mem_sup_right hh)
    exact hMPH.trans (sup_le hPle le_sup_right)
  set W : Subgroup G := xySupOf X₀ Y₀ fun x y => F ⊓ Kxy x y with hW
  have hFW : F ≤ W ⊔ H :=
    hQ.trans (sup_le ((xySupOf_mono h3).trans (xySupOf_sup_le _ H)) le_sup_right)
  have hWF : W ≤ F := xySupOf_le fun _ _ _ _ _ _ => inf_le_left
  intro f hf
  have hf' : f ∈ ((W : Set G) * (H : Set G)) := by
    rw [← coe_mul_of_left_le_normalizer_right W H (hWF.trans hFH)]
    exact hFW hf
  obtain ⟨w, hw, h, hh, rfl⟩ := hf'
  have hhF : h ∈ F := by
    have e : h = w⁻¹ * (w * h) := by group
    rw [e]
    exact mul_mem (inv_mem (hWF hw)) hf
  have hh1 : h = 1 := by
    have hmem : h ∈ F ⊓ H := ⟨hhF, hh⟩
    rwa [hdisj, mem_bot] at hmem
  show w * h ∈ W
  rw [hh1, mul_one]
  exact hw

theorem isKxyGen_of_isKxyGen (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) {H : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hHp : IsPGroup p H) (hHK : H ≤ K) (hHn : (H.subgroupOf K).Normal)
    (hHA : ι.range ≤ normalizer (H : Set G)) (hHgen : IsKxyGen X₀ Y₀ Kxy H) {F : Subgroup G}
    (hFp : IsPGroup p F) (hFK : F ≤ K) (hFA : ι.range ≤ normalizer (F : Set G))
    (hQ : F ≤ xySupOf X₀ Y₀ (fun x y => (F ⊔ H) ⊓ Kxy x y) ⊔ H) :
    IsKxyGen X₀ Y₀ Kxy F := by
  have hFH : F ≤ normalizer (H : Set G) := hFK.trans (le_normalizer_of_normal hHK hHn)
  have hFHp : IsPGroup p (F ⊔ H : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_left' hHp hFp hFH
  have hFHA : ι.range ≤ normalizer ((F ⊔ H : Subgroup G) : Set G) := fun g hg =>
    ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup F H ⟨hFA hg, hHA hg⟩
  have hFHgen : IsKxyGen X₀ Y₀ Kxy (F ⊔ H) := by
    refine sup_le hQ ?_ |>.trans (sup_le le_rfl ?_)
    · exact le_sup_right
    · exact hHgen.trans (xySupOf_mono fun _ _ _ _ _ _ => inf_le_inf_right _ le_sup_right)
  exact hyp.d p (F ⊔ H) hp hFHp (sup_le hFK hHK) hFHA hFHgen F le_sup_left hFA

end Prop22Hyp

section Reduction

variable {A₀ G : Type*} [Group A₀] [Group G] [Finite G] {X₀ Y₀ : Subgroup A₀}
  {Kxy : A₀ → A₀ → Subgroup G}

theorem isKxyGen_of_forall_sylow {F : Subgroup G}
    (h : ∀ p : ℕ, p.Prime → ∃ P : Subgroup G, IsSylowOf p P F ∧ IsKxyGen X₀ Y₀ Kxy P) :
    IsKxyGen X₀ Y₀ Kxy F := by
  set W : Subgroup G := xySupOf X₀ Y₀ fun x y => F ⊓ Kxy x y with hW
  have hrel : (W ⊓ F).relIndex F = 1 := by
    refine Nat.eq_one_iff_not_exists_prime_dvd.mpr fun p hp hdvd => ?_
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP, hPgen⟩ := h p hp
    have hPW : P ≤ W ⊓ F :=
      le_inf (hPgen.trans (xySupOf_mono fun _ _ _ _ _ _ => inf_le_inf_right _ hP.le)) hP.le
    exact (isSylowOf_iff.mp hP).2.2 (hdvd.trans (relIndex_dvd_of_le_left F hPW))
  exact (relIndex_eq_one.mp hrel).trans inf_le_left

end Reduction

theorem prop22Concl_of_step {A₀ : Type*} [Group A₀] {X₀ Y₀ : Subgroup A₀}
    (hstep : Prop22Step.{u} A₀ X₀ Y₀) (G : Type u) [Group G] [Finite G] (ι : A₀ →* G)
    (K : Subgroup G) (Kxy : A₀ → A₀ → Subgroup G) (hyp : Prop22Hyp X₀ Y₀ ι K Kxy) :
    Prop22Concl X₀ Y₀ ι K Kxy := by
  suffices h : ∀ n : ℕ, ∀ (G : Type u) [Group G] [Finite G] (ι : A₀ →* G) (K : Subgroup G)
      (Kxy : A₀ → A₀ → Subgroup G), Nat.card K = n → Prop22Hyp X₀ Y₀ ι K Kxy →
        Prop22Concl X₀ Y₀ ι K Kxy from h _ G ι K Kxy rfl hyp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ ι K Kxy hn hyp
    have IH : ∀ (G' : Type u) [Group G'] [Finite G'] (ι' : A₀ →* G') (K' : Subgroup G')
        (Kxy' : A₀ → A₀ → Subgroup G'), Prop22Hyp X₀ Y₀ ι' K' Kxy' →
          Nat.card K' < Nat.card K → Prop22Concl X₀ Y₀ ι' K' Kxy' :=
      fun G' _ _ ι' K' Kxy' hyp' hlt => ih _ (hn ▸ hlt) G' ι' K' Kxy' rfl hyp'
    by_cases hpow : ∃ p : ℕ, p.Prime ∧ IsPGroup p K
    · obtain ⟨p, hp, hKp⟩ := hpow
      have hKgen : IsKxyGen X₀ Y₀ Kxy K := hyp.gen.trans (xySupOf_mono fun x hx hx1 y hy hy1 =>
        le_inf ((hyp.le x hx hx1 y hy hy1).trans (inf_le_left.trans inf_le_left)) le_rfl)
      intro F hFK hFA
      exact hyp.d p K hp hKp le_rfl hyp.normalizes hKgen F hFK hFA
    · obtain ⟨H, r, hr, hHr, hH1, hHK, hHn, hHA, hHgen⟩ :=
        hstep G ι K Kxy hyp (fun p hp hK => hpow ⟨p, hp, hK⟩) IH
      intro F hFK hFA
      refine isKxyGen_of_forall_sylow fun p hp => ?_
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨P, hP, hPA⟩ := ABGTheoremB.exists_isSylowOf_normalized_of_odd hp
        hyp.isPGroup_range hFA (hyp.odd.of_dvd_nat (card_dvd_of_le hFK))
      refine ⟨P, hP, ?_⟩
      have hPK : P ≤ K := hP.le.trans hFK
      have hQ := hyp.le_xySupOf_sup IH hH1 hHK hHn hHA hPK hPA
      by_cases hpr : p = r
      · subst hpr
        exact hyp.isKxyGen_of_isKxyGen hp hHr hHK hHn hHA hHgen hP.isPGroup hPK hPA hQ
      · exact hyp.isKxyGen_of_coprime hp hr hpr hHr hHK hHn hHA hP.isPGroup hPK hPA hQ

section Bridges

variable {G : Type*} [Group G]

theorem xySupOf_subgroupOf_eq_xySup {X Y J : Subgroup G} (hXJ : X ≤ J) (hYJ : Y ≤ J)
    (f : G → G → Subgroup G) :
    xySupOf (X.subgroupOf J) (Y.subgroupOf J) (fun a b => f a b) = xySup X Y f := by
  apply le_antisymm
  · refine xySupOf_le (f := fun a b : J => f a b) fun a ha ha1 b hb hb1 => ?_
    exact le_iSup₂_of_le (a : G) ha <| le_iSup_of_le (fun h => ha1 (Subtype.ext h)) <|
      le_iSup₂_of_le (b : G) hb <| le_iSup_of_le (fun h => hb1 (Subtype.ext h)) le_rfl
  · refine iSup₂_le fun x hx => iSup_le fun hx1 => iSup₂_le fun y hy => iSup_le fun hy1 => ?_
    exact le_xySupOf (f := fun a b : J => f a b) (x := ⟨x, hXJ hx⟩) (y := ⟨y, hYJ hy⟩) hx
      (fun h => hx1 (congrArg Subtype.val h)) hy (fun h => hy1 (congrArg Subtype.val h))

theorem isKxyGen_iff_eq_xySup {X Y : Subgroup G} (Kxy : G → G → Subgroup G) (F : Subgroup G) :
    IsKxyGen (X.subgroupOf (X ⊔ Y)) (Y.subgroupOf (X ⊔ Y)) (fun a b => Kxy a b) F ↔
      F = xySup X Y fun x y => F ⊓ Kxy x y := by
  have h := xySupOf_subgroupOf_eq_xySup (le_sup_left : X ≤ X ⊔ Y) (le_sup_right : Y ≤ X ⊔ Y)
    (fun x y => F ⊓ Kxy x y)
  unfold IsKxyGen
  rw [h]
  refine ⟨fun hle => le_antisymm hle ?_, fun heq => heq.le⟩
  exact iSup₂_le fun _ _ => iSup_le fun _ => iSup₂_le fun _ _ => iSup_le fun _ => inf_le_left

end Bridges

section ScratchForm

variable {G : Type u} [Group G]

private theorem isKleinFour_subgroupOf {X J : Subgroup G} (hXJ : X ≤ J) (hX : IsKleinFour X) :
    IsKleinFour (X.subgroupOf J) := by
  let e : X.subgroupOf J ≃* X := subgroupOfEquivOfLe hXJ
  exact ⟨by rw [Nat.card_congr e.toEquiv, hX.card_four],
    by rw [Monoid.exponent_eq_of_mulEquiv e, hX.exponent_two]⟩

private theorem mem_zpowers_coe_iff {J : Subgroup G} {a b : J} :
    (b : G) ∈ zpowers (a : G) ↔ b ∈ zpowers a := by
  have h := MonoidHom.map_zpowers J.subtype a
  change J.subtype b ∈ zpowers (J.subtype a) ↔ _
  rw [← h]
  exact mem_map_iff_mem J.subtype_injective

theorem prop22Hyp_of_subgroups {K X Y : Subgroup G} (hK : Odd (Nat.card K))
    (hX : IsKleinFour X) (hY : IsKleinFour Y) (hXY : X ⊓ Y = ⊥)
    (hYX : Y ≤ centralizer (X : Set G)) (hAK : X ⊔ Y ≤ normalizer (K : Set G))
    (Kxy : G → G → Subgroup G)
    (hle : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → Kxy x y ≤ K ⊓ C x ⊓ C y)
    (hnormal : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 →
      ((Kxy x y).subgroupOf (K ⊓ C x ⊓ C y)).Normal)
    (hinv : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → X ⊔ Y ≤ normalizer (Kxy x y : Set G))
    (hgen : K = xySup X Y Kxy)
    (ha : ∀ x ∈ X, x ≠ 1 → ∀ x' ∈ X, x' ≠ 1 → ∀ y ∈ Y, y ≠ 1 → ∀ y' ∈ Y, y' ≠ 1 →
      Kxy x y ⊓ C x' ≤ Kxy x' y ∧ Kxy x y ⊓ C y' ≤ Kxy x y')
    (hb : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ K ⊓ C x ⊓ C y,
      (∀ x' ∈ X, x' ∉ zpowers x → x' * u * x'⁻¹ = u⁻¹) →
      (∀ y' ∈ Y, y' ∉ zpowers y → y' * u * y'⁻¹ = u⁻¹) → u ∈ Kxy x y)
    (hc : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 →
      (∀ u ∈ ⁅⁅K ⊓ C x, Y⁆, ⁅K ⊓ C x, Y⁆⁆ ⊓ C y,
        (∀ y' ∈ Y, y' ∉ zpowers y → y' * u * y'⁻¹ = u⁻¹) → u ∈ Kxy x y) ∧
      (∀ u ∈ ⁅⁅K ⊓ C y, X⁆, ⁅K ⊓ C y, X⁆⁆ ⊓ C x,
        (∀ x' ∈ X, x' ∉ zpowers x → x' * u * x'⁻¹ = u⁻¹) → u ∈ Kxy x y))
    (hd : ∀ (p : ℕ) (P : Subgroup G), p.Prime → IsPGroup p P → P ≤ K →
      X ⊔ Y ≤ normalizer (P : Set G) → P = xySup X Y (fun x y => P ⊓ Kxy x y) →
      ∀ Q ≤ P, X ⊔ Y ≤ normalizer (Q : Set G) → Q = xySup X Y (fun x y => Q ⊓ Kxy x y)) :
    Prop22Hyp (X.subgroupOf (X ⊔ Y)) (Y.subgroupOf (X ⊔ Y)) (X ⊔ Y).subtype K
      (fun a b => Kxy a b) := by
  have hXJ : X ≤ X ⊔ Y := le_sup_left
  have hYJ : Y ≤ X ⊔ Y := le_sup_right
  have hrange : (X ⊔ Y).subtype.range = X ⊔ Y := range_subtype _
  have hne : ∀ a : ↥(X ⊔ Y), a ≠ 1 → (a : G) ≠ 1 := fun a ha h => ha (Subtype.ext h)
  have hXz : ∀ x : ↥(X ⊔ Y), ∀ (P : G → Prop),
      (∀ x' ∈ X.subgroupOf (X ⊔ Y), x' ∉ zpowers x → P x') → ∀ x' ∈ X, x' ∉ zpowers (x : G) →
        P x' := by
    intro x P h x' hx' hx'z
    exact h ⟨x', hXJ hx'⟩ hx' (fun hz => hx'z (mem_zpowers_coe_iff.mpr hz))
  have hYz : ∀ y : ↥(X ⊔ Y), ∀ (P : G → Prop),
      (∀ y' ∈ Y.subgroupOf (X ⊔ Y), y' ∉ zpowers y → P y') → ∀ y' ∈ Y, y' ∉ zpowers (y : G) →
        P y' := by
    intro y P h y' hy' hy'z
    exact h ⟨y', hYJ hy'⟩ hy' (fun hz => hy'z (mem_zpowers_coe_iff.mpr hz))
  have hgenK : ∀ P : Subgroup G,
      IsKxyGen (X.subgroupOf (X ⊔ Y)) (Y.subgroupOf (X ⊔ Y)) (fun a b => Kxy a b) P ↔
        P = xySup X Y fun x y => P ⊓ Kxy x y := fun P => isKxyGen_iff_eq_xySup Kxy P
  refine
    { kleinX := isKleinFour_subgroupOf hXJ hX
      kleinY := isKleinFour_subgroupOf hYJ hY
      inf_eq := ?_
      comm := ?_
      sup_eq := by rw [← subgroupOf_sup hXJ hYJ, subgroupOf_self]
      inj := Subtype.val_injective
      odd := hK
      normalizes := by rw [hrange]; exact hAK
      le := fun x hx hx1 y hy hy1 => hle x hx (hne x hx1) y hy (hne y hy1)
      normal := fun x hx hx1 y hy hy1 => hnormal x hx (hne x hx1) y hy (hne y hy1)
      inv := fun x hx hx1 y hy hy1 => by rw [hrange]; exact hinv x hx (hne x hx1) y hy (hne y hy1)
      gen := by
        rw [xySupOf_subgroupOf_eq_xySup hXJ hYJ Kxy, ← hgen]
      a := fun x hx hx1 x' hx' hx'1 y hy hy1 y' hy' hy'1 =>
        ha x hx (hne x hx1) x' hx' (hne x' hx'1) y hy (hne y hy1) y' hy' (hne y' hy'1)
      b := fun x hx hx1 y hy hy1 u hu hX' hY' => hb x hx (hne x hx1) y hy (hne y hy1) u hu
        (hXz x _ hX') (hYz y _ hY')
      c := fun x hx hx1 y hy hy1 => ⟨fun u hu hY' => (hc x hx (hne x hx1) y hy (hne y hy1)).1 u
          (by rwa [map_subgroupOf_eq_of_le hYJ] at hu) (hYz y _ hY'),
        fun u hu hX' => (hc x hx (hne x hx1) y hy (hne y hy1)).2 u
          (by rwa [map_subgroupOf_eq_of_le hXJ] at hu) (hXz x _ hX')⟩
      d := fun p P hp hPp hPK hPA hPgen Q hQP hQA => (hgenK Q).mpr
        (hd p P hp hPp hPK (by rw [← hrange]; exact hPA) ((hgenK P).mp hPgen) Q hQP
          (by rw [← hrange]; exact hQA)) }
  · rw [eq_bot_iff]
    intro a ha
    have h : (a : G) ∈ X ⊓ Y := ha
    rw [hXY, mem_bot] at h
    exact (mem_bot).mpr (Subtype.ext h)
  · intro b hb
    rw [mem_centralizer_iff]
    intro a ha
    exact Subtype.ext ((mem_centralizer_iff.mp (hYX hb)) a ha)

theorem prop_2_2_of_step [Finite G] {K X Y : Subgroup G}
    (hstep : Prop22Step.{u} (X ⊔ Y : Subgroup G) (X.subgroupOf (X ⊔ Y)) (Y.subgroupOf (X ⊔ Y)))
    (hK : Odd (Nat.card K)) (hX : IsKleinFour X) (hY : IsKleinFour Y) (hXY : X ⊓ Y = ⊥)
    (hYX : Y ≤ centralizer (X : Set G)) (hAK : X ⊔ Y ≤ normalizer (K : Set G))
    (Kxy : G → G → Subgroup G)
    (hle : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → Kxy x y ≤ K ⊓ C x ⊓ C y)
    (hnormal : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 →
      ((Kxy x y).subgroupOf (K ⊓ C x ⊓ C y)).Normal)
    (hinv : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → X ⊔ Y ≤ normalizer (Kxy x y : Set G))
    (hgen : K = xySup X Y Kxy)
    (ha : ∀ x ∈ X, x ≠ 1 → ∀ x' ∈ X, x' ≠ 1 → ∀ y ∈ Y, y ≠ 1 → ∀ y' ∈ Y, y' ≠ 1 →
      Kxy x y ⊓ C x' ≤ Kxy x' y ∧ Kxy x y ⊓ C y' ≤ Kxy x y')
    (hb : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ K ⊓ C x ⊓ C y,
      (∀ x' ∈ X, x' ∉ zpowers x → x' * u * x'⁻¹ = u⁻¹) →
      (∀ y' ∈ Y, y' ∉ zpowers y → y' * u * y'⁻¹ = u⁻¹) → u ∈ Kxy x y)
    (hc : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 →
      (∀ u ∈ ⁅⁅K ⊓ C x, Y⁆, ⁅K ⊓ C x, Y⁆⁆ ⊓ C y,
        (∀ y' ∈ Y, y' ∉ zpowers y → y' * u * y'⁻¹ = u⁻¹) → u ∈ Kxy x y) ∧
      (∀ u ∈ ⁅⁅K ⊓ C y, X⁆, ⁅K ⊓ C y, X⁆⁆ ⊓ C x,
        (∀ x' ∈ X, x' ∉ zpowers x → x' * u * x'⁻¹ = u⁻¹) → u ∈ Kxy x y))
    (hd : ∀ (p : ℕ) (P : Subgroup G), p.Prime → IsPGroup p P → P ≤ K →
      X ⊔ Y ≤ normalizer (P : Set G) → P = xySup X Y (fun x y => P ⊓ Kxy x y) →
      ∀ Q ≤ P, X ⊔ Y ≤ normalizer (Q : Set G) → Q = xySup X Y (fun x y => Q ⊓ Kxy x y)) :
    ∀ F ≤ K, X ⊔ Y ≤ normalizer (F : Set G) → F = xySup X Y (fun x y => F ⊓ Kxy x y) := by
  intro F hFK hFA
  have hyp := prop22Hyp_of_subgroups hK hX hY hXY hYX hAK Kxy hle hnormal hinv hgen ha hb hc hd
  have h := prop22Concl_of_step hstep G (X ⊔ Y).subtype K (fun a b => Kxy a b) hyp F hFK
    (by rw [range_subtype]; exact hFA)
  exact (isKxyGen_iff_eq_xySup Kxy F).mp h

end ScratchForm

end CFSG.GH72
