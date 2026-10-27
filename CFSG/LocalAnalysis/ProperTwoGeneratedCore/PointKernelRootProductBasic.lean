module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

universe u

variable {G : Type u} [Group G]

theorem relIndex_le_two_of_forall {X Y : Subgroup G} {a : G} (ha : a ∈ X)
    (h : ∀ b ∈ X, b ∈ Y ∨ a⁻¹ * b ∈ Y) : Y.relIndex X ≤ 2 := by
  have hdvd : (Y.subgroupOf X).index ∣ 2 := by
    refine Subgroup.index_dvd_two_iff'.mpr ⟨(⟨a, ha⟩ : X)⁻¹, fun b => ?_⟩
    rcases h b b.2 with hb | hb
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr (by simpa using hb))
  exact Nat.le_of_dvd two_pos hdvd

theorem eq_of_inv_mul_mem_of_central_odd {L : Type*} [Group L] [Finite L] {Z : Subgroup L}
    (hZ : Z ≤ Subgroup.center L) (hodd : Odd (Nat.card Z)) {x y : L} {m n : ℕ}
    (hx : x ^ 2 ^ m = 1) (hy : y ^ 2 ^ n = 1) (hxy : x⁻¹ * y ∈ Z) : x = y := by
  have hc : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp (hZ hxy) x
  have hyc : y = x * (x⁻¹ * y) := (mul_inv_cancel_left x y).symm
  have hpow : (x⁻¹ * y) ^ 2 ^ (m + n) = 1 := by
    have h1 : x ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, hx, one_pow]
    have h2 : y ^ 2 ^ (m + n) = 1 := by rw [pow_add, mul_comm, pow_mul, hy, one_pow]
    rwa [hyc, hc.mul_pow, h1, one_mul] at h2
  have hodd' : Odd (orderOf (x⁻¹ * y)) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Z hxy)
  have hone := Nat.Coprime.eq_one_of_dvd (hodd'.coprime_two_right.pow_right (m + n))
    (orderOf_dvd_of_pow_eq_one hpow)
  rw [orderOf_eq_one_iff] at hone
  rw [hyc, hone, mul_one]

theorem mem_sylow_of_mem_normalizer {J : Type*} [Group J] (S : Sylow 2 J) {y : J}
    (hy : y ∈ Subgroup.normalizer ((S : Subgroup J) : Set J)) {k : ℕ} (hk : y ^ 2 ^ k = 1) :
    y ∈ (S : Subgroup J) := by
  have hP : IsPGroup 2 (Subgroup.zpowers y) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (y ^ n) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hmem : y ∈ Subgroup.zpowers y ⊓ (S : Subgroup J) := by
    rw [← hP.inf_normalizer_sylow S]
    exact ⟨Subgroup.mem_zpowers y, hy⟩
  exact hmem.2

theorem centralizer_conj_mem_hull (z w : G) {x l : G}
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hl : l ∈ localInvolutionPointHull z w) :
    x * l * x⁻¹ ∈ localInvolutionPointHull z w :=
  (Subgroup.mem_normalizer_iff.mp
    (CFSG.ProperTwoGeneratedCore.local_point_hull_normalized_by_centralizer z w hx) l).mp hl

@[expose] def hullImage (L Y : Subgroup G) : Subgroup (L ⧸ CFSG.oddCore L) :=
  (Y.subgroupOf L).map (QuotientGroup.mk' _)

theorem mk_mem_hullImage (L : Subgroup G) {Y : Subgroup G} {y : L} (hy : (y : G) ∈ Y) :
    QuotientGroup.mk' (CFSG.oddCore L) y ∈ hullImage L Y :=
  ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem hullImage_mono (L : Subgroup G) {Y Y' : Subgroup G} (h : Y ≤ Y') :
    hullImage L Y ≤ hullImage L Y' :=
  Subgroup.map_mono fun _ hy => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hy))

theorem quotConj_mk (z w : G) (x : Subgroup.centralizer ({w} : Set G))
    (l : localInvolutionPointHull z w) :
    originalCentralizerHullQuotientConjugation z w x (QuotientGroup.mk' _ l) =
      QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w))
        ⟨x * l * x⁻¹, centralizer_conj_mem_hull z w x.2 l.2⟩ :=
  rfl

theorem quotConj_of_mem_hull (z w : G) (x : Subgroup.centralizer ({w} : Set G))
    (hx : (x : G) ∈ localInvolutionPointHull z w) :
    originalCentralizerHullQuotientConjugation z w x =
      MulAut.conj (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w)) ⟨x, hx⟩) := by
  rw [← originalCentralizerHullQuotientConjugation_hull_element z w ⟨x, hx⟩]
  rfl

theorem quotConj_map_hullImage (z w : G) (x : Subgroup.centralizer ({w} : Set G))
    {Y : Subgroup G} (hYL : Y ≤ localInvolutionPointHull z w)
    (hY : ∀ y ∈ Y, (x : G) * y * (x : G)⁻¹ ∈ Y) (hY' : ∀ y ∈ Y, (x : G)⁻¹ * y * x ∈ Y) :
    (hullImage (localInvolutionPointHull z w) Y).map
        (originalCentralizerHullQuotientConjugation z w x).toMonoidHom =
      hullImage (localInvolutionPointHull z w) Y := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    change originalCentralizerHullQuotientConjugation z w x (QuotientGroup.mk' _ y) ∈ _
    rw [quotConj_mk]
    exact mk_mem_hullImage _ (hY y (Subgroup.mem_subgroupOf.mp hy))
  · rintro _ ⟨y, hy, rfl⟩
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    let y' : localInvolutionPointHull z w := ⟨(x : G)⁻¹ * y * x, hYL (hY' y hyY)⟩
    refine ⟨QuotientGroup.mk' _ y', mk_mem_hullImage _ (hY' y hyY), ?_⟩
    change originalCentralizerHullQuotientConjugation z w x (QuotientGroup.mk' _ y') = _
    rw [quotConj_mk]
    congr 1
    apply Subtype.ext
    change (x : G) * ((x : G)⁻¹ * y * x) * (x : G)⁻¹ = y
    group

theorem quotConj_apply_hullImage (z w : G) (x : Subgroup.centralizer ({w} : Set G))
    {Y : Subgroup G} (hY : ∀ y ∈ Y, (x : G) * y = y * x) :
    ∀ a ∈ hullImage (localInvolutionPointHull z w) Y,
      originalCentralizerHullQuotientConjugation z w x a = a := by
  rintro _ ⟨y, hy, rfl⟩
  rw [quotConj_mk]
  congr 1
  apply Subtype.ext
  change (x : G) * y * (x : G)⁻¹ = y
  rw [hY y (Subgroup.mem_subgroupOf.mp hy), mul_inv_cancel_right]

theorem hull_conj_mem {z w x : G} (g : G) (hx : x ∈ localInvolutionPointHull z w) :
    g⁻¹ * x * g ∈ localInvolutionPointHull z (g⁻¹ * w * g) := by
  let φ : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hφ : ∀ y, φ y = g⁻¹ * y * g := fun y => by
    simp [φ]
  have hle : localInvolutionPointHull z w ≤
      (localInvolutionPointHull z (g⁻¹ * w * g)).comap φ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨e, rfl⟩, hyw⟩
    change φ (rightConjugateElem z e) ∈ localInvolutionPointHull z (g⁻¹ * w * g)
    rw [hφ]
    refine mem_localInvolutionPointHull ⟨e * g, ?_⟩ ?_
    · simp only [rightConjugateElem]
      group
    · have hcomm : Commute (rightConjugateElem z e) w :=
        Subgroup.mem_centralizer_singleton_iff.mp hyw
      have := hcomm.map φ
      rwa [hφ, hφ] at this
  have := hle hx
  rwa [Subgroup.mem_comap, hφ] at this

theorem mem_hull_of_isConj {z w t : G} (h : IsConj z t) (hcomm : Commute t w) :
    t ∈ localInvolutionPointHull z w := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  refine mem_localInvolutionPointHull ⟨c⁻¹, ?_⟩ hcomm
  simp only [rightConjugateElem, inv_inv]

theorem commutator_centralizer_le_hull {z w t : G} (I : Subgroup G)
    (ht : t ∈ localInvolutionPointHull z w) :
    ⁅I ⊓ Subgroup.centralizer {w}, Subgroup.zpowers t⁆ ≤ localInvolutionPointHull z w := by
  rw [Subgroup.commutator_le]
  intro c hc k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have htn : t ^ n ∈ localInvolutionPointHull z w := Subgroup.zpow_mem _ ht n
  exact Subgroup.mul_mem _ (centralizer_conj_mem_hull z w hc.2 htn) (Subgroup.inv_mem _ htn)

theorem hull_centralizer_inf_eq_bot [Finite G] (hZ : Subgroup.center G = ⊥)
    {z t u : G} (hz : orderOf z = 2) (hzt : IsConj z t) (hu : orderOf u = 2) (hut : u ≠ t)
    (huz : Commute u z) (hutc : Commute u t)
    (I : Subgroup G) (hIodd : Odd (Nat.card I))
    (huI : u ∈ Subgroup.normalizer (I : Set G)) (htI : t ∈ Subgroup.normalizer (I : Set G))
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ ⁅I, Subgroup.zpowers t⁆ = ⊤)
    {g : G} (hgL : g ∈ localInvolutionPointHull z u) (hgt : g⁻¹ * z * g = t) :
    Subgroup.centralizer (localInvolutionPointHull z u : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z (u * z) : Set G) = ⊥ := by
  set A := Subgroup.centralizer (localInvolutionPointHull z u : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z (u * z) : Set G) with hA
  have ht : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := hzt
    exact hc.orderOf_eq.symm.trans hz
  have hzLu : z ∈ localInvolutionPointHull z u := distinguished_mem_localInvolutionPointHull huz
  have htLu : t ∈ localInvolutionPointHull z u := mem_hull_of_isConj hzt hutc.symm
  have hgu : Commute g u :=
    Subgroup.mem_centralizer_singleton_iff.mp (localInvolutionPointHull_le_centralizer z u hgL)
  have hconjv : g⁻¹ * (u * z) * g = u * t := by
    rw [← hgt]
    have : g⁻¹ * u * g = u := by rw [mul_assoc, ← hgu.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    calc g⁻¹ * (u * z) * g = (g⁻¹ * u * g) * (g⁻¹ * z * g) := by group
      _ = u * (g⁻¹ * z * g) := by rw [this]
  have hAut : ∀ a ∈ A, ∀ y ∈ localInvolutionPointHull z (u * t), Commute a y := by
    intro a haA y hy
    have hy' : g * y * g⁻¹ ∈ localInvolutionPointHull z (u * z) := by
      have h := hull_conj_mem (z := z) g⁻¹ hy
      have hw : g⁻¹⁻¹ * (u * t) * g⁻¹ = u * z := by
        rw [inv_inv, ← hconjv]; group
      rw [hw] at h
      simpa only [inv_inv] using h
    have hag : Commute a g :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 g hgL)).symm
    have hay' : Commute a (g * y * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).2 _ hy').symm
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this]
    exact (hag.inv_right.mul_right hay').mul_right hag
  have htLut : t ∈ localInvolutionPointHull z (u * t) :=
    mem_hull_of_isConj hzt (hutc.symm.mul_right (Commute.refl t)).symm.symm
  have hIt : ⁅I, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (A : Set G) := by
    rw [odd_four_group_ambient_commutator_generation I u t hu ht hut hutc huI htI hIodd]
    apply sup_le
    · intro x hx
      have hxL := commutator_centralizer_le_hull (z := z) I htLu hx
      rw [Subgroup.mem_centralizer_iff]
      intro a haA
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 x hxL)).symm
    · intro x hx
      have hxL := commutator_centralizer_le_hull (z := z) I htLut hx
      rw [Subgroup.mem_centralizer_iff]
      intro a haA
      exact (hAut a haA x hxL).eq
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := by
    rw [← hgen]
    refine sup_le (sup_le ?_ ?_) hIt
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a haA
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 z hzLu)).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a haA
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 t htLu)).symm
  rw [eq_bot_iff, ← hZ]
  intro a haA
  rw [Subgroup.mem_center_iff]
  intro x
  exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top x)) a haA).symm

end CFSG.ProperTwoGeneratedCore.RankOnePair
