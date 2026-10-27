module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndLayer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup)
open CFSG.ComponentClassification.AschbacherKnownGroup (HasDihedralSylowTwo HasCyclicSylowTwo)

section Dihedral

variable {X : Type} [Group X] [Finite X]

theorem exists_commuting_pair_of_isSylowOf {R M : Subgroup X} (hR : IsSylowOf 2 R M)
    (hRd : IsDihedralTwoGroup R) {y : X} (hyM : y ∈ M) (hy : y ^ 2 = 1) :
    ∃ u w : X, u ∈ M ∧ w ∈ M ∧ u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧
      u * w = w * u ∧ u * y = y * u ∧ w * y = y * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcM, hcR⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hy)) ((zpowers_le).mpr hyM)
  have hy' : c⁻¹ * y * c ∈ R := hcR ((mem_rightConjugate_iff _ c _).mpr (by
    rw [show c * (c⁻¹ * y * c) * c⁻¹ = y by group]
    exact mem_zpowers y))
  obtain ⟨n, hn, ⟨e⟩⟩ := hRd
  have hev : Even (2 ^ (n - 1)) := (Nat.even_pow' (by omega)).mpr even_two
  have hy2 : (e ⟨c⁻¹ * y * c, hy'⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨c⁻¹ * y * c, hy'⟩ : R) ^ 2 = 1 := Subtype.ext (by
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [show (c⁻¹ * y * c) ^ 2 = c⁻¹ * y ^ 2 * c by rw [pow_two, pow_two]; group, hy]
      group)
    rw [this, map_one]
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, hc, hay, hby⟩ :=
    AschbacherKnownGroup.FactsL2.dihedral_exists_commuting_involutions hev (by positivity) _ hy2
  set a' : X := ((e.symm a : R) : X)
  set b' : X := ((e.symm b : R) : X)
  have hRM : R ≤ M := hR.le
  have hval : ∀ x y : DihedralGroup (2 ^ (n - 1)), x * y = y * x →
      ((e.symm x : R) : X) * ((e.symm y : R) : X) = ((e.symm y : R) : X) * ((e.symm x : R) : X) :=
    fun x y h => by rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, h]
  have hya : a' * (c⁻¹ * y * c) = (c⁻¹ * y * c) * a' := by
    have h := hval a (e ⟨c⁻¹ * y * c, hy'⟩) hay
    rwa [MulEquiv.symm_apply_apply] at h
  have hyb : b' * (c⁻¹ * y * c) = (c⁻¹ * y * c) * b' := by
    have h := hval b (e ⟨c⁻¹ * y * c, hy'⟩) hby
    rwa [MulEquiv.symm_apply_apply] at h
  have hsq : ∀ x : DihedralGroup (2 ^ (n - 1)), x ^ 2 = 1 → ((e.symm x : R) : X) ^ 2 = 1 :=
    fun x hx => by rw [← coe_pow, ← map_pow, hx, map_one, coe_one]
  have hne : ∀ x : DihedralGroup (2 ^ (n - 1)), x ≠ 1 → ((e.symm x : R) : X) ≠ 1 :=
    fun x hx h => hx (e.symm.injective (Subtype.ext (by rw [h, map_one, coe_one])))
  refine ⟨c * a' * c⁻¹, c * b' * c⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem hcM (hRM (e.symm a).2)) (inv_mem hcM)
  · exact mul_mem (mul_mem hcM (hRM (e.symm b).2)) (inv_mem hcM)
  · rw [conj_pow, hsq a ha]; group
  · rw [conj_pow, hsq b hb]; group
  · intro h
    apply hne a ha1
    show a' = 1
    rw [show a' = c⁻¹ * (c * a' * c⁻¹) * c by group, h]
    group
  · intro h
    apply hne b hb1
    show b' = 1
    rw [show b' = c⁻¹ * (c * b' * c⁻¹) * c by group, h]
    group
  · intro h
    apply hab
    apply e.symm.injective
    apply Subtype.ext
    change a' = b'
    rw [show a' = c⁻¹ * (c * a' * c⁻¹) * c by group, h]
    group
  · calc c * a' * c⁻¹ * (c * b' * c⁻¹) = c * (a' * b') * c⁻¹ := by group
      _ = c * (b' * a') * c⁻¹ := by rw [hval a b hc]
      _ = c * b' * c⁻¹ * (c * a' * c⁻¹) := by group
  · calc c * a' * c⁻¹ * y = c * (a' * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * a') * c⁻¹ := by rw [hya]
      _ = y * (c * a' * c⁻¹) := by group
  · calc c * b' * c⁻¹ * y = c * (b' * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * b') * c⁻¹ := by rw [hyb]
      _ = y * (c * b' * c⁻¹) := by group

theorem hasFourGroup_of_not_hasCyclicSylowTwo {R M Y : Subgroup X} (hR : IsSylowOf 2 R M)
    (hRd : IsDihedralTwoGroup R) (hYM : Y ≤ M) (hY : ¬ HasCyclicSylowTwo Y) :
    HasFourGroup Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Y))
  have hnc : ¬ IsCyclic (P : Subgroup Y) := fun h => hY ⟨P, h⟩
  let e : (P : Subgroup Y) ≃* (P : Subgroup Y).map Y.subtype :=
    (P : Subgroup Y).equivMapOfInjective Y.subtype Y.subtype_injective
  rcases isCyclic_or_dihedral_of_isSylowOf hR hRd ((map_subtype_le _).trans hYM)
      (P.isPGroup'.map Y.subtype) with h | ⟨k, hk, ⟨f⟩⟩
  · exact absurd ((MulEquiv.isCyclic e).mpr h) hnc
  · have hev : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨a, b, ha, hb, ha1, hb1, hab, hc, -, -⟩ :=
      AschbacherKnownGroup.FactsL2.dihedral_exists_commuting_involutions hev
        (by positivity) 1 (one_pow 2)
    have hmem : ∀ x : DihedralGroup (2 ^ k),
        ((f.symm x : (P : Subgroup Y).map Y.subtype) : X) ∈ Y :=
      fun x => map_subtype_le _ (f.symm x).2
    have hinj : ∀ x y : DihedralGroup (2 ^ k),
        ((f.symm x : (P : Subgroup Y).map Y.subtype) : X) = (f.symm y : _) → x = y :=
      fun x y h => f.symm.injective (Subtype.ext h)
    refine hasFourGroup_of_commute (hmem a) (hmem b) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← coe_pow, ← map_pow, ha, map_one, coe_one]
    · rw [← coe_pow, ← map_pow, hb, map_one, coe_one]
    · intro h
      exact ha1 (hinj a 1 (by rw [h, map_one, coe_one]))
    · intro h
      exact hb1 (hinj b 1 (by rw [h, map_one, coe_one]))
    · exact fun h => hab (hinj a b h)
    · rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, hc]

theorem mem_of_mem_centralizer_fourGroup {R M V : Subgroup X} (hR : IsSylowOf 2 R M)
    (hRd : IsDihedralTwoGroup R) (hVM : V ≤ M) (hV : ∀ v ∈ V, v ^ 2 = 1) (hV4 : Nat.card V = 4)
    {x : X} (hxM : x ∈ M) (hx : x ^ 2 = 1) (hxV : x ∈ centralizer (V : Set X)) : x ∈ V := by
  by_contra hxV'
  have hx1 : x ≠ 1 := fun h => hxV' (h ▸ one_mem V)
  have hcent : zpowers x ≤ centralizer (V : Set X) := (zpowers_le).mpr hxV
  have hN : zpowers x ≤ normalizer (V : Set X) := hcent.trans (centralizer_le_normalizer _)
  have hsq : ∀ y ∈ zpowers x ⊔ V, y ^ 2 = 1 := by
    intro y hy
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hN] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hy
    have hab : Commute a b := (mem_centralizer_iff.mp (hcent ha) b hb).symm
    rw [hab.mul_pow, sq_eq_one_of_mem_zpowers hx ha, hV b hb, one_mul]
  have hle := card_le_four_of_sq_eq_one hR hRd (sup_le ((zpowers_le).mpr hxM) hVM) hsq
    (fun a ha b hb => mul_comm_of_sq_eq_one hsq ha hb)
  have h8 := card_sup_mul_card_inf hN
  have hinf : zpowers x ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyx, hyV⟩ := mem_inf.mp hy
    rcases eq_one_or_eq_of_mem_zpowers hx hx1 hyx with rfl | rfl
    · exact one_mem _
    · exact absurd hyV hxV'
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hx hx1, hV4] at h8
  omega

theorem dihedral_eq_mul_of_sq {n : ℕ} (x : DihedralGroup n) :
    ∃ a b : DihedralGroup n, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ x = a * b := by
  rcases x with i | i
  · exact ⟨DihedralGroup.sr 0, DihedralGroup.sr i, by rw [pow_two, DihedralGroup.sr_mul_self],
      by rw [pow_two, DihedralGroup.sr_mul_self], by rw [DihedralGroup.sr_mul_sr, sub_zero]⟩
  · exact ⟨DihedralGroup.sr i, 1, by rw [pow_two, DihedralGroup.sr_mul_self], one_pow 2,
      (mul_one _).symm⟩

theorem mem_of_forall_sq_mem {R M N : Subgroup X} (hR : IsSylowOf 2 R M)
    (hRd : IsDihedralTwoGroup R) (hN : ∀ y ∈ M, y ^ 2 = 1 → y ∈ N) {x : X} (hxM : x ∈ M)
    (hx : IsPGroup 2 (zpowers x)) : x ∈ N := by
  obtain ⟨c, hcM, hcR⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR hx
    ((zpowers_le).mpr hxM)
  have hx' : c⁻¹ * x * c ∈ R := hcR ((mem_rightConjugate_iff _ c _).mpr (by
    rw [show c * (c⁻¹ * x * c) * c⁻¹ = x by group]
    exact mem_zpowers x))
  obtain ⟨n, -, ⟨e⟩⟩ := hRd
  obtain ⟨a, b, ha, hb, hab⟩ := dihedral_eq_mul_of_sq (e ⟨c⁻¹ * x * c, hx'⟩)
  have hRM : R ≤ M := hR.le
  have hsq : ∀ z : DihedralGroup (2 ^ (n - 1)), z ^ 2 = 1 →
      c * ((e.symm z : R) : X) * c⁻¹ ∈ N := fun z hz => by
    refine hN _ (mul_mem (mul_mem hcM (hRM (e.symm z).2)) (inv_mem hcM)) ?_
    rw [conj_pow, ← coe_pow, ← map_pow, hz, map_one, coe_one]
    group
  have hx2 : c⁻¹ * x * c = ((e.symm a : R) : X) * ((e.symm b : R) : X) := by
    rw [← coe_mul, ← map_mul, ← hab, MulEquiv.symm_apply_apply]
  have : x = (c * ((e.symm a : R) : X) * c⁻¹) * (c * ((e.symm b : R) : X) * c⁻¹) := by
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = _ := by rw [hx2]; group
  rw [this]
  exact mul_mem (hsq a ha) (hsq b hb)

end Dihedral

variable {G : Type} [Group G] [Finite G]

theorem bar_inf_centralizer_le {Q Y T : Subgroup G} (hOY : oddCoreIn Q ≤ Y)
    (hYO : Y ≤ normalizer (oddCoreIn Q : Set G)) (hT : IsPGroup 2 T)
    (hTH : T ≤ normalizer (Q : Set G)) :
    bar Q Y ⊓ centralizer (bar Q T : Set (Bar Q)) ≤ bar Q (Y ⊓ centralizer (T : Set G)) := by
  intro z hz
  obtain ⟨hzY, hzC⟩ := mem_inf.mp hz
  obtain ⟨y, hyY, rfl⟩ := (mem_bar_iff Q _ z).mp hzY
  have hTO : T ≤ normalizer (oddCoreIn Q : Set G) :=
    hTH.trans (normalizer_le_normalizer_oddCoreIn Q)
  have hc : ∀ t ∈ T, t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ oddCoreIn Q := by
    intro t ht
    have hcomm : toBar Q ⟨t, hTH ht⟩ * toBar Q y = toBar Q y * toBar Q ⟨t, hTH ht⟩ :=
      mem_centralizer_iff.mp hzC _ (toBar_mem_bar Q (h := ⟨t, hTH ht⟩) ht)
    have h1 : toBar Q (⟨t, hTH ht⟩ * y * (⟨t, hTH ht⟩ : normalizer (Q : Set G))⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    rw [toBar_eq_one_iff] at h1
    exact h1
  obtain ⟨c, hcC, hcO⟩ := exists_mem_centralizer_of_commutator hT (odd_card_oddCoreIn Q) hTO
    (hYO hyY) hc
  have hceq : c = (y : G) * (c⁻¹ * y)⁻¹ := by group
  have hcY : c ∈ Y := by
    rw [hceq]
    exact mul_mem hyY (inv_mem (hOY hcO))
  have hcN : c ∈ normalizer (Q : Set G) := by
    rw [hceq]
    exact mul_mem y.2 (inv_mem (((oddCoreIn_le Q).trans le_normalizer) hcO))
  refine (mem_bar_iff Q _ _).mpr ⟨⟨c, hcN⟩, mem_inf.mpr ⟨hcY, hcC⟩, ?_⟩
  rw [eq_comm, ← mul_inv_eq_one, ← map_inv, ← map_mul, toBar_eq_one_iff]
  show (y : G) * c⁻¹ ∈ oddCoreIn Q
  have : (y : G) * c⁻¹ = c * (c⁻¹ * y) * c⁻¹ := by group
  rw [this]
  exact (mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn Q hcN) _).mp hcO

omit [Finite G] in
theorem centralizer_singleton_le_centralizer_bar_zpowers (Q : Subgroup G) {u : G}
    (huN : u ∈ normalizer (Q : Set G)) :
    centralizer ({toBar Q ⟨u, huN⟩} : Set (Bar Q)) ≤
      centralizer (bar Q (zpowers u) : Set (Bar Q)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro z hz
  obtain ⟨h, hh, rfl⟩ := (mem_bar_iff Q _ z).mp hz
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hh
  have hhi : h = (⟨u, huN⟩ : normalizer (Q : Set G)) ^ i := Subtype.ext (by simp [hi])
  have hx' : Commute (toBar Q ⟨u, huN⟩) x := mem_centralizer_iff.mp hx _ (Set.mem_singleton _)
  rw [hhi, map_zpow]
  exact (hx'.zpow_left i).eq

theorem bar_inf_centralizer_singleton_le {Q Y : Subgroup G} (hOY : oddCoreIn Q ≤ Y)
    (hYO : Y ≤ normalizer (oddCoreIn Q : Set G)) {u : G} (huN : u ∈ normalizer (Q : Set G))
    {k : ℕ} (hu : u ^ 2 ^ k = 1) :
    bar Q Y ⊓ centralizer ({toBar Q ⟨u, huN⟩} : Set (Bar Q)) ≤
      bar Q (Y ⊓ centralizer ({u} : Set G)) := by
  refine (inf_le_inf_left _ (centralizer_singleton_le_centralizer_bar_zpowers Q huN)).trans
    ((bar_inf_centralizer_le hOY hYO (isPGroup_zpowers_of_pow_eq_one hu)
      ((zpowers_le).mpr huN)).trans (bar_mono Q (inf_le_inf_left _ ?_)))
  exact centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers u))

structure EndSetting (Q : Subgroup G) : Prop where
  main : MainSetting Q
  linked : linkedClass Q = {Q}
  even : ¬ OddNormalizerOverlaps Q

@[expose] def IsOverlapInv (Q : Subgroup G) (u : G) : Prop :=
  u ^ 2 = 1 ∧ u ≠ 1 ∧ u ∈ normalizer (Q : Set G) ∧
    ∃ g : G, g ∉ normalizer (Q : Set G) ∧ u ∈ rightConjugate Q g

namespace IsOverlapInv

variable {Q : Subgroup G} {u : G}

omit [Finite G] in
theorem mem_normalizer (hu : IsOverlapInv Q u) : u ∈ normalizer (Q : Set G) := hu.2.2.1

omit [Finite G] in
theorem orderOf_eq (hu : IsOverlapInv Q u) : orderOf u = 2 := orderOf_eq_prime hu.1 hu.2.1

omit [Finite G] in
theorem bar_sq (hu : IsOverlapInv Q u) : toBar Q ⟨u, hu.mem_normalizer⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have : (⟨u, hu.mem_normalizer⟩ : normalizer (Q : Set G)) ^ 2 = 1 :=
    Subtype.ext (by simpa using hu.1)
  rw [this, map_one]

end IsOverlapInv

instance bar_twoPrimeLayerIn_normal (Q : Subgroup G) : (bar Q (twoPrimeLayerIn Q)).Normal := by
  have h : ((twoPrimeLayerIn Q).subgroupOf (normalizer (Q : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer ((twoPrimeLayerIn_le Q).trans le_normalizer)).mpr
      (normalizer_le_normalizer_twoPrimeLayerIn Q)
  exact h.map _ (toBar_surjective Q)

omit [Finite G] in
theorem bar_self_normal (Q : Subgroup G) : (bar Q Q).Normal :=
  (normal_in_normalizer (H := Q)).map _ (toBar_surjective Q)

theorem mem_normalizer_bar_twoPrimeLayerIn (Q : Subgroup G) (x : Bar Q) :
    x ∈ normalizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) := by
  rw [normalizer_eq_top_iff.mpr (bar_twoPrimeLayerIn_normal Q)]
  exact mem_top x

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem exists_isOverlapInv : ∃ u : G, IsOverlapInv Q u := by
  obtain ⟨g, hg, heven⟩ : ∃ g : G, g ∉ normalizer (Q : Set G) ∧
      ¬ Odd (Nat.card (rightConjugate Q g ⊓ normalizer (Q : Set G) : Subgroup G)) := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hE.even h
  rw [Nat.not_odd_iff_even] at heven
  obtain ⟨⟨u, hu⟩, hu2⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(rightConjugate Q g ⊓ normalizer (Q : Set G))) 2 (even_iff_two_dvd.mp heven)
  rw [Subgroup.orderOf_mk] at hu2
  refine ⟨u, ?_, ?_, (mem_inf.mp hu).2, g, hg, (mem_inf.mp hu).1⟩
  · rw [← hu2]
    exact pow_orderOf_eq_one u
  · intro h
    rw [h, orderOf_one] at hu2
    norm_num at hu2

theorem isSimpleGroup_bar : IsSimpleGroup (bar Q (twoPrimeLayerIn Q)) :=
  hE.main.isSimpleGroup_bar hE.linked hE.even

theorem hasDihedralSylowTwo_bar : HasDihedralSylowTwo (bar Q (twoPrimeLayerIn Q)) :=
  hE.main.hasDihedralSylowTwo_bar hE.linked hE.even

theorem inf_centralizer_bar_eq_bot :
    bar Q Q ⊓ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) = ⊥ :=
  hE.main.inf_centralizer_bar_eq_bot hE.linked hE.even

theorem hasCyclicSylowTwo_of_isOverlapInv {u : G} (hu : IsOverlapInv Q u) :
    HasCyclicSylowTwo (bar Q (twoPrimeLayerIn Q) ⊓
      centralizer ({toBar Q ⟨u, hu.mem_normalizer⟩} : Set (Bar Q)) : Subgroup (Bar Q)) := by
  obtain ⟨g, hg, huQg⟩ := hu.2.2.2
  exact hE.main.hasCyclicSylowTwo_inf_centralizer hE.linked hE.even hg huQg hu.mem_normalizer
    hu.1 hu.2.1

theorem not_hasFourGroup_bar_inf_centralizer {u : G} (hu : IsOverlapInv Q u) :
    ¬ HasFourGroup (bar Q Q ⊓ centralizer ({toBar Q ⟨u, hu.mem_normalizer⟩} : Set (Bar Q))) := by
  obtain ⟨g, hg, huQg⟩ := hu.2.2.2
  intro h4
  have hlift := bar_inf_centralizer_singleton_le (Y := Q) (oddCoreIn_le Q)
    (normalIn_le_normalizer (oddCoreIn_normalIn Q)) hu.mem_normalizer (k := 1)
    (by simpa using hu.1)
  have h4' := HasFourGroup.of_bar_of_le (inf_le_left.trans le_normalizer) (h4.mono hlift)
  have hCN := centralizer_le_of_involution (rightConjugate_tightlyEmbedded Q hE.main.tight g)
    huQg hu.orderOf_eq
  exact hE.main.not_hasFourGroup_inf_normalizer hE.linked hg (h4'.mono (inf_le_inf_left Q hCN))

theorem centralizer_le_centralizer_bar :
    centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) ≤ centralizer (bar Q Q : Set (Bar Q)) := by
  have hQn := bar_self_normal Q
  have hLn := bar_twoPrimeLayerIn_normal Q
  have hCn : (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q))).Normal := by
    have := hLn
    infer_instance
  intro c hc
  rw [mem_centralizer_iff]
  intro x hx
  have h1 : x * c * x⁻¹ * c⁻¹ ∈ bar Q Q := by
    rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by group]
    exact mul_mem hx (hQn.conj_mem _ (inv_mem hx) c)
  have h2 : x * c * x⁻¹ * c⁻¹ ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) :=
    mul_mem (hCn.conj_mem _ hc x) (inv_mem hc)
  have h3 : x * c * x⁻¹ * c⁻¹ ∈ (⊥ : Subgroup (Bar Q)) := by
    rw [← hE.inf_centralizer_bar_eq_bot]
    exact mem_inf.mpr ⟨h1, h2⟩
  rw [mem_bot] at h3
  calc x * c = x * c * x⁻¹ * c⁻¹ * (c * x) := by group
    _ = c * x := by rw [h3, one_mul]

theorem hasFourGroup_bar_inf_centralizer_of_sq {y : Bar Q} (hyQ : y ∈ bar Q Q) (hy : y ^ 2 = 1) :
    HasFourGroup (bar Q Q ⊓ centralizer ({y} : Set (Bar Q))) := by
  obtain ⟨R, hR, hRd⟩ := hE.main.exists_isDihedral_sylow hE.linked hE.even
  obtain ⟨u, w, huQ, hwQ, hu, hw, hu1, hw1, huw, hc, huy, hwy⟩ :=
    exists_commuting_pair_of_isSylowOf hR hRd hyQ hy
  have hmem : ∀ v : Bar Q, v ∈ bar Q Q → v * y = y * v →
      v ∈ bar Q Q ⊓ centralizer ({y} : Set (Bar Q)) := fun v hv hvy => by
    refine mem_inf.mpr ⟨hv, mem_centralizer_iff.mpr fun z hz => ?_⟩
    rw [Set.mem_singleton_iff.mp hz]
    exact hvy.symm
  exact hasFourGroup_of_commute (hmem u huQ huy) (hmem w hwQ hwy) hu hw hu1 hw1 huw hc

theorem not_mem_bar_sup_centralizer {u : G} (hu : IsOverlapInv Q u) :
    toBar Q ⟨u, hu.mem_normalizer⟩ ∉
      bar Q Q ⊔ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) := by
  intro h
  have hCC := hE.centralizer_le_centralizer_bar
  have hCN : centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) ≤
      normalizer (bar Q Q : Set (Bar Q)) := hCC.trans (centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hCN] at h
  obtain ⟨y, hy, c, hc, hyc⟩ := Set.mem_mul.mp h
  have hcy : y * c = c * y := mem_centralizer_iff.mp (hCC hc) y hy
  have hy2 : y ^ 2 = 1 := by
    have h1 : (y * c) ^ 2 = 1 := by rw [hyc]; exact hu.bar_sq
    rw [(show Commute y c from hcy).mul_pow] at h1
    have h3 : y ^ 2 ∈ bar Q Q ⊓ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) := by
      refine mem_inf.mpr ⟨pow_mem hy 2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (pow_mem hc 2)
    rw [hE.inf_centralizer_bar_eq_bot, mem_bot] at h3
    exact h3
  apply hE.not_hasFourGroup_bar_inf_centralizer hu
  refine (hE.hasFourGroup_bar_inf_centralizer_of_sq hy hy2).mono fun x hx => ?_
  obtain ⟨hxQ, hxy⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨hxQ, mem_centralizer_iff.mpr fun z hz => ?_⟩
  rw [Set.mem_singleton_iff.mp hz, ← hyc]
  have h1 : y * x = x * y := mem_centralizer_iff.mp hxy y (Set.mem_singleton y)
  have h2 : c * x = x * c := (mem_centralizer_iff.mp (hCC hc) x hxQ).symm
  calc y * c * x = y * (c * x) := by group
    _ = y * (x * c) := by rw [h2]
    _ = (y * x) * c := by group
    _ = x * (y * c) := by rw [h1]; group

theorem not_mem_layer_sup_centralizer {u : G} (hu : IsOverlapInv Q u) :
    toBar Q ⟨u, hu.mem_normalizer⟩ ∉
      bar Q (twoPrimeLayerIn Q) ⊔ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) :=
  fun h => hE.not_mem_bar_sup_centralizer hu
    (sup_le_sup_right (bar_mono Q (twoPrimeLayerIn_le Q)) _ h)

theorem mul_mem_layer_sup_centralizer
    {u : G} (hu : IsOverlapInv Q u) {b : Bar Q} (hb : b ^ 2 = 1)
    (hcb : HasCyclicSylowTwo (bar Q (twoPrimeLayerIn Q) ⊓
      centralizer ({b} : Set (Bar Q)) : Subgroup (Bar Q))) :
    toBar Q ⟨u, hu.mem_normalizer⟩ * b ∈
      bar Q (twoPrimeLayerIn Q) ⊔ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) :=
  (AschbacherKnownGroup.FactsL2.dihedral_outer_involution_holds (Bar Q)
    (bar Q (twoPrimeLayerIn Q)) _ hE.isSimpleGroup_bar hE.hasDihedralSylowTwo_bar
    (mem_normalizer_bar_twoPrimeLayerIn Q _) hu.bar_sq
    (hE.hasCyclicSylowTwo_of_isOverlapInv hu)).2.2.2 b (mem_normalizer_bar_twoPrimeLayerIn Q b)
    hb hcb

theorem mem_layer_of_sq
    {x : Bar Q} (hxQ : x ∈ bar Q Q) (hx : x ^ 2 = 1) :
    x ∈ bar Q (twoPrimeLayerIn Q) := by
  by_contra hxL
  obtain ⟨R, hR, hRd⟩ := hE.main.exists_isDihedral_sylow hE.linked hE.even
  have hLQ : bar Q (twoPrimeLayerIn Q) ≤ bar Q Q := bar_mono Q (twoPrimeLayerIn_le Q)
  obtain ⟨u, hu⟩ := hE.exists_isOverlapInv
  have hcyc : HasCyclicSylowTwo (bar Q (twoPrimeLayerIn Q) ⊓
      centralizer ({x} : Set (Bar Q)) : Subgroup (Bar Q)) := by
    by_contra hnc
    obtain ⟨V, hV, hVe, hV4⟩ :=
      hasFourGroup_of_not_hasCyclicSylowTwo hR hRd (inf_le_left.trans hLQ) hnc
    have hxV : x ∈ centralizer (V : Set (Bar Q)) := mem_centralizer_iff.mpr fun v hv =>
      (mem_centralizer_iff.mp (mem_inf.mp (hV hv)).2 x (Set.mem_singleton x)).symm
    exact hxL ((mem_inf.mp (hV (mem_of_mem_centralizer_fourGroup hR hRd
      ((hV.trans inf_le_left).trans hLQ) hVe hV4 hxQ hx hxV))).1)
  have h := hE.mul_mem_layer_sup_centralizer hu hx hcyc
  apply hE.not_mem_bar_sup_centralizer hu
  have : toBar Q ⟨u, hu.mem_normalizer⟩ = (toBar Q ⟨u, hu.mem_normalizer⟩ * x) * x⁻¹ := by group
  rw [this]
  exact mul_mem (sup_le_sup_right hLQ _ h) (mem_sup_left (inv_mem hxQ))

theorem mem_layer_of_isPGroup
    {x : Bar Q} (hxQ : x ∈ bar Q Q) (hx : IsPGroup 2 (zpowers x)) :
    x ∈ bar Q (twoPrimeLayerIn Q) := by
  obtain ⟨R, hR, hRd⟩ := hE.main.exists_isDihedral_sylow hE.linked hE.even
  exact mem_of_forall_sq_mem hR hRd (fun y hyQ hy => hE.mem_layer_of_sq hyQ hy) hxQ hx

theorem le_layer_of_isPGroup
    {P : Subgroup (Bar Q)} (hPQ : P ≤ bar Q Q) (hP : IsPGroup 2 P) :
    P ≤ bar Q (twoPrimeLayerIn Q) := fun _ hx =>
  hE.mem_layer_of_isPGroup (hPQ hx) (hP.to_le ((zpowers_le).mpr hx))

end EndSetting

end CFSG.ComponentClassification.Asc75T4
