module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoM11Aut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoM11Local
public import CFSG.GH74.E2.BlackBoxesStdM11
public import CFSG.LocalAnalysis.ComponentClassification.AS76bBasic
public import Certificates.Certificate110
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.GH74.SectionalRank
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.ComponentClassification.RankTwoM11

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

section Klein

@[expose] def kleinOf (u v : G) (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) :
    Subgroup G where
  carrier := {1, u, v, u * v}
  mul_mem' := by
    have h1 : ∀ x, u * (u * x) = x := fun x => by rw [← mul_assoc, hu, one_mul]
    have h3 : ∀ x, v * (u * x) = u * (v * x) := fun x => by rw [← mul_assoc, ← huv, mul_assoc]
    have h4 : v * u = u * v := huv.symm
    rintro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, hu, hv, h1, h3, h4]
  one_mem' := by simp
  inv_mem' := by
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
    rintro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, hu', hv', huv.symm]

variable {u v : G} {hu : u * u = 1} {hv : v * v = 1} {huv : u * v = v * u}

theorem mem_kleinOf {x : G} :
    x ∈ kleinOf u v hu hv huv ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v :=
  Iff.rfl

theorem kleinOf_mul_self {x : G} (hx : x ∈ kleinOf u v hu hv huv) : x * x = 1 := by
  have h3 : ∀ y, v * (u * y) = u * (v * y) := fun y => by rw [← mul_assoc, ← huv, mul_assoc]
  rcases mem_kleinOf.mp hx with rfl | rfl | rfl | rfl <;> simp [mul_assoc, hu, hv, h3]

theorem kleinOf_comm {x y : G} (hx : x ∈ kleinOf u v hu hv huv) (hy : y ∈ kleinOf u v hu hv huv) :
    x * y = y * x := by
  have h1 : ∀ z, u * (u * z) = z := fun z => by rw [← mul_assoc, hu, one_mul]
  have h3 : ∀ z, v * (u * z) = u * (v * z) := fun z => by rw [← mul_assoc, ← huv, mul_assoc]
  rcases mem_kleinOf.mp hx with rfl | rfl | rfl | rfl <;>
    rcases mem_kleinOf.mp hy with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, hu, hv, h1, h3, huv.symm]

theorem isElementaryAbelian_kleinOf : IsElementaryAbelian 2 (kleinOf u v hu hv huv) where
  is_comm := ⟨fun x y => Subtype.ext (kleinOf_comm x.2 y.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [pow_two]; exact kleinOf_mul_self x.2)

theorem isPGroup_kleinOf : IsPGroup 2 (kleinOf u v hu hv huv) := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact kleinOf_mul_self x.2)⟩

theorem card_kleinOf (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) :
    Nat.card (kleinOf u v hu hv huv) = 4 := by
  classical
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have huv1 : u * v ≠ 1 := fun h => hne (by rw [eq_inv_of_mul_eq_one_left h, hv'])
  have huvu : u * v ≠ u := fun h => hv1 (by simpa using h)
  have huvv : u * v ≠ v := fun h => hu1 (by simpa using h)
  have hcard : Nat.card (kleinOf u v hu hv huv) = ({1, u, v, u * v} : Finset G).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [mem_kleinOf])
  rw [hcard, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_pair_eq_two_iff.mpr huvv.symm]
  · simp [hne, huvu.symm]
  · simp [hu1.symm, hv1.symm, huv1.symm]

end Klein

theorem not_odd_card_of_orderOf_eq_two [Finite G] {H : Subgroup G} {x : G} (hx : x ∈ H)
    (h2 : orderOf x = 2) : ¬ Odd (Nat.card H) := by
  intro hodd
  have hdvd : orderOf x ∣ Nat.card H := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  rw [h2] at hdvd
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)

theorem mul_self_eq_one_of_orderOf_eq_two {x : G} (h2 : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← h2, pow_orderOf_eq_one]

theorem ne_one_of_orderOf_eq_two {x : G} (h2 : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h2
  omega

theorem one_lt_pRank_of_commute [Finite G] {H : Subgroup G} {u v : G} (huH : u ∈ H)
    (hvH : v ∈ H) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) (hne : u ≠ v)
    (hc : u * v = v * u) : 1 < CFSG.pRank 2 H := by
  have hu' : (⟨u, huH⟩ : H) * ⟨u, huH⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hu2)
  have hv' : (⟨v, hvH⟩ : H) * ⟨v, hvH⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hv2)
  have hc' : (⟨u, huH⟩ : H) * ⟨v, hvH⟩ = ⟨v, hvH⟩ * ⟨u, huH⟩ := Subtype.ext hc
  have hmem : 2 ∈ {r | ∃ E : Subgroup H, IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ r} :=
    ⟨kleinOf _ _ hu' hv' hc', isElementaryAbelian_kleinOf,
      (card_kleinOf (fun h => ne_one_of_orderOf_eq_two hu2 (congrArg Subtype.val h))
        (fun h => ne_one_of_orderOf_eq_two hv2 (congrArg Subtype.val h))
        (fun h => hne (congrArg Subtype.val h))).trans (by norm_num)⟩
  have hbdd : BddAbove {r | ∃ E : Subgroup H, IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ r} := by
    refine ⟨Nat.card H, fun r hr => ?_⟩
    obtain ⟨E, -, hE⟩ := hr
    calc r ≤ 2 ^ r := Nat.lt_two_pow_self.le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card H := Subgroup.card_le_card_group E
  have := le_csSup hbdd hmem
  unfold CFSG.pRank
  omega

theorem standardComponentIsStandard_of_isStandardSubgroup {L : Subgroup G}
    (h : IsStandardSubgroup L) : standardComponentIsStandard L :=
  CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 h

theorem standardComponentOddCore_eq_bot [Finite G] (hsimple : IsSimpleGroup G)
    (heven : Even (Nat.card G)) : standardComponentOddCore G = ⊥ := by
  refine sSup_eq_bot.mpr fun N hN => ?_
  have := hN.1
  rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · have hodd := hN.2
    rw [h, Subgroup.card_top] at hodd
    exact absurd heven (Nat.not_even_iff_odd.mpr hodd)

theorem mem_normalizer_of_commute [Finite G] {L : Subgroup G} (h : IsStandardSubgroup L)
    {u : G} (hu : u ∈ centralizer (L : Set G)) (hu2 : orderOf u = 2) {x : G}
    (hx : x * u = u * x) : x ∈ normalizer (centralizer (L : Set G) : Set G) :=
  h.standardComponentIsStandard.mem_normalizer_centralizer_of_commute hu hu2 hx

theorem mem_map_conj_iff {A : Subgroup G} {g x : G} :
    x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem centralizer_map_conj_le (A : Subgroup G) (g : G) :
    centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      (centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom := by
  intro x hx
  rw [mem_map_conj_iff, mem_centralizer_iff]
  intro a ha
  have h := mem_centralizer_iff.mp hx (g * a * g⁻¹) (mem_map_conj_iff.mpr (by group; exact ha))
  calc a * (g⁻¹ * x * g) = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
    _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [h]
    _ = g⁻¹ * x * g * a := by group

theorem conj_mem_normalizer_map {A : Subgroup G} {n : G} (hn : n ∈ normalizer (A : Set G))
    (g : G) :
    g * n * g⁻¹ ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_map_conj_iff, mem_map_conj_iff, (mem_normalizer_iff.mp hn) (g⁻¹ * x * g)]
  constructor <;> intro h <;> convert h using 1 <;> group

theorem pow_two_eq_one_of_lemma32 [Finite G] {K : Subgroup G}
    (hR : ∀ R : Subgroup G, IsSylowOf 2 R K → IsElemAbelian 2 R) {w : G} (hw : w ∈ K)
    (h4 : w ^ 4 = 1) : w ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers (⟨w, hw⟩ : K)) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨2, Subtype.ext ?_⟩
    have h4' : (⟨w, hw⟩ : K) ^ 4 = 1 := Subtype.ext h4
    change ((⟨w, hw⟩ : K) ^ n) ^ 4 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h4', one_zpow]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hsyl : IsSylowOf 2 ((P : Subgroup K).map K.subtype) K := ⟨P, rfl⟩
  exact (hR _ hsyl).2 w ⟨⟨w, hw⟩, hP (mem_zpowers _), rfl⟩

theorem exists_conj_mem_of_isSylowOf [Finite G] {X T : Subgroup G} (hT : IsSylowOf 2 T X)
    {u v : G} (hu : u ∈ X) (hv : v ∈ X) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (huv : u * v = v * u) : ∃ x ∈ X, x * u * x⁻¹ ∈ T ∧ x * v * x⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hT
  let V : Subgroup X := kleinOf (⟨u, hu⟩ : X) ⟨v, hv⟩ (Subtype.ext hu2) (Subtype.ext hv2)
    (Subtype.ext huv)
  obtain ⟨P, hP⟩ := (isPGroup_kleinOf : IsPGroup 2 V).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P Q
  have hmem : ∀ w : X, w ∈ V → x * w * x⁻¹ ∈ (Q : Subgroup X) := by
    intro w hw
    rw [← hx, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul w (MulAut.conj x) _ (hP hw)
  refine ⟨x, x.2, ⟨_, hmem ⟨u, hu⟩ (mem_kleinOf.mpr (Or.inr (Or.inl rfl))), rfl⟩,
    ⟨_, hmem ⟨v, hv⟩ (mem_kleinOf.mpr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩⟩

theorem orderOf_mul_eq_two {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hne : x ≠ y) : orderOf (x * y) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
      _ = x * (x * y) * y := by rw [hxy]
      _ = x * x * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  · intro h
    apply hne
    calc x = x * (y * y) := by rw [hy, mul_one]
      _ = x * y * y := by group
      _ = y := by rw [h, one_mul]

theorem false_of_orderFour [Finite G] {K B : Subgroup G}
    (hB : ∀ n ∈ normalizer (B : Set G), ∃ y ∈ B, y⁻¹ * n ∈ centralizer (B : Set G))
    (hZ : ∀ z ∈ B, z ∈ centralizer (B : Set G) → z = 1)
    (hloc : ∀ t ∈ B, ∀ s ∈ B, t * t = 1 → t ≠ 1 → s * s = 1 → s ≠ 1 → t ≠ s → t * s = s * t →
      ∃ c ∈ B, c * t = t * c ∧ (s * (c * s * c⁻¹)) ^ 2 ≠ 1 ∧ (s * (c * s * c⁻¹)) ^ 4 = 1)
    (hodd : Odd (Nat.card ↥(K ⊓ centralizer (B : Set G))))
    (htight : ∀ u ∈ K, orderOf u = 2 → ∀ x : G, x * u = u * x → x ∈ normalizer (K : Set G))
    (hexp : ∀ w ∈ K, w ^ 4 = 1 → w ^ 2 = 1)
    {u v : G} (hu : u ∈ K) (hv : v ∈ K) (huN : u ∈ normalizer (B : Set G))
    (hvN : v ∈ normalizer (B : Set G)) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) (hne : u ≠ v)
    (hc : u * v = v * u) : False := by
  have hnot : ∀ x ∈ K, x ∈ centralizer (B : Set G) → orderOf x ≠ 2 := fun x hxK hxC hx2 =>
    not_odd_card_of_orderOf_eq_two (H := K ⊓ centralizer (B : Set G)) ⟨hxK, hxC⟩ hx2 hodd
  have hsplit : ∀ {y m : G}, y ∈ B → m ∈ centralizer (B : Set G) → y * m * (y * m) = 1 →
      y * y = 1 ∧ m * m = 1 := by
    intro y m hy hm h
    have hym : y * m = m * y := mem_centralizer_iff.mp hm y hy
    have hyy : y * y = (m * m)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc y * y * (m * m) = y * (y * m) * m := by group
        _ = y * (m * y) * m := by rw [hym]
        _ = y * m * (y * m) := by group
        _ = 1 := h
    have h1 : y * y = 1 := hZ _ (B.mul_mem hy hy) (by rw [hyy]; exact inv_mem (mul_mem hm hm))
    refine ⟨h1, ?_⟩
    rw [h1, eq_comm, inv_eq_one] at hyy
    exact hyy
  obtain ⟨a, ha, hka⟩ := hB u huN
  obtain ⟨b, hb, hkb⟩ := hB v hvN
  obtain ⟨k, rfl⟩ : ∃ k, u = a * k := ⟨a⁻¹ * u, by group⟩
  obtain ⟨l, rfl⟩ : ∃ l, v = b * l := ⟨b⁻¹ * v, by group⟩
  rw [inv_mul_cancel_left] at hka hkb
  have hkc : ∀ x ∈ B, x * k = k * x := fun x hx => mem_centralizer_iff.mp hka x hx
  have hlc : ∀ x ∈ B, x * l = l * x := fun x hx => mem_centralizer_iff.mp hkb x hx
  have hu1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have hv1 := mul_self_eq_one_of_orderOf_eq_two hv2
  obtain ⟨ha2, hk2⟩ := hsplit ha hka hu1
  obtain ⟨hb2, hl2⟩ := hsplit hb hkb hv1
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hnot _ hu (by rw [one_mul]; exact hka) hu2
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hnot _ hv (by rw [one_mul]; exact hkb) hv2
  have hab : a * b = b * a := by
    have h1 : a * b * (k * l) = b * a * (l * k) := by
      calc a * b * (k * l) = a * (b * k) * l := by group
        _ = a * (k * b) * l := by rw [hkc b hb]
        _ = a * k * (b * l) := by group
        _ = b * l * (a * k) := hc
        _ = b * (l * a) * k := by group
        _ = b * (a * l) * k := by rw [hlc a ha]
        _ = b * a * (l * k) := by group
    have hz : (b * a)⁻¹ * (a * b) = l * k * (k * l)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul]
      calc a * b = a * b * (k * l) * (k * l)⁻¹ := by group
        _ = b * a * (l * k) * (k * l)⁻¹ := by rw [h1]
        _ = b * a * (l * k * (k * l)⁻¹) := by group
    have hzC : (b * a)⁻¹ * (a * b) ∈ centralizer (B : Set G) := by
      rw [hz]
      exact mul_mem (mul_mem hkb hka) (inv_mem (mul_mem hka hkb))
    have h' := hZ _ (B.mul_mem (B.inv_mem (B.mul_mem hb ha)) (B.mul_mem ha hb)) hzC
    rw [inv_mul_eq_one] at h'
    exact h'.symm
  have hab' : a ≠ b := by
    rintro rfl
    have hkl : a * k * (a * l) = k * l := by
      calc a * k * (a * l) = a * (k * a) * l := by group
        _ = a * (a * k) * l := by rw [hkc a ha]
        _ = a * a * (k * l) := by group
        _ = k * l := by rw [ha2, one_mul]
    exact hnot _ (K.mul_mem hu hv) (by rw [hkl]; exact mul_mem hka hkb)
      (orderOf_mul_eq_two hu1 hv1 hc hne)
  obtain ⟨c, hcB, hca, h2, h4⟩ := hloc a ha b hb ha2 ha1 hb2 hb1 hab' hab
  have hcu : c * (a * k) = a * k * c := by
    calc c * (a * k) = c * a * k := by group
      _ = a * c * k := by rw [hca]
      _ = a * (c * k) := by group
      _ = a * (k * c) := by rw [hkc c hcB]
      _ = a * k * c := by group
  have hcv : c * (b * l) * c⁻¹ ∈ K := (mem_normalizer_iff.mp (htight _ hu hu2 c hcu) _).mp hv
  have hlc' : c * l * c⁻¹ = l := by rw [hlc c hcB, mul_inv_cancel_right]
  have hcbc : c * b * c⁻¹ ∈ B := B.mul_mem (B.mul_mem hcB hb) (B.inv_mem hcB)
  have hw : b * l * (c * (b * l) * c⁻¹) = b * (c * b * c⁻¹) := by
    calc b * l * (c * (b * l) * c⁻¹) = b * l * (c * b * c⁻¹ * (c * l * c⁻¹)) := by group
      _ = b * (l * (c * b * c⁻¹)) * l := by rw [hlc']; group
      _ = b * (c * b * c⁻¹ * l) * l := by rw [hlc _ hcbc]
      _ = b * (c * b * c⁻¹) * (l * l) := by group
      _ = b * (c * b * c⁻¹) := by rw [hl2, mul_one]
  have h22 := hexp _ (K.mul_mem hv hcv) (by rw [hw]; exact h4)
  rw [hw] at h22
  exact h2 h22

theorem hyp31_of_m11 {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {A : Subgroup G} (hstd : IsStandardSubgroup A)
    (e : ↥A ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) {u v : G} (hu2 : orderOf u = 2)
    (hv2 : orderOf v = 2) (hne : u ≠ v) (hc : u * v = v * u)
    (hu : u ∈ centralizer (A : Set G)) (hv : v ∈ centralizer (A : Set G)) : AS76b.Hyp31 A := by
  have heven : Even (Nat.card G) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hstd.2.1).trans (Subgroup.card_subgroup_dvd_card _))
  refine ⟨standardComponentIsStandard_of_isStandardSubgroup hstd, hypII_of_equiv e,
    standardComponentOddCore_eq_bot hsimple heven,
    by rw [← AS76b.pRank_type_eq_open]; exact one_lt_pRank_of_commute hu hv hu2 hv2 hne hc,
    fun hN => ?_⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal A with h | h
  · apply hstd.2.2.2.2 1
    rw [h, Subgroup.commutator_bot_left]
  · have hcenter : Subgroup.center G = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
      · exact h'
      · obtain ⟨x, y, hxy⟩ := hnonab
        exact absurd (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top y) x) hxy
    have huc : u ∈ Subgroup.center G := by
      rw [h, Subgroup.coe_top, Subgroup.centralizer_univ] at hu
      exact hu
    rw [hcenter, Subgroup.mem_bot] at huc
    exact ne_one_of_orderOf_eq_two hu2 huc

theorem aschbacherStandardM11_of (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    CFSG.GH74.E2.AschbacherStandardM11 := by
  intro G _ _ hsimple hnonab _ A hstd ⟨e⟩ ⟨u, v, hu2, hv2, hne, hc, hu, hv⟩
  have hyp := hyp31_of_m11 hsimple hnonab hstd e hu2 hv2 hne hc hu hv
  obtain ⟨g, hg, T, hT1, hT2⟩ := h33 G A hyp
  have hR := h32 G A hyp
  have htight : ∀ w ∈ centralizer (A : Set G), orderOf w = 2 → ∀ z : G, z * w = w * z →
      z ∈ normalizer (centralizer (A : Set G) : Set G) :=
    fun w hw hw2 z hz => mem_normalizer_of_commute hstd hw hw2 hz
  have hodd : Odd (Nat.card ↥(centralizer (A : Set G) ⊓
      (centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom)) := by
    have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := fun h =>
      hg (hstd.2.2.2.1 ▸ h)
    exact hstd.standardComponentIsStandard.2.2.1 g hgK
  have hCB := centralizer_map_conj_le A g
  have hNB : ∀ n ∈ normalizer (A : Set G), g * n * g⁻¹ ∈
      normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    fun n hn => conj_mem_normalizer_map hn g
  have eB : ↥(A.map (MulAut.conj g).toMonoidHom) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier .M11 :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, centralizer (A : Set G) = K := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, A.map (MulAut.conj g).toMonoidHom = B := ⟨_, rfl⟩
  rw [hK] at hu hv htight hodd hT1 hT2 hR hCB
  rw [hB] at hCB hNB eB
  have hexp : ∀ w ∈ K, w ^ 4 = 1 → w ^ 2 = 1 := fun w hw h4 =>
    pow_two_eq_one_of_lemma32 hR hw h4
  have hodd' : Odd (Nat.card ↥(K ⊓ centralizer (B : Set G))) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_inf_left _ hCB))
  have hu1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have hv1 := mul_self_eq_one_of_orderOf_eq_two hv2
  have hu' : g⁻¹ * u * g ∈ rightConjugate K g := by
    rw [mem_rightConjugate_iff, show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
    exact hu
  have hv' : g⁻¹ * v * g ∈ rightConjugate K g := by
    rw [mem_rightConjugate_iff, show g * (g⁻¹ * v * g) * g⁻¹ = v by group]
    exact hv
  obtain ⟨x, hx, hxu, hxv⟩ := exists_conj_mem_of_isSylowOf hT2 hu' hv'
    (by rw [show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu1]; group)
    (by rw [show g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g by group, hv1]; group)
    (by rw [show g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g by group, hc,
      show g⁻¹ * (v * u) * g = g⁻¹ * v * g * (g⁻¹ * u * g) by group])
  have hyK : g * x * g⁻¹ ∈ K := (mem_rightConjugate_iff K g x).mp hx
  have hconj : ∀ w : G, g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ =
      g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ := fun w => by group
  have hmemK : ∀ w ∈ K, g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ ∈ K := fun w hw =>
    K.mul_mem (K.mul_mem hyK hw) (K.inv_mem hyK)
  have hmemN : ∀ w : G, x * (g⁻¹ * w * g) * x⁻¹ ∈ T →
      g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ ∈ normalizer (B : Set G) := fun w hw => by
    rw [← hconj]
    exact hNB _ (hT1.le hw).2
  have hord : ∀ w : G, orderOf (g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹) = orderOf w := fun w =>
    MulEquiv.orderOf_eq (MulAut.conj (g * x * g⁻¹)) w
  have hBN : ∀ n ∈ normalizer (B : Set G), ∃ z ∈ B, z⁻¹ * n ∈ centralizer (B : Set G) :=
    fun n hn => exists_inv_mul_mem_centralizer ⟨eB⟩ hn
  have hZ : ∀ z ∈ B, z ∈ centralizer (B : Set G) → z = 1 := by
    intro z hzB hzC
    have h := eq_one_of_forall_commute_of_equiv eB (z := ⟨z, hzB⟩)
      (fun w => Subtype.ext (mem_centralizer_iff.mp hzC w w.2).symm)
    exact congrArg Subtype.val h
  have hloc : ∀ t ∈ B, ∀ s ∈ B, t * t = 1 → t ≠ 1 → s * s = 1 → s ≠ 1 → t ≠ s →
      t * s = s * t →
      ∃ c ∈ B, c * t = t * c ∧ (s * (c * s * c⁻¹)) ^ 2 ≠ 1 ∧ (s * (c * s * c⁻¹)) ^ 4 = 1 := by
    intro t ht s hs ht2 ht1 hs2 hs1 hts hcomm
    obtain ⟨c, hct, h2, h4⟩ := exists_orderFour_of_equiv eB (t := ⟨t, ht⟩) (s := ⟨s, hs⟩)
      (Subtype.ext ht2) (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext hs2)
      (fun h => hs1 (congrArg Subtype.val h)) (fun h => hts (congrArg Subtype.val h))
      (Subtype.ext hcomm)
    refine ⟨c, c.2, congrArg Subtype.val hct, fun h => h2 (Subtype.ext ?_), ?_⟩
    · simpa using h
    · simpa using congrArg Subtype.val h4
  refine false_of_orderFour hBN hZ hloc hodd' htight hexp (hmemK u hu) (hmemK v hv)
    (hmemN u hxu) (hmemN v hxv) ((hord u).trans hu2) ((hord v).trans hv2) ?_ ?_
  · intro h
    apply hne
    have h' := congrArg (fun w => (g * x * g⁻¹)⁻¹ * w * (g * x * g⁻¹)) h
    simpa [mul_assoc] using h'
  · calc g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ * (g * x * g⁻¹ * v * (g * x * g⁻¹)⁻¹) =
          g * x * g⁻¹ * (u * v) * (g * x * g⁻¹)⁻¹ := by group
      _ = g * x * g⁻¹ * (v * u) * (g * x * g⁻¹)⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * v * (g * x * g⁻¹)⁻¹ * (g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹) := by group

end CFSG.ComponentClassification.RankTwoM11
