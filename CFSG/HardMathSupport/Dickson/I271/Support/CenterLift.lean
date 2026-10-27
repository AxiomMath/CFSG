module

public import CFSG.HardMathSupport.Dickson.I271.Support.Action
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

section Norm

variable {X : Type*} [Group X]

theorem iterate_conj {Z : Type*} [Group Z] (ι : Z →* X) (φ : Z →* Z) (b : X)
    (hφ : ∀ z, ι (φ z) = b * ι z * b⁻¹) (z : Z) (n : ℕ) :
    ι (φ^[n] z) = b ^ n * ι z * (b ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hφ, ih, pow_succ', mul_inv_rev]
    group

theorem mul_pow_eq_prod {Z : Type*} [CommGroup Z] (ι : Z →* X) (φ : Z →* Z) (b : X)
    (hφ : ∀ z, ι (φ z) = b * ι z * b⁻¹) (z : Z) (n : ℕ) :
    (ι z * b) ^ n = ι (∏ i ∈ Finset.range n, φ^[i] z) * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Finset.prod_range_succ, map_mul, iterate_conj ι φ b hφ, pow_succ]
    group

theorem pow_eq_one_of_norm_eq_one {Z : Type*} [CommGroup Z] {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime)
    (φ : Z →* Z) (hfix : ∀ y : Z, y ^ p = 1 → φ y = y)
    (hpow : ∀ z : Z, ∃ n, z ^ (p ^ n) = 1) (w : Z)
    (hN : ∏ i ∈ Finset.range p, φ^[i] w = 1) : w ^ p = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := hp.eq_two_or_odd'.resolve_left hp2 |>.exists_bit1
  have key : ∀ n : ℕ, ∀ w : Z, w ^ (p ^ n) = 1 → ∏ i ∈ Finset.range p, φ^[i] w = 1 →
      w ^ p = 1 := by
    intro n
    induction n with
    | zero =>
      intro w hw _
      rw [pow_zero, pow_one] at hw
      rw [hw, one_pow]
    | succ n ih =>
      cases n with
      | zero =>
        intro w hw _
        simpa using hw
      | succ n =>
        intro w hw hN
        have h1 : (w ^ p) ^ (p ^ (n + 1)) = 1 := by
          rw [← pow_mul, ← pow_succ']
          exact hw
        have h2 : ∏ i ∈ Finset.range p, φ^[i] (w ^ p) = 1 := by
          have : ∏ i ∈ Finset.range p, φ^[i] (w ^ p) = (∏ i ∈ Finset.range p, φ^[i] w) ^ p := by
            rw [← Finset.prod_pow]
            exact Finset.prod_congr rfl fun i _ => iterate_map_pow φ i w p
          rw [this, hN, one_pow]
        have h3 : (w ^ p) ^ p = 1 := ih (w ^ p) h1 h2
        have hy : φ (w ^ p) = w ^ p := hfix _ h3
        set x : Z := φ w * w⁻¹ with hx
        have hxp : x ^ p = 1 := by
          rw [hx, mul_pow, inv_pow, ← map_pow, hy, mul_inv_cancel]
        have hxf : φ x = x := hfix x hxp
        have hit : ∀ i : ℕ, φ^[i] w = w * x ^ i := by
          intro i
          induction i with
          | zero => simp
          | succ i ihi =>
            rw [Function.iterate_succ_apply', ihi, map_mul, map_pow, hxf, pow_succ']
            have : φ w = x * w := by rw [hx]; group
            rw [this]
            ac_rfl
        have hprod : ∏ i ∈ Finset.range p, φ^[i] w = w ^ p * x ^ (p * m) := by
          rw [Finset.prod_congr rfl fun i _ => hit i, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_range, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
          congr 2
          rw [hm]
          have : (2 * m + 1) * (2 * m + 1 - 1) / 2 = (2 * m + 1) * m := by
            rw [Nat.add_sub_cancel, show (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) by ring,
              Nat.mul_div_cancel_left _ (by norm_num)]
          rw [this]
        rw [hprod, pow_mul, hxp, one_pow, mul_one] at hN
        exact hN
  obtain ⟨n, hn⟩ := hpow w
  exact key n w hn hN

theorem fix_of_pow_eq_one {Z : Type*} [Group Z] {p : ℕ} (hp : p.Prime) (φ : Z →* Z)
    (hφ : ∀ z, φ^[p] z = z)
    (hΩ : ∀ y y' : Z, y ≠ 1 → y ^ p = 1 → y' ^ p = 1 → y' ∈ Subgroup.zpowers y)
    (y : Z) (hy : y ^ p = 1) : φ y = y := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hy1 : y = 1
  · rw [hy1, map_one]
  have hφy : (φ y) ^ p = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hΩ y (φ y) hy1 hy hφy)
  have hit : ∀ m : ℕ, φ^[m] y = y ^ (j ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [Function.iterate_succ_apply', ihm, map_zpow, ← hj, ← zpow_mul, pow_succ']
  have h1 : y ^ (j ^ p) = y := by rw [← hit p, hφ]
  have hord : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy
  have h2 : y ^ (j ^ p) = y ^ j := by
    rw [zpow_eq_zpow_iff_modEq]
    have hfermat : j ^ p ≡ j [ZMOD p] :=
      (ZMod.intCast_eq_intCast_iff (j ^ p) j p).1 (by push_cast; exact ZMod.pow_card _)
    exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 hord) hfermat
  rw [← hj, ← h2, h1]

theorem pow_eq_one_of_mul_pow_eq_one {Z : Type*} [Group Z] (hcomm : ∀ a b : Z, a * b = b * a)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ι : Z →* X) (hι : Function.Injective ι) (φ : Z →* Z)
    (b : X) (hφ : ∀ z, ι (φ z) = b * ι z * b⁻¹) (hb : b ^ p = 1)
    (hΩ : ∀ y y' : Z, y ≠ 1 → y ^ p = 1 → y' ^ p = 1 → y' ∈ Subgroup.zpowers y)
    (hpow : ∀ z : Z, ∃ n, z ^ (p ^ n) = 1) (w : Z) (h : (ι w * b) ^ p = 1) : w ^ p = 1 := by
  have hφp : ∀ z, φ^[p] z = z := by
    intro z
    apply hι
    rw [iterate_conj ι φ b hφ, hb, one_mul, inv_one, mul_one]
  have hfix := fix_of_pow_eq_one hp φ hφp hΩ
  letI : CommGroup Z := { ‹Group Z› with mul_comm := hcomm }
  have h1 := mul_pow_eq_prod ι φ b hφ w p
  rw [h, hb, mul_one] at h1
  have h2 : ∏ i ∈ Finset.range p, φ^[i] w = 1 := hι (by rw [← h1, map_one])
  exact pow_eq_one_of_norm_eq_one hp2 hp φ hfix hpow w h2

end Norm

section Centre

theorem mem_zpowers_of_pRank_le_one {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (hrk : CFSG.Open.pRank p (Subgroup.center G) ≤ 1) {y y' : G} (hy : y ∈ Subgroup.center G)
    (hy' : y' ∈ Subgroup.center G) (hne : y ≠ 1) (hyp : y ^ p = 1) (hy'p : y' ^ p = 1) :
    y' ∈ Subgroup.zpowers y := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E : Subgroup G := Subgroup.closure {y, y'} with hE
  have hcomm : ∀ a ∈ ({y, y'} : Set G), ∀ b ∈ ({y, y'} : Set G), a * b = b * a := by
    intro a ha b hb
    have hbc : b ∈ Subgroup.center G := by
      rcases hb with rfl | hb
      · exact hy
      · rw [Set.mem_singleton_iff.1 hb]; exact hy'
    exact Subgroup.mem_center_iff.1 hbc a
  have hall : ∀ a ∈ ({y, y'} : Set G), a ^ p = 1 := by
    intro a ha
    rcases ha with rfl | ha
    · exact hyp
    · rw [Set.mem_singleton_iff.1 ha]; exact hy'p
  have hEel : IsElemAbelian p E := IsElemAbelian.closure_of_commute hcomm hall
  have hEle : E ≤ Subgroup.center G := by
    rw [hE, Subgroup.closure_le]
    intro a ha
    rcases ha with rfl | ha
    · exact hy
    · rw [Set.mem_singleton_iff.1 ha]; exact hy'
  obtain ⟨k, hk⟩ := i271_exists_card_eq hp hEel
  have hkle : k ≤ 1 := (CFSG.SectionRank.le_pRank hp.one_lt hEle hEel hk).trans hrk
  have hz : Subgroup.zpowers y ≤ E :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have hcz : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hyp hne
  have hcard : Nat.card E ≤ Nat.card (Subgroup.zpowers y) := by
    rw [hk, hcz]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hkle
      _ = p := pow_one p
  have : Subgroup.zpowers y = E := Subgroup.eq_of_le_of_card_ge hz hcard
  rw [this]
  exact Subgroup.subset_closure (by simp)

variable {X : Type} [Group X]

@[expose] noncomputable def centerConj (K : Subgroup X)
    (n : ↥(Subgroup.normalizer (K : Set X))) : ↥(Subgroup.center ↥K) →* ↥(Subgroup.center ↥K) :=
  ((K.normalizerMonoidHom n).toMonoidHom.comp (Subgroup.center ↥K).subtype).codRestrict
    (Subgroup.center ↥K) fun z =>
      Subgroup.map_center_le_center (f := K.normalizerMonoidHom n)
        (K.normalizerMonoidHom n).surjective ⟨z, z.2, rfl⟩

@[expose] def centerIncl (K : Subgroup X) : ↥(Subgroup.center ↥K) →* X :=
  K.subtype.comp (Subgroup.center ↥K).subtype

theorem centerIncl_injective (K : Subgroup X) : Function.Injective (centerIncl K) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem centerIncl_centerConj (K : Subgroup X) (n : ↥(Subgroup.normalizer (K : Set X)))
    (z : ↥(Subgroup.center ↥K)) :
    centerIncl K (centerConj K n z) = (n : X) * centerIncl K z * (n : X)⁻¹ := rfl

theorem conj_eq_of_pow_eq_one {p : ℕ} [Finite X] (hp : p.Prime) {K : Subgroup X}
    (hrk : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1) {b : X}
    (hbN : b ∈ Subgroup.normalizer (K : Set X)) (hb : b ^ p = 1)
    (y : ↥(Subgroup.center ↥K)) (hy : y ^ p = 1) :
    b * centerIncl K y * b⁻¹ = centerIncl K y := by
  have hφ : ∀ z, centerIncl K (centerConj K ⟨b, hbN⟩ z) = b * centerIncl K z * b⁻¹ :=
    fun z => centerIncl_centerConj K ⟨b, hbN⟩ z
  have hφp : ∀ z, (centerConj K ⟨b, hbN⟩)^[p] z = z := by
    intro z
    apply centerIncl_injective K
    rw [iterate_conj (centerIncl K) (centerConj K ⟨b, hbN⟩) b hφ, hb, one_mul, inv_one, mul_one]
  have hΩ : ∀ y y' : ↥(Subgroup.center ↥K), y ≠ 1 → y ^ p = 1 → y' ^ p = 1 →
      y' ∈ Subgroup.zpowers y := by
    intro y y' hne hyp hy'p
    have hne' : (y : ↥K) ≠ 1 := fun h => hne (Subtype.ext h)
    have h1 := mem_zpowers_of_pRank_le_one hp hrk y.2 y'.2 hne'
      (congrArg Subtype.val hyp) (congrArg Subtype.val hy'p)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨j, Subtype.ext hj⟩
  have := fix_of_pow_eq_one hp (centerConj K ⟨b, hbN⟩) hφp hΩ y hy
  rw [← hφ y, this]

theorem centerLift_of_pRank_le_one {p : ℕ} [Finite X] (hp : p.Prime) (hp2 : p ≠ 2) {B K : Subgroup X}
    (hB : IsSCp p ⊤ B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hZp : IsPGroup p (Subgroup.center ↥K)) (hrk : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1) :
    CenterLift B K := by
  intro b hb k hk hw
  have hbN : b ∈ Subgroup.normalizer (K : Set X) := hBN hb
  have hbp : b ^ p = 1 := hB.2.1.2 b hb
  obtain ⟨hwK, hwc⟩ := mem_centreOf.1 hw
  set w : X := k * b * k⁻¹ * b⁻¹ with hwdef
  set z : ↥(Subgroup.center ↥K) := ⟨⟨w, hwK⟩, hwc⟩ with hzdef
  have hzw : centerIncl K z = w := rfl
  have hcomm : ∀ a c : ↥(Subgroup.center ↥K), a * c = c * a :=
    fun a c => Subtype.ext (Subgroup.mem_center_iff.1 c.2 a)
  have hφ : ∀ u, centerIncl K (centerConj K ⟨b, hbN⟩ u) = b * centerIncl K u * b⁻¹ :=
    fun u => centerIncl_centerConj K ⟨b, hbN⟩ u
  have hΩ : ∀ y y' : ↥(Subgroup.center ↥K), y ≠ 1 → y ^ p = 1 → y' ^ p = 1 →
      y' ∈ Subgroup.zpowers y := by
    intro y y' hne hyp hy'p
    have hne' : (y : ↥K) ≠ 1 := fun h => hne (Subtype.ext h)
    have h1 := mem_zpowers_of_pRank_le_one hp hrk y.2 y'.2 hne'
      (congrArg Subtype.val hyp) (congrArg Subtype.val hy'p)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨j, Subtype.ext hj⟩
  have hcw : (centerIncl K z * b) ^ p = 1 := by
    have : centerIncl K z * b = k * b * k⁻¹ := by rw [hzw, hwdef]; group
    rw [this, conj_pow, hbp]
    group
  have hzp : z ^ p = 1 :=
    pow_eq_one_of_mul_pow_eq_one hcomm hp hp2 (centerIncl K) (centerIncl_injective K)
      (centerConj K ⟨b, hbN⟩) b hφ hbp hΩ hZp z hcw
  have hwp : w ^ p = 1 := by
    rw [← hzw, ← map_pow, hzp, map_one]
  have hcommB : ∀ a ∈ B, a * w = w * a := by
    intro a ha
    have h1 := conj_eq_of_pow_eq_one hp hrk (hBN ha) (hB.2.1.2 a ha) z hzp
    rw [hzw] at h1
    calc a * w = (a * w * a⁻¹) * a := by group
      _ = w * a := by rw [h1]
  have hzel : IsElemAbelian p (Subgroup.zpowers w) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha c hc
      rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hc]
    · intro a ha
      rw [Set.mem_singleton_iff.1 ha]
      exact hwp
  have hsup : IsElemAbelian p (B ⊔ Subgroup.zpowers w) := by
    refine IsElemAbelian.sup_of_commute hB.2.1 hzel ?_
    intro a ha c hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact ((Commute.zpow_right (show Commute a w from hcommB a ha) j)).eq
  have hmax := hB.2.2 (B ⊔ Subgroup.zpowers w) le_top hsup le_sup_left
  rw [← hmax]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)

end Centre

end CFSG.HardMathSupport.Dickson.I271
