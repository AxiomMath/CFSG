module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise commutatorElement

variable {X : Type*} [Group X]

theorem normalizer_le_normalizer_map_of_characteristic (J : Subgroup X) (K : Subgroup J)
    [hK : K.Characteristic] :
    normalizer (J : Set X) ≤ normalizer (K.map J.subtype : Set X) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  have hmap := mem_normalizer_iff_map_conj_eq.mp hg
  let e : J ≃* J := ((MulAut.conj g).subgroupMap J).trans (MulEquiv.subgroupCongr hmap)
  have hey : e y ∈ K := by
    rw [← characteristic_iff_map_eq.mp hK e]
    exact mem_map_of_mem e.toMonoidHom hy
  exact mem_map.mpr ⟨e y, hey, rfl⟩

theorem odd_card_map_pPrimeCore_two [Finite X] (J : Subgroup X) :
    Odd (Nat.card ((pPrimeCore 2 J).map J.subtype)) := by
  rw [← Nat.card_congr ((pPrimeCore 2 J).equivMapOfInjective _ J.subtype_injective).toEquiv]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem le_pPrimeCore_two_of_normal_odd {G : Type*} [Group G] {S : Subgroup G} (hS : S.Normal)
    (hodd : Odd (Nat.card S)) : S ≤ pPrimeCore 2 G :=
  le_sSup ⟨hS, Nat.coprime_two_left.mpr hodd⟩

theorem inf_le_map_pPrimeCore_two [Finite X] {J Y : Subgroup X}
    (hJY : J ≤ normalizer (Y : Set X)) (hY : Odd (Nat.card Y)) :
    J ⊓ Y ≤ (pPrimeCore 2 J).map J.subtype := by
  have hnormal : ((J ⊓ Y).subgroupOf J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf, mem_inf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact ⟨mul_mem (mul_mem g.2 hn.1) (inv_mem g.2),
      (mem_normalizer_iff.mp (hJY g.2) n).mp hn.2⟩
  have hodd : Odd (Nat.card ((J ⊓ Y).subgroupOf J)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : J ⊓ Y ≤ J)).toEquiv]
    exact Odd.of_dvd_nat hY (card_dvd_of_le inf_le_right)
  have hle := map_mono (f := J.subtype) (le_pPrimeCore_two_of_normal_odd hnormal hodd)
  rwa [map_subgroupOf_eq_of_le inf_le_left] at hle

theorem mem_sup_iff_exists_mul {H K : Subgroup X} (hHK : H ≤ normalizer (K : Set X)) {x : X} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H K hHK]
  exact Set.mem_mul

structure SharedInvolutionData (J L : Subgroup X) (a : X) : Prop where
  normalizes_left : J ≤ normalizer (L : Set X)
  normalizes_right : L ≤ normalizer (J : Set X)
  commutator_le : ⁅J, L⁆ ≤ (pPrimeCore 2 J).map J.subtype ⊓ (pPrimeCore 2 L).map L.subtype
  mem_left : a ∈ J
  mem_right : a ∈ L
  central_left : ∀ j ∈ J, a * j = j * a
  central_right : ∀ l ∈ L, a * l = l * a
  orderOf_eq : orderOf a = 2
  center_left : center (J ⧸ pPrimeCore 2 J) = zpowers ((⟨a, mem_left⟩ : J) : J ⧸ pPrimeCore 2 J)
  center_right :
    center (L ⧸ pPrimeCore 2 L) = zpowers ((⟨a, mem_right⟩ : L) : L ⧸ pPrimeCore 2 L)

namespace SharedInvolutionData

variable {J L : Subgroup X} {a : X}

theorem core_left_le_normalizer_right (h : SharedInvolutionData J L a) :
    L ≤ normalizer (((pPrimeCore 2 J).map J.subtype : Subgroup X) : Set X) :=
  h.normalizes_right.trans (normalizer_le_normalizer_map_of_characteristic J _)

theorem core_left_le_normalizer_left (J : Subgroup X) :
    J ≤ normalizer (((pPrimeCore 2 J).map J.subtype : Subgroup X) : Set X) :=
  le_normalizer.trans (normalizer_le_normalizer_map_of_characteristic J _)

theorem core_right_le_normalizer_left (h : SharedInvolutionData J L a) :
    J ≤ normalizer (((pPrimeCore 2 L).map L.subtype : Subgroup X) : Set X) :=
  h.normalizes_left.trans (normalizer_le_normalizer_map_of_characteristic L _)

theorem sup_le_normalizer_core (h : SharedInvolutionData J L a) :
    J ⊔ L ≤ normalizer ((((pPrimeCore 2 J).map J.subtype ⊔
      (pPrimeCore 2 L).map L.subtype : Subgroup X)) : Set X) := by
  refine sup_le ?_ ?_
  · exact le_trans (le_inf (core_left_le_normalizer_left J) h.core_right_le_normalizer_left)
      (inf_normalizer_le_normalizer_sup _ _)
  · exact le_trans (le_inf h.core_left_le_normalizer_right
      (core_left_le_normalizer_left L)) (inf_normalizer_le_normalizer_sup _ _)

theorem core_inf_left [Finite X] (h : SharedInvolutionData J L a) :
    ((pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype) ⊓ J =
      (pPrimeCore 2 J).map J.subtype := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxN, hxJ⟩ := mem_inf.mp hx
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (mem_sup_iff_exists_mul ((map_subtype_le _).trans h.core_right_le_normalizer_left)).mp hxN
    have huJ : u ∈ J := map_subtype_le (pPrimeCore 2 J) hu
    have hvJ : v ∈ J := by
      have := mul_mem (inv_mem huJ) hxJ
      rwa [inv_mul_cancel_left] at this
    have hv' := inf_le_map_pPrimeCore_two h.core_right_le_normalizer_left
      (odd_card_map_pPrimeCore_two L) ⟨hvJ, hv⟩
    exact mul_mem hu hv'
  · exact le_inf le_sup_left (map_subtype_le _)

theorem core_inf_right [Finite X] (h : SharedInvolutionData J L a) :
    ((pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype) ⊓ L =
      (pPrimeCore 2 L).map L.subtype := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxN, hxL⟩ := mem_inf.mp hx
    obtain ⟨u, hu, v, hv, rfl⟩ :=
      (mem_sup_iff_exists_mul ((map_subtype_le _).trans h.core_right_le_normalizer_left)).mp hxN
    have hvL : v ∈ L := map_subtype_le (pPrimeCore 2 L) hv
    have huL : u ∈ L := by
      have := mul_mem hxL (inv_mem hvL)
      rwa [mul_inv_cancel_right] at this
    have hu' := inf_le_map_pPrimeCore_two h.core_left_le_normalizer_right
      (odd_card_map_pPrimeCore_two J) ⟨huL, hu⟩
    exact mul_mem hu' hv
  · exact le_inf le_sup_right (map_subtype_le _)

theorem core_sup_le [Finite X] (h : SharedInvolutionData J L a) :
    (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype ≤
      (pPrimeCore 2 ↥(J ⊔ L)).map (J ⊔ L).subtype := by
  have hE := h.sup_le_normalizer_core
  have hpiece : ∀ (K : Subgroup X), K ≤ J ⊔ L → J ⊔ L ≤ normalizer (K : Set X) →
      Odd (Nat.card K) → K ≤ (pPrimeCore 2 ↥(J ⊔ L)).map (J ⊔ L).subtype := by
    intro K hKE hnorm hodd
    have hnormal : (K.subgroupOf (J ⊔ L)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hKE).mpr hnorm
    have hodd' : Odd (Nat.card (K.subgroupOf (J ⊔ L))) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hKE).toEquiv]
    have hle := map_mono (f := (J ⊔ L).subtype) (le_pPrimeCore_two_of_normal_odd hnormal hodd')
    rwa [map_subgroupOf_eq_of_le hKE] at hle
  refine sup_le (hpiece _ ((map_subtype_le _).trans le_sup_left) ?_
    (odd_card_map_pPrimeCore_two J)) (hpiece _ ((map_subtype_le _).trans le_sup_right) ?_
    (odd_card_map_pPrimeCore_two L))
  · exact sup_le (core_left_le_normalizer_left J) h.core_left_le_normalizer_right
  · exact sup_le h.core_right_le_normalizer_left (core_left_le_normalizer_left L)

theorem odd_card_core_sup [Finite X] (h : SharedInvolutionData J L a) :
    Odd (Nat.card ((pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype :
      Subgroup X)) :=
  Odd.of_dvd_nat (odd_card_map_pPrimeCore_two (J ⊔ L)) (card_dvd_of_le h.core_sup_le)

theorem zpow_eq_one_of_mem_odd [Finite X] (h : SharedInvolutionData J L a) {K : Subgroup X}
    (hK : Odd (Nat.card K)) {k : ℤ} (hk : a ^ k ∈ K) : a ^ k = 1 := by
  have h1 : orderOf (a ^ k) ∣ 2 := by
    rw [← h.orderOf_eq]
    exact orderOf_dvd_of_pow_eq_one (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, pow_orderOf_eq_one, one_zpow])
  have h2 : orderOf (a ^ k) ∣ Nat.card K := K.orderOf_dvd_natCard hk
  have h3 : orderOf (a ^ k) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h1' | h2'
    · exact h1'
    · rw [h2'] at h2
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hK)
  exact orderOf_eq_one_iff.mp h3

theorem quotient_structure [Finite X] (h : SharedInvolutionData J L a)
    (M : Subgroup ↥(J ⊔ L)) [M.Normal]
    (hM : ∀ e : ↥(J ⊔ L), e ∈ M ↔
      (e : X) ∈ (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype) :
    ∃ μ : (J ⧸ pPrimeCore 2 J) × (L ⧸ pPrimeCore 2 L) →* ↥(J ⊔ L) ⧸ M,
      (∀ (j : J) (l : L), μ ((j : J ⧸ pPrimeCore 2 J), (l : L ⧸ pPrimeCore 2 L)) =
        ((⟨j * l, mul_mem_sup j.2 l.2⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ M)) ∧
      Function.Surjective μ ∧
      μ.ker = zpowers (((⟨a, h.mem_left⟩ : J) : J ⧸ pPrimeCore 2 J),
        ((⟨a, h.mem_right⟩ : L) : L ⧸ pPrimeCore 2 L)) ∧
      center (↥(J ⊔ L) ⧸ M) =
        zpowers ((⟨a, mem_sup_left h.mem_left⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ M) ∧
      orderOf ((⟨a, mem_sup_left h.mem_left⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ M) = 2 ∧
      pPrimeCore 2 (↥(J ⊔ L) ⧸ M) = ⊥ := by
  set N := (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype with hNdef
  let gJ : J →* ↥(J ⊔ L) ⧸ M := (QuotientGroup.mk' M).comp (inclusion le_sup_left)
  let gL : L →* ↥(J ⊔ L) ⧸ M := (QuotientGroup.mk' M).comp (inclusion le_sup_right)
  have hgJ : pPrimeCore 2 J ≤ gJ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change (((inclusion le_sup_left x : ↥(J ⊔ L))) : ↥(J ⊔ L) ⧸ M) = 1
    rw [QuotientGroup.eq_one_iff, hM]
    exact mem_sup_left (mem_map_of_mem _ hx)
  have hgL : pPrimeCore 2 L ≤ gL.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change (((inclusion le_sup_right x : ↥(J ⊔ L))) : ↥(J ⊔ L) ⧸ M) = 1
    rw [QuotientGroup.eq_one_iff, hM]
    exact mem_sup_right (mem_map_of_mem _ hx)
  let fJ : J ⧸ pPrimeCore 2 J →* ↥(J ⊔ L) ⧸ M := QuotientGroup.lift _ gJ hgJ
  let fL : L ⧸ pPrimeCore 2 L →* ↥(J ⊔ L) ⧸ M := QuotientGroup.lift _ gL hgL
  have hfJ : ∀ j : J, fJ (j : J ⧸ pPrimeCore 2 J) =
      ((⟨j, mem_sup_left j.2⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ M) := fun _ => rfl
  have hfL : ∀ l : L, fL (l : L ⧸ pPrimeCore 2 L) =
      ((⟨l, mem_sup_right l.2⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ M) := fun _ => rfl
  have hcommute : ∀ x y, Commute (fJ x) (fL y) := by
    intro x y
    induction x using QuotientGroup.induction_on with | H j => ?_
    induction y using QuotientGroup.induction_on with | H l => ?_
    rw [hfJ, hfL]
    change _ * _ = _ * _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hM]
    have hc : ⁅(l : X)⁻¹, (j : X)⁻¹⁆ ∈ ⁅J, L⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator (inv_mem l.2) (inv_mem j.2)
    have hN := h.commutator_le hc
    convert mem_sup_left (mem_inf.mp hN).1 using 1
    simp only [coe_mul, coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
    group
  let μ := fJ.noncommCoprod fL hcommute
  have hμ : ∀ (j : J) (l : L), μ ((j : J ⧸ pPrimeCore 2 J), (l : L ⧸ pPrimeCore 2 L)) =
      ((⟨j * l, mul_mem_sup j.2 l.2⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ M) := by
    intro j l
    rw [MonoidHom.noncommCoprod_apply, hfJ, hfL, ← QuotientGroup.mk_mul]
    rfl
  have hinjJ : Function.Injective fJ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with | H j => ?_
    rw [hfJ, QuotientGroup.eq_one_iff, hM] at hx
    rw [QuotientGroup.eq_one_iff]
    have hmem : (j : X) ∈ N ⊓ J := mem_inf.mpr ⟨hx, j.2⟩
    rw [h.core_inf_left] at hmem
    exact (mem_map_iff_mem J.subtype_injective).mp hmem
  have hinjL : Function.Injective fL := by
    rw [injective_iff_map_eq_one]
    intro y hy
    induction y using QuotientGroup.induction_on with | H l => ?_
    rw [hfL, QuotientGroup.eq_one_iff, hM] at hy
    rw [QuotientGroup.eq_one_iff]
    have hmem : (l : X) ∈ N ⊓ L := mem_inf.mpr ⟨hy, l.2⟩
    rw [h.core_inf_right] at hmem
    exact (mem_map_iff_mem L.subtype_injective).mp hmem
  have hsurj : Function.Surjective μ := by
    intro w
    induction w using QuotientGroup.induction_on with | H e => ?_
    obtain ⟨j, hj, l, hl, hjl⟩ := (mem_sup_iff_exists_mul h.normalizes_left).mp e.2
    refine ⟨(((⟨j, hj⟩ : J) : J ⧸ pPrimeCore 2 J), ((⟨l, hl⟩ : L) : L ⧸ pPrimeCore 2 L)), ?_⟩
    rw [hμ]
    congr 1
    exact Subtype.ext hjl
  set aJ : J := ⟨a, h.mem_left⟩ with haJdef
  set aL : L := ⟨a, h.mem_right⟩ with haLdef
  set ah : ↥(J ⊔ L) ⧸ M := ((⟨a, mem_sup_left h.mem_left⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ M)
    with hahdef
  have hfaJ : fJ (aJ : J ⧸ pPrimeCore 2 J) = ah := rfl
  have hfaL : fL (aL : L ⧸ pPrimeCore 2 L) = ah := by
    rw [hfL]
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one a
  have hah2 : ah ^ 2 = 1 := by
    rw [hahdef, ← QuotientGroup.mk_pow]
    have : (⟨a, mem_sup_left h.mem_left⟩ : ↥(J ⊔ L)) ^ 2 = 1 := Subtype.ext (by simp [ha2])
    rw [this, QuotientGroup.mk_one]
  have hah1 : ah ≠ 1 := by
    intro h1
    rw [hahdef, QuotientGroup.eq_one_iff, hM] at h1
    have := h.zpow_eq_one_of_mem_odd h.odd_card_core_sup (k := 1) (by rwa [zpow_one])
    rw [zpow_one] at this
    have hord := h.orderOf_eq
    rw [this, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have horder : orderOf ah = 2 := orderOf_eq_prime hah2 hah1
  have haJ2 : (aJ : J ⧸ pPrimeCore 2 J) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : aJ ^ 2 = 1 := Subtype.ext (by simp only [haJdef, SubmonoidClass.mk_pow, ha2]; rfl)
    rw [this, QuotientGroup.mk_one]
  have haL2 : (aL : L ⧸ pPrimeCore 2 L) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : aL ^ 2 = 1 := Subtype.ext (by simp only [haLdef, SubmonoidClass.mk_pow, ha2]; rfl)
    rw [this, QuotientGroup.mk_one]
  have haJc : (aJ : J ⧸ pPrimeCore 2 J) ∈ center (J ⧸ pPrimeCore 2 J) := by
    rw [h.center_left]
    exact mem_zpowers _
  have haLc : (aL : L ⧸ pPrimeCore 2 L) ∈ center (L ⧸ pPrimeCore 2 L) := by
    rw [h.center_right]
    exact mem_zpowers _
  have hZJ : ∀ x, (∀ x', fJ x * fJ x' = fJ x' * fJ x) → x ∈ center (J ⧸ pPrimeCore 2 J) := by
    intro x hx
    rw [mem_center_iff]
    intro x'
    apply hinjJ
    rw [map_mul, map_mul]
    exact (hx x').symm
  have hZL : ∀ y, (∀ y', fL y * fL y' = fL y' * fL y) → y ∈ center (L ⧸ pPrimeCore 2 L) := by
    intro y hy
    rw [mem_center_iff]
    intro y'
    apply hinjL
    rw [map_mul, map_mul]
    exact (hy y').symm
  have hpowJ : ∀ x ∈ center (J ⧸ pPrimeCore 2 J), ∃ k : ℤ, fJ x = ah ^ k := by
    intro x hx
    rw [h.center_left] at hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact ⟨k, by rw [map_zpow, ← haJdef, hfaJ]⟩
  have hpowL : ∀ y ∈ center (L ⧸ pPrimeCore 2 L), ∃ k : ℤ, fL y = ah ^ k := by
    intro y hy
    rw [h.center_right] at hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact ⟨k, by rw [map_zpow, ← haLdef, hfaL]⟩
  have hcenter : center (↥(J ⊔ L) ⧸ M) = zpowers ah := by
    apply le_antisymm
    · intro w hw
      obtain ⟨⟨x, y⟩, rfl⟩ := hsurj w
      rw [mem_center_iff] at hw
      have hw' : ∀ z, z * (fJ x * fL y) = fJ x * fL y * z := fun z => hw z
      have hx : x ∈ center (J ⧸ pPrimeCore 2 J) := by
        refine hZJ x fun x' => ?_
        have key : fJ x' * fJ x * fL y = fJ x * fJ x' * fL y := by
          calc fJ x' * fJ x * fL y = fJ x' * (fJ x * fL y) := mul_assoc _ _ _
            _ = fJ x * fL y * fJ x' := hw' (fJ x')
            _ = fJ x * (fL y * fJ x') := mul_assoc _ _ _
            _ = fJ x * (fJ x' * fL y) := by rw [← (hcommute x' y).eq]
            _ = fJ x * fJ x' * fL y := (mul_assoc _ _ _).symm
        exact (mul_right_cancel key).symm
      have hy : y ∈ center (L ⧸ pPrimeCore 2 L) := by
        refine hZL y fun y' => ?_
        have key : fJ x * (fL y' * fL y) = fJ x * (fL y * fL y') := by
          calc fJ x * (fL y' * fL y) = (fJ x * fL y') * fL y := (mul_assoc _ _ _).symm
            _ = (fL y' * fJ x) * fL y := by rw [(hcommute x y').eq]
            _ = fL y' * (fJ x * fL y) := mul_assoc _ _ _
            _ = fJ x * fL y * fL y' := hw' (fL y')
            _ = fJ x * (fL y * fL y') := mul_assoc _ _ _
        exact (mul_left_cancel key).symm
      obtain ⟨k, hk⟩ := hpowJ x hx
      obtain ⟨m, hm⟩ := hpowL y hy
      change fJ x * fL y ∈ zpowers ah
      rw [hk, hm, ← zpow_add]
      exact zpow_mem (mem_zpowers ah) _
    · rw [zpowers_le, mem_center_iff]
      intro w
      obtain ⟨⟨x, y⟩, rfl⟩ := hsurj w
      change fJ x * fL y * ah = ah * (fJ x * fL y)
      have h1 : fJ x * ah = ah * fJ x := by
        rw [← hfaJ, ← map_mul, ← map_mul, (mem_center_iff.mp haJc x)]
      have h2 : fL y * ah = ah * fL y := by
        rw [← hfaL, ← map_mul, ← map_mul, (mem_center_iff.mp haLc y)]
      rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hker : μ.ker = zpowers ((aJ : J ⧸ pPrimeCore 2 J), (aL : L ⧸ pPrimeCore 2 L)) := by
    apply le_antisymm
    · rintro ⟨x, y⟩ hxy
      rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hxy
      have hfx : fJ x = fL y⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left hxy
      have hx : x ∈ center (J ⧸ pPrimeCore 2 J) := by
        refine hZJ x fun x' => ?_
        rw [hfx]
        exact ((hcommute x' y⁻¹).eq).symm
      rw [h.center_left] at hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
      have hy : y⁻¹ = (aL : L ⧸ pPrimeCore 2 L) ^ k := by
        apply hinjL
        rw [← hfx, ← hk, map_zpow, map_zpow, hfaJ, hfaL]
      refine mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [Prod.pow_def]
      ext
      · exact hk
      · change (aL : L ⧸ pPrimeCore 2 L) ^ k = y
        have hsq : ((aL : L ⧸ pPrimeCore 2 L) ^ k) ^ 2 = 1 := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, haL2, one_zpow]
        rw [← inv_inv y, hy]
        exact (inv_eq_of_mul_eq_one_left (by rw [← pow_two, hsq])).symm
    · rw [zpowers_le, MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply]
      change fJ (aJ : J ⧸ pPrimeCore 2 J) * fL (aL : L ⧸ pPrimeCore 2 L) = 1
      rw [hfaJ, hfaL, ← pow_two, hah2]
  set R := pPrimeCore 2 (↥(J ⊔ L) ⧸ M) with hRdef
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hRJ : ∀ x, fJ x ∈ R → x = 1 := by
    intro x hx
    have hS : R.comap fJ ≤ pPrimeCore 2 (J ⧸ pPrimeCore 2 J) := by
      refine le_pPrimeCore_two_of_normal_odd (Normal.comap inferInstance fJ) ?_
      rw [← card_map_of_injective hinjJ]
      exact Odd.of_dvd_nat hRodd (card_dvd_of_le (map_comap_le _ _))
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hS
    exact mem_bot.mp (hS hx)
  have hRL : ∀ y, fL y ∈ R → y = 1 := by
    intro y hy
    have hS : R.comap fL ≤ pPrimeCore 2 (L ⧸ pPrimeCore 2 L) := by
      refine le_pPrimeCore_two_of_normal_odd (Normal.comap inferInstance fL) ?_
      rw [← card_map_of_injective hinjL]
      exact Odd.of_dvd_nat hRodd (card_dvd_of_le (map_comap_le _ _))
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hS
    exact mem_bot.mp (hS hy)
  have hRcenter : R ≤ center (↥(J ⊔ L) ⧸ M) := by
    intro r hr
    obtain ⟨⟨x₀, y₀⟩, hr₀⟩ := hsurj r
    have hr₀' : r = fJ x₀ * fL y₀ := hr₀.symm
    have hcommJ : ∀ x, r * fJ x = fJ x * r := by
      intro x
      have hconj : r * fJ x * r⁻¹ = fJ (x₀ * x * x₀⁻¹) := by
        rw [hr₀', map_mul, map_mul, map_inv, mul_inv_rev]
        calc fJ x₀ * fL y₀ * fJ x * ((fL y₀)⁻¹ * (fJ x₀)⁻¹)
            = fJ x₀ * (fL y₀ * fJ x) * (fL y₀)⁻¹ * (fJ x₀)⁻¹ := by group
          _ = fJ x₀ * (fJ x * fL y₀) * (fL y₀)⁻¹ * (fJ x₀)⁻¹ := by
            rw [(hcommute x y₀).eq]
          _ = fJ x₀ * fJ x * (fJ x₀)⁻¹ := by group
      have hmem : fJ (x₀ * x * x₀⁻¹ * x⁻¹) ∈ R := by
        rw [map_mul, ← hconj, map_inv]
        have hrinv : fJ x * r⁻¹ * (fJ x)⁻¹ ∈ R :=
          (inferInstance : R.Normal).conj_mem _ (inv_mem hr) _
        have := mul_mem hr hrinv
        simpa only [mul_assoc] using this
      have h1 := hRJ _ hmem
      have h2 : x₀ * x * x₀⁻¹ = x := by
        calc x₀ * x * x₀⁻¹ = x₀ * x * x₀⁻¹ * x⁻¹ * x := by group
          _ = x := by rw [h1, one_mul]
      calc r * fJ x = r * fJ x * r⁻¹ * r := by group
        _ = fJ x * r := by rw [hconj, h2]
    have hcommL : ∀ y, r * fL y = fL y * r := by
      intro y
      have hconj : r * fL y * r⁻¹ = fL (y₀ * y * y₀⁻¹) := by
        rw [hr₀', map_mul, map_mul, map_inv, mul_inv_rev]
        calc fJ x₀ * fL y₀ * fL y * ((fL y₀)⁻¹ * (fJ x₀)⁻¹)
            = fJ x₀ * (fL y₀ * fL y * (fL y₀)⁻¹) * (fJ x₀)⁻¹ := by group
          _ = (fL y₀ * fL y * (fL y₀)⁻¹) * fJ x₀ * (fJ x₀)⁻¹ := by
            rw [← map_inv, ← map_mul, ← map_mul, (hcommute x₀ _).eq]
          _ = fL y₀ * fL y * (fL y₀)⁻¹ := by group
      have hmem : fL (y₀ * y * y₀⁻¹ * y⁻¹) ∈ R := by
        rw [map_mul, ← hconj, map_inv]
        have hrinv : fL y * r⁻¹ * (fL y)⁻¹ ∈ R :=
          (inferInstance : R.Normal).conj_mem _ (inv_mem hr) _
        have := mul_mem hr hrinv
        simpa only [mul_assoc] using this
      have h1 := hRL _ hmem
      have h2 : y₀ * y * y₀⁻¹ = y := by
        calc y₀ * y * y₀⁻¹ = y₀ * y * y₀⁻¹ * y⁻¹ * y := by group
          _ = y := by rw [h1, one_mul]
      calc r * fL y = r * fL y * r⁻¹ * r := by group
        _ = fL y * r := by rw [hconj, h2]
    rw [mem_center_iff]
    intro w
    obtain ⟨⟨x, y⟩, rfl⟩ := hsurj w
    change fJ x * fL y * r = r * (fJ x * fL y)
    calc fJ x * fL y * r = fJ x * (fL y * r) := mul_assoc _ _ _
      _ = fJ x * (r * fL y) := by rw [← hcommL]
      _ = fJ x * r * fL y := (mul_assoc _ _ _).symm
      _ = r * fJ x * fL y := by rw [← hcommJ]
      _ = r * (fJ x * fL y) := mul_assoc _ _ _
  have hRbot : R = ⊥ := by
    have hdvd : Nat.card R ∣ 2 := by
      rw [← horder, ← Nat.card_zpowers, ← hcenter]
      exact card_dvd_of_le hRcenter
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact card_eq_one.mp h1
    · rw [h2] at hRodd
      exact absurd hRodd (by decide)
  exact ⟨μ, hμ, hsurj, hker, hcenter, horder, hRbot⟩

theorem inf_prod_mulEquiv [Finite X] (h : SharedInvolutionData J L a) :
    ∃ e : ↥((pPrimeCore 2 J).map J.subtype ⊓ (pPrimeCore 2 L).map L.subtype) × ↥(zpowers a) ≃*
        ↥(J ⊓ L), ∀ x y, (e (x, y) : X) = x * y := by
  set P := (pPrimeCore 2 J).map J.subtype ⊓ (pPrimeCore 2 L).map L.subtype with hPdef
  have hPT : P ≤ J ⊓ L := inf_le_inf (map_subtype_le _) (map_subtype_le _)
  have hZT : zpowers a ≤ J ⊓ L := zpowers_le.mpr (mem_inf.mpr ⟨h.mem_left, h.mem_right⟩)
  let φ₁ : P →* ↥(J ⊓ L) := inclusion hPT
  let φ₂ : zpowers a →* ↥(J ⊓ L) := inclusion hZT
  have hcomm : ∀ x y, Commute (φ₁ x) (φ₂ y) := by
    rintro x ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have hxJ : (x : X) ∈ J := map_subtype_le (pPrimeCore 2 J) (mem_inf.mp x.2).1
    have hca : Commute a (x : X) := h.central_left _ hxJ
    exact Subtype.ext ((hca.zpow_left k).symm.eq)
  let φ := φ₁.noncommCoprod φ₂ hcomm
  have hPodd : Odd (Nat.card P) :=
    Odd.of_dvd_nat (odd_card_map_pPrimeCore_two J) (card_dvd_of_le inf_le_left)
  have hPZ : P ⊓ zpowers a = ⊥ := by
    rw [← disjoint_iff]
    apply disjoint_of_coprime_natCard
    rw [Nat.card_zpowers, h.orderOf_eq]
    exact Nat.coprime_two_right.mpr hPodd
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨inclusion_injective _, inclusion_injective _, ?_⟩
    rw [disjoint_iff, eq_bot_iff]
    intro t ht
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := mem_inf.mp ht
    have htP : (t : X) ∈ P := by rw [← hx]; exact x.2
    have htZ : (t : X) ∈ zpowers a := by rw [← hy]; exact y.2
    have ht1 : (t : X) ∈ P ⊓ zpowers a := mem_inf.mpr ⟨htP, htZ⟩
    rw [hPZ] at ht1
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp ht1))
  have hsurj : Function.Surjective φ := by
    intro t
    have htJ : (t : X) ∈ J := (mem_inf.mp t.2).1
    have htL : (t : X) ∈ L := (mem_inf.mp t.2).2
    have hcJ : ((⟨t, htJ⟩ : J) : J ⧸ pPrimeCore 2 J) ∈ center (J ⧸ pPrimeCore 2 J) := by
      rw [mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with | H j => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        ← mem_map_iff_mem J.subtype_injective]
      have hc : ⁅(t : X)⁻¹, (j : X)⁻¹⁆ ∈ ⁅J, L⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator (inv_mem htL) (inv_mem j.2)
      convert (mem_inf.mp (h.commutator_le hc)).1 using 1
      simp only [subtype_apply, coe_mul, coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
      group
    have hcL : ((⟨t, htL⟩ : L) : L ⧸ pPrimeCore 2 L) ∈ center (L ⧸ pPrimeCore 2 L) := by
      rw [mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with | H l => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        ← mem_map_iff_mem L.subtype_injective]
      have hc : ⁅(t : X)⁻¹, (l : X)⁻¹⁆ ∈ ⁅J, L⁆ :=
        commutator_mem_commutator (inv_mem htJ) (inv_mem l.2)
      convert (mem_inf.mp (h.commutator_le hc)).2 using 1
      simp only [subtype_apply, coe_mul, coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
      group
    rw [h.center_left] at hcJ
    rw [h.center_right] at hcL
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hcJ
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hcL
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, ← mem_map_iff_mem J.subtype_injective] at hk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, ← mem_map_iff_mem L.subtype_injective] at hm
    simp only [subtype_apply, coe_mul, coe_inv, coe_zpow] at hk hm
    have hkm : a ^ (m - k) = 1 := by
      apply h.zpow_eq_one_of_mem_odd h.odd_card_core_sup
      have := mul_mem (mem_sup_left hk : _ ∈ (pPrimeCore 2 J).map J.subtype ⊔
        (pPrimeCore 2 L).map L.subtype) (inv_mem (mem_sup_right hm))
      convert this using 1
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    have hmk : a ^ m = a ^ k := by
      rw [zpow_sub, mul_inv_eq_one] at hkm
      exact hkm
    have hu : (a ^ k)⁻¹ * (t : X) ∈ P := mem_inf.mpr ⟨hk, hmk ▸ hm⟩
    refine ⟨(⟨_, hu⟩, ⟨a ^ k, zpow_mem (mem_zpowers a) k⟩), Subtype.ext ?_⟩
    change (a ^ k)⁻¹ * (t : X) * a ^ k = t
    have hca : Commute a (t : X) := h.central_left _ htJ
    rw [mul_assoc, ← (hca.zpow_left k).eq, inv_mul_cancel_left]
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun x y => rfl⟩

end SharedInvolutionData

theorem shared_involution_odd_core_product_quotient [Finite X] {J L : Subgroup X}
    (hJL : J ≤ normalizer (L : Set X)) (hLJ : L ≤ normalizer (J : Set X))
    (hcomm : ⁅J, L⁆ ≤ (pPrimeCore 2 J).map J.subtype ⊓ (pPrimeCore 2 L).map L.subtype)
    {a : X} (haJ : a ∈ J) (haL : a ∈ L) (hacJ : ∀ j ∈ J, a * j = j * a)
    (hacL : ∀ l ∈ L, a * l = l * a) (ha2 : orderOf a = 2)
    (hZA : center (J ⧸ pPrimeCore 2 J) = zpowers ((⟨a, haJ⟩ : J) : J ⧸ pPrimeCore 2 J))
    (hZB : center (L ⧸ pPrimeCore 2 L) = zpowers ((⟨a, haL⟩ : L) : L ⧸ pPrimeCore 2 L)) :
    (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype =
        (pPrimeCore 2 ↥(J ⊔ L)).map (J ⊔ L).subtype ∧
    ((pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype) ⊓ J =
        (pPrimeCore 2 J).map J.subtype ∧
    ((pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype) ⊓ L =
        (pPrimeCore 2 L).map L.subtype ∧
    (∃ e : ↥((pPrimeCore 2 J).map J.subtype ⊓ (pPrimeCore 2 L).map L.subtype) ×
        ↥(zpowers a) ≃* ↥(J ⊓ L), ∀ x y, (e (x, y) : X) = x * y) ∧
    (∃ μ : (J ⧸ pPrimeCore 2 J) × (L ⧸ pPrimeCore 2 L) →* ↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L),
      (∀ (j : J) (l : L), μ ((j : J ⧸ pPrimeCore 2 J), (l : L ⧸ pPrimeCore 2 L)) =
        ((⟨j * l, mul_mem_sup j.2 l.2⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L))) ∧
      Function.Surjective μ ∧
      μ.ker = zpowers (((⟨a, haJ⟩ : J) : J ⧸ pPrimeCore 2 J),
        ((⟨a, haL⟩ : L) : L ⧸ pPrimeCore 2 L)) ∧
      (∃ Φ : ((J ⧸ pPrimeCore 2 J) × (L ⧸ pPrimeCore 2 L)) ⧸ μ.ker ≃*
          ↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L), ∀ x, Φ (QuotientGroup.mk x) = μ x) ∧
      μ (((⟨a, haJ⟩ : J) : J ⧸ pPrimeCore 2 J), 1) =
        ((⟨a, mem_sup_left haJ⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L)) ∧
      center (↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L)) =
        zpowers ((⟨a, mem_sup_left haJ⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L)) ∧
      Nat.card (center (↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L))) = 2) ∧
    (∃ ν : ↥(J ⊔ L) →* ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) ×
        ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)),
      Function.Surjective ν ∧
      ν.ker = (((pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype) ⊔
        zpowers a).subgroupOf (J ⊔ L) ∧
      (∀ j : J, ν ⟨j, mem_sup_left j.2⟩ =
        (((j : J ⧸ pPrimeCore 2 J) : (J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)), 1)) ∧
      (∀ l : L, ν ⟨l, mem_sup_right l.2⟩ =
        (1, ((l : L ⧸ pPrimeCore 2 L) : (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)))) ∧
      ∃ Ψ : ↥(J ⊔ L) ⧸ ν.ker ≃* ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) ×
          ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)),
        ∀ x, Ψ (QuotientGroup.mk x) = ν x) := by
  have h : SharedInvolutionData J L a := ⟨hJL, hLJ, hcomm, haJ, haL, hacJ, hacL, ha2, hZA, hZB⟩
  set N := (pPrimeCore 2 J).map J.subtype ⊔ (pPrimeCore 2 L).map L.subtype with hNdef
  have hNE : N ≤ J ⊔ L := sup_le ((map_subtype_le _).trans le_sup_left)
    ((map_subtype_le _).trans le_sup_right)
  have hNnormal : (N.subgroupOf (J ⊔ L)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNE).mpr h.sup_le_normalizer_core
  obtain ⟨-, -, -, -, -, -, hR⟩ :=
    h.quotient_structure (N.subgroupOf (J ⊔ L)) (fun e => mem_subgroupOf)
  have hNeq : N.subgroupOf (J ⊔ L) = pPrimeCore 2 ↥(J ⊔ L) := by
    apply le_antisymm
    · apply le_pPrimeCore_two_of_normal_odd hNnormal
      rw [Nat.card_congr (subgroupOfEquivOfLe hNE).toEquiv]
      exact h.odd_card_core_sup
    · have himg : (pPrimeCore 2 ↥(J ⊔ L)).map (QuotientGroup.mk' (N.subgroupOf (J ⊔ L))) ≤
          pPrimeCore 2 (↥(J ⊔ L) ⧸ N.subgroupOf (J ⊔ L)) := by
        apply le_pPrimeCore_two_of_normal_odd
          (Normal.map inferInstance _ (QuotientGroup.mk'_surjective _))
        exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
          (card_map_dvd _ _)
      rw [hR, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg
      exact himg
  have hi : N = (pPrimeCore 2 ↥(J ⊔ L)).map (J ⊔ L).subtype := by
    rw [← hNeq, map_subgroupOf_eq_of_le hNE]
  obtain ⟨μ, hμ, hsurj, hker, hcenter, horder, -⟩ :=
    h.quotient_structure (pPrimeCore 2 ↥(J ⊔ L)) (fun e => by rw [← hNeq, mem_subgroupOf])
  have hμa : μ (((⟨a, haJ⟩ : J) : J ⧸ pPrimeCore 2 J), 1) =
      ((⟨a, mem_sup_left haJ⟩ : ↥(J ⊔ L)) : ↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L)) := by
    have := hμ ⟨a, haJ⟩ 1
    rw [QuotientGroup.mk_one] at this
    rw [this]
    congr 1
    exact Subtype.ext (by simp)
  set A := J ⧸ pPrimeCore 2 J
  set B := L ⧸ pPrimeCore 2 L
  let q : A × B →* (A ⧸ center A) × (B ⧸ center B) :=
    MonoidHom.prodMap (QuotientGroup.mk' (center A)) (QuotientGroup.mk' (center B))
  have hkq : μ.ker ≤ q.ker := by
    rw [hker, zpowers_le, MonoidHom.mem_ker]
    change (((((⟨a, haJ⟩ : J) : A)) : A ⧸ center A), (((⟨a, haL⟩ : L) : B) : B ⧸ center B)) = 1
    rw [Prod.mk_eq_one, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff, hZA, hZB]
    exact ⟨mem_zpowers _, mem_zpowers _⟩
  let Φ := QuotientGroup.quotientKerEquivOfSurjective μ hsurj
  let ν : ↥(J ⊔ L) →* (A ⧸ center A) × (B ⧸ center B) :=
    (QuotientGroup.lift μ.ker q hkq).comp (Φ.symm.toMonoidHom.comp (QuotientGroup.mk' _))
  have hν : ∀ (j : J) (l : L), ν ⟨j * l, mul_mem_sup j.2 l.2⟩ =
      (((j : A) : A ⧸ center A), ((l : B) : B ⧸ center B)) := by
    intro j l
    have hΦ : Φ.symm (((⟨j * l, mul_mem_sup j.2 l.2⟩ : ↥(J ⊔ L)) :
        ↥(J ⊔ L) ⧸ pPrimeCore 2 ↥(J ⊔ L))) = (((j : A), (l : B)) : (A × B) ⧸ μ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      exact (hμ j l).symm
    change QuotientGroup.lift μ.ker q hkq (Φ.symm (QuotientGroup.mk' _ _)) = _
    rw [QuotientGroup.mk'_apply, hΦ, QuotientGroup.lift_mk]
    rfl
  have hνJ : ∀ j : J, ν ⟨j, mem_sup_left j.2⟩ =
      (((j : A) : A ⧸ center A), 1) := by
    intro j
    have := hν j 1
    have he : (⟨j * ((1 : L) : X), mul_mem_sup j.2 (1 : L).2⟩ : ↥(J ⊔ L)) =
        ⟨j, mem_sup_left j.2⟩ := Subtype.ext (by simp)
    rw [he, QuotientGroup.mk_one, QuotientGroup.mk_one] at this
    exact this
  have hνL : ∀ l : L, ν ⟨l, mem_sup_right l.2⟩ =
      (1, ((l : B) : B ⧸ center B)) := by
    intro l
    have := hν 1 l
    have he : (⟨((1 : J) : X) * l, mul_mem_sup (1 : J).2 l.2⟩ : ↥(J ⊔ L)) =
        ⟨l, mem_sup_right l.2⟩ := Subtype.ext (by simp)
    rw [he, QuotientGroup.mk_one, QuotientGroup.mk_one] at this
    exact this
  have hνsurj : Function.Surjective ν := by
    rintro ⟨u, v⟩
    induction u using QuotientGroup.induction_on with | H x => ?_
    induction v using QuotientGroup.induction_on with | H y => ?_
    induction x using QuotientGroup.induction_on with | H j => ?_
    induction y using QuotientGroup.induction_on with | H l => ?_
    exact ⟨_, hν j l⟩
  have hνker : ν.ker = (N ⊔ zpowers a).subgroupOf (J ⊔ L) := by
    apply le_antisymm
    · intro e he
      rw [mem_subgroupOf]
      obtain ⟨j, hj, l, hl, hjl⟩ := (mem_sup_iff_exists_mul hJL).mp e.2
      have he' : e = ⟨((⟨j, hj⟩ : J) : X) * ((⟨l, hl⟩ : L) : X),
          mul_mem_sup hj hl⟩ := Subtype.ext hjl.symm
      rw [MonoidHom.mem_ker, he', hν, Prod.mk_eq_one, QuotientGroup.eq_one_iff,
        QuotientGroup.eq_one_iff, hZA, hZB] at he
      obtain ⟨hjz, hlz⟩ := he
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hjz
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hlz
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, ← mem_map_iff_mem J.subtype_injective] at hk
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, ← mem_map_iff_mem L.subtype_injective] at hm
      simp only [subtype_apply, coe_mul, coe_inv, coe_zpow] at hk hm
      rw [← hjl, show j * l = a ^ k * ((a ^ k)⁻¹ * j) * (a ^ m * ((a ^ m)⁻¹ * l)) by group]
      exact mul_mem (mul_mem (mem_sup_right (zpow_mem (mem_zpowers a) k))
        (mem_sup_left (mem_sup_left hk))) (mul_mem (mem_sup_right (zpow_mem (mem_zpowers a) m))
        (mem_sup_left (mem_sup_right hm)))
    · intro e he
      rw [mem_subgroupOf] at he
      have hle : N ⊔ zpowers a ≤ ν.ker.map (J ⊔ L).subtype := by
        refine sup_le ?_ ?_
        · intro n hn
          obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_exists_mul
            ((map_subtype_le _).trans h.core_right_le_normalizer_left)).mp hn
          obtain ⟨u', hu', rfl⟩ := mem_map.mp hu
          obtain ⟨v', hv', rfl⟩ := mem_map.mp hv
          refine ⟨⟨u' * v', mul_mem_sup u'.2 v'.2⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, hν, (QuotientGroup.eq_one_iff u').mpr hu',
            (QuotientGroup.eq_one_iff v').mpr hv', QuotientGroup.mk_one, QuotientGroup.mk_one]
          rfl
        · rw [zpowers_le]
          refine ⟨⟨a, mem_sup_left haJ⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, hνJ ⟨a, haJ⟩, Prod.mk_eq_one,
            QuotientGroup.eq_one_iff, hZA]
          exact ⟨mem_zpowers _, rfl⟩
      obtain ⟨e', he', hee'⟩ := mem_map.mp (hle he)
      rwa [← Subtype.ext hee']
  refine ⟨hi, h.core_inf_left, h.core_inf_right, h.inf_prod_mulEquiv,
    ⟨μ, hμ, hsurj, hker, ⟨Φ, fun x => rfl⟩, hμa, hcenter, ?_⟩,
    ⟨ν, hνsurj, hνker, hνJ, hνL, ⟨QuotientGroup.quotientKerEquivOfSurjective ν hνsurj,
      fun x => rfl⟩⟩⟩
  rw [hcenter, Nat.card_zpowers, horder]

end CFSG.ComponentClassification.UnbalancedGS
