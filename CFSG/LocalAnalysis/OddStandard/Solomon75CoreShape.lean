module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreHyp
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Pairing

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

namespace CoreAux

theorem isElemAbelian_iff {K : Type*} [Group K] {p : ℕ} {U : Subgroup K} :
    Open.IsElemAbelian p U ↔ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ ∀ x ∈ U, x ^ p = 1 := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨fun x hx y hy => ?_, hp⟩
    exact congrArg Subtype.val (isMulCommutative_iff.mp hc ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro ⟨hc, hp⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem isElemAbelian_mono {K : Type*} [Group K] {p : ℕ} {U V : Subgroup K} (h : U ≤ V)
    (hV : Open.IsElemAbelian p V) : Open.IsElemAbelian p U := CFSG.Open.IsElemAbelian.mono hV h

theorem orderOf_eq_two_of_isElemAbelian {K : Type*} [Group K] {U : Subgroup K}
    (hU : Open.IsElemAbelian 2 U) {x : K} (hx : x ∈ U) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by simpa using (isElemAbelian_iff.mp hU).2 x hx) hx1

section Transport

variable {K K' : Type} [Group K] [Group K'] {S : Subgroup K} {S' : Subgroup K'}

@[expose] def shapeMap (e : ↥S ≃* ↥S') (U : Subgroup K) : Subgroup K' :=
  ((U.subgroupOf S).map e.toMonoidHom).map S'.subtype

theorem mem_shapeMap {e : ↥S ≃* ↥S'} {U : Subgroup K} {x : K'} :
    x ∈ shapeMap e U ↔ ∃ s : ↥S, (s : K) ∈ U ∧ ((e s : ↥S') : K') = x := by
  simp only [shapeMap, Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩

theorem shapeMap_le (e : ↥S ≃* ↥S') (U : Subgroup K) : shapeMap e U ≤ S' :=
  Subgroup.map_subtype_le _

theorem shapeMap_mono (e : ↥S ≃* ↥S') {U V : Subgroup K} (h : U ≤ V) :
    shapeMap e U ≤ shapeMap e V := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := mem_shapeMap.mp hx
  exact mem_shapeMap.mpr ⟨s, h hs, rfl⟩

theorem shapeMap_symm (e : ↥S ≃* ↥S') {U : Subgroup K} (hU : U ≤ S) :
    shapeMap e.symm (shapeMap e U) = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨s', hs', rfl⟩ := mem_shapeMap.mp hx
    obtain ⟨s, hs, hse⟩ := mem_shapeMap.mp hs'
    have : e s = s' := Subtype.ext hse
    rw [← this, MulEquiv.symm_apply_apply]
    exact hs
  · intro hx
    refine mem_shapeMap.mpr ⟨e ⟨x, hU hx⟩, mem_shapeMap.mpr ⟨⟨x, hU hx⟩, hx, rfl⟩, ?_⟩
    simp

theorem shapeMap_shapeMap_symm (e : ↥S ≃* ↥S') {U : Subgroup K'} (hU : U ≤ S') :
    shapeMap e (shapeMap e.symm U) = U :=
  shapeMap_symm e.symm hU

theorem card_shapeMap (e : ↥S ≃* ↥S') {U : Subgroup K} (hU : U ≤ S) :
    Nat.card (shapeMap e U) = Nat.card U := by
  rw [shapeMap, Subgroup.card_map_of_injective S'.subtype_injective,
    Subgroup.card_map_of_injective e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv

theorem isElemAbelian_shapeMap (e : ↥S ≃* ↥S') {U : Subgroup K} (hU : Open.IsElemAbelian 2 U) :
    Open.IsElemAbelian 2 (shapeMap e U) := by
  rw [isElemAbelian_iff] at hU ⊢
  constructor
  · intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := mem_shapeMap.mp hx
    obtain ⟨t, ht, rfl⟩ := mem_shapeMap.mp hy
    have h : s * t = t * s := Subtype.ext (hU.1 _ hs _ ht)
    rw [← Subgroup.coe_mul, ← map_mul, h, map_mul, Subgroup.coe_mul]
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_shapeMap.mp hx
    have h : s ^ 2 = 1 := Subtype.ext (hU.2 _ hs)
    rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]

end Transport

theorem finite_of_doubleCover {K : Type} [Group K] {n : ℕ} (h : IsDoubleCoverOfAlt K n) :
    Finite K :=
  Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.Recognition.LyonsSims.card_eq_two_mul_of_doubleCover h]
    exact (Nat.mul_pos (by norm_num) Nat.card_pos).ne')

theorem exists_fourSub_of_two_le_pRank {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (h : 2 ≤ Open.pRank 2 Q) :
    ∃ U : Subgroup G, U ≤ Q ∧ Open.IsElemAbelian 2 U ∧ Nat.card U = 4 := by
  obtain ⟨E, hEQ, hE, hcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 2 Nat.prime_two Q
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 2 ∣ Nat.card E := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 h
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 hdvd
  refine ⟨V.map E.subtype, (Subgroup.map_subtype_le V).trans hEQ, ?_, ?_⟩
  · exact isElemAbelian_mono (Subgroup.map_subtype_le V) hE
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hV]
    norm_num

end CoreAux

open CoreAux

structure SylowShape (n : ℕ) {K : Type} [Group K] [Finite K] (S : Subgroup K) : Prop where
  card : Nat.card S = if n ≤ 9 then 128 else 256
  rank : Open.pRank 2 S = 4
  four_in_E8 : ∀ U : Subgroup K, U ≤ S → Open.IsElemAbelian 2 U → Nat.card U = 4 →
    ∃ E : Subgroup K, E ≤ S ∧ Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E
  connected : ∀ U V : FourSub S, Relation.ReflTransGen (FourAdj S) U V
  half : ∃ y ∈ S, orderOf y = 2 ∧ (¬ ∀ s ∈ S, s * y = y * s) ∧
    ∃ R : Subgroup K, R ≤ S ∧ (∀ r ∈ R, r * y = y * r) ∧ Nat.card R * 2 = Nat.card S

theorem SylowShape.of_mulEquiv {n : ℕ} {K K' : Type} [Group K] [Group K'] [Finite K] [Finite K']
    {S : Subgroup K} {S' : Subgroup K'} (e : ↥S ≃* ↥S') (h : SylowShape n S) :
    SylowShape n S' where
  card := by rw [← h.card]; exact Nat.card_congr e.symm.toEquiv
  rank := by
    rw [← h.rank]
    exact CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 2 Nat.prime_two S' S
      e.symm
  four_in_E8 := by
    intro U hUS hUab hU4
    have h0 : shapeMap e.symm U ≤ S := shapeMap_le e.symm U
    obtain ⟨E₀, hE₀S, hE₀ab, hE₀8, hUE₀⟩ := h.four_in_E8 (shapeMap e.symm U) h0
      (isElemAbelian_shapeMap e.symm hUab) (by rw [card_shapeMap e.symm hUS, hU4])
    refine ⟨shapeMap e E₀, shapeMap_le e E₀, isElemAbelian_shapeMap e hE₀ab, ?_, ?_⟩
    · rw [card_shapeMap e hE₀S]
      exact hE₀8
    · rw [← shapeMap_shapeMap_symm e hUS]
      exact shapeMap_mono e hUE₀
  connected := by
    let ι : FourSub S' → FourSub S := fun V =>
      ⟨shapeMap e.symm V.1, shapeMap_le e.symm _, isElemAbelian_shapeMap e.symm V.2.2.1,
        by rw [card_shapeMap e.symm V.2.1, V.2.2.2]⟩
    let κ : FourSub S → FourSub S' := fun V =>
      ⟨shapeMap e V.1, shapeMap_le e _, isElemAbelian_shapeMap e V.2.2.1,
        by rw [card_shapeMap e V.2.1, V.2.2.2]⟩
    have hκι : ∀ V : FourSub S', κ (ι V) = V := fun V =>
      Subtype.ext (shapeMap_shapeMap_symm e V.2.1)
    have hκ : ∀ U V : FourSub S, FourAdj S U V → FourAdj S' (κ U) (κ V) := by
      rintro U V ⟨E, hES, hEab, hE8, hUE, hVE⟩
      exact ⟨shapeMap e E, shapeMap_le e E, isElemAbelian_shapeMap e hEab,
        by rw [card_shapeMap e hES]; exact hE8, shapeMap_mono e hUE, shapeMap_mono e hVE⟩
    intro V W
    have : Relation.ReflTransGen (FourAdj S') (κ (ι V)) (κ (ι W)) :=
      Relation.ReflTransGen.lift κ hκ _ _ (h.connected (ι V) (ι W))
    rwa [hκι, hκι] at this
  half := by
    obtain ⟨y, hyS, hy2, hnc, R, hRS, hRy, hRc⟩ := h.half
    refine ⟨((e ⟨y, hyS⟩ : ↥S') : K'), (e ⟨y, hyS⟩).2, ?_, ?_, shapeMap e R, shapeMap_le e R, ?_,
      ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
    · intro hall
      apply hnc
      intro s hs
      have h1 := hall ((e ⟨s, hs⟩ : ↥S') : K') (e ⟨s, hs⟩).2
      have h2 : e ⟨s, hs⟩ * e ⟨y, hyS⟩ = e ⟨y, hyS⟩ * e ⟨s, hs⟩ := Subtype.ext h1
      have h3 : (⟨s, hs⟩ : ↥S) * ⟨y, hyS⟩ = ⟨y, hyS⟩ * ⟨s, hs⟩ := by
        apply e.injective
        rw [map_mul, map_mul, h2]
      exact congrArg Subtype.val h3
    · intro r' hr'
      obtain ⟨r, hr, rfl⟩ := mem_shapeMap.mp hr'
      have h3 : r * (⟨y, hyS⟩ : ↥S) = ⟨y, hyS⟩ * r := Subtype.ext (hRy _ hr)
      rw [← Subgroup.coe_mul, ← map_mul, h3, map_mul, Subgroup.coe_mul]
    · have hS : Nat.card S' = Nat.card S := Nat.card_congr e.symm.toEquiv
      rw [card_shapeMap e hRS, hRc, hS]

theorem CoverSylowData.shape {n : ℕ} (hn : 8 ≤ n) (hD : CoverSylowData n) {K : Type} [Group K]
    [Finite K] (hK : IsDoubleCoverOfAlt K n) (S : Sylow 2 K) :
    SylowShape n (S : Subgroup K) where
  card := hD.card K hK S
  rank := hD.rank K hK S
  four_in_E8 := hD.four_in_E8 K hK S
  connected := hD.connected K hK S
  half := by
    obtain ⟨y, hyS, hy2, hyc, hidx⟩ := hD.half_centralizer K hK S
    refine ⟨y, hyS, hy2, ?_, centralizer ({y} : Set K) ⊓ (S : Subgroup K), inf_le_right, ?_, ?_⟩
    · intro hall
      apply hyc
      have hw2 : y * y = 1 := by
        rw [← pow_two]
        exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hy2)
      exact mem_center_of_mem_center_sylow hn hK S (fun s hs => hall s hs) hw2
    · intro r hr
      exact mem_centralizer_singleton_iff.mp hr.1
    · have h1 := Subgroup.card_mul_index
        ((centralizer ({y} : Set K)).subgroupOf (S : Subgroup K))
      rw [hidx] at h1
      rw [← h1]
      congr 1
      rw [← Subgroup.inf_subgroupOf_right]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem sylowShape_of_hasSylowTwoTypeAhat {n : ℕ} (hn : 8 ≤ n) (hD : CoverSylowData n)
    {G : Type} [Group G] [Finite G] (h : HasSylowTwoTypeAhat G n) (P : Sylow 2 G) :
    SylowShape n (P : Subgroup G) := by
  obtain ⟨X, _, hX, P', Q, ⟨e⟩⟩ := h
  have := finite_of_doubleCover hX
  have e2 : ↥(P : Subgroup G) ≃* ↥(Q : Subgroup X) := (Sylow.equiv P P').trans e
  exact (hD.shape hn hX Q).of_mulEquiv e2.symm

end CFSG.OddStandard.Solomon75
