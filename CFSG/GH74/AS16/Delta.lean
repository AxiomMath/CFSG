module

public import CFSG.GH74.AS16.Chain
public import CFSG.GH74.AS16.TightEmb

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

section Aux

variable {G : Type*} [Group G]

theorem map_conj_eq_rightConjugate (K : Subgroup G) (g : G) :
    K.map (MulAut.conj g).toMonoidHom = rightConjugate K g⁻¹ := by
  simp [rightConjugate]

theorem mem_normalizer_rightConjugate (K : Subgroup G) (g x : G) :
    x ∈ normalizer ((rightConjugate K g : Subgroup G) : Set G) ↔
      g * x * g⁻¹ ∈ normalizer (K : Set G) := by
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_eq_self_iff, rightConjugate_mul]
  constructor
  · intro h
    have h1 : rightConjugate (rightConjugate K (g * x)) g⁻¹ =
        rightConjugate (rightConjugate K g) g⁻¹ := by rw [h]
    rwa [rightConjugate_mul, rightConjugate_rightConjugate_inv] at h1
  · intro h
    have h1 : rightConjugate (rightConjugate K (g * x * g⁻¹)) g = rightConjugate K g := by rw [h]
    rwa [rightConjugate_mul, show g * x * g⁻¹ * g = g * x by group] at h1

theorem le_normalizer_inf {R A B : Subgroup G} (hA : R ≤ normalizer (A : Set G))
    (hB : R ≤ normalizer (B : Set G)) : R ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro r hr
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyA, hyB⟩
    exact ⟨(mem_normalizer_iff.mp (hA hr) y).mp hyA, (mem_normalizer_iff.mp (hB hr) y).mp hyB⟩
  · rintro ⟨hyA, hyB⟩
    exact ⟨(mem_normalizer_iff.mp (hA hr) y).mpr hyA, (mem_normalizer_iff.mp (hB hr) y).mpr hyB⟩

variable [Finite G]

theorem card_sup_eq_mul {N R : Subgroup G} (hRN : R ≤ normalizer (N : Set G)) (hNR : N ⊓ R = ⊥) :
    Nat.card ↥(N ⊔ R) = Nat.card N * Nat.card R :=
  le_antisymm (card_sup_le_of_le_normalizer hRN) (card_mul_le_card_sup hNR le_sup_left le_sup_right)

theorem isSylowOf_sup_of_normalizes {N X R : Subgroup G} (hX : IsSylowOf 2 X N)
    (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (N : Set G)) (hRX : R ≤ normalizer (X : Set G))
    (hNR : N ⊓ R = ⊥) : IsSylowOf 2 (X ⊔ R) (N ⊔ R) := by
  have hXN : X ≤ N := hX.le
  have hXR : X ⊓ R = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right R hXN).trans hNR.le)
  have h1 := card_sup_eq_mul hRN hNR
  have h2 := card_sup_eq_mul hRX hXR
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hR0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
  refine isSylowOf_of_card (sup_le_sup_right hXN R) ?_
  rw [h2, h1, Nat.factorization_mul hN0 hR0, Finsupp.add_apply, hX.card_eq, ha,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same, pow_add]

end Aux

section Standard

variable {G : Type} [Group G]

theorem standard_tight {L : Subgroup G} (hS : IsStandardSubgroup L) :
    TightlyEmbedded (centralizer (L : Set G)) :=
  ⟨hS.2.1, hS.2.2.1⟩

theorem centralizer_le_normalizer' (L : Subgroup G) :
    centralizer (L : Set G) ≤ normalizer (L : Set G) :=
  le_normalizer_of_forall_comm (fun _ hk u hu => ((mem_centralizer_iff.mp hk) u hu).symm)

end Standard

section TSide

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

omit [Finite G] in
theorem Pair.le_centralizer (hp : Pair T z L) :
    (T : Subgroup G) ≤ centralizer ({z} : Set G) := fun t ht =>
  mem_centralizer_singleton_iff.mpr (hp.central t ht)

omit [Finite G] in
theorem LNormal.centralizer_le_normalizer (hN : LNormal z L) (hL : L ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  have hnorm := (Subgroup.normal_subgroupOf_iff hL).mp hN
  exact le_normalizer_of_conj_mem (fun c hc l hl => hnorm l c hl hc)

omit [Finite G] in
theorem Pair.le_normalizer (hp : Pair T z L) (hN : LNormal z L) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  hp.le_centralizer.trans (hN.centralizer_le_normalizer hp.isComp.1)

theorem Pair.isSylowOf_normalizer (hp : Pair T z L) (hN : LNormal z L) :
    IsSylowOf 2 (T : Subgroup G) (normalizer (L : Set G)) := by
  have hTop : IsSylowOf 2 (T : Subgroup G) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩
  exact hTop.of_le (hp.le_normalizer hN) le_top

theorem Pair.isSylowOf_TC (hp : Pair T z L) (hN : LNormal z L) (hS : IsStandardSubgroup L) :
    IsSylowOf 2 ((T : Subgroup G) ⊓ centralizer (L : Set G)) (centralizer (L : Set G)) :=
  (hp.isSylowOf_normalizer hN).inf_of_le_normalizer (centralizer_le_normalizer' L)
    hS.2.2.2.1.ge

end TSide

section Delta

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L K' R : Subgroup G}

structure Lemma1642One (T : Sylow 2 G) (L K' R : Subgroup G) : Prop where
  inf_eq_bot : R ⊓ centralizer (L : Set G) = ⊥
  equiv : Nonempty (↥R ≃*
    ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (R : Set G)))
  normalizer_eq_centralizer : ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (R : Set G) =
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G)
  normalizer_eq : ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (R : Set G) =
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (K' : Set G)
  sylow : IsSylowOf 2 (((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (K' : Set G))
    (centralizer (L : Set G) ⊓ normalizer (K' : Set G))
  card_eq : Nat.card ↥R =
    Nat.card ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ normalizer (K' : Set G))

theorem lemma1642_one (hp : Pair T z L) (hN : LNormal z L) (hS : IsStandardSubgroup L)
    (hK' : InDelta (centralizer (L : Set G)) K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hRT : R ≤ (T : Subgroup G)) : Lemma1642One T L K' R := by
  set C : Subgroup G := centralizer (L : Set G) with hC
  obtain ⟨⟨g₀, hg₀⟩, hne, hev⟩ := hK'
  have hK'conj : K' = rightConjugate C g₀⁻¹ := by rw [hg₀, map_conj_eq_rightConjugate]
  have hRK' : R ≤ K' := hR.le.trans inf_le_left
  have hRN : R ≤ normalizer (C : Set G) := hR.le.trans inf_le_right
  have hR2 : IsPGroup 2 R := hR.isPGroup
  have hRne : R ≠ ⊥ := ne_bot_of_isSylowOf_even hR hev
  have htightK' : TightlyEmbedded K' := by
    rw [hK'conj]
    exact tightlyEmbedded_rightConjugate (standard_tight hS) _
  have hg : g₀⁻¹ ∉ normalizer (C : Set G) := fun hgn =>
    hne (by rw [hK'conj]; exact (rightConjugate_eq_self_iff C _).mpr hgn)
  have hodd : Odd (Nat.card ↥(C ⊓ K')) := by
    rw [hK'conj]
    exact (standard_tight hS).2 _ hg
  have hCR : C ⊓ R = ⊥ :=
    two_subgroup_of_odd_eq_bot _ _ (hR2.to_le inf_le_right) hodd (inf_le_inf_left C hRK')
  have hTC := hp.isSylowOf_TC hN hS
  have hRTC : R ≤ normalizer (((T : Subgroup G) ⊓ C : Subgroup G) : Set G) :=
    le_normalizer_inf (hRT.trans le_normalizer) hRN
  have hsylS : IsSylowOf 2 (((T : Subgroup G) ⊓ C) ⊔ R) (C ⊔ R) :=
    isSylowOf_sup_of_normalizes hTC hR2 hRN hRTC hCR
  have hdata : Data77 K' C R (((T : Subgroup G) ⊓ C) ⊔ R) :=
    { tight := htightK'
      conj := ⟨g₀, by rw [hK'conj, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]⟩
      ne := hne.symm
      R_ne := hRne
      R_syl := hR
      S_syl := hsylS
      R_le_S := le_sup_right }
  have hconc := hdata.conclusion
  have hS₀ : (((T : Subgroup G) ⊓ C) ⊔ R) ⊓ C = (T : Subgroup G) ⊓ C := by
    apply le_antisymm
    · intro y hy
      have hmul : (↑(((T : Subgroup G) ⊓ C) ⊔ R) : Set G) =
          (((T : Subgroup G) ⊓ C : Subgroup G) : Set G) * (R : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left _ R hRTC
      have hy1 : y ∈ (((T : Subgroup G) ⊓ C : Subgroup G) : Set G) * (R : Set G) := by
        rw [← hmul]
        exact hy.1
      obtain ⟨t, ht, r, hr, hyr⟩ := hy1
      have hyr' : t * r = y := hyr
      have hrC : r ∈ C ⊓ R := by
        refine ⟨?_, hr⟩
        have : r = t⁻¹ * y := by rw [← hyr']; group
        rw [this]
        exact C.mul_mem (C.inv_mem ht.2) hy.2
      rw [hCR, mem_bot] at hrC
      rw [← hyr', hrC, mul_one]
      exact ht
    · exact le_inf le_sup_left inf_le_right
  have e1 := hconc.normalizer_eq_centralizer
  have e2 := hconc.sylow
  rw [hS₀] at e1 e2
  have e3 := hconc.equiv
  rw [hS₀] at e3
  have hle1 : ((T : Subgroup G) ⊓ C) ⊓ normalizer (R : Set G) ≤
      ((T : Subgroup G) ⊓ C) ⊓ normalizer (K' : Set G) :=
    inf_le_inf_left _ (normalizer_two_subgroup_le K' R htightK' hR2 hRK' hRne)
  have hDeq : ((T : Subgroup G) ⊓ C) ⊓ normalizer (K' : Set G) =
      ((T : Subgroup G) ⊓ C) ⊓ normalizer (R : Set G) :=
    e2.eq_of_le hle1 (inf_le_inf_right _ (inf_le_right : (T : Subgroup G) ⊓ C ≤ C))
      (T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
  have hN_eq := hDeq.symm
  refine ⟨?_, ?_, e1, hN_eq, ?_, ?_⟩
  · rw [inf_comm]
    exact hCR
  · exact ⟨e3.some.symm⟩
  · rw [← hN_eq]
    exact e2
  · rw [← hN_eq]
    exact (Nat.card_congr e3.some.toEquiv).symm

omit [Finite G] in
theorem InDelta.tight {L : Subgroup G} (hS : IsStandardSubgroup L)
    (hK' : InDelta (centralizer (L : Set G)) K') : TightlyEmbedded K' := by
  obtain ⟨⟨g₀, hg₀⟩, -, -⟩ := hK'
  rw [hg₀, map_conj_eq_rightConjugate]
  exact tightlyEmbedded_rightConjugate (standard_tight hS) _

theorem lemma1642_three (hp : Pair T z L) (hN : LNormal z L) (hS : IsStandardSubgroup L)
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hRT : R ≤ (T : Subgroup G)) : K' ⊓ (T : Subgroup G) = R :=
  hR.eq_of_le (le_inf (hR.le.trans inf_le_left) hRT)
    (inf_le_inf_left K' ((hp.le_normalizer hN).trans hS.2.2.2.1.ge))
    (T.isPGroup'.to_le inf_le_right)

theorem lemma1642_four (hp : Pair T z L) (hN : LNormal z L) (hS : IsStandardSubgroup L)
    (hK' : InDelta (centralizer (L : Set G)) K') :
    ∃ g : G, K' = rightConjugate (centralizer (L : Set G)) g ∧
      (T : Subgroup G) ⊓ normalizer (K' : Set G) ≤ rightConjugate (T : Subgroup G) g := by
  obtain ⟨⟨g₀, hg₀⟩, -, -⟩ := hK'
  have hK'conj : K' = rightConjugate (centralizer (L : Set G)) g₀⁻¹ := by
    rw [hg₀, map_conj_eq_rightConjugate]
  set g₁ := g₀⁻¹ with hg₁
  have hTN : (T : Subgroup G) ≤ normalizer (centralizer (L : Set G) : Set G) :=
    (hp.le_normalizer hN).trans hS.2.2.2.1.ge
  have hTg : rightConjugate (T : Subgroup G) g₁ ≤ normalizer (K' : Set G) := by
    intro x hx
    rw [hK'conj, mem_normalizer_rightConjugate]
    rw [mem_rightConjugate_iff] at hx
    exact hTN hx
  have hTtop : IsSylowOf 2 (T : Subgroup G) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩
  have hTgtop : IsSylowOf 2 (rightConjugate (T : Subgroup G) g₁) ⊤ :=
    isSylowOf_of_card le_top (by rw [rightConjugate_card, hTtop.card_eq])
  have hTgK' : IsSylowOf 2 (rightConjugate (T : Subgroup G) g₁) (normalizer (K' : Set G)) :=
    hTgtop.of_le hTg le_top
  obtain ⟨T', hT', hNT'⟩ := exists_isSylowOf_ge (N := normalizer (K' : Set G))
    (X := (T : Subgroup G) ⊓ normalizer (K' : Set G)) inf_le_right
    (T.isPGroup'.to_le inf_le_left)
  obtain ⟨k, hk, hkconj⟩ := hTgK'.exists_mem_conj hT'
  have hT'eq : T' = rightConjugate (T : Subgroup G) (g₁ * k⁻¹) := by
    ext x
    rw [hkconj x, mem_rightConjugate_iff, mem_rightConjugate_iff]
    simp [mul_assoc]
  refine ⟨g₁ * k⁻¹, ?_, hT'eq ▸ hNT'⟩
  calc K' = rightConjugate K' k⁻¹ :=
        ((rightConjugate_eq_self_iff K' k⁻¹).mpr (inv_mem hk)).symm
    _ = rightConjugate (rightConjugate (centralizer (L : Set G)) g₁) k⁻¹ := by rw [← hK'conj]
    _ = rightConjugate (centralizer (L : Set G)) (g₁ * k⁻¹) := rightConjugate_mul _ _ _

theorem lemma1642_five (hS : IsStandardSubgroup L) (hK' : InDelta (centralizer (L : Set G)) K')
    (hR2 : IsPGroup 2 R) (hRK' : R ≤ K') {X : Subgroup G} (hXR : X ≤ R) (hX : X ≠ ⊥) :
    normalizer (X : Set G) ≤ normalizer (K' : Set G) :=
  normalizer_two_subgroup_le K' X (InDelta.tight hS hK') (hR2.to_le hXR) (hXR.trans hRK') hX

omit [Finite G] in
theorem mem_TC_centralizer (hp : Pair T z L) (hRT : R ≤ (T : Subgroup G)) :
    z ∈ ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G) :=
  ⟨⟨hp.mem_sylow, hp.mem_centralizer⟩, mem_centralizer_iff.mpr
    (fun r hr => hp.central r (hRT hr))⟩

theorem lemma1644_one (hp : Pair T z L) (hN : LNormal z L) (hS : IsStandardSubgroup L)
    (hK' : InDelta (centralizer (L : Set G)) K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hRT : R ≤ (T : Subgroup G)) (hR2 : Nat.card R = 2) :
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G) = zpowers z := by
  have h1 := lemma1642_one hp hN hS hK' hR hRT
  have hzTC := mem_TC_centralizer hp hRT
  have hcard : Nat.card ↥(((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G)) =
      2 := by
    rw [← h1.normalizer_eq_centralizer]
    exact (Nat.card_congr h1.equiv.some.toEquiv).symm.trans hR2
  have hle : zpowers z ≤
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓ centralizer (R : Set G) :=
    zpowers_le.mpr hzTC
  have hz : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, hp.orderOf_eq]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hz])).symm

theorem lemma1652_one (hS : IsStandardSubgroup L) (hK' : InDelta (centralizer (L : Set G)) K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (centralizer (L : Set G) : Set G)))
    (hZ : ∃ x ∈ R, x ≠ 1 ∧ ∀ t ∈ (T : Subgroup G), t * x = x * t) {g : G}
    (hTg : (T : Subgroup G) ⊓ normalizer (K' : Set G) ≤ rightConjugate (T : Subgroup G) g) :
    g ∈ normalizer ((T : Subgroup G) : Set G) := by
  obtain ⟨x, hxR, hx1, hxc⟩ := hZ
  have hRK' : R ≤ K' := hR.le.trans inf_le_left
  have hTN : (T : Subgroup G) ≤ normalizer (K' : Set G) := by
    intro t ht
    have hxN : t ∈ normalizer ((zpowers x : Subgroup G) : Set G) :=
      mem_normalizer_zpowers_of_commute (hxc t ht)
    exact lemma1642_five hS hK' hR.isPGroup hRK' (X := zpowers x) (zpowers_le.mpr hxR)
      (zpowers_ne_bot_of_ne_one hx1) hxN
  have hle : (T : Subgroup G) ≤ rightConjugate (T : Subgroup G) g :=
    fun t ht => hTg ⟨ht, hTN ht⟩
  have heq : (T : Subgroup G) = rightConjugate (T : Subgroup G) g :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  exact (rightConjugate_eq_self_iff _ g).mp heq.symm

end Delta

end CFSG.GH74.AS16
