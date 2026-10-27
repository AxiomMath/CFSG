module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710YBasic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {B T I : Subgroup G}

omit [Finite G] in
theorem xq_isKGroup (hKp : CFSG.Open.IsKProper G) (hY : yOf B T I ≠ ⊤) :
    CFSG.Open.IsKGroup (XQ B T I) := by
  have hW : wOf B T I ≠ ⊤ := fun hW => hY (eq_top_iff.2 (hW ▸ inf_le_right))
  exact isKGroup_of_surjective (piQ B T I) (QuotientGroup.mk'_surjective _)
    (isKGroup_of_isKProper hKp hW)

theorem xq_centralizer_le (h : Setup710 B T I) (hf : YFacts B T I) :
    Subgroup.centralizer (CFSG.Open.pCore 2 (XQ B T I) : Set (XQ B T I)) ≤
      CFSG.Open.pCore 2 (XQ B T I) := by
  classical
  set W := wOf B T I with hW
  set S := sOf B T I with hS
  set Y := yOf B T I with hY
  set Z := zOf B T I with hZ
  set π := piQ B T I with hπ
  set C : Subgroup G := Y ⊓ Subgroup.centralizer (S : Set G) with hC
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS2 : IsPGroup 2 ↥S := hf.sylow.1
  have hSW : S ≤ W := inf_le_left.trans (t_le_wOf h)
  have hSP : S ≤ pOf B T I := inf_le_right
  have hWN : W ≤ Subgroup.normalizer (S : Set G) := inf_le_left
  have hWY : W ≤ Y := inf_le_right
  have hCN : C ≤ Subgroup.normalizer (S : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (S : Set G))
  have hCW : C ≤ W := le_inf hCN inf_le_left
  have hSn : (S.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSW).2 hWN
  have hCn : (C.subgroupOf W).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCW).2 fun g hg => ?_
    exact Sec7.inf_normalizer_le_normalizer_inf _ _
      ⟨Subgroup.le_normalizer hg.2, normalizer_le_normalizer_centralizer _ hg.1⟩
  have hcent : ∀ Q : Subgroup G, Q ≤ C → IsPGroup 2 ↥Q → ∀ c ∈ C, ∀ q ∈ Q, q * c = c * q := by
    intro Q hQC hQ2 c hc q hq
    have hQS : Q ≤ S :=
      le_of_normalizes_sylow hS2 hSP hf.sylow.2 (hQC.trans hf.cent) hQ2 (hQC.trans hCN)
    exact Subgroup.mem_centralizer_iff.1 hc.2 q (hQS hq)
  have hSbn : ((S.subgroupOf W).map π).Normal := hSn.map π hπs
  have hSb2 : IsPGroup 2 ↥((S.subgroupOf W).map π) := hS2.comap_subtype.map π
  have hSb := le_pCore_of_normal hSbn hSb2
  have hCbn : ((C.subgroupOf W).map π).Normal := hCn.map π hπs
  have hCb2 : IsPGroup 2 ↥((C.subgroupOf W).map π) := by
    rintro ⟨_, c, hc, rfl⟩
    obtain ⟨n, hn⟩ := exists_pow_two_mem_primeCore hcent (Subgroup.mem_subgroupOf.1 hc)
    refine ⟨n, Subtype.ext ?_⟩
    have hz : c ^ (2 ^ n) ∈ Z.subgroupOf W := by
      rw [Subgroup.mem_subgroupOf]
      exact hn
    have h1 : π (c ^ (2 ^ n)) = 1 := (QuotientGroup.eq_one_iff _).2 hz
    simpa [map_pow] using h1
  have hCb := le_pCore_of_normal hCbn hCb2
  intro x hx
  have hxSb : x ∈ Subgroup.centralizer (((S.subgroupOf W).map π : Subgroup _) : Set _) :=
    Subgroup.centralizer_le hSb hx
  obtain ⟨g, rfl⟩ := hπs x
  suffices hgC : g ∈ C.subgroupOf W from hCb ⟨g, hgC, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  refine ⟨hWY g.2, ?_⟩
  show g.1 ∈ Subgroup.centralizer (S : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs' : (⟨s, hSW hs⟩ : ↥W) ∈ S.subgroupOf W := hs
  have hcomm := Subgroup.mem_centralizer_iff.1 hxSb (π ⟨s, hSW hs⟩) ⟨_, hs', rfl⟩
  have hmul : π (⟨s, hSW hs⟩ * g) = π (g * ⟨s, hSW hs⟩) := by
    rw [map_mul, map_mul]
    exact hcomm
  have hZ' : ((⟨s, hSW hs⟩ * g)⁻¹ * (g * ⟨s, hSW hs⟩) : ↥W) ∈ Z.subgroupOf W :=
    QuotientGroup.eq.1 hmul
  have hZ'' : (s * g.1)⁻¹ * (g.1 * s) ∈ Z := Subgroup.mem_subgroupOf.1 hZ'
  have hSe : (s * g.1)⁻¹ * (g.1 * s) ∈ S := by
    have h1 : g.1⁻¹ * s⁻¹ * g.1 ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 (hWN (inv_mem g.2)) s⁻¹).1 (inv_mem hs)
      simpa using this
    have h2 : (s * g.1)⁻¹ * (g.1 * s) = (g.1⁻¹ * s⁻¹ * g.1) * s := by group
    rw [h2]
    exact S.mul_mem h1 hs
  have h1 : (s * g.1)⁻¹ * (g.1 * s) = 1 :=
    eq_one_of_mem_two_of_mem_odd hS2 (not_two_dvd_card_zOf B T I) hSe hZ''
  have h2 : s * g.1 = g.1 * s := inv_mul_eq_one.1 h1
  exact h2

omit [Finite G] in
theorem bX_elemAbelian (h : Setup710 B T I) : IsElemAbelian 3 (bX B T I) :=
  CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf h.bElem (wOf B T I)) (piQ B T I)

theorem tX_isMax (h : Setup710 B T I) (hf : YFacts B T I) :
    IsMaxBInvariantTwo (bX B T I) (tX B T I) := by
  classical
  set W := wOf B T I with hW
  set π := piQ B T I with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hBW : B ≤ W := b_le_wOf h
  have hTW : T ≤ W := t_le_wOf h
  set B' : Subgroup ↥W := B.subgroupOf W with hB'
  set T' : Subgroup ↥W := T.subgroupOf W with hT'
  have hT'2 : IsPGroup 2 ↥T' := h.tTwo.comap_subtype
  have hB'3 : IsPGroup 3 ↥B' := fun g => ⟨1, Subtype.ext (Subtype.ext (by simpa using h.bElem.2 g.1.1 g.2))⟩
  have hB'T' : B' ≤ Subgroup.normalizer (T' : Set ↥W) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    exact Subgroup.le_normalizer_iff.1 h.bnT b.1 hb t.1 ht
  refine ⟨hT'2.map π, ?_, ?_⟩
  · rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨b, hb, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨b * t * b⁻¹, Subgroup.le_normalizer_iff.1 hB'T' b hb t ht, by simp⟩
  · intro U hU hbU htU
    refine le_antisymm ?_ htU
    set K' : Subgroup ↥W := U.comap π with hK'
    have hB'K' : B' ≤ Subgroup.normalizer (K' : Set ↥W) := by
      rw [Subgroup.le_normalizer_iff]
      intro b hb y hy
      have hb' : π b ∈ bX B T I := ⟨b, hb, rfl⟩
      have := Subgroup.le_normalizer_iff.1 hbU (π b) hb' (π y) hy
      show π (b * y * b⁻¹) ∈ U
      simpa using this
    have hT'K' : T' ≤ K' := fun t ht => htU ⟨t, ht, rfl⟩
    have h3 : ¬ 3 ∣ Nat.card K' := by
      intro hdvd
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
      have hw3 : (x.1 : ↥W) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
      have hwK : π x.1 ∈ U := x.2
      obtain ⟨n, hn⟩ := hU ⟨π x.1, hwK⟩
      have hn' : (π x.1) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      have hpi3 : (π x.1) ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
      have hord : orderOf (π x.1) = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
          (orderOf_dvd_of_pow_eq_one hpi3) (orderOf_dvd_of_pow_eq_one hn')
      have hpw : π x.1 = 1 := orderOf_eq_one_iff.1 hord
      have hwZ : (x.1 : ↥W) ∈ (zOf B T I).subgroupOf W := (QuotientGroup.eq_one_iff _).1 hpw
      have hwZ' : (x.1 : ↥W).1 ∈ zOf B T I := Subgroup.mem_subgroupOf.1 hwZ
      have hwne : (x.1 : ↥W).1 ≠ 1 := by
        intro h1
        have : x = 1 := Subtype.ext (Subtype.ext h1)
        rw [this, orderOf_one] at hx
        omega
      have hord3 : orderOf (x.1 : ↥W).1 = 3 :=
        orderOf_eq_prime (by simpa using congrArg (fun z : ↥W => z.1) hw3) hwne
      have : 3 ∣ Nat.card (pOf B T I) :=
        hord3 ▸ Subgroup.orderOf_dvd_natCard _ (zOf_le_pOf hf hwZ')
      exact not_three_dvd_card_pOf B T I this
    obtain ⟨Q, hTQ, -, hQ2, hQodd, hQn⟩ := exists_invariant_sylow_containing_of_pGroup
      Nat.prime_three Nat.prime_two hB'3 hB'K' h3 hT'K' hT'2 hB'T'
    have hQT : Q.map W.subtype = T := by
      refine h.tMax _ (hQ2.map _) ?_ ?_
      · rw [Subgroup.le_normalizer_iff]
        rintro b hb _ ⟨q, hq, rfl⟩
        exact ⟨⟨b, hBW hb⟩ * q * ⟨b, hBW hb⟩⁻¹,
          Subgroup.le_normalizer_iff.1 hQn ⟨b, hBW hb⟩ hb q hq, rfl⟩
      · intro t ht
        exact ⟨⟨t, hTW ht⟩, hTQ ht, rfl⟩
    have hQeq : Q = T' := by
      have := congrArg (Subgroup.comap W.subtype) hQT
      rwa [Subgroup.comap_map_eq_self_of_injective W.subtype_injective] at this
    have hsup := le_sup_of_relIndex ((zOf B T I).subgroupOf W) U hU T' (hQeq ▸ hQodd)
    intro u hu
    obtain ⟨w, rfl⟩ := hπs u
    have hw : w ∈ T' ⊔ (zOf B T I).subgroupOf W := hsup hu
    have hmem : π w ∈ (T' ⊔ (zOf B T I).subgroupOf W).map π := ⟨w, hw, rfl⟩
    have hZ0 : ((zOf B T I).subgroupOf W).map π = ⊥ :=
      (Subgroup.map_eq_bot_iff _).2 (by rw [hπ, QuotientGroup.ker_mk'])
    rw [Subgroup.map_sup, hZ0, sup_bot_eq] at hmem
    exact hmem

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
