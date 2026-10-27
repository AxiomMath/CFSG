module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Vac

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

structure T263VHyp (p : ℕ) (S B : Subgroup Ω) : Prop where
  normal : S.Normal
  qs : CFSG.Open.IsQuasisimple ↥S
  core : GLAPPrimeCore p ↥S = ⊥
  elem : CFSG.Open.IsElemAbelian p B
  card : p ^ 4 ≤ Nat.card ↥B
  twogrp : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set Ω)

theorem t263VHyp_of_data {S B : Subgroup Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hB : GLAIsBmax p B) (hp : p.Prime) (h4 : 4 ≤ GLATwoLocalRank p Ω)
    (hT : ∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) :
    T263VHyp p S B := by
  obtain ⟨hBel, hBcard, -, -, -⟩ :
      CFSG.Open.IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p Ω ∧
        ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
  obtain ⟨T, hTne, hT2, hTS, hBT⟩ := hT
  exact ⟨hSn, hSq, hSp, hBel, hBcard ▸ Nat.pow_le_pow_right hp.pos h4, T, hTS, hT2, hTne, hBT⟩

theorem t263_normalizer_of_normal {K : Subgroup Ω} (hK : K.Normal) {g : Ω} :
    g ∈ Subgroup.normalizer (K : Set Ω) :=
  Subgroup.normalizer_eq_top_iff.2 hK ▸ Subgroup.mem_top g

theorem t263_actionHom_eq_one_iff (hp : p.Prime) {S B : Subgroup Ω} (h : T263VHyp p S B) (b : ↥B) :
    actionHom S B (fun g _ => t263_normalizer_of_normal h.normal) p b = 1 ↔
      (b : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
  have hcomp : GLAPComponent p S S := glaPComponent_self_p h.qs h.core
  have hbN : (b : Ω) ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal h.normal
  have := chevAut_eq_one_iff hp hcomp hbN
  rw [← centMod_iff_centralizer h.core hbN]
  exact this

theorem t263_card_actionHom (hp : p.Prime) {S B : Subgroup Ω} (h : T263VHyp p S B)
    (hBK : B ≤ Subgroup.normalizer (S : Set Ω)) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) * Nat.card ↥(actionHom S B hBK p).range =
      Nat.card B := by
  set ψ := actionHom S B hBK p with hψ
  have hmap : ψ.ker.map B.subtype = B ⊓ Subgroup.centralizer (S : Set Ω) := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (t263_actionHom_eq_one_iff hp h x).1 hx⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩, (t263_actionHom_eq_one_iff hp h ⟨g, hgB⟩).2 hgC, rfl⟩
  have hker : Nat.card ψ.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := by
    rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective]
  rw [← hker]
  exact Subgroup.card_ker_mul_card_range ψ

theorem t263_false_of_not_sq_dvd (hp : p.Prime) {S B : Subgroup Ω} (h : T263VHyp p S B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3) {S' : Type} [Group S']
    (e : ↥S ⧸ Subgroup.center ↥S ≃* S') (hS : ¬ p ^ 2 ∣ Nat.card (MulAut S')) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hBK : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ => t263_normalizer_of_normal h.normal
  set ψ := actionHom S B hBK p with hψ
  have hcard := t263_card_actionHom hp h hBK
  have hBp : IsPGroup p ↥B := isPGroup_of_isElemAbelian h.elem
  have hrp : IsPGroup p ↥ψ.range := hBp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := hrp.exists_card_eq
  let eS : PSimple p S ≃* S' := (pSimpleEquiv h.core).trans e
  have hAut : Nat.card (MulAut (PSimple p S)) = Nat.card (MulAut S') :=
    Nat.card_congr (MulAut.congr eS).toEquiv
  have hdvd : p ^ j ∣ Nat.card (MulAut S') := by
    rw [← hAut, ← hj]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    exact hS ((pow_dvd_pow p hj2).trans hdvd)
  have hrange : Nat.card ψ.range ≤ p := by
    rw [hj]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hj1
      _ = p := pow_one p
  have h4 := h.card
  have hCpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := Nat.card_pos
  have hBle : Nat.card B ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := by
    rw [← hcard, mul_comm]
    exact Nat.mul_le_mul_right _ hrange
  have : p ^ 4 ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := h4.trans hBle
  have h3 : p ^ 3 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := by
    have : p * p ^ 3 ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := by
      calc p * p ^ 3 = p ^ 4 := by ring
        _ ≤ _ := this
    exact Nat.le_of_mul_le_mul_left this hp.pos
  omega

theorem t263_not_mem_center_of_orderOf_two (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Ω}
    (hcore : GLAPPrimeCore p ↥S = ⊥) {k : ↥S} (hk : orderOf k = 2) : k ∉ Subgroup.center ↥S := by
  intro hz
  have hpg := KD264Z.isPGroup_center_of_pPrimeCore hp hcore
  obtain ⟨j, hj⟩ := hpg ⟨k, hz⟩
  have hord : orderOf (⟨k, hz⟩ : Subgroup.center ↥S) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hk
  have := orderOf_dvd_of_pow_eq_one hj
  rw [hord] at this
  have hdvd : 2 ∣ p ^ j := this
  have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p).symm

theorem t263_false_of_rank_bound' (hp : p.Prime) (hp2 : p ≠ 2) {S B : Subgroup Ω} (h : T263VHyp p S B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3) {S' : Type} [Group S']
    (e : ↥S ⧸ Subgroup.center ↥S ≃* S') (hZ : Subgroup.center S' = ⊥) {m r : ℕ}
    (hOut : ∀ P : Subgroup (MulAut S'), IsElemAbelian p P → Nat.card P ≤ m * Nat.card ↥(P ⊓ inner S'))
    (hS : ∀ E T : Subgroup S', IsElemAbelian p E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S') → Nat.card E ≤ r)
    (hmr : m * r < p ^ 2) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite S' := Finite.of_equiv _ e.toEquiv
  have hBK : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ => t263_normalizer_of_normal h.normal
  let eS : PSimple p S ≃* S' := (pSimpleEquiv h.core).trans e
  set ψ := actionHom S B hBK p with hψ
  have hcardψ := t263_card_actionHom hp h hBK
  have hCp : IsPGroup p ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono h.elem inf_le_left)
  obtain ⟨j, hj⟩ := hCp.exists_card_eq
  have hj2 : j ≤ 2 := by
    by_contra hj3
    push Not at hj3
    have : p ^ 3 ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj3
    omega
  have hR : p ^ 2 ≤ Nat.card ψ.range := by
    have h4 := h.card
    rw [← hcardψ, hj] at h4
    have : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card ψ.range :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ p ^ j * Nat.card ψ.range := h4
        _ ≤ p ^ 2 * Nat.card ψ.range := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos hj2)
    exact Nat.le_of_mul_le_mul_left this (pow_pos hp.pos 2)
  let θ : ↥B →* MulAut S' := (MulAut.congr eS).toMonoidHom.comp ψ
  set Bh : Subgroup (MulAut S') := θ.range with hBh
  have hBhcard : Nat.card Bh = Nat.card ψ.range := by
    have : Bh = ψ.range.map (MulAut.congr eS).toMonoidHom :=
      MonoidHom.range_comp (MulAut.congr eS).toMonoidHom ψ
    rw [this, Subgroup.card_map_of_injective (MulAut.congr eS).injective]
  have hBhexp : ∀ α ∈ Bh, α ^ p = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ p = 1 := Subtype.ext (by simpa using h.elem.2 v v.2)
    rw [this, map_one]
  have hBhcomm : ∀ α ∈ Bh, ∀ β ∈ Bh, α * β = β * α := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hxy : x * y = y * x := Subtype.ext (isElemAbelian_commute h.elem x.2 y.2)
    rw [← map_mul, ← map_mul, hxy]
  have hBhel : IsElemAbelian p Bh := ⟨⟨⟨fun a b => Subtype.ext (hBhcomm _ a.2 _ b.2)⟩⟩, hBhexp⟩
  have hcjinj : Function.Injective (MulAut.conj : S' →* MulAut S') :=
    conj_injective_of_center_eq_bot hZ
  set Eb : Subgroup S' := Bh.comap (MulAut.conj : S' →* MulAut S') with hEb
  have hEbcard : Nat.card Eb = Nat.card ↥(Bh ⊓ inner S') := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun s : Eb => (⟨MulAut.conj (s : S'), s.2, ⟨s, rfl⟩⟩ : ↥(Bh ⊓ inner S')))
      ⟨fun s t hst => Subtype.ext (hcjinj (congrArg Subtype.val hst)), fun α => ?_⟩)
    obtain ⟨s, hs⟩ := α.2.2
    exact ⟨⟨s, by rw [hEb, Subgroup.mem_comap, hs]; exact α.2.1⟩, Subtype.ext hs⟩
  have hEbel : IsElemAbelian p Eb := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hcjinj
      change MulAut.conj ((a : S') * b) = MulAut.conj ((b : S') * a)
      rw [map_mul, map_mul]
      exact hBhcomm _ a.2 _ b.2
    · apply hcjinj
      rw [map_pow, map_one]
      exact hBhexp _ hx
  obtain ⟨T, hTK, hT2, hTne, hBT⟩ := h.twogrp
  let πK : ↥S →* S' := eS.toMonoidHom.comp (chevQuotHom p S)
  set Tb : Subgroup S' := (T.subgroupOf S).map πK with hTb
  have hTb2 : IsPGroup 2 Tb := (hT2.comap_subtype).map πK
  have hTbne : Tb ≠ ⊥ := by
    obtain ⟨t, htT, ht2⟩ := exists_orderOf_two_of_isPGroup hT2 hTne
    set k : ↥S := ⟨t, hTK htT⟩ with hk
    have hk2 : orderOf k = 2 := by
      rw [← ht2, ← Subgroup.orderOf_coe]
    have hkc := t263_not_mem_center_of_orderOf_two hp hp2 h.core hk2
    intro hbot
    have hmem : πK k ∈ Tb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 htT)
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hkc
    have h1 : e (pSimpleEquiv h.core (chevQuotHom p S k)) = 1 := hmem
    rw [pSimpleEquiv_chevQuotHom h.core, ← map_one e] at h1
    exact (QuotientGroup.eq_one_iff k).1 (e.injective h1)
  have key : ∀ s ∈ Eb, ∀ x ∈ Tb, s * x * s⁻¹ ∈ Tb := by
    intro s hs x hx
    obtain ⟨b, hb⟩ : MulAut.conj s ∈ θ.range := hs
    obtain ⟨k, hkT, rfl⟩ := hx
    have h1 : s * πK k * s⁻¹ = (θ b) (πK k) := by
      rw [hb]
      simp [MulAut.conj_apply]
    have h2 : (θ b) (πK k) = πK (S.normalizerMonoidHom ⟨(b : Ω), hBK b.2⟩ k) := by
      have h3 := chevAut_chevQuotHom p S ⟨(b : Ω), hBK b.2⟩ k
      have hψb : ψ b = chevAut p S ⟨(b : Ω), hBK b.2⟩ := actionHom_apply S B hBK p b
      show (MulAut.congr eS (ψ b)) (eS (chevQuotHom p S k)) =
        eS (chevQuotHom p S (S.normalizerMonoidHom ⟨(b : Ω), hBK b.2⟩ k))
      rw [hψb]
      simp [MulAut.congr_apply, h3]
    rw [h1, h2]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
    have hkT' : (k : Ω) ∈ T := Subgroup.mem_subgroupOf.1 hkT
    have := (Subgroup.mem_normalizer_iff.1 (hBT b.2) (k : Ω)).1 hkT'
    exact this
  have hnorm : Eb ≤ Subgroup.normalizer (Tb : Set S') := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    refine fun y => ⟨key x hx y, fun hy => ?_⟩
    have := key x⁻¹ (Eb.inv_mem hx) _ hy
    simpa [mul_assoc] using this
  have hle := hS Eb Tb hEbel hTb2 hTbne hnorm
  have hBhle := hOut Bh hBhel
  have hmul : m * Nat.card ↥(Bh ⊓ inner S') ≤ m * r := by
    rw [← hEbcard]
    exact Nat.mul_le_mul_left m hle
  have hfin : p ^ 2 ≤ m * r :=
    calc p ^ 2 ≤ Nat.card ψ.range := hR
      _ = Nat.card Bh := hBhcard.symm
      _ ≤ m * Nat.card ↥(Bh ⊓ inner S') := hBhle
      _ ≤ m * r := hmul
  exact absurd hmr (not_lt.2 hfin)

theorem t263_false_of_rank_bound (hp : p.Prime) (hp2 : p ≠ 2) {S B : Subgroup Ω} (h : T263VHyp p S B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3) {S' : Type} [Group S']
    (e : ↥S ⧸ Subgroup.center ↥S ≃* S') (hZ : Subgroup.center S' = ⊥)
    (hOut : ∀ α : MulAut S', α ^ p = 1 → α ∈ inner S')
    (hS : ∀ E T : Subgroup S', IsElemAbelian p E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S') → Nat.card E ≤ p) : False := by
  refine t263_false_of_rank_bound' (m := 1) (r := p) hp hp2 h hc e hZ (fun P hP => ?_) hS ?_
  · have hle : P ≤ inner S' := fun α hα => hOut α (hP.2 α hα)
    rw [inf_eq_left.2 hle, one_mul]
  · rw [one_mul]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

end Vac

@[expose] def T263Vac (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    catalogIs (↥S ⧸ Subgroup.center ↥S) Q →
    (p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1)) →
    GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 → False

theorem t263CaseIx_of_vac {Q : TauCeti.CFSGIndex → Prop} (h : T263Vac Q) : T263CaseIx Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT B₀ hB₀ hdich hCc hB₀c hBc b hb hbB₀
    hfield hlay
  exact (h p hp hp2 Ω S B hSn hSq hSp hQ hF2 hB h4 hT
    (hCc ▸ Nat.pow_lt_pow_right hp.one_lt (by norm_num))).elim

theorem t263Desc_of_vac {Q : TauCeti.CFSGIndex → Prop} (h : T263Vac Q) : T263Desc Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T' hT'ne hT'2 hT'S
    hBT' hker x hxB₀ hxC hxcomm
  exact (h p hp hp2 Ω S B hSn hSq hSp hQ hF2 hB h4 hT hC).elim

end CFSG.LocalAnalysis.GLTheoremA.T263

end
