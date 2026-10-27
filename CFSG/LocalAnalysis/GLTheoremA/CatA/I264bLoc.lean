module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section General

variable {S : Type} [Group S] [Finite S]

theorem exists_sub_card_pow {p n : ℕ} (hp : p.Prime) {E : Subgroup S} (hE : IsElemAbelian p E)
    (hcard : p ^ n ≤ Nat.card E) : ∃ E' : Subgroup S, E' ≤ E ∧ Nat.card E' = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  have hn : n ≤ a := by
    rw [ha] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  have hdvd : p ^ n ∣ Nat.card E := by
    rw [ha]
    exact pow_dvd_pow p hn
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨T.map E.subtype, Subgroup.map_subtype_le T, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hT]

theorem conj_injective_of_center_eq_bot {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center M := Subgroup.mem_center_iff.2 fun x => by
    have := congrArg (fun α : MulAut M => α x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem sq_le_card_of_lt {p : ℕ} (hp : p.Prime) {E : Subgroup S} (hE : IsElemAbelian p E)
    (hlt : p < Nat.card E) : p ^ 2 ≤ Nat.card E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  have hp2' := hp.two_le
  have ha2 : 2 ≤ a := by
    by_contra ha'
    push Not at ha'
    interval_cases a
    · rw [pow_zero] at ha
      omega
    · rw [pow_one] at ha
      omega
  rw [ha]
  exact Nat.pow_le_pow_right hp.pos ha2

theorem rankBound_of_localRank_le_one {p : ℕ} (hp : p.Prime)
    (h : CFSG.Assembly.RankThreeEven.localRank p S ≤ 1) :
    ∀ E T : Subgroup S, IsElemAbelian p E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ p := by
  intro E T hE hT2 hT hET
  by_contra hlt
  push Not at hlt
  obtain ⟨E', hE'E, hE'c⟩ := exists_sub_card_pow hp hE (sq_le_card_of_lt hp hE hlt)
  have h2 : 2 ≤ CFSG.Assembly.RankThreeEven.localRank p S :=
    CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer hp hT hT2
      (isElemAbelian_mono hE hE'E) hE'c (hE'E.trans hET)
  omega

theorem rankBound_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (h : ¬ p ^ 2 ∣ Nat.card S) :
    ∀ E T : Subgroup S, IsElemAbelian p E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ p := by
  intro E T hE _ _ _
  by_contra hlt
  push Not at hlt
  have : Fact p.Prime := ⟨hp⟩
  have h2 := sq_le_card_of_lt hp hE hlt
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  have ha2 : 2 ≤ a := by
    rw [ha] at h2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
  apply h
  have : p ^ 2 ∣ Nat.card E := by
    rw [ha]
    exact pow_dvd_pow p ha2
  exact this.trans (Subgroup.card_subgroup_dvd_card E)

theorem card_mulAut_eq_mul_outer {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {n : ℕ}
    (hS : Nat.card S = n) (hnp : ¬ n.Prime) : Nat.card (MulAut S) = n * Nat.card (Outer S) := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h1 | h1
    · exact h1
    · exfalso
      have hc : IsMulCommutative S := Subgroup.center_eq_top_iff.1 h1
      have hp := (@Group.is_simple_iff_prime_card S _ hc).1 inferInstance
      rw [hS] at hp
      exact hnp hp
  have hinner : Nat.card (inner S) = Nat.card S := by
    have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hc : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
        have := congrArg (fun α : MulAut S => α x) hg
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc x * g = g * x * g⁻¹ * g := by rw [this]
          _ = g * x := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact hc
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have hMul := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner S)
  have hOut' : Nat.card (MulAut S ⧸ inner S) = Nat.card (Outer S) := rfl
  rw [hinner, hS, hOut'] at hMul
  rw [hMul, mul_comm]

theorem card_le_mul_card_inf_inner (P : Subgroup (MulAut S)) :
    Nat.card P ≤ Nat.card (Outer S) * Nat.card ↥(P ⊓ inner S) := by
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun α : MulAut S => (α : S → S)) DFunLike.coe_injective
  have hn : (inner S).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have h1 := Subgroup.relIndex_mul_card (H := inner S) (K := P)
  have h2 : (inner S).relIndex P ∣ Nat.card (Outer S) := by
    have := Subgroup.relIndex_dvd_index_of_normal (inner S) P
    rwa [Subgroup.index] at this
  have h3 : (inner S).relIndex P ≤ Nat.card (Outer S) := Nat.le_of_dvd Nat.card_pos h2
  rw [inf_comm] at h1
  calc Nat.card P = (inner S).relIndex P * Nat.card ↥(P ⊓ inner S) := h1.symm
    _ ≤ Nat.card (Outer S) * Nat.card ↥(P ⊓ inner S) := Nat.mul_le_mul_right _ h3

theorem inner_of_pow_eq_one_of_not_dvd_outer {p : ℕ} (hp : p.Prime) (hOut : ¬ p ∣ Nat.card (Outer S))
    (α : MulAut S) (hα : α ^ p = 1) : α ∈ inner S := by
  have h1 : orderOf (QuotientGroup.mk α : Outer S) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hα]
    rfl
  have h2 := orderOf_dvd_natCard (QuotientGroup.mk α : Outer S)
  have h3 : orderOf (QuotientGroup.mk α : Outer S) = 1 := by
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hOut
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)

end General

section Involution

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_orderOf_two_of_isPGroup {T : Subgroup Y} (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥) :
    ∃ t ∈ T, orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hT2.exists_card_eq
  have hjne : j ≠ 0 := by
    rintro rfl
    apply hTne
    rw [Subgroup.eq_bot_iff_card, hj]
    rfl
  have h2U : 2 ∣ Nat.card T := by
    rw [hj]
    exact dvd_pow_self 2 hjne
  haveI : Fintype T := Fintype.ofFinite T
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥T) 2 (by rwa [← Nat.card_eq_fintype_card])
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem not_mem_center_of_orderOf_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y}
    (h : KHyp p K B) {k : ↥K} (hk : orderOf k = 2) : k ∉ Subgroup.center ↥K := by
  intro hz
  have hpg := KD264Z.isPGroup_center_of_pPrimeCore hp h.core
  obtain ⟨j, hj⟩ := hpg ⟨k, hz⟩
  have hord : orderOf (⟨k, hz⟩ : Subgroup.center ↥K) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hk
  have := orderOf_dvd_of_pow_eq_one hj
  rw [hord] at this
  have hdvd : 2 ∣ p ^ j := this
  have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p).symm

end Involution

section Tool3

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem false_of_rank_bound' (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y} (h : KHyp p K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) {S : Type} [Group S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S) (hZ : Subgroup.center S = ⊥) {m r : ℕ}
    (hOut : ∀ P : Subgroup (MulAut S), IsElemAbelian p P → Nat.card P ≤ m * Nat.card ↥(P ⊓ inner S))
    (hS : ∀ E T : Subgroup S, IsElemAbelian p E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ r)
    (hmr : m * r < p ^ 2) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite S := Finite.of_equiv _ e.toEquiv
  have hBK : B ≤ Subgroup.normalizer (K : Set Y) := fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 h.normal]
    exact Subgroup.mem_top g
  let eS : PSimple p K ≃* S := (pSimpleEquiv h.core).trans e
  set ψ := actionHom K B hBK p with hψ
  have hcardψ := card_actionHom hp h hBK
  have hCp : IsPGroup p ↥(B ⊓ Subgroup.centralizer (K : Set Y)) :=
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
  let θ : ↥B →* MulAut S := (MulAut.congr eS).toMonoidHom.comp ψ
  set Bh : Subgroup (MulAut S) := θ.range with hBh
  have hBhcard : Nat.card Bh = Nat.card ψ.range := by
    have : Bh = ψ.range.map (MulAut.congr eS).toMonoidHom := MonoidHom.range_comp (MulAut.congr eS).toMonoidHom ψ
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
  have hcjinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hZ
  set Eb : Subgroup S := Bh.comap (MulAut.conj : S →* MulAut S) with hEb
  have hEbcard : Nat.card Eb = Nat.card ↥(Bh ⊓ inner S) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun s : Eb => (⟨MulAut.conj (s : S), s.2, ⟨s, rfl⟩⟩ : ↥(Bh ⊓ inner S)))
      ⟨fun s t hst => Subtype.ext (hcjinj (congrArg Subtype.val hst)), fun α => ?_⟩)
    obtain ⟨s, hs⟩ := α.2.2
    exact ⟨⟨s, by rw [hEb, Subgroup.mem_comap, hs]; exact α.2.1⟩, Subtype.ext hs⟩
  have hEbel : IsElemAbelian p Eb := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hcjinj
      change MulAut.conj ((a : S) * b) = MulAut.conj ((b : S) * a)
      rw [map_mul, map_mul]
      exact hBhcomm _ a.2 _ b.2
    · apply hcjinj
      rw [map_pow, map_one]
      exact hBhexp _ hx
  obtain ⟨T, hTK, hT2, hTne, hBT⟩ := h.twogrp
  let πK : ↥K →* S := eS.toMonoidHom.comp (chevQuotHom p K)
  set Tb : Subgroup S := (T.subgroupOf K).map πK with hTb
  have hTb2 : IsPGroup 2 Tb := (hT2.comap_subtype).map πK
  have hTbne : Tb ≠ ⊥ := by
    obtain ⟨t, htT, ht2⟩ := exists_orderOf_two_of_isPGroup hT2 hTne
    set k : ↥K := ⟨t, hTK htT⟩ with hk
    have hk2 : orderOf k = 2 := by
      rw [← ht2, ← Subgroup.orderOf_coe]
    have hkc := not_mem_center_of_orderOf_two hp hp2 h hk2
    intro hbot
    have hmem : πK k ∈ Tb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 htT)
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hkc
    have h1 : e (pSimpleEquiv h.core (chevQuotHom p K k)) = 1 := hmem
    rw [pSimpleEquiv_chevQuotHom h.core, ← map_one e] at h1
    exact (QuotientGroup.eq_one_iff k).1 (e.injective h1)
  have key : ∀ s ∈ Eb, ∀ x ∈ Tb, s * x * s⁻¹ ∈ Tb := by
    intro s hs x hx
    obtain ⟨b, hb⟩ : MulAut.conj s ∈ θ.range := hs
    obtain ⟨k, hkT, rfl⟩ := hx
    have h1 : s * πK k * s⁻¹ = (θ b) (πK k) := by
      rw [hb]
      simp [MulAut.conj_apply]
    have h2 : (θ b) (πK k) = πK (K.normalizerMonoidHom ⟨(b : Y), hBK b.2⟩ k) := by
      have h3 := chevAut_chevQuotHom p K ⟨(b : Y), hBK b.2⟩ k
      have hψb : ψ b = chevAut p K ⟨(b : Y), hBK b.2⟩ := actionHom_apply K B hBK p b
      show (MulAut.congr eS (ψ b)) (eS (chevQuotHom p K k)) =
        eS (chevQuotHom p K (K.normalizerMonoidHom ⟨(b : Y), hBK b.2⟩ k))
      rw [hψb]
      simp [MulAut.congr_apply, h3]
    rw [h1, h2]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
    have hkT' : (k : Y) ∈ T := Subgroup.mem_subgroupOf.1 hkT
    have := (Subgroup.mem_normalizer_iff.1 (hBT b.2) (k : Y)).1 hkT'
    exact this
  have hnorm : Eb ≤ Subgroup.normalizer (Tb : Set S) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    refine fun y => ⟨key x hx y, fun hy => ?_⟩
    have := key x⁻¹ (Eb.inv_mem hx) _ hy
    simpa [mul_assoc] using this
  have hle := hS Eb Tb hEbel hTb2 hTbne hnorm
  have hBhle := hOut Bh hBhel
  have hmul : m * Nat.card ↥(Bh ⊓ inner S) ≤ m * r := by
    rw [← hEbcard]
    exact Nat.mul_le_mul_left m hle
  have hfin : p ^ 2 ≤ m * r :=
    calc p ^ 2 ≤ Nat.card ψ.range := hR
      _ = Nat.card Bh := hBhcard.symm
      _ ≤ m * Nat.card ↥(Bh ⊓ inner S) := hBhle
      _ ≤ m * r := hmul
  exact absurd hmr (not_lt.2 hfin)

theorem false_of_rank_bound (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y} (h : KHyp p K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3) {S : Type} [Group S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S) (hZ : Subgroup.center S = ⊥)
    (hOut : ∀ α : MulAut S, α ^ p = 1 → α ∈ inner S)
    (hS : ∀ E T : Subgroup S, IsElemAbelian p E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ p) : False := by
  refine false_of_rank_bound' (m := 1) (r := p) hp hp2 h hc e hZ (fun P hP => ?_) hS ?_
  · have hle : P ≤ inner S := fun α hα => hOut α (hP.2 α hα) 
    rw [inf_eq_left.2 hle, one_mul]
  · rw [one_mul]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

end Tool3

end CFSG.LocalAnalysis.GLTheoremA
