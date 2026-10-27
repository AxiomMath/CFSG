module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526LN
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
import CFSG.Goldschmidt.Steps.G63Basic
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import Certificates.Kernel.ThCent.Leaves
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsH

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

namespace two_le_pRank_centralizer_of_pComponent_aux

theorem pRank_ge_of_commute {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (A : ℕ → Subgroup Y) (m : ℕ)
    (hcomm : ∀ i j, i < m → j < m → i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (hone : ∀ i, i < m → 1 ≤ CFSG.Open.pRank p (A i))
    (hZ : ∀ i, i < m → ∀ x ∈ A i, orderOf x = p → (∀ a ∈ A i, a * x = x * a) → False) :
    ∀ n : ℕ, n ≤ m → n ≤ CFSG.Open.pRank p ((Finset.range n).sup A) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hnm
    have ih' := ih (by omega)
    have hBle : (Finset.range n).sup A ≤ Subgroup.centralizer (A n : Set Y) := by
      refine Finset.sup_le fun i hi => ?_
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hi' := Finset.mem_range.1 hi
      exact hcomm n i (by omega) (by omega) hi'.ne' b hb a ha
    have hc : ∀ a ∈ (Finset.range n).sup A, ∀ b ∈ A n, a * b = b * a := by
      intro a ha b hb
      exact ((Subgroup.mem_centralizer_iff.1 (hBle ha)) b hb).symm
    have hinf : CFSG.Open.pRank p ((Finset.range n).sup A ⊓ A n) = 0 := by
      by_contra hne
      obtain ⟨E, hE, hEA, hEcard⟩ :=
        CFSG.SectionRank.exists_pRank hp.one_lt ((Finset.range n).sup A ⊓ A n)
      have h1 : 1 < Nat.card E := by
        rw [hEcard]
        exact Nat.one_lt_pow hne hp.one_lt
      haveI := Finite.one_lt_card_iff_nontrivial.1 h1
      obtain ⟨⟨x, hxE⟩, hx1⟩ := exists_ne (1 : ↥E)
      have hxp : x ^ p = 1 := hEA.2 x hxE
      have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      refine hZ n (by omega) x (hE hxE).2 (orderOf_eq_prime hxp hx1') ?_
      intro a ha
      exact (Subgroup.mem_centralizer_iff.1 (hBle (hE hxE).1)) a ha
    have key := pRank_add_le_pRank_sup_add_pRank_inf hc hp
    rw [Finset.range_add_one, Finset.sup_insert, sup_comm]
    have := hone n (by omega)
    omega

open scoped IsMulCommutative in
theorem no_central_prime_of_perfect {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hperf : Group.IsPerfect K)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) {z : K} (hz : orderOf z = p)
    (hzc : z ∈ Subgroup.center K) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzp : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨P, hzP⟩ := hzp.exists_le_sylow
  have hcyc : IsCyclic (P : Subgroup K) := by
    by_contra hnc
    obtain ⟨E, -, hE, hcard⟩ :=
      CFSG.Goldschmidt.G63.exists_isElemAbelian_card_sq hp hp2 P.isPGroup' hnc
    have := CFSG.SectionRank.le_pRank hp.one_lt (le_top : E ≤ ⊤) hE hcard
    omega
  haveI : IsMulCommutative (P : Subgroup K) := inferInstance
  have hzPm : z ∈ (P : Subgroup K) := hzP (Subgroup.mem_zpowers z)
  have hT := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup K)) z (fun k g₀ hk => by
    have hc := Subgroup.mem_center_iff.1 (Subgroup.pow_mem (Subgroup.center K) hzc k) g₀⁻¹
    rw [hc, inv_mul_cancel_right])
  have hT1 : MonoidHom.transfer (MonoidHom.id (P : Subgroup K)) z = 1 := by
    have hker : commutator K ≤ (MonoidHom.transfer (MonoidHom.id (P : Subgroup K))).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      simp [commutatorElement_def, mul_comm]
    have : z ∈ commutator K := by
      rw [hperf.commutator_eq_top]
      exact Subgroup.mem_top z
    exact MonoidHom.mem_ker.1 (hker this)
  rw [hT1] at hT
  have h1 : z ^ (P : Subgroup K).index = 1 := by
    have := congrArg Subtype.val hT.symm
    simpa using this
  have h2 : p ∣ (P : Subgroup K).index := by
    have := orderOf_dvd_of_pow_eq_one h1
    rwa [hz] at this
  exact P.not_dvd_index h2

theorem pRank_map_eq_of_ker {H D : Type} [Group H] [Group D] [Finite H] [Finite D] {p : ℕ}
    (hp : p.Prime) (φ : H →* D) (hker : ¬ p ∣ Nat.card φ.ker) (U : Subgroup H) :
    CFSG.Open.pRank p (U.map φ) = CFSG.Open.pRank p U := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp φ hker U) ?_
  obtain ⟨E, hEU, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt U
  have hEp : IsPGroup p E := IsPGroup.iff_card.2 ⟨_, hcard⟩
  have hbot : E ⊓ φ.ker = ⊥ :=
    CFSG.RankThree.PartTwo.Sec4.inf_eq_bot_of_isPGroup_of_not_dvd hp hEp hker
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : (e : H) ∈ φ.ker := he
    have h2 : (e : H) ∈ E ⊓ φ.ker := ⟨e.2, h1⟩
    rw [hbot, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  haveI := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 _ a.2)) hcard _ hinj ?_
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact Subgroup.map_mono hEU

theorem mem_normalizer_of_map_conj_eq {D : Type} [Group D] {K : Subgroup D} {a b : D}
    (h : K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom) :
    b⁻¹ * a ∈ Subgroup.normalizer (K : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : a * x * a⁻¹ ∈ K.map (MulAut.conj a).toMonoidHom := ⟨x, hx, rfl⟩
    rw [h] at h1
    obtain ⟨k, hk, hkx⟩ := h1
    have hkx' : b * k * b⁻¹ = a * x * a⁻¹ := hkx
    have : b⁻¹ * a * x * (b⁻¹ * a)⁻¹ = k := by
      calc b⁻¹ * a * x * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by group
        _ = b⁻¹ * (b * k * b⁻¹) * b := by rw [hkx']
        _ = k := by group
    rw [this]
    exact hk
  · intro hx
    have h1 : b * (b⁻¹ * a * x * (b⁻¹ * a)⁻¹) * b⁻¹ ∈ K.map (MulAut.conj b).toMonoidHom :=
      ⟨_, hx, rfl⟩
    rw [← h] at h1
    obtain ⟨k, hk, hkx⟩ := h1
    have hkx' : a * k * a⁻¹ = b * (b⁻¹ * a * x * (b⁻¹ * a)⁻¹) * b⁻¹ := hkx
    have : a * k * a⁻¹ = a * x * a⁻¹ := by
      rw [hkx']
      group
    have hkx2 : k = x := by
      have := mul_left_cancel (mul_right_cancel this)
      exact this
    rw [← hkx2]
    exact hk

theorem orderSeven_mem_normalizer {H : Type} [Group H] [Finite H] {I : Subgroup H}
    (hIc : CFSG.IsPComponent 7 I) (hI1 : CFSG.Open.pRank 7 I = 1)
    (hH6 : CFSG.Open.pRank 7 (⊤ : Subgroup H) ≤ 6) {e : H} (he : orderOf e = 7) :
    e ∈ Subgroup.normalizer (I : Set H) := by
  haveI hF7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : Nat.Prime 7 := hF7.out
  by_contra hne
  obtain ⟨K, hKc, hIsub, hmap, hmin⟩ := id hIc
  let π : H →* H ⧸ CFSG.pPrimeCore 7 H := QuotientGroup.mk' (CFSG.pPrimeCore 7 H)
  have hker : ¬ 7 ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp7).1 (CFSG.pPrimeCore_coprime_card (p := 7) (G := H))
  have hKrank : CFSG.Open.pRank 7 K = 1 := by
    rw [← hmap]
    exact (pRank_map_eq_of_ker hp7 π hker I).trans hI1
  have hDrank : CFSG.Open.pRank 7 (⊤ : Subgroup (H ⧸ CFSG.pPrimeCore 7 H)) ≤ 6 := by
    have := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp7 π hker (⊤ : Subgroup H)
    rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at this
    omega
  have hē : π e ∉ Subgroup.normalizer (K : Set (H ⧸ CFSG.pPrimeCore 7 H)) := by
    intro h
    apply hne
    apply CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hIc
    rw [hmap]
    exact h
  have he7 : e ^ 7 = 1 := by
    have := pow_orderOf_eq_one e
    rwa [he] at this
  have hπe7 : (π e) ^ 7 = 1 := by
    rw [← map_pow, he7, map_one]
  have hπe1 : π e ≠ 1 := fun h => hē (h ▸ Subgroup.one_mem _)
  have hord : orderOf (π e) = 7 := orderOf_eq_prime hπe7 hπe1
  set g : H ⧸ CFSG.pPrimeCore 7 H := π e with hg
  let A : ℕ → Subgroup (H ⧸ CFSG.pPrimeCore 7 H) := fun i => K.map (MulAut.conj (g ^ i)).toMonoidHom
  have hAc : ∀ i, CFSG.IsComponent (A i) := fun i =>
    CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent (MulAut.conj (g ^ i)) hKc
  have hArank : ∀ i, CFSG.Open.pRank 7 (A i) = 1 := fun i => by
    show CFSG.Open.pRank 7 (K.map (MulAut.conj (g ^ i)).toMonoidHom) = 1
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 7
      (MulAut.conj (g ^ i)).injective, hKrank]
  have hnotN : ∀ m : ℕ, 0 < m → m < 7 → g ^ m ∉ Subgroup.normalizer (K : Set _) := by
    intro m hm0 hm7 h
    apply hē
    have hgcd : m.gcd (orderOf g) = 1 := by
      rw [hord]
      exact ((Nat.Prime.coprime_iff_not_dvd hp7).2 (Nat.not_dvd_of_pos_of_lt hm0 hm7)).symm
    have : g ∈ Subgroup.zpowers (g ^ m) := mem_zpowers_pow_iff.2 hgcd
    exact (Subgroup.zpowers_le.2 h) this
  have hdist : ∀ a b : ℕ, a < b → b < 7 → A a ≠ A b := by
    intro a b hab hb7 heq
    have h := mem_normalizer_of_map_conj_eq heq
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab.le
    have h2 : g ^ c ∈ Subgroup.normalizer (K : Set _) := by
      have : ((g ^ (a + c))⁻¹ * g ^ a)⁻¹ = g ^ c := by
        rw [pow_add]
        group
      rw [← this]
      exact Subgroup.inv_mem _ h
    exact hnotN c (by omega) (by omega) h2
  have hcomm : ∀ i j : ℕ, i < 7 → j < 7 → i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := by
    intro i j hi hj hij a ha b hb
    have hne' : A i ≠ A j := by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact hdist i j h (by omega)
      · exact (hdist j i h (by omega)).symm
    have hc := kComp_holds.1 _ (A i) (A j) ((CFSG.isComponent_iff_open _).1 (hAc i))
      ((CFSG.isComponent_iff_open _).1 (hAc j)) hne'
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc ha
    exact ((Subgroup.mem_centralizer_iff.1 h1) b hb).symm
  have hone : ∀ i, i < 7 → 1 ≤ CFSG.Open.pRank 7 (A i) := fun i _ => (hArank i).ge
  have hZ : ∀ i, i < 7 → ∀ x ∈ A i, orderOf x = 7 → (∀ a ∈ A i, a * x = x * a) → False := by
    intro i _ x hx hxo hxc
    refine no_central_prime_of_perfect hp7 (by norm_num) (hAc i).1.1 ?_
      (z := (⟨x, hx⟩ : ↥(A i))) ?_ ?_
    · exact ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 7) (A i)).symm.le).trans
        (hArank i).le
    · rw [Subgroup.orderOf_mk]
      exact hxo
    · rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (hxc a a.2)
  have h4 := pRank_ge_of_commute hp7 A 7 hcomm hone hZ 7 le_rfl
  have h5 : CFSG.Open.pRank 7 ((Finset.range 7).sup A) ≤
      CFSG.Open.pRank 7 (⊤ : Subgroup (H ⧸ CFSG.pPrimeCore 7 H)) :=
    CFSG.SectionRank.pRank_mono hp7.one_lt le_top
  omega

theorem exists_mul_mem_normalizer_sylow {X : Type} [Group X] [Finite X] {I Q : Subgroup X}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) {e : X}
    (heN : e ∈ Subgroup.normalizer (I : Set X)) :
    ∃ j ∈ I, e * j ∈ Subgroup.normalizer (Q : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q', rfl⟩ := hQ
  let Γ : Subgroup X := Subgroup.normalizer (I : Set X)
  have hIΓ : I ≤ Γ := Subgroup.le_normalizer
  let N : Subgroup ↥Γ := I.subgroupOf Γ
  haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hIΓ).2 le_rfl
  let e₀ : ↥N ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIΓ
  have hsurj : Function.Surjective e₀.symm.toMonoidHom := e₀.symm.surjective
  let P'' : Sylow 3 ↥N := Q'.mapSurjective hsurj
  have hfr := Sylow.normalizer_sup_eq_top P''
  have hmem : (⟨e, heN⟩ : ↥Γ) ∈
      Subgroup.normalizer (((P'' : Subgroup ↥N).map N.subtype : Subgroup ↥Γ) : Set ↥Γ) ⊔ N := by
    rw [hfr]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, m, hm, hhm⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hS : ((P'' : Subgroup ↥N).map N.subtype).map Γ.subtype =
      (Q' : Subgroup ↥I).map I.subtype := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    refine congrArg (fun f => Subgroup.map f (Q' : Subgroup ↥I)) ?_
    ext x
    rfl
  refine ⟨((m : ↥Γ) : X)⁻¹, ?_, ?_⟩
  · exact I.inv_mem hm
  · have hhe : e * ((m : ↥Γ) : X)⁻¹ = (h : X) := by
      have := congrArg (fun z : ↥Γ => (z : X)) hhm
      simp only [Subgroup.coe_mul] at this
      rw [← this]
      group
    rw [hhe, Subgroup.mem_normalizer_iff]
    intro x
    rw [← hS]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h * y * h⁻¹, (Subgroup.mem_normalizer_iff.1 hh y).1 hy, rfl⟩
    · rintro ⟨y', hy', hy'x⟩
      have hy'x' : (y' : X) = (h : X) * x * (h : X)⁻¹ := hy'x
      refine ⟨h⁻¹ * y' * h, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.1 hh (h⁻¹ * y' * h)).2 ?_
        rw [show h * (h⁻¹ * y' * h) * h⁻¹ = y' by group]
        exact hy'
      · show ((h⁻¹ * y' * h : ↥Γ) : X) = x
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hy'x']
        group

theorem exists_order_seven_normalizer {X : Type} [Group X] [Finite X] {I Q C : Subgroup X}
    (hIC : I ≤ C) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) {e : X} (heC : e ∈ C)
    (heN : e ∈ Subgroup.normalizer (I : Set X)) (he : orderOf e = 7) (heI : e ∉ I) :
    ∃ y ∈ C, orderOf y = 7 ∧ y ∈ Subgroup.normalizer (Q : Set X) := by
  have hp7 : Nat.Prime 7 := by norm_num
  obtain ⟨j, hjI, hy⟩ := exists_mul_mem_normalizer_sylow hQ heN
  have hy'C : e * j ∈ C := C.mul_mem heC (hIC hjI)
  have hpow : ∀ k : ℕ, ∃ jk ∈ I, (e * j) ^ k = e ^ k * jk := by
    intro k
    induction k with
    | zero => exact ⟨1, I.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨jk, hjk, h⟩ := ih
      have h1 : e⁻¹ * jk * e⁻¹⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ heN) jk).1 hjk
      rw [inv_inv] at h1
      refine ⟨(e⁻¹ * jk * e) * j, I.mul_mem h1 hjI, ?_⟩
      rw [pow_succ, h, pow_succ]
      group
  have h7 : 7 ∣ orderOf (e * j) := by
    by_contra hnd
    obtain ⟨jm, hjm, hm⟩ := hpow (orderOf (e * j))
    rw [pow_orderOf_eq_one] at hm
    have hem : e ^ orderOf (e * j) = jm⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact (mul_eq_one_iff_eq_inv.1 hm.symm).symm ▸ (by simp)
    have hgcd : (orderOf (e * j)).gcd (orderOf e) = 1 := by
      rw [he]
      exact ((Nat.Prime.coprime_iff_not_dvd hp7).2 hnd).symm
    have hez : e ∈ Subgroup.zpowers (e ^ orderOf (e * j)) := mem_zpowers_pow_iff.2 hgcd
    apply heI
    have : e ^ orderOf (e * j) ∈ I := by
      rw [hem]
      exact I.inv_mem hjm
    exact (Subgroup.zpowers_le.2 this) hez
  refine ⟨(e * j) ^ (orderOf (e * j) / 7), C.pow_mem hy'C _, ?_, Subgroup.pow_mem _ hy _⟩
  exact orderOf_pow_orderOf_div (orderOf_pos _).ne' h7

theorem card_modEq_fixed_seven {S : Type} [Finite S] (f : S → S) (hf : ∀ x, f^[7] x = x) :
    Nat.card S ≡ Nat.card {x : S | f x = x} [MOD 7] := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI := Fintype.ofFinite S
  classical
  have key := Equiv.Perm.card_fixedPoints_modEq (α := S) (f := (f : Function.End S)) (p := 7)
    (n := 1) (by
      funext x
      show f^[7 ^ 1] x = x
      rw [pow_one]
      exact hf x)
  have h1 : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  have h2 : Nat.card {x : S | f x = x} = Fintype.card ↥(Function.fixedPoints f) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [h1, h2]
  exact key

theorem mulAut_eq_one_of_card_le {Z : Type} [Group Z] [Finite Z] (hZ : IsPGroup 3 Z)
    (hcard : Nat.card Z ≤ 3 ^ 5) {β : MulAut Z} (hβ : β ^ 7 = 1) : β = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ (n : ℕ) (z : Z), (⇑β)^[n] z = (β ^ n) z := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih z, pow_succ']
      rfl
  have hβ7 : ∀ z : Z, (⇑β)^[7] z = z := by
    intro z
    rw [hpow, hβ]
    rfl
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hZ
  have ha5 : a ≤ 5 := by
    have : 3 ^ a ≤ 3 ^ 5 := ha ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  let F : Subgroup Z := MonoidHom.eqLocus (β : Z →* Z) (MonoidHom.id Z)
  have hFmem : ∀ x, x ∈ F ↔ β x = x := fun x => Iff.rfl
  obtain ⟨c, hc⟩ : ∃ c, Nat.card F = 3 ^ c := by
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (ha ▸ Subgroup.card_subgroup_dvd_card F)
    exact ⟨c, hc⟩
  have hmod := card_modEq_fixed_seven (⇑β) hβ7
  have hFset : Nat.card {x : Z | β x = x} = Nat.card F := rfl
  rw [hFset, hc, ha] at hmod
  have hca : c ≤ a := by
    have : 3 ^ c ≤ 3 ^ a :=
      ha ▸ hc ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card F)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hca' : c = a := by
    interval_cases a <;> interval_cases c <;> simp [Nat.ModEq] at hmod ⊢
  have hFtop : F = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hc, ha, hca']
  refine MulEquiv.ext fun z => ?_
  rw [MulAut.one_apply]
  exact (hFmem z).1 (hFtop ▸ Subgroup.mem_top z)

theorem mulAut_eq_one_of_pRank_le_two {P : Type} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup P) ≤ 2) {α : MulAut P} (hα : α ^ 7 = 1) :
    α = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hnt : Nontrivial P
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact MulEquiv.ext fun x => Subsingleton.elim _ _
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ :=
    CFSG.SectionRank.Ccomm.supercritical_witness (by norm_num : (3 : ℕ) ≠ 2) hP
  haveI := hDc
  have hDp : IsPGroup 3 D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ 3 = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDrank : CFSG.Open.pRank 3 (⊤ : Subgroup D) ≤ 2 := by
    rw [← CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 3
      D.subtype_injective]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hrank
  have hWcard : Nat.card (D ⧸ frattini D) ≤ 3 ^ 2 :=
    (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hDp hDexp' hDrank).2
  have hσ : CFSG.SectionRank.Ccomm.frattiniAction D α = 1 := by
    refine mulAut_eq_one_of_card_le (hDp.to_quotient _)
      (hWcard.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))) ?_
    rw [← map_pow, hα, map_one]
  have hmem : α ∈ (CFSG.SectionRank.Ccomm.frattiniAction D).ker := hσ
  obtain ⟨k, hk⟩ := hker ⟨α, hmem⟩
  have hk' : α ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf α ∣ 7 := orderOf_dvd_of_pow_eq_one hα
  have h2 : orderOf α ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf α ∣ Nat.gcd 7 (3 ^ k) := Nat.dvd_gcd h1 h2
  have hcop : Nat.gcd 7 (3 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  rw [hcop] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem exists_order_seven_not_mem {X : Type} [Group X] [Finite X] {C I : Subgroup X}
    (hC : 2 ≤ CFSG.Open.pRank 7 C) (hI1 : CFSG.Open.pRank 7 I ≤ 1) :
    ∃ e ∈ C, orderOf e = 7 ∧ e ∉ I := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E, hEC, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 7) C
  by_contra hcon
  push Not at hcon
  have hEI : E ≤ I := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact I.one_mem
    · exact hcon x (hEC hx) (orderOf_eq_prime (hE.2 x hx) hx1)
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 7) hEI hE hcard
  omega

theorem mem_normalizer_of_subgroupOf {X : Type} [Group X] {C I : Subgroup X} (hI : I ≤ C) {e : X}
    (heC : e ∈ C)
    (h : (⟨e, heC⟩ : ↥C) ∈ Subgroup.normalizer ((I.subgroupOf C : Subgroup ↥C) : Set ↥C)) :
    e ∈ Subgroup.normalizer (I : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro x
  constructor
  · intro hx
    exact (h ⟨x, hI hx⟩).1 hx
  · intro hx
    have hxC : x ∈ C := by
      have h1 : e * x * e⁻¹ ∈ C := hI hx
      have h2 := C.mul_mem (C.mul_mem (C.inv_mem heC) h1) heC
      simpa [mul_assoc] using h2
    exact (h ⟨x, hxC⟩).2 hx

theorem mem_centralizer_of_order_seven {X : Type} [Group X] [Finite X]
    {Q : Subgroup X} (hQ3 : IsPGroup 3 Q) (hQ2 : CFSG.Open.pRank 3 Q ≤ 2) {y : X}
    (hy : orderOf y = 7) (hyN : y ∈ Subgroup.normalizer (Q : Set X)) :
    y ∈ Subgroup.centralizer (Q : Set X) := by
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Q) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Q]
    exact hQ2
  let g : ↥(Subgroup.normalizer (Q : Set X)) := ⟨y, hyN⟩
  have hg7 : g ^ 7 = 1 := by
    apply Subtype.ext
    have h7 : y ^ 7 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy] at this
    simpa using h7
  have hα1 : Q.normalizerMonoidHom g = 1 := by
    refine mulAut_eq_one_of_pRank_le_two hQ3 hrk ?_
    rw [← map_pow, hg7, map_one]
  have hker : g ∈ Q.normalizerMonoidHom.ker := hα1
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact Subgroup.mem_subgroupOf.1 hker

theorem center_barO2_eq_bot (hKSML3 : KSML3) {X : Type} [Group X] [Finite X] {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (h3 : IsLThreeOfExp 1 ↥Ls) : Subgroup.center ↥(barO2 L) = ⊥ := by
  obtain ⟨⟨e1⟩, -, -⟩ := centre_of_lift hX hLs hL
  obtain ⟨-, hZ⟩ := dvd_and_center_of_isLThreeOfExp_one h3
  have hZbot : Subgroup.center ↥Ls = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  have hq : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  rcases h3 with ⟨-, d, q, hq7, hd, ⟨e2⟩⟩ | ⟨h2, -⟩
  · let e3 : (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* (TauCeti.CFSGIndex.lie d).Group :=
      e1.trans ((QuotientGroup.quotientMulEquivOfEq hZbot).trans
        (QuotientGroup.quotientBot.trans e2))
    have := (hKSML3 ↥(barO2 L) hq d ⟨e3⟩ (centre_barO2_odd hL.1)).1 (Or.inr ⟨q, hq7, hd⟩)
    exact Subgroup.eq_bot_of_card_eq _ this
  · omega

theorem two_le_pRank_centralizer_final {X : Type} [Group X] [Finite X] {L Q : Subgroup X}
    (hZ : Subgroup.center ↥(barO2 L) = ⊥) {ℓ : X} (hℓL : ℓ ∈ L) (hℓ7 : orderOf ℓ = 7)
    (hQ3 : IsPGroup 3 Q) (hQC : Q ≤ cMHat L) {y : X} (hy7 : orderOf y = 7) (hyC : y ∈ cMHat L)
    (hyQ : y ∈ Subgroup.centralizer (Q : Set X)) :
    2 ≤ CFSG.Open.pRank 7 (Subgroup.centralizer (Q : Set X)) := by
  haveI hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN7 : ¬ 7 ∣ Nat.card (CFSG.pCore 2 X) := pRank_barO2_eq_aux_notDvdCard (by norm_num) (by norm_num)
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 X) := pRank_barO2_eq_aux_notDvdCard (by norm_num) (by norm_num)
  let π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X)
  have hord : ∀ z : X, orderOf z = 7 → (π z) ^ 7 = 1 ∧ π z ≠ 1 := by
    intro z hz
    have hz7 : z ^ 7 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    refine ⟨by rw [← map_pow, hz7, map_one], fun h => ?_⟩
    have hzN : z ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff z).1 h
    have h1 : orderOf z ∣ Nat.card (CFSG.pCore 2 X) := Subgroup.orderOf_dvd_natCard _ hzN
    rw [hz] at h1
    exact hN7 h1
  obtain ⟨hy7', hy1⟩ := hord y hy7
  obtain ⟨hℓ7', hℓ1⟩ := hord ℓ hℓ7
  have hcomm : π y * π ℓ = π ℓ * π y := by
    have hmem : π y ∈ cMBar L := hyC
    exact ((Subgroup.mem_centralizer_iff.1 hmem) (π ℓ) ⟨ℓ, hℓL, rfl⟩).symm
  have hnot : π y ∉ Subgroup.zpowers (π ℓ) := by
    intro hmem
    have hℓbar : π ℓ ∈ barO2 L := ⟨ℓ, hℓL, rfl⟩
    have hmemL : π y ∈ barO2 L := (Subgroup.zpowers_le.2 hℓbar) hmem
    have hcent : (⟨π y, hmemL⟩ : ↥(barO2 L)) ∈ Subgroup.center ↥(barO2 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hmem' : π y ∈ cMBar L := hyC
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hmem') g.1 g.2)
    rw [hZ, Subgroup.mem_bot] at hcent
    exact hy1 (congrArg Subtype.val hcent)
  obtain ⟨hEel, hEcard⟩ := CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian (p := 7) (by norm_num) hy7' hℓ7' hℓ1 hnot hcomm
  have hlift := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 (CFSG.pCore 2 X)
    hN3 Q hQ3
  have hEle : Subgroup.zpowers (π y) ⊔ Subgroup.zpowers (π ℓ) ≤
      barO2 (Subgroup.centralizer (Q : Set X)) := by
    show _ ≤ (Subgroup.centralizer (Q : Set X)).map π
    rw [hlift]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have := (Subgroup.mem_centralizer_iff.1 hyQ) q hq
      show π q * π y = π y * π q
      rw [← map_mul, ← map_mul, this]
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have hq' : π q ∈ cMBar L := hQC hq
      have := (Subgroup.mem_centralizer_iff.1 hq') (π ℓ) ⟨ℓ, hℓL, rfl⟩
      exact this.symm
  have h2 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 7) hEle hEel hEcard
  have h3 := pRank_barO2_eq_aux_eq (Subgroup.centralizer (Q : Set X)) (q := 7) (by norm_num)
    (by norm_num)
  omega

end two_le_pRank_centralizer_of_pComponent_aux

variable {X : Type} [Group X] [Finite X]

open two_le_pRank_centralizer_of_pComponent_aux in
theorem two_le_pRank_centralizer_of_pComponent_le_six (hKSML3 : KSML3) {T : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (h3 : IsLThreeOfExp 1 ↥Ls) (h7 : CFSG.Open.pRank 7 (⊤ : Subgroup X) ≤ 6)
    (hrank : 1 < CFSG.Open.pRank 7 (cMBar L)) {I Q : Subgroup X} (hI : I ≤ cMHat L)
    (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L))) (hI1 : CFSG.Open.pRank 7 I = 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) (hQ2 : CFSG.Open.pRank 3 Q ≤ 2) :
    2 ≤ CFSG.Open.pRank 7 (Subgroup.centralizer (Q : Set X)) := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hC2 : 2 ≤ CFSG.Open.pRank 7 (cMHat L) := by
    have h1 : barO2 (cMHat L) = cMBar L :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have h2 := pRank_barO2_eq_aux_eq (cMHat L) (q := 7) hp7 (by norm_num)
    rw [h1] at h2
    omega
  obtain ⟨e, heC, he, heI⟩ := exists_order_seven_not_mem hC2 hI1.le
  have heN : e ∈ Subgroup.normalizer (I : Set X) := by
    refine mem_normalizer_of_subgroupOf hI heC ?_
    refine orderSeven_mem_normalizer hIc ?_ ?_ (e := (⟨e, heC⟩ : ↥(cMHat L))) ?_
    · rw [← CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 7
        (cMHat L).subtype_injective, Subgroup.map_subgroupOf_eq_of_le hI]
      exact hI1
    · exact ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 7) (cMHat L)).symm.le).trans
        ((CFSG.SectionRank.pRank_mono hp7.one_lt le_top).trans h7)
    · rw [Subgroup.orderOf_mk]
      exact he
  obtain ⟨y, hyC, hy7, hyN⟩ := exists_order_seven_normalizer hI hQ heC heN he heI
  have hQ3 : IsPGroup 3 Q := hQ.isPGroup
  have hyQ : y ∈ Subgroup.centralizer (Q : Set X) :=
    mem_centralizer_of_order_seven hQ3 hQ2 hy7 hyN
  have hZ := center_barO2_eq_bot hKSML3 hX hLs hL h3
  have hdvd : 7 ∣ Nat.card L := by
    have h168 : Nat.card Ls = 168 := card_eq_of_isLThreeOfExp_one h3
    have := Subgroup.card_map_dvd L (toStar T)
    rw [hL.2, h168] at this
    exact (by norm_num : 7 ∣ 168).trans this
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  obtain ⟨ℓ, hℓ⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 hdvd
  exact two_le_pRank_centralizer_final hZ ℓ.2 (by rw [Subgroup.orderOf_coe]; exact hℓ) hQ3
    (hQ.le.trans hI) hy7 hyC hyQ

theorem two_le_pRank_centralizer_of_pComponent (hKSML3 : KSML3) {T : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (h3 : IsLThreeOfExp 1 ↥Ls) (h7 : CFSG.Open.pRank 7 (⊤ : Subgroup X) ≤ 3)
    (hrank : 1 < CFSG.Open.pRank 7 (cMBar L)) {I Q : Subgroup X} (hI : I ≤ cMHat L)
    (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L))) (hI1 : CFSG.Open.pRank 7 I = 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) (hQ2 : CFSG.Open.pRank 3 Q ≤ 2) :
    2 ≤ CFSG.Open.pRank 7 (Subgroup.centralizer (Q : Set X)) :=
  two_le_pRank_centralizer_of_pComponent_le_six hKSML3 hX hLs hL h3 (h7.trans (by norm_num))
    hrank hI hIc hI1 hQ hQ2

end CFSG.LocalAnalysis.RankThreeUC.S15
