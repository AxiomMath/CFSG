module

public import CFSG.Goldschmidt.Steps.G63Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Elem
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def RkAut (p : ℕ) (J : Type) [Group J] : Prop :=
  ∀ β : MulAut J, β ^ p = 1 → ∃ E : Subgroup J, IsElemAbelian p E ∧
    p ^ 2 * Nat.card (Subgroup.center J) ≤ Nat.card E ∧ ∀ e ∈ E, β e = e

section RankLemma

variable {Y : Type} [Group Y] [Finite Y]

theorem sq_le_autOrderIn_of_rkAut {p : ℕ} (hp : p.Prime) {J B : Subgroup Y}
    (hB : IsSCp p ⊤ B) (hBN : B ≤ Subgroup.normalizer (J : Set Y)) (hrk : RkAut p ↥J) :
    p ^ 2 ≤ autOrderIn B J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := hB.2.1
  by_contra hlt
  push Not at hlt
  set N := Subgroup.normalizer (J : Set Y) with hNdef
  set φ : ↥N →* MulAut ↥J := J.normalizerMonoidHom with hφ
  set A : Subgroup (MulAut ↥J) := (B.subgroupOf N).map φ with hAdef
  have hrelB : (Subgroup.centralizer (J : Set Y)).relIndex B = autOrderIn B J := by
    unfold autOrderIn
    rw [inf_of_le_left hBN]
  have hcardA : Nat.card A = autOrderIn B J := by
    rw [hAdef, ← Subgroup.relIndex_ker, hφ, Subgroup.normalizerMonoidHom_ker,
      Subgroup.relIndex_subgroupOf hBN]
    exact hrelB
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hBel hBN
  have hr1 : r ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right hp.pos h
    omega
  have hAcyc : IsCyclic A := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr1 with h0 | h1
    · have hc1 : Nat.card A = 1 := by rw [hcardA, hr, h0]; simp
      haveI : Subsingleton A := (Nat.card_eq_one_iff_unique.1 hc1).1
      exact isCyclic_of_subsingleton
    · have hcp : Nat.card A = p := by rw [hcardA, hr, h1]; simp
      exact isCyclic_of_prime_card hcp
  obtain ⟨β₀, hβ₀⟩ := hAcyc.exists_generator
  have hβ₀p : ((β₀ : MulAut ↥J)) ^ p = 1 := by
    have h1 : β₀ ^ p = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      refine (orderOf_dvd_natCard β₀).trans ?_
      rw [hcardA, hr]
      simpa using pow_dvd_pow p hr1
    have h2 := congrArg (fun x : A => (x : MulAut ↥J)) h1
    simpa using h2
  obtain ⟨E, hEel, hEcard, hEfix⟩ := hrk (β₀ : MulAut ↥J) hβ₀p
  have hAfix : ∀ α ∈ A, ∀ e ∈ E, α e = e := by
    intro α hα e he
    have hstab : Subgroup.zpowers (β₀ : MulAut ↥J) ≤ MulAction.stabilizer (MulAut ↥J) e := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hEfix e he
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hβ₀ ⟨α, hα⟩)
    have hαn : (β₀ : MulAut ↥J) ^ n = α := by
      have := congrArg (fun x : A => (x : MulAut ↥J)) hn
      simpa using this
    have hmem : α ∈ MulAction.stabilizer (MulAut ↥J) e := by
      rw [← hαn]
      exact hstab (Subgroup.zpow_mem_zpowers _ _)
    exact MulAction.mem_stabilizer_iff.1 hmem
  set E' : Subgroup Y := E.map J.subtype with hE'
  have hE'J : E' ≤ J := Subgroup.map_subtype_le E
  have hE'el : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hEel J.subtype
  have hE'card : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective J.subtype_injective
  have hcomm : ∀ x ∈ B, ∀ e ∈ E', x * e = e * x := by
    intro x hx e he
    obtain ⟨e', he', rfl⟩ := he
    have h1 : φ ⟨x, hBN hx⟩ ∈ A := ⟨⟨x, hBN hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have h2 := hAfix _ h1 e' he'
    have h3 : x * (e' : Y) * x⁻¹ = e' := congrArg Subtype.val h2
    calc x * (e' : Y) = x * e' * x⁻¹ * x := by group
      _ = e' * x := by rw [h3]
  have hsup : IsElemAbelian p (B ⊔ E') :=
    GL83.PiGen.isElemAbelian_sup hBel hE'el (fun b hb z hz => hcomm b hb z hz)
  have hBE : B ⊔ E' = B := hB.2.2 _ le_top hsup le_sup_left
  have hE'B : E' ≤ B := le_sup_right.trans hBE.le
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (J : Set Y)) (K := E')
  have hne : (Subgroup.centralizer (J : Set Y)).relIndex B ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h2 : (Subgroup.centralizer (J : Set Y)).relIndex E' ≤ autOrderIn B J := by
    rw [← hrelB]
    exact Subgroup.relIndex_le_of_le_right hE'B hne
  have h3 : Nat.card (Subgroup.centralizer (J : Set Y) ⊓ E' : Subgroup Y) ≤
      Nat.card (Subgroup.center ↥J) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨x.1, hE'J x.2.2⟩, ?_⟩ : Subgroup.center ↥J)) ?_
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 x.2.1 g g.2)
    · intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : Subgroup.center ↥J => ((z : ↥J) : Y)) hxy
  have hZpos : 0 < Nat.card (Subgroup.center ↥J) := Nat.card_pos
  have h4 : Nat.card E' ≤ autOrderIn B J * Nat.card (Subgroup.center ↥J) := by
    rw [← h1]
    exact Nat.mul_le_mul h2 h3
  have h5 : autOrderIn B J * Nat.card (Subgroup.center ↥J) <
      p ^ 2 * Nat.card (Subgroup.center ↥J) := Nat.mul_lt_mul_of_pos_right hlt hZpos
  have h6 : p ^ 2 * Nat.card (Subgroup.center ↥J) ≤ Nat.card E' := by rw [hE'card]; exact hEcard
  omega

end RankLemma

section NoIsolated

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_sq_of_mem {p : ℕ} (hp : p.Prime)
    (hex : ∃ E₀ : Subgroup G, IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2) {j : G}
    (hj : orderOf j = p) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ p ^ 2 ≤ Nat.card E ∧ j ∈ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, hE₀el, hE₀card⟩ := hex
  have hE₀p : IsPGroup p E₀ := IsPGroup.of_card (n := 2) hE₀card
  obtain ⟨P₀, hP₀⟩ := hE₀p.exists_le_sylow
  have hjp : IsPGroup p (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hj, pow_one])
  obtain ⟨P₁, hP₁⟩ := hjp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P₁
  set E₁ : Subgroup G := E₀.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁P : E₁ ≤ (P₁ : Subgroup G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) (P₀ : Subgroup G) (hP₀ he)
  have hE₁el : IsElemAbelian p E₁ := CFSG.SectionRank.isElemAbelian_map hE₀el _
  have hE₁card : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀card]
  have hjP : j ∈ (P₁ : Subgroup G) := hP₁ (Subgroup.mem_zpowers j)
  have hj1 : j ≠ 1 := fun h => by
    rw [h, orderOf_one] at hj
    exact hp.one_lt.ne hj
  have hjpow : j ^ p = 1 := by rw [← hj]; exact pow_orderOf_eq_one j
  by_cases hcen : ∀ x ∈ (P₁ : Subgroup G), x * j = j * x
  ·
    have hnot : ¬ E₁ ≤ Subgroup.zpowers j := by
      intro h
      have := Subgroup.card_le_of_le h
      rw [hE₁card, Nat.card_zpowers, hj] at this
      have h2 : p ^ 2 = p * p := by ring
      nlinarith [hp.two_le]
    obtain ⟨t, htE, htj⟩ := Set.not_subset.1 hnot
    have htp : t ^ p = 1 := hE₁el.2 t htE
    obtain ⟨hel, hcard⟩ := CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian hp htp hjpow hj1 htj
      (hcen t (hE₁P htE))
    exact ⟨_, hel, hcard.ge, Subgroup.mem_sup_right (Subgroup.mem_zpowers j)⟩
  ·
    push Not at hcen
    obtain ⟨x, hx, hxj⟩ := hcen
    haveI : Nontrivial (P₁ : Subgroup G) :=
      ⟨⟨⟨j, hjP⟩, 1, fun h => hj1 (congrArg Subtype.val h)⟩⟩
    haveI : Nontrivial (Subgroup.center (P₁ : Subgroup G)) := (P₁.isPGroup').center_nontrivial
    have hZpg : IsPGroup p (Subgroup.center (P₁ : Subgroup G)) :=
      (P₁.isPGroup').to_subgroup (Subgroup.center (P₁ : Subgroup G))
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZpg
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 : 1 < Nat.card (Subgroup.center (P₁ : Subgroup G)) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rw [hn, pow_zero] at h1
      exact lt_irrefl _ h1
    have hdvd : p ∣ Nat.card (Subgroup.center (P₁ : Subgroup G)) := by
      rw [hn]; exact dvd_pow_self p hn0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    set ze : G := ((z : (P₁ : Subgroup G)) : G) with hze
    have hzeo : orderOf ze = p := by
      rw [hze, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
    have hze1 : ze ≠ 1 := fun h => by
      rw [h, orderOf_one] at hzeo
      exact hp.one_lt.ne hzeo
    have hzep : ze ^ p = 1 := by rw [← hzeo]; exact pow_orderOf_eq_one ze
    have hzc : ∀ y ∈ (P₁ : Subgroup G), y * ze = ze * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)
    have hjz : j ∉ Subgroup.zpowers ze := by
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
      apply hxj
      rw [← hm]
      exact ((Commute.zpow_right (show Commute x ze from hzc x hx) m).eq)
    obtain ⟨hel, hcard⟩ := CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian hp hjpow hzep hze1 hjz
      (hzc j hjP)
    exact ⟨_, hel, hcard.ge, Subgroup.mem_sup_left (Subgroup.mem_zpowers j)⟩

end NoIsolated

section RkSimple

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem mem_innerAut_of_pow_eq_one' {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hO : Nat.Coprime p (Nat.card (Outer G))) {ψ : MulAut G} (hψ : ψ ^ p = 1) :
    ψ ∈ innerAut G := by
  have h1 : (QuotientGroup.mk ψ : Outer G) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hψ, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk ψ : Outer G) ∣ Nat.gcd p (Nat.card (Outer G)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
  rw [hO, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem rkAut_of_simple {J : Type} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center J = ⊥) (hO : Nat.Coprime p (Nat.card (Outer J)))
    (hex : ∃ E₀ : Subgroup J, IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2) : RkAut p J := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro β hβ
  obtain ⟨j, hj⟩ := mem_innerAut_of_pow_eq_one' hO hβ
  have hcard : Nat.card (Subgroup.center J) = 1 := by rw [hZ]; simp
  by_cases hj1 : j = 1
  · obtain ⟨E₀, h1, h2⟩ := hex
    refine ⟨E₀, h1, ?_, fun e he => ?_⟩
    · rw [hcard, h2]; simp
    · rw [← hj, hj1]; simp
  · have hjp : j ^ p = 1 := by
      have h1 : MulAut.conj (j ^ p) = 1 := by rw [map_pow, hj]; exact hβ
      have h2 : j ^ p ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut J => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * j ^ p = (j ^ p * g * (j ^ p)⁻¹) * j ^ p := by rw [this]
          _ = j ^ p * g := by group
      rw [hZ, Subgroup.mem_bot] at h2
      exact h2
    obtain ⟨E, hE, hEc, hjE⟩ := exists_elemAbelian_sq_of_mem hp hex (orderOf_eq_prime hjp hj1)
    refine ⟨E, hE, by rwa [hcard, mul_one], fun e he => ?_⟩
    rw [← hj, MulAut.conj_apply]
    have hc := congrArg Subtype.val (hE.1.is_comm.comm ⟨j, hjE⟩ ⟨e, he⟩)
    show j * (e : J) * j⁻¹ = e
    calc j * (e : J) * j⁻¹ = (e : J) * j * j⁻¹ := by rw [show j * (e : J) = e * j from hc]
      _ = e := by group

end RkSimple

end CFSG.HardMathSupport.Dickson.I271
