module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThreeGroup
import CFSG.Goldschmidt.Steps.Sec82PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

private theorem exists_ne_one_mem_centralizer_of_le {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    [Finite H] {S S₀ : Subgroup H} (hSp : IsPGroup p S) (hS₀S : S₀ ≤ S)
    (hn : S ≤ normalizer (S₀ : Set H)) (hS₀1 : S₀ ≠ ⊥) :
    ∃ v ∈ S₀, v ∈ centralizer (S : Set H) ∧ v ≠ 1 := by
  have : Group.IsNilpotent S := hSp.isNilpotent
  have hN : (S₀.subgroupOf S).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have := (mem_normalizer_iff.mp (hn g.2) x).mp hx
    simpa [mem_subgroupOf] using this
  have hne : S₀.subgroupOf S ≠ ⊥ := by
    intro h
    apply hS₀1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hS₀S hx⟩ : S) ∈ S₀.subgroupOf S := hx
    rw [h, mem_bot] at this
    simpa using congrArg Subtype.val this
  obtain ⟨z, hz1⟩ := (ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨((z : S) : H), (mem_inf.1 z.2).1, ?_, fun h => hz1 (Subtype.ext (Subtype.ext h))⟩
  rw [mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.1 z.2).2 ⟨y, hy⟩)

private theorem le_normalizer_inf_of_normal (R C : Subgroup G) [C.Normal] :
    R ≤ normalizer ((R ⊓ C : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨R.mul_mem (R.mul_mem hg h1) (R.inv_mem hg), ‹C.Normal›.conj_mem h h2 g⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := R.mul_mem (R.mul_mem (R.inv_mem hg) h1) hg
      simpa [mul_assoc] using this
    · have := ‹C.Normal›.conj_mem _ h2 g⁻¹
      simpa [mul_assoc] using this

theorem isCyclic_inf_of_forall_mem_zpowers {C R : Subgroup G} [C.Normal] {z x : G}
    (hz : orderOf z = 3) [(zpowers z).Normal]
    (hi : ∀ c ∈ C, c ^ 3 = 1 → ⁅x, c⁆ ∈ zpowers z → c ∈ zpowers z)
    (hR : IsPGroup 3 R) (hxR : x ∈ R) : IsCyclic (R ⊓ C : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnc
  obtain ⟨V, hVRC, hRV, hVc, hVe, -⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le Nat.prime_three (by norm_num) hR
      inf_le_left (le_normalizer_inf_of_normal R C) hnc
  let π := QuotientGroup.mk' (zpowers z)
  have hπ : ∀ g : G, π g = 1 ↔ g ∈ zpowers z := fun g => QuotientGroup.eq_one_iff g
  have hVbar : V.map π ≠ ⊥ := by
    intro h
    have hle : V ≤ zpowers z := by
      intro v hv
      have : π v ∈ V.map π := mem_map_of_mem π hv
      rw [h, mem_bot] at this
      exact (hπ v).1 this
    have := Subgroup.card_dvd_of_le hle
    rw [hVc, Nat.card_zpowers, hz] at this
    norm_num at this
  obtain ⟨vb, hvb, hvbc, hvb1⟩ := exists_ne_one_mem_centralizer_of_le (hR.map π)
    (map_mono (hVRC.trans inf_le_left)) ((map_mono hRV).trans (le_normalizer_map π)) hVbar
  obtain ⟨v, hv, rfl⟩ := mem_map.1 hvb
  have hxv : π x * π v = π v * π x :=
    mem_centralizer_iff.1 hvbc (π x) (mem_map_of_mem π hxR)
  refine hvb1 ((hπ v).2 (hi v (mem_inf.1 (hVRC hv)).2 (hVe v hv) ((hπ _).1 ?_)))
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hxv]

theorem false_of_isSylowOf_zpowers_pow_three {N : Subgroup G} [N.Normal] {f w : G}
    (hf3 : f ^ 3 = 1) (hfN : f ∉ N) (hwf : w * f⁻¹ ∈ N) (hw : IsPGroup 3 (zpowers w))
    (hQ : IsSylowOf 3 (zpowers (w ^ 3)) N) (hw1 : w ^ 3 ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := N ⊔ zpowers f with hH
  have hfH : f ∈ H := mem_sup_right (mem_zpowers f)
  have hwH : w ∈ H := by
    have e : w = (w * f⁻¹) * f := by group
    rw [e]
    exact mul_mem (mem_sup_left hwf) hfH
  obtain ⟨b, hb⟩ : ∃ b : ℕ, orderOf w = 3 ^ b := by
    obtain ⟨k, hk⟩ := hw ⟨w, mem_zpowers w⟩
    have hdvd : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨b, hb⟩
  have hb2 : 2 ≤ b := by
    by_contra h
    apply hw1
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hb]
    interval_cases b <;> norm_num
  have hw3 : orderOf (w ^ 3) = 3 ^ (b - 1) := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hb]; exact dvd_pow_self 3 (by omega)), hb]
    rw [show b = (b - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    simp
  have hfo : orderOf f = 3 := orderOf_eq_prime hf3 (fun h => hfN (h ▸ one_mem N))
  have hNf : (N ⊓ zpowers f : Subgroup G) = ⊥ := by
    have hdvd : Nat.card (N ⊓ zpowers f : Subgroup G) ∣ 3 := by
      rw [← hfo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : (N ⊓ zpowers f : Subgroup G) = zpowers f :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hfo])
      have hf' : f ∈ (N ⊓ zpowers f : Subgroup G) := by
        rw [heq]
        exact mem_zpowers f
      exact hfN hf'.1
  have hidx : N.relIndex H = 3 := by
    rw [hH, relIndex_sup_left]
    have h := relIndex_mul_card N (zpowers f)
    rw [hNf, Nat.card_zpowers, hfo] at h
    simpa using h
  have hcardH : Nat.card H = 3 * Nat.card N := by
    have h := relIndex_mul_card N H
    rw [inf_eq_left.2 (le_sup_left : N ≤ H), hidx] at h
    exact h.symm
  have hQidx := (isSylowOf_iff.1 hQ).2.2
  have hQcard : (zpowers (w ^ 3)).relIndex N * 3 ^ (b - 1) = Nat.card N := by
    have h := relIndex_mul_card (zpowers (w ^ 3)) N
    rw [inf_eq_left.2 (isSylowOf_iff.1 hQ).1, Nat.card_zpowers, hw3] at h
    exact h
  have hSyl : IsSylowOf 3 (zpowers w) H := by
    refine isSylowOf_iff.2 ⟨zpowers_le.2 hwH, hw, ?_⟩
    have h := relIndex_mul_card (zpowers w) H
    rw [inf_eq_left.2 (zpowers_le.2 hwH), Nat.card_zpowers, hb, hcardH, ← hQcard] at h
    have e : (zpowers w).relIndex H = (zpowers (w ^ 3)).relIndex N := by
      have hpos : 0 < 3 ^ b := by positivity
      apply Nat.eq_of_mul_eq_mul_right hpos
      have e3 : (3 : ℕ) ^ b = 3 ^ (b - 1) * 3 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [h, e3]
      ring
    rw [e]
    exact hQidx
  have hfp : IsPGroup 3 (zpowers f) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hfo, pow_one])
  obtain ⟨S, hS⟩ := (hfp.comap_subtype (K := H)).exists_le_sylow
  have hP' : IsSylowOf 3 ((S : Subgroup H).map H.subtype) H := ⟨S, rfl⟩
  have hfP' : f ∈ (S : Subgroup H).map H.subtype :=
    ⟨⟨f, hfH⟩, hS (show (⟨f, hfH⟩ : H) ∈ (zpowers f).comap H.subtype from mem_zpowers f), rfl⟩
  obtain ⟨k, hkH, hk⟩ := hSyl.exists_mem_conj hP'
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 ((hk f).1 hfP')
  have hj3 : (w ^ j) ^ (3 : ℤ) = 1 := by
    rw [hj, show k⁻¹ * f * k = k⁻¹ * f * k⁻¹⁻¹ by rw [inv_inv], conj_zpow]
    simp [hf3]
  have hdvd : (orderOf w : ℤ) ∣ j * 3 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul]
    exact hj3
  rw [hb] at hdvd
  have h3j : (3 : ℤ) ∣ j := by
    have h9 : (3 : ℤ) * 3 ∣ j * 3 := by
      refine dvd_trans ?_ hdvd
      rw [show b = (b - 2) + 2 by omega, pow_add]
      push_cast
      exact dvd_mul_of_dvd_right (by norm_num) _
    exact Int.dvd_of_mul_dvd_mul_right (by norm_num) h9
  obtain ⟨i, rfl⟩ := h3j
  have hwj : w ^ ((3 : ℤ) * i) ∈ N := by
    rw [zpow_mul]
    exact hQ.le (zpow_mem (mem_zpowers_iff.2 ⟨1, by simp⟩) i)
  rw [hj] at hwj
  apply hfN
  have := ‹N.Normal›.conj_mem _ hwj k
  simpa [mul_assoc] using this

private theorem le_normalizer_of_normal (C K : Subgroup G) [C.Normal] :
    K ≤ normalizer (C : Set G) := fun g _ => mem_normalizer_iff.2 fun h =>
  ⟨fun hh => ‹C.Normal›.conj_mem h hh g, fun hh => by
    simpa [mul_assoc] using ‹C.Normal›.conj_mem _ hh g⁻¹⟩

theorem isSylowOf_zpowers_of_commutator {C : Subgroup G} [C.Normal] {z x c : G}
    (hz : orderOf z = 3) [(zpowers z).Normal] (hzC : z ∈ C)
    (hCz : ∀ q ∈ C, q * z = z * q) (hxz : x * z = z * x) (hx3 : x ^ 3 = 1)
    (hi : ∀ q ∈ C, q ^ 3 = 1 → ⁅x, q⁆ ∈ zpowers z → q ∈ zpowers z)
    (hcC : c ∈ C) (hcp : IsPGroup 3 (zpowers c)) (hxc : ⁅x, c⁆ ∈ zpowers z)
    (hxc1 : ⁅x, c⁆ ≠ 1) : IsSylowOf 3 (zpowers c) C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  set B := zpowers c ⊔ zpowers z with hB
  have hZp : IsPGroup 3 (zpowers z) := isPGroup_zpowers_of_pow_eq_one (n := 1) (by simpa using hz3)
  have hBp : IsPGroup 3 B := hcp.to_sup_of_normal_right hZp
  have hxB : x ∈ normalizer (B : Set G) := by
    refine mem_normalizer_of_pow_three hx3 fun a ha => ?_
    have hle : B ≤ B.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · show x * c * x⁻¹ ∈ B
        have e : x * c * x⁻¹ = ⁅x, c⁆ * c := by rw [commutatorElement_def]; group
        rw [e]
        exact mul_mem (mem_sup_right hxc) (mem_sup_left (mem_zpowers c))
      · show x * z * x⁻¹ ∈ B
        rw [hxz, mul_inv_cancel_right]
        exact mem_sup_right (mem_zpowers z)
    exact hle ha
  have hxp : IsPGroup 3 (zpowers x) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by simpa using hx3)
  have hP3 : IsPGroup 3 (zpowers x ⊔ B : Subgroup G) :=
    hxp.to_sup_of_normal_right' hBp (zpowers_le.2 hxB)
  set M₁ := C ⊔ zpowers x with hM₁
  have hP3M : zpowers x ⊔ B ≤ M₁ :=
    sup_le le_sup_right (sup_le ((zpowers_le.2 hcC).trans le_sup_left)
      ((zpowers_le.2 hzC).trans le_sup_left))
  obtain ⟨S, hS⟩ := (hP3.comap_subtype (K := M₁)).exists_le_sylow
  set R := (S : Subgroup M₁).map M₁.subtype with hRdef
  have hR : IsSylowOf 3 R M₁ := ⟨S, rfl⟩
  have hPR : zpowers x ⊔ B ≤ R := fun y hy => ⟨⟨y, hP3M hy⟩, hS hy, rfl⟩
  have hQ : IsSylowOf 3 (R ⊓ C) C :=
    hR.inf_of_le_normalizer le_sup_left (le_normalizer_of_normal C M₁)
  have hxR : x ∈ R := hPR (mem_sup_left (mem_zpowers x))
  have hQc : IsCyclic (R ⊓ C : Subgroup G) :=
    isCyclic_inf_of_forall_mem_zpowers hz hi hR.isPGroup hxR
  have hQp : IsPGroup 3 (R ⊓ C : Subgroup G) := hR.isPGroup.to_le inf_le_left
  have hcQ : c ∈ R ⊓ C := ⟨hPR (mem_sup_right (mem_sup_left (mem_zpowers c))), hcC⟩
  have hzQ : z ∈ R ⊓ C := ⟨hPR (mem_sup_right (mem_sup_right (mem_zpowers z))), hzC⟩
  have hxN : x ∈ normalizer ((R ⊓ C : Subgroup G) : Set G) :=
    le_normalizer_inf_of_normal R C hxR
  have heq : zpowers c = R ⊓ C := by
    refine zpowers_eq_of_forall_pow_three_ne hQc hQp hcQ fun q hq hqc => hxc1 ?_
    have hxq : x * q * x⁻¹ ∈ R ⊓ C := (mem_normalizer_iff.1 hxN q).1 hq
    have heQ : ⁅x, q⁆ ∈ R ⊓ C := by
      rw [commutatorElement_def]
      exact mul_mem hxq (inv_mem hq)
    have he : ⁅x, q⁆ ∈ zpowers z := mem_zpowers_of_pow_three_eq_one hQc hz hzQ heQ
      (commutator_pow_three_of_isCyclic hQc hQp hxN hx3 hq)
    have h1 : x * q * x⁻¹ = ⁅x, q⁆ * q := by rw [commutatorElement_def]; group
    have hzq : Commute z q := (hCz q hq.2).symm
    have heq' : Commute ⁅x, q⁆ q := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 he
      rw [← hk]
      exact hzq.zpow_left k
    have h3 : x * q ^ 3 * x⁻¹ = q ^ 3 := by
      rw [← conj_pow, h1, heq'.mul_pow, pow_three_eq_one_of_mem_zpowers hz3 he, one_mul]
    rw [← hqc, commutatorElement_def, h3, mul_inv_cancel]
  rw [heq]
  exact hQ

theorem exists_mul_inv_mem_commute_pow_three {C : Subgroup G} [C.Normal] {z x f₁ : G}
    (hz : orderOf z = 3) [(zpowers z).Normal] (hzC : z ∈ C)
    (hCz : ∀ q ∈ C, q * z = z * q) (hz3e : ∀ g : G, IsPGroup 3 (zpowers g) → g * z = z * g)
    (hx3 : x ^ 3 = 1) (hi : ∀ q ∈ C, q ^ 3 = 1 → ⁅x, q⁆ ∈ zpowers z → q ∈ zpowers z)
    (hf₁ : IsPGroup 3 (zpowers f₁)) (hf₁x : ⁅f₁, x⁆ ∈ C) :
    ∃ f₂ : G, f₂ * f₁⁻¹ ∈ C ∧ IsPGroup 3 (zpowers f₂) ∧ f₂ ^ 3 * x = x * f₂ ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hxp : IsPGroup 3 (zpowers x) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by simpa using hx3)
  have hxz : x * z = z * x := hz3e x hxp
  let ψ := QuotientGroup.mk' C
  have hψ : ∀ g : G, ψ g = 1 ↔ g ∈ C := fun g => QuotientGroup.eq_one_iff g
  have hc : ψ f₁ * ψ x = ψ x * ψ f₁ := by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (hψ _).2 hf₁x
  set A := closure ({ψ x, ψ f₁} : Set (G ⧸ C)) with hA
  have hpair : ({ψ x, ψ f₁} : Set (G ⧸ C)).Pairwise Commute := by
    rintro u (rfl | rfl) v (rfl | rfl) - <;>
      first | exact Commute.refl _ | exact hc.symm | exact hc
  have hAab := isMulCommutative_closure hpair
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    simpa using congrArg Subtype.val (hAab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set X := A.comap ψ with hX
  have hXab : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ C := fun a ha b hb => (hψ _).1 (by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hAc _ ha _ hb)
  have hxX : x ∈ X := subset_closure (Set.mem_insert _ _)
  have hf₁X : f₁ ∈ X := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hCX : C ≤ X := fun c hc => by
    show ψ c ∈ A
    rw [(hψ c).2 hc]
    exact one_mem _
  have hZp : IsPGroup 3 (zpowers z) := isPGroup_zpowers_of_pow_eq_one (n := 1) (by simpa using hz3)
  have hPp : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) := hxp.to_sup_of_normal_right hZp
  have hPX : zpowers x ⊔ zpowers z ≤ X := sup_le (zpowers_le.2 hxX) (zpowers_le.2 (hCX hzC))
  obtain ⟨S, hS⟩ := (hPp.comap_subtype (K := X)).exists_le_sylow
  set R := (S : Subgroup X).map X.subtype with hRdef
  have hR : IsSylowOf 3 R X := ⟨S, rfl⟩
  have hPR : zpowers x ⊔ zpowers z ≤ R := fun y hy => ⟨⟨y, hPX hy⟩, hS hy, rfl⟩
  obtain ⟨S', hS'⟩ := (hf₁.comap_subtype (K := X)).exists_le_sylow
  have hR' : IsSylowOf 3 ((S' : Subgroup X).map X.subtype) X := ⟨S', rfl⟩
  have hf₁R' : f₁ ∈ (S' : Subgroup X).map X.subtype :=
    ⟨⟨f₁, hf₁X⟩, hS' (show (⟨f₁, hf₁X⟩ : X) ∈ (zpowers f₁).comap X.subtype from
      mem_zpowers f₁), rfl⟩
  obtain ⟨k, hkX, hk⟩ := hR.exists_mem_conj hR'
  set f₂ := k⁻¹ * f₁ * k with hf₂
  have hf₂R : f₂ ∈ R := (hk f₁).1 hf₁R'
  have hf₂X : f₂ ∈ X := hR.le hf₂R
  have hf₂f₁ : f₂ * f₁⁻¹ ∈ C := by
    have e : f₂ * f₁⁻¹ = ⁅k⁻¹, f₁⁆ := by rw [commutatorElement_def, inv_inv]
    rw [e]
    exact hXab _ (inv_mem hkX) _ hf₁X
  have hf₂p : IsPGroup 3 (zpowers f₂) := hR.isPGroup.to_le (zpowers_le.2 hf₂R)
  have hxR : x ∈ R := hPR (mem_sup_left (mem_zpowers x))
  have hzR : z ∈ R := hPR (mem_sup_right (mem_zpowers z))
  set c₂ := ⁅x, f₂⁆ with hc₂
  have hc₂C : c₂ ∈ C := hXab _ hxX _ hf₂X
  have hc₂R : c₂ ∈ R := by
    rw [hc₂, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxR hf₂R) (inv_mem hxR)) (inv_mem hf₂R)
  have hQc : IsCyclic (R ⊓ C : Subgroup G) :=
    isCyclic_inf_of_forall_mem_zpowers hz hi hR.isPGroup hxR
  have hQp : IsPGroup 3 (R ⊓ C : Subgroup G) := hR.isPGroup.to_le inf_le_left
  have hxN : x ∈ normalizer ((R ⊓ C : Subgroup G) : Set G) :=
    le_normalizer_inf_of_normal R C hxR
  have hzQ : z ∈ R ⊓ C := ⟨hzR, hzC⟩
  have hc₂Q : c₂ ∈ R ⊓ C := ⟨hc₂R, hc₂C⟩
  set e := ⁅x, c₂⁆ with he
  have heQ : e ∈ R ⊓ C := by
    rw [he, commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.1 hxN c₂).1 hc₂Q) (inv_mem hc₂Q)
  have heZ : e ∈ zpowers z := mem_zpowers_of_pow_three_eq_one hQc hz hzQ heQ
    (commutator_pow_three_of_isCyclic hQc hQp hxN hx3 hc₂Q)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 heZ
  have h1 : x * f₂ * x⁻¹ = c₂ * f₂ := by rw [hc₂, commutatorElement_def]; group
  have h2 : x * c₂ * x⁻¹ = e * c₂ := by rw [he, commutatorElement_def]; group
  have hxe : x * e * x⁻¹ = e := by
    have hcx : Commute x e := by
      rw [← hj]
      exact (show Commute x z from hxz).zpow_right j
    rw [hcx.eq, mul_inv_cancel_right]
  have hec : c₂ * e = e * c₂ := by
    have hcz : Commute c₂ z := hCz c₂ hc₂C
    rw [← hj]
    exact (hcz.zpow_right j).eq
  have he3 : e ^ 3 = 1 := pow_three_eq_one_of_mem_zpowers hz3 heZ
  have hc₂3 : c₂ ^ 3 = 1 := by
    have s1 : x * (c₂ * f₂) * x⁻¹ = e * c₂ * (c₂ * f₂) := by
      calc x * (c₂ * f₂) * x⁻¹ = (x * c₂ * x⁻¹) * (x * f₂ * x⁻¹) := by group
        _ = e * c₂ * (c₂ * f₂) := by rw [h2, h1]
    have s2 : x * (e * c₂ * (c₂ * f₂)) * x⁻¹ = e * (e * c₂) * (e * c₂) * (c₂ * f₂) := by
      calc x * (e * c₂ * (c₂ * f₂)) * x⁻¹ =
            (x * e * x⁻¹) * (x * c₂ * x⁻¹) * (x * c₂ * x⁻¹) * (x * f₂ * x⁻¹) := by group
        _ = e * (e * c₂) * (e * c₂) * (c₂ * f₂) := by rw [hxe, h2, h1]
    have s3 : e * (e * c₂) * (e * c₂) * (c₂ * f₂) = e ^ 3 * c₂ ^ 3 * f₂ := by
      calc e * (e * c₂) * (e * c₂) * (c₂ * f₂) = e * e * (c₂ * e) * c₂ * c₂ * f₂ := by group
        _ = e * e * (e * c₂) * c₂ * c₂ * f₂ := by rw [hec]
        _ = e ^ 3 * c₂ ^ 3 * f₂ := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have h3 : x ^ 3 * f₂ * (x ^ 3)⁻¹ = x * (x * (x * f₂ * x⁻¹) * x⁻¹) * x⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [hx3, h1, s1, s2, s3, he3, one_mul] at h3
    simpa using h3.symm
  have hc₂Z : c₂ ∈ zpowers z := mem_zpowers_of_pow_three_eq_one hQc hz hzQ hc₂Q hc₂3
  have hcf : Commute c₂ f₂ := by
    obtain ⟨i, hi'⟩ := mem_zpowers_iff.1 hc₂Z
    rw [← hi']
    exact ((show Commute f₂ z from hz3e f₂ hf₂p).zpow_right i).symm
  refine ⟨f₂, hf₂f₁, hf₂p, ?_⟩
  have h4 : x * f₂ ^ 3 * x⁻¹ = f₂ ^ 3 := by
    rw [← conj_pow, h1, hcf.mul_pow, hc₂3, one_mul]
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
