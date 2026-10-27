module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSplit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34OddCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Product

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem mem_sylow_of_mem_center [Finite G] {c : G} (hc : c ∈ Subgroup.center G)
    (hcc : c * c = 1) (T : Sylow 2 G) : c ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNc : Subgroup.zpowers c ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hc
  have hN : (Subgroup.zpowers c).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hNc hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hp : IsPGroup 2 (Subgroup.zpowers c) := by
    have hdvd : orderOf c ∣ 2 ^ 1 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hcc)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  exact hp.le_sylow_of_normal T (Subgroup.mem_zpowers c)

omit [Finite G] in
theorem commutatorElement_mul_left_of_commute {a x y : G} (hax : Commute a x)
    (hay : Commute a y) : ⁅a * x, y⁆ = ⁅x, y⁆ := by
  have hc : Commute a (x * y * x⁻¹) := (hax.mul_right hay).mul_right hax.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc a * x * y * (a * x)⁻¹ * y⁻¹ = a * (x * y * x⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * a * a⁻¹ * y⁻¹ := by rw [hc.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

omit [Finite G] in
theorem commutatorElement_mul_right_of_commute {b x y : G} (hbx : Commute b x)
    (hby : Commute b y) : ⁅x, b * y⁆ = ⁅x, y⁆ := by
  have hc : Commute b (x * y * x⁻¹ * y⁻¹) :=
    ((hbx.mul_right hby).mul_right hbx.inv_right).mul_right hby.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (b * y) * x⁻¹ * (b * y)⁻¹ = b * (x * y * x⁻¹ * y⁻¹) * b⁻¹ := by
        rw [show x * (b * y) = b * x * y by rw [← mul_assoc, ← hbx.eq]]
        group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hc.eq, mul_inv_cancel_right]

section Hull

variable {z u : G}

omit [Finite G] in
theorem commutator_hull_eq_bot_of_central {t₀ : G} (ht₀ : t₀ ∈ involutionPointClass z)
    (hcen : ∀ y ∈ involutionPointHull z, Commute t₀ y) :
    ⁅involutionPointHull z, involutionPointHull z⁆ = ⊥ := by
  have hN := minimalLocalFailure_hull_normal z
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (Subgroup.closure_le _).mpr fun t ht => ?_
  obtain ⟨h₀, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := ht
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro y hy
  show y * rightConjugateElem z g = rightConjugateElem z g * y
  set c := h₀⁻¹ * g with hc
  have hgc : rightConjugateElem z g = c⁻¹ * rightConjugateElem z h₀ * c := by
    simp only [rightConjugateElem, hc]
    group
  have hyc : c * y * c⁻¹ ∈ involutionPointHull z := by
    have := hN.conj_mem y hy c
    exact this
  have h1 := (hcen _ hyc).eq
  rw [hgc]
  calc y * (c⁻¹ * rightConjugateElem z h₀ * c)
      = c⁻¹ * ((c * y * c⁻¹) * rightConjugateElem z h₀) * c := by group
    _ = c⁻¹ * (rightConjugateElem z h₀ * (c * y * c⁻¹)) * c := by rw [h1]
    _ = c⁻¹ * rightConjugateElem z h₀ * c * y := by group

omit [Finite G] in
theorem exists_zpow_mul_mem_of_mem_hull
    (hucen : ∀ y ∈ involutionPointHull z, Commute u y) {x : G}
    (hx : x ∈ involutionPointHull z) :
    ∃ k : ℤ, u ^ k * x ∈
      Subgroup.closure ((fun t => u⁻¹ * t) '' involutionPointClass z) := by
  induction hx using Subgroup.closure_induction with
  | mem t ht => exact ⟨-1, Subgroup.subset_closure ⟨t, ht, by rw [zpow_neg_one]⟩⟩
  | one => exact ⟨0, by rw [zpow_zero, one_mul]; exact Subgroup.one_mem _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨k, hk⟩ := ihx
    obtain ⟨l, hl⟩ := ihy
    refine ⟨k + l, ?_⟩
    have hcomm : Commute (u ^ l) x := (hucen x hx).zpow_left l
    have := Subgroup.mul_mem _ hk hl
    rwa [show u ^ k * x * (u ^ l * y) = u ^ (k + l) * (x * y) by
      rw [zpow_add, mul_assoc, ← mul_assoc x, ← hcomm.eq, mul_assoc, mul_assoc]] at this
  | inv x hx ihx =>
    obtain ⟨k, hk⟩ := ihx
    refine ⟨-k, ?_⟩
    have hcomm : Commute (u ^ (-k)) x⁻¹ := ((hucen x hx).zpow_left (-k)).inv_right
    have := Subgroup.inv_mem _ hk
    rwa [mul_inv_rev, ← zpow_neg, ← hcomm.eq] at this

omit [Finite G] in
theorem commutator_hull_odd_index (hz : orderOf z = 2) (huL : u ∈ involutionPointHull z)
    (hucen : ∀ y ∈ involutionPointHull z, Commute u y) (hu2 : u * u = 1)
    (hclass : ∀ t ∈ involutionPointClass z,
      u⁻¹ * t ∈ ⁅involutionPointHull z, involutionPointHull z⁆) :
    ∀ N : Subgroup (⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup G),
      N.Normal → Odd N.index → N = ⊤ := by
  set L := involutionPointHull z with hLdef
  set K := ⁅L, L⁆ with hKdef
  set M := Subgroup.closure ((fun t => u⁻¹ * t) '' involutionPointClass z) with hMdef
  have hKM : K ≤ M := by
    rw [hKdef, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, hk⟩ := exists_zpow_mul_mem_of_mem_hull hucen hx
    obtain ⟨l, hl⟩ := exists_zpow_mul_mem_of_mem_hull hucen hy
    have hyL : u ^ l * y ∈ L := L.mul_mem (L.zpow_mem huL l) hy
    have heq : ⁅x, y⁆ = ⁅u ^ k * x, u ^ l * y⁆ := by
      rw [commutatorElement_mul_left_of_commute ((hucen x hx).zpow_left k)
          ((hucen _ hyL).zpow_left k),
        commutatorElement_mul_right_of_commute ((hucen x hx).zpow_left l)
          ((hucen y hy).zpow_left l)]
    rw [heq, commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hk hl) (M.inv_mem hk)) (M.inv_mem hl)
  intro N hN hodd
  have hgen : ∀ s : K, s * s = 1 → s ∈ N := by
    intro s hss
    have hq2 : orderOf (QuotientGroup.mk' N s) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [sq, ← map_mul, hss, map_one])
    have hqN : orderOf (QuotientGroup.mk' N s) ∣ Nat.card (K ⧸ N) := orderOf_dvd_natCard _
    rw [← Subgroup.index_eq_card] at hqN
    have hcop : Nat.Coprime 2 N.index := Nat.coprime_two_left.mpr hodd
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hq2 hqN
    rw [orderOf_eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff s).mp h1
  have hMN : M ≤ N.map K.subtype := by
    rw [hMdef, Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    have htK := hclass t ht
    refine ⟨⟨u⁻¹ * t, htK⟩, hgen _ (Subtype.ext ?_), rfl⟩
    have htL : t ∈ L := Subgroup.subset_closure ht
    have htt : t * t = 1 := class_mul_self hz ht
    have hut : u⁻¹ * t = t * u⁻¹ := (hucen t htL).inv_left.eq
    change u⁻¹ * t * (u⁻¹ * t) = 1
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
    rw [mul_assoc, ← mul_assoc t, ← hut, mul_assoc, ← mul_assoc u⁻¹, htt, mul_one, huinv, hu2]
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hMN (hKM x.2)
  rwa [← Subtype.ext hyx]

end Hull

namespace Minimal

variable (m : Minimal S A₁ A₂)
include m

theorem not_mem_center {b : G} (hb : b ∈ (A₁ : Set G) ∪ A₂) (hb1 : b ≠ 1) :
    b ∉ Subgroup.center G := fun hc => m.ne_top (eq_top_iff.mpr fun g _ =>
  m.centralizer_le hb hb1
    (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hc g)))

theorem productUniqueContainment {z₀ : G} (hz₀ : z₀ ∈ A₁) (hz₀2 : orderOf z₀ = 2)
    (hchoice : z₀ ∈ A₂ ∨ A₁ ⊓ A₂ = ⊥) :
    ProductUniqueContainment (overlapClosure A₁ A₂) z₀ := by
  have h := m.hyp
  set H := overlapClosure A₁ A₂ with hHdef
  intro t ht hzt hne g
  have hz1 : z₀ ≠ 1 := (orderOf_eq_prime_iff.mp hz₀2).2
  have hzz : z₀ * z₀ = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hz₀2).1
  have htt : t * t = 1 := class_mul_self hz₀2 ht
  have ht2 : orderOf t = 2 := class_orderOf hz₀2 ht
  have hzC : Subgroup.centralizer ({z₀} : Set G) ≤ H := m.centralizer_le (Or.inl hz₀) hz1
  have hwH : z₀ * t ∈ H := hzC (Subgroup.mem_centralizer_singleton_iff.mpr
    ((Commute.refl z₀).mul_right hzt).eq.symm)
  constructor
  swap
  · intro hg
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hwH) hg
  suffices hfix : FixesOnly H (Subgroup.zpowers (z₀ * t)) from fixesOnly_zpowers_iff.mp hfix g
  let V := commutingPairSubgroup z₀ t hzz htt hzt
  have hVH : V ≤ H := by
    intro x hx
    apply hzC
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases mem_commutingPairSubgroup.mp hx with rfl | rfl | rfl | rfl
    · simp
    · rfl
    · exact hzt.eq.symm
    · exact ((Commute.refl z₀).mul_right hzt).eq.symm
  have hVp : IsPGroup 2 V := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (commutingPairSubgroup_sq x.property)⟩
  obtain ⟨k, hk, hkS⟩ := exists_conj_le_sylow m.sylow_le hVH hVp
  have hz'S : k⁻¹ * z₀ * k ∈ (S : Subgroup G) :=
    hkS z₀ (mem_commutingPairSubgroup.mpr (Or.inr (Or.inl rfl)))
  have ht'S : k⁻¹ * t * k ∈ (S : Subgroup G) :=
    hkS t (mem_commutingPairSubgroup.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hz'U := m.conj_mem (Or.inl hz₀) hz'S
  obtain ⟨g₁, hg₁⟩ := ht
  have htg : t = g₁⁻¹ * z₀ * g₁ := hg₁.symm
  have ht'U : k⁻¹ * t * k ∈ (A₁ : Set G) ∪ A₂ := by
    have heq : k⁻¹ * t * k = (g₁ * k)⁻¹ * z₀ * (g₁ * k) := by rw [htg]; group
    rw [heq] at ht'S ⊢
    exact m.conj_mem (Or.inl hz₀) ht'S
  have hreduce : FixesOnly H (Subgroup.zpowers (k⁻¹ * (z₀ * t) * k)) →
      FixesOnly H (Subgroup.zpowers (z₀ * t)) := by
    intro hf
    rw [fixesOnly_zpowers_iff] at hf ⊢
    intro g' hg'
    have h1 := hf (k⁻¹ * g') (by
      rw [show (k⁻¹ * g')⁻¹ * (k⁻¹ * (z₀ * t) * k) * (k⁻¹ * g') = g'⁻¹ * (z₀ * t) * g' by group]
      exact hg')
    have := H.mul_mem hk h1
    rwa [mul_inv_cancel_left] at this
  apply hreduce
  have hw' : k⁻¹ * (z₀ * t) * k = (k⁻¹ * z₀ * k) * (k⁻¹ * t * k) := by group
  have hord : ∀ {b : G}, orderOf b = 2 → orderOf (k⁻¹ * b * k) = 2 := fun hb => by
    rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]; exact hb
  have hw1 : k⁻¹ * (z₀ * t) * k ≠ 1 := by
    intro h1
    apply hne
    have : z₀ * t = 1 := by
      calc z₀ * t = k * (k⁻¹ * (z₀ * t) * k) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    calc t = z₀ * (z₀ * t) := by rw [← mul_assoc, hzz, one_mul]
      _ = z₀ := by rw [this, mul_one]
  have hcomm' : Commute (k⁻¹ * z₀ * k) (k⁻¹ * t * k) := by
    have := hzt.map (MulAut.conj k⁻¹).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  have hwc : k⁻¹ * (z₀ * t) * k ∉ Subgroup.center G := by
    intro hc
    have hcc : k⁻¹ * (z₀ * t) * k * (k⁻¹ * (z₀ * t) * k) = 1 := by
      rw [hw', mul_assoc, hcomm'.symm.left_comm, ← mul_assoc, ← mul_assoc,
        show k⁻¹ * z₀ * k * (k⁻¹ * z₀ * k) = k⁻¹ * (z₀ * z₀) * k by group, hzz,
        show k⁻¹ * 1 * k = 1 by group, one_mul,
        show k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k by group, htt]
      group
    rcases hchoice with hz₀₂ | hI
    ·
      have hc0 : z₀ * t ∈ Subgroup.center G := by
        have heq : z₀ * t = k * (k⁻¹ * (z₀ * t) * k) * k⁻¹ := by group
        rw [heq, mul_assoc, ← Subgroup.mem_center_iff.mp hc k⁻¹, ← mul_assoc, mul_inv_cancel,
          one_mul]
        exact hc
      have hcc0 : z₀ * t * (z₀ * t) = 1 := by
        rw [mul_assoc, hzt.symm.left_comm, ← mul_assoc, hzz, one_mul, htt]
      have hcS : z₀ * t ∈ (S : Subgroup G) := mem_sylow_of_mem_center hc0 hcc0 S
      have htz : t = z₀ * (z₀ * t) := by rw [← mul_assoc, hzz, one_mul]
      have htS : t ∈ (S : Subgroup G) := by
        rw [htz]
        exact Subgroup.mul_mem _ (h.le_one hz₀) hcS
      have htU : t ∈ (A₁ : Set G) ∪ A₂ := by
        rw [htg] at htS ⊢
        exact m.conj_mem (Or.inl hz₀) htS
      have hcU : z₀ * t ∈ (A₁ : Set G) ∪ A₂ := by
        rcases htU with ht₁ | ht₂
        · exact Or.inl (A₁.mul_mem hz₀ ht₁)
        · exact Or.inr (A₂.mul_mem hz₀₂ ht₂)
      have hc1 : z₀ * t ≠ 1 := by
        intro h1
        apply hne
        calc t = z₀ * (z₀ * t) := htz
          _ = z₀ := by rw [h1, mul_one]
      exact m.not_mem_center hcU hc1 hc0
    ·
      have hmemI : ∀ {b : G}, b ∈ A₁ → b ∈ A₂ → b = 1 := by
        intro b hb₁ hb₂
        have : b ∈ A₁ ⊓ A₂ := ⟨hb₁, hb₂⟩
        rwa [hI, Subgroup.mem_bot] at this
      have hz'1 : k⁻¹ * z₀ * k ≠ 1 := (orderOf_eq_prime_iff.mp (hord hz₀2)).2
      have ht'1 : k⁻¹ * t * k ≠ 1 := (orderOf_eq_prime_iff.mp (hord ht2)).2
      rcases hz'U with hz'₁ | hz'₂ <;> rcases ht'U with ht'₁ | ht'₂
      · exact m.not_mem_center (Or.inl (hw' ▸ A₁.mul_mem hz'₁ ht'₁)) hw1 hc
      · refine m.false_of_central_of_inf_eq_bot hI hc hcc (fun hw₁ => ht'1 ?_)
          (fun hw₂ => hz'1 ?_)
        · refine hmemI ?_ ht'₂
          have := A₁.mul_mem (A₁.inv_mem hz'₁) (hw' ▸ hw₁)
          rwa [inv_mul_cancel_left] at this
        · refine hmemI hz'₁ ?_
          have := A₂.mul_mem (hw' ▸ hw₂) (A₂.inv_mem ht'₂)
          rwa [mul_inv_cancel_right] at this
      · refine m.false_of_central_of_inf_eq_bot hI hc hcc (fun hw₁ => hz'1 ?_)
          (fun hw₂ => ht'1 ?_)
        · refine hmemI ?_ hz'₂
          have := A₁.mul_mem (hw' ▸ hw₁) (A₁.inv_mem ht'₁)
          rwa [mul_inv_cancel_right] at this
        · refine hmemI ht'₁ ?_
          have := A₂.mul_mem (A₂.inv_mem hz'₂) (hw' ▸ hw₂)
          rwa [inv_mul_cancel_left] at this
      · exact m.not_mem_center (Or.inr (hw' ▸ A₂.mul_mem hz'₂ ht'₂)) hw1 hc
  rcases hz'U with hz'₁ | hz'₂ <;> rcases ht'U with ht'₁ | ht'₂
  · exact m.fixesOnly (Or.inl (hw' ▸ A₁.mul_mem hz'₁ ht'₁)) hw1
  · rw [hw'] at hwc ⊢
    exact m.fixesOnly_of_mul hz'₁ (hord hz₀2) ht'₂ (hord ht2) hwc
  · rw [hw', hcomm'.eq] at hwc ⊢
    exact m.fixesOnly_of_mul ht'₁ (hord ht2) hz'₂ (hord hz₀2) hwc
  · exact m.fixesOnly (Or.inr (hw' ▸ A₂.mul_mem hz'₂ ht'₂)) hw1

theorem theorem33
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity) {z₀ : G} (hz₀ : z₀ ∈ A₁) (hz₀2 : orderOf z₀ = 2)
    (hchoice : z₀ ∈ A₂ ∨ A₁ ⊓ A₂ = ⊥) :
    (∀ g : G, z₀ ∈ rightConjugate (overlapClosure A₁ A₂) g ↔ g ∈ overlapClosure A₁ A₂) ∧
      CentralProductCentralizer (overlapClosure A₁ A₂) z₀ ∧
      PointHullStrongSplit (overlapClosure A₁ A₂) z₀ := by
  have hz1 : z₀ ≠ 1 := (orderOf_eq_prime_iff.mp hz₀2).2
  have huniq : ∀ g : G, z₀ ∈ rightConjugate (overlapClosure A₁ A₂) g ↔
      g ∈ overlapClosure A₁ A₂ :=
    unique_of_fixesOnly (m.hyp.mem_overlapClosure_of_mem_union (Or.inl hz₀))
      (m.fixesOnly (Or.inl hz₀) hz1)
  obtain ⟨h12, h23, -⟩ := theorem_3_3 himp hcov (overlapClosure A₁ A₂) z₀ hz₀2 m.ne_top huniq
  have h2 := h12 (m.productUniqueContainment hz₀ hz₀2 hchoice)
  exact ⟨huniq, h2, h23 h2⟩

theorem exists_bender
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity) :
    ∃ K : Subgroup G, K.Normal ∧ CFSG.Open.fusionIsBenderGroup K ∧
      fusionStronglyEmbedded ((overlapClosure A₁ A₂).subgroupOf K) ∧
      CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo K := by
  have h := m.hyp
  obtain ⟨z₀, hz₀, hz₀2, hchoice⟩ : ∃ z₀ ∈ A₁, orderOf z₀ = 2 ∧ (z₀ ∈ A₂ ∨ A₁ ⊓ A₂ = ⊥) := by
    by_cases hI : A₁ ⊓ A₂ = ⊥
    · obtain ⟨w, hw, hw2, -⟩ := exists_central_involution (S.isPGroup'.to_le h.le_one)
        h.ne_bot_one
      exact ⟨w, hw, hw2, Or.inr hI⟩
    · obtain ⟨w, hw, hw2, -⟩ :=
        exists_central_involution (S.isPGroup'.to_le (inf_le_left.trans h.le_one)) hI
      exact ⟨w, hw.1, hw2, Or.inl hw.2⟩
  have hz1 : z₀ ≠ 1 := (orderOf_eq_prime_iff.mp hz₀2).2
  obtain ⟨huniq, h2, h3⟩ := m.theorem33 himp hcov hz₀ hz₀2 hchoice
  have hO := m.oddCore_eq_bot
  have hrank := two_le_twoRank_hull hz₀2 m.ne_top huniq h2.1 hO
  rcases h3 with hlow | ⟨u, hu2, hucen, -, -, hse, hclass⟩
  · omega
  have hLn : (involutionPointHull z₀).Normal := minimalLocalFailure_hull_normal z₀
  have hcoreL : CFSG.oddCore (involutionPointHull z₀) = ⊥ :=
    oddCore_eq_bot_of_normal' hO (involutionPointHull z₀)
  let q := QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z₀))
  have hinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcoreL
  have hcomm : ∀ y ∈ (involutionPointHull z₀), Commute (u : G) y := by
    intro y hy
    have h1 : q ⟨y, hy⟩ * q u = q u * q ⟨y, hy⟩ := Subgroup.mem_center_iff.mp hucen _
    rw [← map_mul, ← map_mul] at h1
    exact (congrArg Subtype.val (hinj h1)).symm
  have hu2' : (u : G) * u = 1 := by
    have : ((u ^ 2 : (involutionPointHull z₀)) : G) = 1 := by rw [hu2]; rfl
    rwa [Subgroup.coe_pow, sq] at this
  have hKn : ⁅involutionPointHull z₀, involutionPointHull z₀⁆.Normal :=
    Subgroup.commutator_normal (involutionPointHull z₀) (involutionPointHull z₀)
  have hgen := commutator_hull_odd_index hz₀2 u.2 hcomm hu2' hclass
  obtain ⟨t, ht, hzt, hne⟩ : ∃ t ∈ involutionPointClass z₀, Commute z₀ t ∧ t ≠ z₀ := by
    by_contra hcon
    have hz0c := mem_center_of_isolated hO hz₀2 h2.1 (fun t ht hzt => by
      by_contra hne
      exact hcon ⟨t, ht, hzt, hne⟩)
    exact m.not_mem_center (Or.inl hz₀) hz1 hz0c
  have hKne : ⁅involutionPointHull z₀, involutionPointHull z₀⁆ ≠ ⊥ := by
    intro hbot
    apply hse.1
    rw [eq_top_iff]
    intro x _
    have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp ((le_of_eq hbot) x.2))
    rw [hx1]
    exact Subgroup.one_mem _
  have hnc : ∀ {t₀ : G}, t₀ ∈ involutionPointClass z₀ → t₀ ≠ u := by
    intro t₀ ht₀ heq
    apply hKne
    refine commutator_hull_eq_bot_of_central ht₀ fun y hy => ?_
    rw [heq]
    exact hcomm y hy
  have hzK := hclass z₀ (distinguished_mem_pointClass z₀)
  have htK := hclass t ht
  have hzL : z₀ ∈ (involutionPointHull z₀) :=
    Subgroup.subset_closure (distinguished_mem_pointClass z₀)
  have htL : t ∈ (involutionPointHull z₀) := Subgroup.subset_closure ht
  have hzz : z₀ * z₀ = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hz₀2).1
  have htt : t * t = 1 := class_mul_self hz₀2 ht
  have huinv : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_left hu2'
  have hsq : ∀ {s : G}, s ∈ (involutionPointHull z₀) → s * s = 1 →
      (u : G)⁻¹ * s * ((u : G)⁻¹ * s) = 1 := by
    intro s hs hss
    rw [huinv, mul_assoc, ← mul_assoc s, ← (hcomm s hs).eq, mul_assoc, ← mul_assoc (u : G),
      hu2', one_mul, hss]
  have hne1 : ∀ {s : G}, s ≠ (u : G) → (u : G)⁻¹ * s ≠ 1 := by
    intro s hs h1
    apply hs
    calc s = (u : G) * ((u : G)⁻¹ * s) := by group
      _ = u := by rw [h1, mul_one]
  set k₁ : ↥(⁅involutionPointHull z₀, involutionPointHull z₀⁆ : Subgroup G) :=
    ⟨(u : G)⁻¹ * z₀, hzK⟩ with hk₁
  set k₂ : ↥(⁅involutionPointHull z₀, involutionPointHull z₀⁆ : Subgroup G) :=
    ⟨(u : G)⁻¹ * t, htK⟩ with hk₂
  have hk₁1 : k₁ ≠ 1 := fun h1 =>
    hne1 (hnc (distinguished_mem_pointClass z₀)) (congrArg Subtype.val h1)
  have hk₂1 : k₂ ≠ 1 := fun h1 => hne1 (hnc ht) (congrArg Subtype.val h1)
  have hk₁k₁ : k₁ * k₁ = 1 := Subtype.ext (hsq hzL hzz)
  have hk₂k₂ : k₂ * k₂ = 1 := Subtype.ext (hsq htL htt)
  have hk₁2 : orderOf k₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hk₁k₁) hk₁1
  have hk₂2 : orderOf k₂ = 2 := orderOf_eq_prime (by rw [sq]; exact hk₂k₂) hk₂1
  have hk12 : Commute k₁ k₂ := by
    apply Subtype.ext
    change (u : G)⁻¹ * z₀ * ((u : G)⁻¹ * t) = (u : G)⁻¹ * t * ((u : G)⁻¹ * z₀)
    have h1 : Commute (u : G)⁻¹ z₀ := (hcomm z₀ hzL).inv_left
    have h2' : Commute (u : G)⁻¹ t := (hcomm t htL).inv_left
    calc (u : G)⁻¹ * z₀ * ((u : G)⁻¹ * t) = (u : G)⁻¹ * (z₀ * (u : G)⁻¹) * t := by group
      _ = (u : G)⁻¹ * ((u : G)⁻¹ * z₀) * t := by rw [← h1.eq]
      _ = (u : G)⁻¹ * (u : G)⁻¹ * (z₀ * t) := by group
      _ = (u : G)⁻¹ * (u : G)⁻¹ * (t * z₀) := by rw [hzt.eq]
      _ = (u : G)⁻¹ * ((u : G)⁻¹ * t) * z₀ := by group
      _ = (u : G)⁻¹ * (t * (u : G)⁻¹) * z₀ := by rw [h2'.eq]
      _ = (u : G)⁻¹ * t * ((u : G)⁻¹ * z₀) := by group
  have hk12ne : k₁ ≠ k₂ := by
    intro heq
    apply hne
    have := congrArg Subtype.val heq
    change (u : G)⁻¹ * z₀ = (u : G)⁻¹ * t at this
    exact (mul_left_cancel this).symm
  refine ⟨⁅involutionPointHull z₀, involutionPointHull z₀⁆, hKn,
    fusionIsBenderGroup_of_stronglyEmbedded
      (oddCore_eq_bot_of_normal' hO ⁅involutionPointHull z₀, involutionPointHull z₀⁆) hgen
    hse hk₁2 hk₂2 hk12 hk12ne, hse, ?_⟩
  refine ⟨commutingPairSubgroup k₁ k₂ hk₁k₁ hk₂k₂ hk12, ?_, fun x => ?_⟩
  · rw [commutingPairSubgroup_card hk₁1 hk₂1 hk12ne]
    norm_num
  · exact Subtype.ext (commutingPairSubgroup_sq x.property)

end Minimal

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
