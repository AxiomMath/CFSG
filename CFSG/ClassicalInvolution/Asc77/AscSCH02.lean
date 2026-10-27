module

public import CFSG.ClassicalInvolution.Asc77.AscSCH01
public import CFSG.RankThree.Classical.CentralPairing

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open scoped commutatorElement

variable {E J : Type*} [Group E] [Group J]

theorem factorization_sup_zpowers_ge {p : ℕ} [Fact p.Prime] [Finite J] (T : Subgroup J) (c : J)
    (hc : c ∈ Subgroup.normalizer (T : Set J)) (hcT : c ∉ T) (hcp : c ^ p = 1) :
    (Nat.card T).factorization p + 1 ≤
      (Nat.card ↥(T ⊔ Subgroup.zpowers c)).factorization p := by
  classical
  set Q₀ : Subgroup J := T ⊔ Subgroup.zpowers c with hQ₀
  have hle : T ≤ Q₀ := le_sup_left
  have hcQ : c ∈ Q₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hnorm : Q₀ ≤ Subgroup.normalizer (T : Set J) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hc)
  have : (T.subgroupOf Q₀).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hnorm
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf Q₀)
  have hN : Nat.card (T.subgroupOf Q₀) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  set x : Q₀ ⧸ T.subgroupOf Q₀ := (QuotientGroup.mk (⟨c, hcQ⟩ : Q₀)) with hx
  have hx1 : x ≠ 1 := by
    intro h
    rw [hx, ← QuotientGroup.mk_one, QuotientGroup.eq, mul_one, inv_mem_iff,
      Subgroup.mem_subgroupOf] at h
    exact hcT h
  have hxp : x ^ p = 1 := by
    rw [hx, ← QuotientGroup.mk_pow]
    have : (⟨c, hcQ⟩ : Q₀) ^ p = 1 := Subtype.ext (by simpa using hcp)
    rw [this, QuotientGroup.mk_one]
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hdvd : p ∣ Nat.card (Q₀ ⧸ T.subgroupOf Q₀) := hord ▸ orderOf_dvd_natCard x
  rw [hcard, hN, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
  have h1 : 1 ≤ (Nat.card (Q₀ ⧸ T.subgroupOf Q₀)).factorization p :=
    (Fact.out : p.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hdvd
  omega

theorem eq_one_of_central_inv {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (π : E →* J)
    (hCp : IsPGroup p π.ker)
    {z : E} (hz : z ∈ π.ker) (hzz : z = z⁻¹) : z = 1 := by
  have hsq : z ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [hzz]
    exact inv_mul_cancel z
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hCp) ⟨z, hz⟩
  rw [Subgroup.orderOf_mk] at hn
  refine CFSG.SectionRank.OddCover.eq_one_of_sq_eq_one_of_odd hsq ?_
  rw [hn]
  exact (((Fact.out : p.Prime).odd_of_ne_two hp2).pow)

@[expose] def twistRange (A : Subgroup E) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (c : E)
    (hc : ∀ x ∈ A, c * x * c⁻¹ ∈ A) : Subgroup E where
  carrier := {x | ∃ a ∈ A, x = a * (c * a * c⁻¹)⁻¹}
  one_mem' := ⟨1, A.one_mem, by group⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, A.mul_mem ha hb, ?_⟩
    have hcomm := hA _ (A.inv_mem (hc a ha)) _ (A.mul_mem hb (A.inv_mem (hc b hb)))
    calc a * (c * a * c⁻¹)⁻¹ * (b * (c * b * c⁻¹)⁻¹)
        = a * ((c * a * c⁻¹)⁻¹ * (b * (c * b * c⁻¹)⁻¹)) := by group
      _ = a * ((b * (c * b * c⁻¹)⁻¹) * (c * a * c⁻¹)⁻¹) := by rw [hcomm]
      _ = a * b * (c * (a * b) * c⁻¹)⁻¹ := by group
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, ?_⟩
    calc (a * (c * a * c⁻¹)⁻¹)⁻¹ = (c * a * c⁻¹) * a⁻¹ := by group
      _ = a⁻¹ * (c * a * c⁻¹) := (hA _ (hc a ha) _ (A.inv_mem ha))
      _ = a⁻¹ * (c * a⁻¹ * c⁻¹)⁻¹ := by group

theorem twistRange_le {A : Subgroup E} {hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {c : E}
    {hc : ∀ x ∈ A, c * x * c⁻¹ ∈ A} : twistRange A hA c hc ≤ A := by
  rintro _ ⟨a, ha, rfl⟩
  exact A.mul_mem ha (A.inv_mem (hc a ha))

theorem conj_mem_twistRange {A : Subgroup E} {hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {c : E}
    {hc : ∀ x ∈ A, c * x * c⁻¹ ∈ A} (hc' : ∀ x ∈ A, c⁻¹ * x * c ∈ A) {x : E}
    (hx : x ∈ twistRange A hA c hc) :
    c * x * c⁻¹ ∈ twistRange A hA c hc ∧ c⁻¹ * x * c ∈ twistRange A hA c hc := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨⟨c * a * c⁻¹, hc a ha, by group⟩, ⟨c⁻¹ * a * c, hc' a ha, by group⟩⟩

theorem mem_comap_sup_zpowers (π : E →* J) (T : Subgroup J) (c : J) (c' : E) (hπc' : π c' = c)
    (hc : c ∈ Subgroup.normalizer (T : Set J)) {x : E}
    (hx : x ∈ (T ⊔ Subgroup.zpowers c).comap π) :
    ∃ a ∈ T.comap π, ∃ k : ℤ, x = a * c' ^ k := by
  have hnorm : Subgroup.zpowers c ≤ Subgroup.normalizer (T : Set J) := Subgroup.zpowers_le.2 hc
  have hx' : π x ∈ ((T ⊔ Subgroup.zpowers c : Subgroup J) : Set J) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left T (Subgroup.zpowers c) hnorm] at hx'
  obtain ⟨t, ht, y, hy, hty⟩ := hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨x * c' ^ (-k), ?_, k, by group⟩
  rw [Subgroup.mem_comap, map_mul, map_zpow, hπc', zpow_neg, ← hty, mul_inv_cancel_right]
  exact ht

theorem ker_eq_bot_of_torus {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite E] [Group.IsPerfect E]
    (π : E →* J) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) (T : Subgroup J) (c g : J)
    (hTab : ∀ x ∈ T.comap π, ∀ y ∈ T.comap π, x * y = y * x)
    (hc : c ∈ Subgroup.normalizer (T : Set J)) (hgc : g * c * g⁻¹ = c⁻¹)
    (hgT : ∀ t ∈ T, c * t * c⁻¹ = t → g * t * g⁻¹ = t)
    (hord : (Nat.card J).factorization p ≤
      (Nat.card ↥(T ⊔ Subgroup.zpowers c)).factorization p) :
    π.ker = ⊥ := by
  classical
  have hJ : Finite J := Finite.of_surjective π hπ
  set Q : Subgroup J := T ⊔ Subgroup.zpowers c with hQ
  set A : Subgroup E := T.comap π with hA
  set Q' : Subgroup E := Q.comap π with hQ'
  set c' : E := Function.surjInv hπ c with hc'
  have hπc' : π c' = c := Function.surjInv_eq hπ c
  have hker : π.ker ≤ ⁅Q', Q'⁆ :=
    ker_le_comm_sub π hC hCp Q' (factorization_comap_ge π hπ Q hord)
  have hσ : ∀ a ∈ A, c' * a * c'⁻¹ ∈ A := by
    intro a ha
    rw [hA, Subgroup.mem_comap] at ha ⊢
    rw [map_mul, map_mul, map_inv, hπc']
    exact (Subgroup.mem_normalizer_iff.1 hc (π a)).1 ha
  have hσ' : ∀ a ∈ A, c'⁻¹ * a * c' ∈ A := by
    intro a ha
    rw [hA, Subgroup.mem_comap] at ha ⊢
    rw [map_mul, map_mul, map_inv, hπc']
    refine (Subgroup.mem_normalizer_iff.1 hc (c⁻¹ * π a * c)).2 ?_
    rw [show c * (c⁻¹ * π a * c) * c⁻¹ = π a by group]
    exact ha
  let M : Subgroup E := twistRange A hTab c' hσ
  have hMmem : ∀ x, x ∈ M ↔ ∃ a ∈ A, x = a * (c' * a * c'⁻¹)⁻¹ := fun x => Iff.rfl
  have hMA : M ≤ A := twistRange_le
  have hAQ : A ≤ Q' := Subgroup.comap_mono le_sup_left
  have hc'Q : c' ∈ Q' := by
    rw [hQ', Subgroup.mem_comap, hπc']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hMc1 : ∀ x ∈ M, c' * x * c'⁻¹ ∈ M := fun x hx => (conj_mem_twistRange hσ' hx).1
  have hMc2 : ∀ x ∈ M, c'⁻¹ * x * c' ∈ M := fun x hx => (conj_mem_twistRange hσ' hx).2
  have hc'N : c' ∈ Subgroup.normalizer (M : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨hMc1 m, fun hm => ?_⟩
    have := hMc2 _ hm
    rwa [show c'⁻¹ * (c' * m * c'⁻¹) * c' = m by group] at this
  have hAN : A ≤ Subgroup.normalizer (M : Set E) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      have h1 : a * m * a⁻¹ = m := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hTab _ ha _ (hMA hm)
      rw [h1]
      exact hm
    · intro hm
      have hyA := hMA hm
      have h1 : a⁻¹ * (a * m * a⁻¹) * a = a * m * a⁻¹ := by
        rw [hTab _ (A.inv_mem ha) _ hyA]
        group
      have h2 : m = a⁻¹ * (a * m * a⁻¹) * a := by group
      rw [h2, h1]
      exact hm
  have hQN : Q' ≤ Subgroup.normalizer (M : Set E) := by
    intro x hx
    obtain ⟨a, ha, k, rfl⟩ := mem_comap_sup_zpowers π T c c' hπc' hc hx
    exact (Subgroup.normalizer (M : Set E)).mul_mem (hAN ha) (zpow_mem hc'N k)
  have hMQ : M ≤ Q' := hMA.trans hAQ
  have hNnormal : (M.subgroupOf Q').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMQ).2 hQN
  have hcommMQ : ⁅Q', Q'⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    let q : Q' →* Q' ⧸ M.subgroupOf Q' := QuotientGroup.mk' _
    have hAcomm : ∀ (a : E) (ha : a ∈ A) (b : E) (hb : b ∈ A),
        Commute (q ⟨a, hAQ ha⟩) (q ⟨b, hAQ hb⟩) := by
      intro a ha b hb
      show q ⟨a, hAQ ha⟩ * q ⟨b, hAQ hb⟩ = q ⟨b, hAQ hb⟩ * q ⟨a, hAQ ha⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hTab a ha b hb)
    have hAc : ∀ (a : E) (ha : a ∈ A), Commute (q ⟨a, hAQ ha⟩) (q ⟨c', hc'Q⟩) := by
      intro a ha
      show q ⟨a, hAQ ha⟩ * q ⟨c', hc'Q⟩ = q ⟨c', hc'Q⟩ * q ⟨a, hAQ ha⟩
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf]
      refine (hMmem _).2 ⟨c'⁻¹ * a⁻¹ * c', hσ' _ (A.inv_mem ha), ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hdec : ∀ x : Q', ∃ (a : E) (ha : a ∈ A) (k : ℤ),
        q x = q ⟨a, hAQ ha⟩ * q ⟨c', hc'Q⟩ ^ k := by
      intro x
      obtain ⟨a, ha, k, hk⟩ := mem_comap_sup_zpowers π T c c' hπc' hc x.2
      refine ⟨a, ha, k, ?_⟩
      have : x = ⟨a, hAQ ha⟩ * ⟨c', hc'Q⟩ ^ k := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_zpow]
        exact hk)
      rw [this, map_mul, map_zpow]
    have hcomm : ∀ x y : Q', q x * q y = q y * q x := by
      intro x y
      obtain ⟨a, ha, k, hx⟩ := hdec x
      obtain ⟨b, hb, l, hy⟩ := hdec y
      have h1 : Commute (q ⟨a, hAQ ha⟩ * q ⟨c', hc'Q⟩ ^ k)
          (q ⟨b, hAQ hb⟩ * q ⟨c', hc'Q⟩ ^ l) :=
        Commute.mul_left (Commute.mul_right (hAcomm a ha b hb) ((hAc a ha).zpow_right l))
          (Commute.mul_right (((hAc b hb).symm).zpow_left k) (Commute.zpow_zpow_self _ k l))
      rw [hx, hy]
      exact h1.eq
    have hq : q ⁅(⟨g₁, hg₁⟩ : Q'), (⟨g₂, hg₂⟩ : Q')⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
    have hmem := (QuotientGroup.eq_one_iff _).1 hq
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa [commutatorElement_def] using hmem
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨a, ha, hza⟩ := (hMmem z).1 (hcommMQ (hker hz))
  have hzc : z ∈ Subgroup.center E := hC hz
  have hπz : π z = 1 := hz
  have hπa : c * π a * c⁻¹ = π a := by
    rw [hza, map_mul, map_inv, map_mul, map_mul, map_inv, hπc'] at hπz
    have h1 : π a = (c * π a * c⁻¹) := by
      rw [mul_inv_eq_one] at hπz
      exact hπz
    exact h1.symm
  have hπaT : π a ∈ T := by
    rw [hA, Subgroup.mem_comap] at ha
    exact ha
  have hga : g * π a * g⁻¹ = π a := hgT _ hπaT hπa
  set g' : E := Function.surjInv hπ g with hg'
  have hπg' : π g' = g := Function.surjInv_eq hπ g
  have hz1 : (g' * a * g'⁻¹) * a⁻¹ ∈ Subgroup.center E := by
    refine hC ?_
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hπg']
    rw [hga, mul_inv_cancel]
  have hz2 : (g' * c' * g'⁻¹) * c' ∈ Subgroup.center E := by
    refine hC ?_
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hπg', hπc']
    rw [hgc, inv_mul_cancel]
  have hz' : z = ⁅a, c'⁆ := by rw [hza, commutatorElement_def]; group
  have hzz : z = z⁻¹ := by
    have e1 : g' * a * g'⁻¹ = ((g' * a * g'⁻¹) * a⁻¹) * a := by group
    have e2 : g' * c' * g'⁻¹ = ((g' * c' * g'⁻¹) * c') * c'⁻¹ := by group
    have h3 : ⁅g' * a * g'⁻¹, g' * c' * g'⁻¹⁆ = ⁅a, c'⁻¹⁆ := by
      rw [e1, e2]
      exact CFSG.RankThree.Classical.commutatorElement_central_mul' hz1 hz2
    have h4 : ⁅g' * a * g'⁻¹, g' * c' * g'⁻¹⁆ = ⁅a, c'⁆ := by
      refine CFSG.RankThree.Classical.commutatorElement_conj_of_mem_center ?_ g'
      rw [← hz']
      exact hzc
    have hcen : c'⁻¹ * z⁻¹ = z⁻¹ * c'⁻¹ :=
      Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hzc) (c'⁻¹)
    have h5 : ⁅a, c'⁻¹⁆ = z⁻¹ := by
      have hzi : z⁻¹ = c' * a * c'⁻¹ * a⁻¹ := by rw [hz', commutatorElement_def]; group
      calc ⁅a, c'⁻¹⁆ = c'⁻¹ * (c' * a * c'⁻¹ * a⁻¹) * c' := by rw [commutatorElement_def]; group
        _ = c'⁻¹ * z⁻¹ * c' := by rw [hzi]
        _ = z⁻¹ := by rw [hcen]; group
    calc z = ⁅a, c'⁆ := hz'
      _ = ⁅a, c'⁻¹⁆ := h4.symm.trans h3
      _ = z⁻¹ := h5
  exact Subgroup.mem_bot.2 (eq_one_of_central_inv hp2 π hCp hz hzz)

end CFSG.ClassicalInvolution.Asc77.SCH
