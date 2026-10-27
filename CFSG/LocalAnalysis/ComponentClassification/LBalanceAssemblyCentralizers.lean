module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyElement

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open Subgroup

namespace Asm

variable {X : Type*} [Group X]

theorem exists_sup_zpowers [Finite X] {p : ℕ} [Fact p.Prime] {P : Subgroup X}
    (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q < Nat.card P ∧
      ∃ x ∈ P, x ∈ normalizer (Q : Set X) ∧ P ≤ Q ⊔ zpowers x := by
  have hp : p.Prime := Fact.out
  have : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hne
  have : Group.IsNilpotent P := hP.isNilpotent
  have hdvd : p ∣ Nat.card P := hP.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
  obtain ⟨Q, hindex, hQ⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  obtain ⟨x, hx⟩ : ∃ x : P, x ∉ Q := by
    by_contra! h
    have htop : Q = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, index_top] at hindex
    exact hp.one_lt.ne hindex
  have hsup : Q ⊔ zpowers x = ⊤ := by
    have hmul := relIndex_mul_index (le_sup_left : Q ≤ Q ⊔ zpowers x)
    rw [hindex] at hmul
    rcases hp.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hmul) with h | h
    · exact index_eq_one.mp h
    · rw [h] at hmul
      have hrel : Q.relIndex (Q ⊔ zpowers x) = 1 :=
        Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans (one_mul p).symm)
      exact (hx (relIndex_eq_one.mp hrel (mem_sup_right (mem_zpowers x)))).elim
  refine ⟨Q.map P.subtype, map_subtype_le Q, ?_, x, x.2, ?_, ?_⟩
  · rw [card_map_of_injective P.subtype_injective]
    have hcard := Q.card_mul_index
    rw [hindex] at hcard
    calc Nat.card Q < Nat.card Q * p := lt_mul_of_one_lt_right Nat.card_pos hp.one_lt
      _ = Nat.card P := hcard
  · have h := le_normalizer_map (H := Q) P.subtype
    rw [normalizer_eq_top Q, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h x.2
  · have h : (Q ⊔ zpowers x).map P.subtype = Q.map P.subtype ⊔ zpowers (x : X) := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    refine le_of_eq ?_
    rw [← h, hsup, ← MonoidHom.range_eq_map, range_subtype]

theorem mem_normalizer_centralizer {Q : Subgroup X} {x : X} (hx : x ∈ normalizer (Q : Set X)) :
    x ∈ normalizer (centralizer (Q : Set X) : Set X) := by
  rw [mem_normalizer_iff] at hx ⊢
  intro c
  simp only [mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hc q hq
    have hq' : x⁻¹ * q * x ∈ Q :=
      (hx _).mpr (by rwa [show x * (x⁻¹ * q * x) * x⁻¹ = q by group])
    calc q * (x * c * x⁻¹) = x * ((x⁻¹ * q * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * q * x)) * x⁻¹ := by rw [hc _ hq']
      _ = x * c * x⁻¹ * q := by group
  · intro hc q hq
    have h := hc _ ((hx q).mp hq)
    have h2 : x * (q * c) * x⁻¹ = x * (c * q) * x⁻¹ :=
      calc x * (q * c) * x⁻¹ = x * q * x⁻¹ * (x * c * x⁻¹) := by group
        _ = x * c * x⁻¹ * (x * q * x⁻¹) := h
        _ = x * (c * q) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem le_of_perfect_le_sup_zpowers {Y L : Subgroup X} {x : X}
    (hx : x ∈ normalizer (Y : Set X)) [Group.IsPerfect L] (hL : L ≤ Y ⊔ zpowers x) : L ≤ Y := by
  obtain ⟨M, hM⟩ : ∃ M : Subgroup X, M = Y ⊔ zpowers x := ⟨_, rfl⟩
  have hYM : Y ≤ M := by
    rw [hM]
    exact le_sup_left
  have hxM : x ∈ M := by
    rw [hM]
    exact mem_sup_right (mem_zpowers x)
  have hLM : L ≤ M := hM ▸ hL
  have : (Y.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYM).mpr
      (hM.le.trans (sup_le le_normalizer (zpowers_le.mpr hx)))
  have hgen : ∀ m : M, (m : M ⧸ Y.subgroupOf M) ∈
      zpowers ((⟨x, hxM⟩ : M) : M ⧸ Y.subgroupOf M) := by
    let S : Subgroup M := (zpowers ((⟨x, hxM⟩ : M) : M ⧸ Y.subgroupOf M)).comap
      (QuotientGroup.mk' (Y.subgroupOf M))
    have hle : M ≤ S.map M.subtype := by
      refine hM.le.trans (sup_le (fun y hy => mem_map.mpr ⟨⟨y, hYM hy⟩, ?_, rfl⟩)
        (zpowers_le.mpr (mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩)))
      · show ((⟨y, hYM hy⟩ : M) : M ⧸ Y.subgroupOf M) ∈ zpowers _
        rw [(QuotientGroup.eq_one_iff (N := Y.subgroupOf M) (⟨y, hYM hy⟩ : M)).mpr hy]
        exact one_mem _
      · exact mem_zpowers _
    intro m
    obtain ⟨m', hm', hmm'⟩ := mem_map.mp (hle m.2)
    rw [show m' = m from Subtype.ext hmm'] at hm'
    exact hm'
  have hcomm : ∀ a b : M ⧸ Y.subgroupOf M, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hgen a)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hgen b)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  let f : L →* M ⧸ Y.subgroupOf M := (QuotientGroup.mk' (Y.subgroupOf M)).comp (inclusion hLM)
  have : IsMulCommutative f.range := ⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  intro l hl
  have h1 : f ⟨l, hl⟩ = 1 :=
    congrArg Subtype.val
      (Subsingleton.elim (⟨f ⟨l, hl⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : f.range) 1)
  exact (QuotientGroup.eq_one_iff (N := Y.subgroupOf M) (⟨l, hLM hl⟩ : M)).mp h1

end Asm

section

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem lBalancePLayer_centralizer_le (hX : SchreierSections X) (P : Subgroup X)
    (hP : IsPGroup p P) : lBalancePLayer p (centralizer (P : Set X)) ≤ lBalancePLayer p ⊤ := by
  induction hn : Nat.card P using Nat.strong_induction_on generalizing P with
  | h n ih =>
  by_cases hbot : P = ⊥
  · subst hbot
    have htop : centralizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (SetLike.coe_subset_coe.mpr bot_le)
    exact (congrArg (lBalancePLayer p) htop).le
  obtain ⟨Q, hQP, hcard, x, hxP, hxQ, hPQ⟩ := Asm.exists_sup_zpowers hP hbot
  have hxY := Asm.mem_normalizer_centralizer hxQ
  have hYM : centralizer (Q : Set X) ≤ centralizer (Q : Set X) ⊔ zpowers x := le_sup_left
  have hxM : x ∈ centralizer (Q : Set X) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hMN : centralizer (Q : Set X) ⊔ zpowers x ≤ normalizer (centralizer (Q : Set X) : Set X) :=
    sup_le le_normalizer (zpowers_le.mpr hxY)
  have hCP : centralizer (P : Set X) = centralizer (Q : Set X) ⊓ centralizer ({x} : Set X) := by
    refine le_antisymm (le_inf (centralizer_le hQP)
      (centralizer_le (Set.singleton_subset_iff.mpr hxP))) ?_
    rintro z ⟨hzQ, hzx⟩
    have hle : Q ⊔ zpowers x ≤ centralizer ({z} : Set X) := by
      refine sup_le (fun q hq => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hzQ q hq)) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hzx).symm
    exact mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (hle (hPQ hg))
  rw [hCP]
  have : ((centralizer (Q : Set X) ⊓ centralizer ({x} : Set X)).subgroupOf
      ((centralizer (Q : Set X) ⊔ zpowers x) ⊓ centralizer ({x} : Set X))).Normal := by
    refine (normal_subgroupOf_iff (inf_le_inf_right _ hYM)).mpr fun z c hz hc =>
      mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hMN (mem_inf.mp hc).1) z).mp (mem_inf.mp hz).1
    · exact mul_mem (mul_mem (mem_inf.mp hc).2 (mem_inf.mp hz).2) (inv_mem (mem_inf.mp hc).2)
  have h1 := pLayer_relative_normal_mono p _ _ (inf_le_inf_right (centralizer ({x} : Set X)) hYM)
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h2 := lBalancePLayer_inf_centralizer_le (p := p) hX hxM
    ⟨k, by simpa using congrArg Subtype.val hk⟩
  have : ((centralizer (Q : Set X)).subgroupOf (centralizer (Q : Set X) ⊔ zpowers x)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYM).mpr hMN
  have h3 : lBalancePLayer p (centralizer (Q : Set X) ⊔ zpowers x) ≤
      lBalancePLayer p (centralizer (Q : Set X)) := by
    refine Asm.pLayer_le_of_pComponents_le p _ _ hYM fun L hL => ?_
    have : Group.IsPerfect L := pComponent_perfect p _ L hL
    exact Asm.le_of_perfect_le_sup_zpowers hxY (subnormal_le hL.1)
  have h4 := ih (Nat.card Q) (hcard.trans_eq hn) Q (hP.to_le hQP) rfl
  exact h1.trans (h2.trans (h3.trans h4))

theorem lBalancePLayer_normalizer_le_centralizer (P : Subgroup X) (hP : IsPGroup p P) :
    lBalancePLayer p (normalizer (P : Set X)) ≤ lBalancePLayer p (centralizer (P : Set X)) := by
  refine Asm.pLayer_le_of_pComponents_le p _ _ (centralizer_le_normalizer _) fun L hL => ?_
  have hLN : L ≤ normalizer (P : Set X) := subnormal_le hL.1
  have hnative := (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ L hLN).mpr hL
  have hPN : IsPGroup p (P.subgroupOf (normalizer (P : Set X))) :=
    hP.comap_of_injective _ (normalizer (P : Set X)).subtype_injective
  have hcent := CatalogueBAlternating.pComponent_le_centralizer_normal_p p _ _ hnative hPN
  intro l hl
  refine mem_centralizer_iff.mpr fun g hg => ?_
  have h := mem_centralizer_iff.mp
    (hcent (show (⟨l, hLN hl⟩ : normalizer (P : Set X)) ∈ L.subgroupOf _ from hl))
    ⟨g, le_normalizer hg⟩ hg
  exact congrArg Subtype.val h

end

theorem l_balance_clauses_of_schreierSections {X : Type*} [Group X] [Finite X]
    (hX : SchreierSections X) (p : ℕ) (hp : p.Prime) (P : Subgroup X) (hP : IsPGroup p P) :
    lBalancePLayer p (normalizer (P : Set X)) ≤ lBalancePLayer p ⊤ ∧
      lBalancePLayer p (centralizer (P : Set X)) ≤ lBalancePLayer p ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have h := lBalancePLayer_centralizer_le hX P hP
  exact ⟨(lBalancePLayer_normalizer_le_centralizer P hP).trans h, h⟩

end CFSG.ComponentClassification.LBalance
