module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
import CFSG.FeitThompson.Representations.TIDadeMapEqualsInduction
import CFSG.FeitThompson.Representations.TISetDadeData
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise MulAction Subgroup

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}

structure IsFreeCentralSection (p a : ℕ) (L P E Z : Subgroup G) : Prop where
  prime : p.Prime
  odd_prime : Odd p
  one_le_exponent : 1 ≤ a
  natCard_P : Nat.card P = p ^ a
  odd_natCard_L : Odd (Nat.card L)
  P_le : P ≤ L
  le_normalizer_P : L ≤ normalizer (P : Set G)
  E_le : E ≤ L
  sup_eq : P ⊔ E = L
  inf_eq_bot : P ⊓ E = ⊥
  E_ne_bot : E ≠ ⊥
  Z_ne_bot : Z ≠ ⊥
  le_normalizer_Z : L ≤ normalizer (Z : Set G)
  Z_le_center : Z ≤ P ⊓ centralizer (P : Set G)
  inf_centralizer_eq_bot : ∀ u ∈ E, u ≠ 1 → Z ⊓ centralizer ({u} : Set G) = ⊥
  stabilizer_punctured_eq : {g : G | (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1})
    = (P : Set G) \ {1}} = (L : Set G)
  inter_conj_eq_empty : ∀ g ∉ L, ((P : Set G) \ {1})
    ∩ ((fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1})) = ∅

theorem orderOf_eq_of_isConj {x y : G} (hxy : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  exact SemiconjBy.orderOf_eq c (by unfold SemiconjBy; group)

namespace IsFreeCentralSection

variable (h : IsFreeCentralSection p a L P E Z)

include h

theorem isPGroup_P : IsPGroup p P := IsPGroup.of_card h.natCard_P

theorem P_ne_bot : P ≠ ⊥ := by
  have hpa : 1 < Nat.card P := by
    rw [h.natCard_P]
    have ha := h.one_le_exponent
    exact Nat.one_lt_pow (by omega) h.prime.one_lt
  intro hbot
  rw [hbot, Subgroup.card_bot] at hpa
  omega

theorem Z_le_P : Z ≤ P := h.Z_le_center.trans inf_le_left

theorem Z_le : Z ≤ L := h.Z_le_P.trans h.P_le

theorem isPGroup_Z : IsPGroup p Z := h.isPGroup_P.to_le h.Z_le_P

theorem E_le_normalizer_P : E ≤ normalizer (P : Set G) := h.E_le.trans h.le_normalizer_P

theorem E_le_normalizer_Z : E ≤ normalizer (Z : Set G) := h.E_le.trans h.le_normalizer_Z

theorem normal_subgroupOf : (P.subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.P_le).2 h.le_normalizer_P

theorem isTI : IsTIWithNormalizer ((P : Set G) \ {1}) L := by
  have hne : ((P : Set G) \ {1}).Nonempty := by
    have hP := h.P_ne_bot
    rw [Subgroup.ne_bot_iff_exists_ne_one] at hP
    obtain ⟨x, hx⟩ := hP
    exact ⟨x, x.2, by simpa using hx⟩
  have h1 : (1 : G) ∉ (P : Set G) \ {1} := by simp
  have hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) ∩ ((P : Set G) \ {1}) = ∅ := by
    intro g
    by_cases hg : g ∈ L
    · refine Or.inl ?_
      have hg' : g ∈ (L : Set G) := hg
      rw [← h.stabilizer_punctured_eq] at hg'
      exact hg'
    · exact Or.inr (by rw [Set.inter_comm]; exact h.inter_conj_eq_empty g hg)
  have key := isTIWithNormalizer_normalizer hne h1 hTI
  have hLeq : Subgroup.normalizer ((P : Set G) \ {1}) = L := by
    refine SetLike.ext' ?_
    rw [← h.stabilizer_punctured_eq]
    exact Set.ext fun g => mem_normalizer_iff_conjInv_image_eq
  rwa [hLeq] at key

theorem normalizer_eq : normalizer (P : Set G) = L := by
  rw [← h.isTI.normalizer_eq]
  ext g
  simp only [Subgroup.mem_set_normalizer_iff, Set.mem_sdiff, Set.mem_singleton_iff,
    SetLike.mem_coe]
  refine ⟨fun hg x => ⟨fun hx => ⟨(hg x).1 hx.1, by simpa using hx.2⟩,
      fun hx => ⟨(hg x).2 hx.1, by simpa using hx.2⟩⟩, fun hg x => ?_⟩
  by_cases hx1 : x = 1
  · subst hx1; simp
  · exact ⟨fun hx => ((hg x).1 ⟨hx, hx1⟩).1, fun hx => ((hg x).2 ⟨hx, by simpa using hx1⟩).1⟩

theorem coe_L_eq_mul : (L : Set G) = (P : Set G) * (E : Set G) := by
  rw [← h.sup_eq]
  exact Subgroup.coe_mul_of_right_le_normalizer_left P E h.E_le_normalizer_P

theorem exists_mem_mul {l : G} (hl : l ∈ L) : ∃ v ∈ P, ∃ u ∈ E, v * u = l := by
  have hmem : l ∈ (P : Set G) * (E : Set G) := by rw [← h.coe_L_eq_mul]; exact hl
  obtain ⟨v, hv, u, hu, hvu⟩ := Set.mem_mul.1 hmem
  exact ⟨v, hv, u, hu, hvu⟩

theorem natCard_mul_natCard : Nat.card P * Nat.card E = Nat.card L := by
  have key := natCard_sup_mul_natCard_inf_of_le_normalizer (S := P) (T := E) h.E_le_normalizer_P
  rw [h.sup_eq, h.inf_eq_bot] at key
  simpa using key.symm

theorem index_subgroupOf_eq [Finite G] : (P.subgroupOf L).index = Nat.card E := by
  have h1 : Nat.card (P.subgroupOf L) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe h.P_le).toEquiv
  have h2 := Subgroup.index_mul_card (P.subgroupOf L)
  rw [h1] at h2
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P)) ?_
  rw [h2, ← h.natCard_mul_natCard, Nat.mul_comm]

theorem natCard_E_dvd [Finite G] : Nat.card E ∣ Nat.card Z - 1 := by
  let φ : E →* MulAut Z := (Z.normalizerMonoidHom).comp (Subgroup.inclusion h.E_le_normalizer_Z)
  have hφ : ∀ u : E, u ≠ 1 → ∀ z : Z, φ u z = z → z = 1 := by
    intro u hu z hz
    have hc : (u : G) * (z : G) * (u : G)⁻¹ = (z : G) := by
      have := congrArg Subtype.val hz
      simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    have hz' : (z : G) ∈ Z ⊓ centralizer ({(u : G)} : Set G) :=
      Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_iff.2 (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact mul_inv_eq_iff_eq_mul.1 hc)⟩
    rw [h.inf_centralizer_eq_bot u u.2 (by simpa using hu)] at hz'
    exact Subtype.ext (by simpa using hz')
  let _ : MulDistribMulAction E Z := MulDistribMulAction.compHom (↥Z) φ
  let S : SubMulAction E Z :=
    { carrier := {1}ᶜ
      smul_mem' := fun u _ hx hx1 => hx (smul_left_cancel u (by rw [hx1, smul_one])) }
  have hst : ∀ x : S, stabilizer E x = ⊥ := by
    intro x
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    by_contra hu1
    exact x.2 (hφ u hu1 x.1 (congrArg Subtype.val (mem_stabilizer_iff.1 hu)))
  have h1 : Nat.card S = Nat.card (Quotient (orbitRel E S)) * Nat.card E := by
    rw [Nat.card_congr (selfEquivOrbitsQuotientProd hst), Nat.card_prod]
  have h2 : Nat.card S = Nat.card Z - 1 := by
    classical
    have : Fintype Z := Fintype.ofFinite _
    have h3 : Nat.card S = Nat.card {x : Z // ¬ x = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    rw [h3, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun x : Z => x = 1)]
    simp
  exact ⟨_, by rw [← h2, h1, Nat.mul_comm]⟩

theorem not_dvd_natCard_E [Finite G] : ¬ p ∣ Nat.card E := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hZnt : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).2 h.Z_ne_bot
  obtain ⟨n, hn, hZ⟩ := h.isPGroup_Z.nontrivial_iff_card.1 hZnt
  intro hpe
  have hp1 : p ∣ Nat.card Z - 1 := hpe.trans h.natCard_E_dvd
  have hpZ : p ∣ Nat.card Z := hZ ▸ dvd_pow_self p hn.ne'
  have h1 : 1 ≤ Nat.card Z := Nat.card_pos
  have hd := Nat.dvd_sub hpZ hp1
  rw [Nat.sub_sub_self h1] at hd
  exact h.prime.one_lt.ne' (Nat.dvd_one.1 hd)

theorem coprime_natCard [Finite G] : Nat.Coprime (Nat.card P) (Nat.card E) := by
  rw [h.natCard_P]
  exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd h.prime).2 h.not_dvd_natCard_E)

theorem mem_P_of_orderOf_eq_pow [Finite G] {x : G} (hx : x ∈ L) {k : ℕ}
    (hord : orderOf x = p ^ k) : x ∈ P := by
  have _ := h.normal_subgroupOf
  set y : L := ⟨x, hx⟩ with hy
  have hyord : orderOf y = p ^ k := by rw [← Subgroup.orderOf_coe y, ← hord]
  set q : L →* L ⧸ P.subgroupOf L := QuotientGroup.mk' (P.subgroupOf L) with hq
  have h1 : orderOf (q y) ∣ p ^ k := hyord ▸ orderOf_map_dvd q y
  have h2 : orderOf (q y) ∣ Nat.card E := by
    rw [← h.index_subgroupOf_eq, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card E) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd h.prime).2 h.not_dvd_natCard_E)
  have h3 : q y = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  simpa [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hy] using h3

theorem mem_P_of_isPGroup [Finite G] {R : Subgroup G} (hR : IsPGroup p R) {x : G}
    (hxR : x ∈ R) (hxL : x ∈ L) : x ∈ P := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hR ⟨x, hxR⟩
  rw [Subgroup.orderOf_mk] at hk
  exact h.mem_P_of_orderOf_eq_pow hxL hk

theorem natCard_P_eq_factorization [Finite G] :
    Nat.card P = p ^ ((Nat.card G).factorization p) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨R, hPR⟩ := h.isPGroup_P.exists_le_sylow
  have hnorm : normalizer ((P.subgroupOf R : Subgroup R) : Set R) ≤ P.subgroupOf R := by
    intro x hx
    rw [← Subgroup.subgroupOf_normalizer_eq hPR, Subgroup.mem_subgroupOf] at hx
    rw [h.normalizer_eq] at hx
    exact Subgroup.mem_subgroupOf.2 (h.mem_P_of_isPGroup R.isPGroup' x.2 hx)
  have htop : P.subgroupOf (R : Subgroup G) = ⊤ := by
    by_contra hne
    have hlt : P.subgroupOf (R : Subgroup G) < ⊤ := lt_of_le_of_ne le_top hne
    have _ : Group.IsNilpotent (R : Subgroup G) := R.isPGroup'.isNilpotent
    exact absurd (Group.normalizerCondition_of_isNilpotent _ hlt) (not_lt_of_ge hnorm)
  rw [le_antisymm hPR (Subgroup.subgroupOf_eq_top.1 htop)]
  exact R.card_eq_multiplicity

noncomputable def sylow [Finite G] : Sylow p G :=
  have : Fact p.Prime := ⟨h.prime⟩
  Sylow.ofCard P h.natCard_P_eq_factorization

@[simp] theorem coe_sylow [Finite G] : (h.sylow : Subgroup G) = P := (rfl)

theorem centralizer_eq {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) = P := by
  have hzc := Subgroup.mem_inf.1 (h.Z_le_center hz)
  have hzU : z ∈ (P : Set G) \ {1} := ⟨hzc.1, by simpa using hz1⟩
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨v, hv, u, hu, rfl⟩ := h.exists_mem_mul (h.isTI.centralizer_le hzU hx)
    have hzv : z * v = v * z := (hzc.2 v hv).symm
    have hzx : z * (v * u) = v * u * z := hx z rfl
    have hzu : z * u = u * z := by
      refine mul_left_cancel (a := v) ?_
      calc v * (z * u) = (v * z) * u := by group
        _ = (z * v) * u := by rw [hzv]
        _ = z * (v * u) := by group
        _ = v * u * z := hzx
        _ = v * (u * z) := by group
    have hu1 : u = 1 := by
      by_contra hu1
      have hmem : z ∈ Z ⊓ centralizer ({u} : Set G) :=
        Subgroup.mem_inf.2 ⟨hz, Subgroup.mem_centralizer_iff.2 (by
          intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact hzu.symm)⟩
      rw [h.inf_centralizer_eq_bot u hu hu1] at hmem
      exact hz1 (by simpa using hmem)
    rw [hu1, mul_one]
    exact hv
  · exact Subgroup.mem_centralizer_iff.2 (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hzc.2 x hx).symm)

theorem inf_centralizer_eq_P {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    L ⊓ centralizer ({z} : Set G) = P := by
  rw [h.centralizer_eq hz hz1]
  exact inf_eq_right.2 h.P_le

theorem indClassFun_restrict [Fintype G] {f : L → ℂ} (hf : IsClassFun f)
    (hf0 : ∀ x : L, (x : G) ∉ (P : Set G) \ {1} → f x = 0) (l : L) :
    indClassFun L f (l : G) = f l := by
  rw [← tiDadeMap_eq_indClassFun h.isTI hf hf0]
  by_cases hl : (l : G) ∈ (P : Set G) \ {1}
  · exact tiDadeMap_apply_mem h.isTI hf l hl
  · rw [tiDadeMap_eq_zero ?_, (hf0 l hl).symm]
    intro x hx hxl
    refine hl ⟨?_, ?_⟩
    · have : Fact p.Prime := ⟨h.prime⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h.isPGroup_P ⟨(x : G), hx.1⟩
      rw [Subgroup.orderOf_mk] at hk
      exact h.mem_P_of_orderOf_eq_pow l.2 ((orderOf_eq_of_isConj hxl).symm.trans hk)
    · intro hl1
      refine hx.2 ?_
      rw [Set.mem_singleton_iff] at hl1 ⊢
      have hord := orderOf_eq_of_isConj hxl
      rw [hl1, orderOf_one] at hord
      exact orderOf_eq_one_iff.1 hord

end IsFreeCentralSection

end CFSG.FeitThompson
