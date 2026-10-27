module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup MulAction

@[expose] def FooteThompsonFusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (t t' : H), orderOf t = 2 →
    ∀ P : Sylow 2 ↥(centralizer ({t} : Set H)),
    (∀ x : H, (x ∈ (P : Subgroup _).map (centralizer ({t} : Set H)).subtype ∧ IsConj t x) ↔
      x = t ∨ x = t') →
    t ∉ normalClosure ({t * t'} : Set H)

variable {H : Type} [Group H]

theorem mem_fixedBy_quotient_iff (K : Subgroup H) (t g : H) :
    (g : H ⧸ K) ∈ fixedBy (H ⧸ K) t ↔ g⁻¹ * t * g ∈ K := by
  rw [mem_fixedBy, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    show (t * g)⁻¹ * g = (g⁻¹ * t * g)⁻¹ by group, inv_mem_iff]

theorem card_fixedBy_mul_card [Finite H] (K : Subgroup H) (t : H) :
    Nat.card (fixedBy (H ⧸ K) t) * Nat.card K = Nat.card {g : H // g⁻¹ * t * g ∈ K} := by
  let e : H ≃ (H ⧸ K) × K := groupEquivQuotientProdSubgroup
  have he : ∀ g : H, (e g).1 = (g : H ⧸ K) := fun g => rfl
  let e' : {g : H // g⁻¹ * t * g ∈ K} ≃ {x : (H ⧸ K) × K // x.1 ∈ fixedBy (H ⧸ K) t} :=
    e.subtypeEquiv fun g => by rw [he, mem_fixedBy_quotient_iff]
  rw [Nat.card_congr (e'.trans (Equiv.prodSubtypeFstEquivSubtypeProd)), Nat.card_prod]

theorem card_conj_eq [Finite H] {t x : H} (hx : IsConj t x) :
    Nat.card {g : H // g⁻¹ * t * g = x} = Nat.card (centralizer ({t} : Set H)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hx
  refine Nat.card_congr ⟨fun g => ⟨g.1 * c, ?_⟩, fun g => ⟨g.1 * c⁻¹, ?_⟩, fun g => ?_,
    fun g => ?_⟩
  · have h := g.2
    apply mem_centralizer_singleton_iff.mpr
    calc g.1 * c * t = g.1 * (c * t * c⁻¹) * c := by group
      _ = g.1 * (g.1⁻¹ * t * g.1) * c := by rw [h]
      _ = t * (g.1 * c) := by group
  · have h := mem_centralizer_singleton_iff.mp g.2
    calc (g.1 * c⁻¹)⁻¹ * t * (g.1 * c⁻¹) = c * (g.1⁻¹ * (t * g.1)) * c⁻¹ := by group
      _ = c * (g.1⁻¹ * (g.1 * t)) * c⁻¹ := by rw [h]
      _ = c * t * c⁻¹ := by group
  · ext
    simp
  · ext
    simp

variable [Finite H]

theorem card_conj_mem_eq {t t' : H} (htt' : t ≠ t') (P : Subgroup H)
    (hP : ∀ x : H, (x ∈ P ∧ IsConj t x) ↔ x = t ∨ x = t') :
    Nat.card {g : H // g⁻¹ * t * g ∈ P} = 2 * Nat.card (centralizer ({t} : Set H)) := by
  classical
  have hconj : ∀ g : H, IsConj t (g⁻¹ * t * g) := fun g =>
    isConj_iff.mpr ⟨g⁻¹, by group⟩
  have ht' : IsConj t t' := ((hP t').mpr (Or.inr rfl)).2
  have hiff : ∀ g : H, g⁻¹ * t * g ∈ P ↔ g⁻¹ * t * g = t ∨ g⁻¹ * t * g = t' := fun g =>
    ⟨fun h => (hP _).mp ⟨h, hconj g⟩, fun h => ((hP _).mpr h).1⟩
  have : Fintype H := Fintype.ofFinite H
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
    Fintype.card_subtype_or_disjoint _ _ (fun p hp hq g hg => htt' ((hp g hg).symm.trans
      (hq g hg))), ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_conj_eq (IsConj.refl t), card_conj_eq ht', two_mul]

theorem card_fixedBy_eq {t t' : H} (htt' : t ≠ t') (P : Subgroup H)
    (hPC : P ≤ centralizer ({t} : Set H))
    (hP : ∀ x : H, (x ∈ P ∧ IsConj t x) ↔ x = t ∨ x = t') :
    Nat.card (fixedBy (H ⧸ P) t) = 2 * (P.subgroupOf (centralizer ({t} : Set H))).index := by
  have h := card_fixedBy_mul_card P t
  rw [card_conj_mem_eq htt' P hP] at h
  have hidx := (P.subgroupOf (centralizer ({t} : Set H))).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv] at hidx
  have hpos : 0 < Nat.card P := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, mul_assoc, hidx]

theorem two_dvd_index_of_two_conjugates {t t' : H} (ht : orderOf t = 2) (htt' : t ≠ t')
    (P : Subgroup H) (hPC : P ≤ centralizer ({t} : Set H))
    (hP : ∀ x : H, (x ∈ P ∧ IsConj t x) ↔ x = t ∨ x = t') : 2 ∣ P.index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (H ⧸ P) := Fintype.ofFinite _
  let f : Function.End (H ⧸ P) := fun x => t • x
  have hf : f ^ 2 ^ 1 = 1 := by
    funext x
    show t • t • x = x
    rw [← mul_smul, ← sq, ← ht, pow_orderOf_eq_one, one_smul]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) hf
  have hfix : Fintype.card (Function.fixedPoints f) = Nat.card (fixedBy (H ⧸ P) t) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hfix, card_fixedBy_eq htt' P hPC hP, ← Nat.card_eq_fintype_card] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 2 _)))

theorem not_mem_normalClosure_of_four_dvd_index {t t' : H} (ht : orderOf t = 2)
    (P : Subgroup H) (hPC : P ≤ centralizer ({t} : Set H))
    (hPodd : ¬ 2 ∣ (P.subgroupOf (centralizer ({t} : Set H))).index)
    (hP : ∀ x : H, (x ∈ P ∧ IsConj t x) ↔ x = t ∨ x = t')
    (h4 : 4 ∣ (centralizer ({t} : Set H)).index) :
    t ∉ normalClosure ({t * t'} : Set H) := by
  classical
  by_cases htt' : t = t'
  · subst htt'
    rw [← sq, ← ht, pow_orderOf_eq_one]
    intro h
    have hle : normalClosure ({1} : Set H) ≤ ⊥ :=
      normalClosure_le_normal (by simp)
    rw [mem_bot.mp (hle h), orderOf_one] at ht
    exact absurd ht (by norm_num)
  have : Fintype (H ⧸ P) := Fintype.ofFinite _
  let sgn : H →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom H (H ⧸ P))
  have hst : sgn t = -1 := by
    have hσ : (MulAction.toPerm t : Equiv.Perm (H ⧸ P)) ^ 2 = 1 := by
      ext x
      rw [sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      show t • t • x = x
      rw [← mul_smul, ← sq, ← ht, pow_orderOf_eq_one, one_smul]
    show Equiv.Perm.sign (MulAction.toPerm t) = -1
    have hfix : Fintype.card (Function.fixedPoints (MulAction.toPerm t : Equiv.Perm (H ⧸ P))) =
        Nat.card (fixedBy (H ⧸ P) t) := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [Equiv.Perm.sign_of_pow_two_eq_one hσ, hfix, ← Nat.card_eq_fintype_card,
      card_fixedBy_eq htt' P hPC hP]
    have hmul : (P.subgroupOf (centralizer ({t} : Set H))).index *
        (centralizer ({t} : Set H)).index = P.index := relIndex_mul_index hPC
    set m := (P.subgroupOf (centralizer ({t} : Set H))).index
    have hm : Odd m := Nat.odd_iff.mpr (by omega)
    obtain ⟨j, hj⟩ := h4
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
      have := (centralizer ({t} : Set H)).index_ne_zero_of_finite
      exact ⟨j - 1, by omega⟩
    have e1 : m * (4 * (j' + 1)) = 2 * (m * (2 * j' + 1)) + 2 * m := by ring
    show (-1 : ℤˣ) ^ ((P.index - 2 * m) / 2) = -1
    rw [← hmul, hj, e1, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num)]
    exact (hm.mul (odd_two_mul_add_one j')).neg_one_pow
  have hconj : IsConj t t' := ((hP t').mpr (Or.inr rfl)).2
  have hst' : sgn t' = sgn t := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    rw [map_mul, map_mul, map_inv, mul_comm (sgn c), mul_inv_cancel_right]
  have hz : normalClosure ({t * t'} : Set H) ≤ sgn.ker := by
    refine normalClosure_le_normal ?_
    rintro _ rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, hst', hst]
    rfl
  intro h
  have := hz h
  rw [MonoidHom.mem_ker, hst] at this
  exact absurd this (by decide)

end CFSG.ComponentClassification.FooteLit
