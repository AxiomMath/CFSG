module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsBasic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeReduce
import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ComponentClassification
open scoped MatrixGroups

section Components

variable {F : Type} [Field F] [Finite F]

theorem quasisimple_or_solvable_sl (k : ℕ) :
    CFSG.Open.IsQuasisimple SL(k, F) ∨ Group.IsSolvable SL(k, F) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · right
    have := ModelFacts.subsingleton_sl_of_le_one (F := F) (a := k) (by omega)
    infer_instance
  · rcases Nat.lt_or_ge (Nat.card F) 4 with hF | hF
    · rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · right
        obtain rfl : k = 2 := by omega
        refine CFSG.GroupTheory.groups_order_below_sixty_solvable ?_
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
        have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
        interval_cases (Nat.card F) <;> norm_num
      · left
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        exact ModelFacts.open_isQuasisimple
          (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F (by omega))
    · left
      exact ModelFacts.open_isQuasisimple_sl hk hF

omit [Finite F] in
theorem exists_two_commuting_involutions_sl (h2 : (2 : F) ≠ 0) {a : ℕ} (ha : 3 ≤ a) :
    ∃ s t : SL(a, F), s * s = 1 ∧ t * t = 1 ∧ s ≠ 1 ∧ t ≠ 1 ∧ s * t = t * s ∧ s ≠ t := by
  let T₁ : Pair a := ⟨{⟨0, by omega⟩, ⟨1, by omega⟩},
    Finset.card_pair (by simp [Fin.ext_iff])⟩
  let T₂ : Pair a := ⟨{⟨1, by omega⟩, ⟨2, by omega⟩},
    Finset.card_pair (by simp [Fin.ext_iff])⟩
  have hne1 : ∀ T : Pair a, zElt F T ≠ 1 := fun T hT => by
    have h1 : zMat F a T.1 = zMat F a (∅ : Finset (Fin a)) := by
      rw [zMat_empty, ← coe_zElt T, hT, Matrix.SpecialLinearGroup.coe_one]
    have := zMat_inj h2 h1
    have h3 := T.2
    rw [this] at h3
    simp at h3
  refine ⟨zElt F T₁, zElt F T₂, zElt_mul_self T₁, zElt_mul_self T₂, hne1 T₁, hne1 T₂,
    signGroup_comm (zElt_mem_signGroup T₁) (zElt_mem_signGroup T₂), fun h => ?_⟩
  have h1 : zMat F a T₁.1 = zMat F a T₂.1 := by
    rw [← coe_zElt T₁, ← coe_zElt T₂, h]
  have := zMat_inj h2 h1
  have h0 : (⟨0, by omega⟩ : Fin a) ∈ T₁.1 := by simp [T₁]
  rw [this] at h0
  simp [T₂, Fin.ext_iff] at h0

end Components

section Main

variable {p f : ℕ} [Fact p.Prime]

open CFSG.ClassicalInvolution.ModelFacts in
theorem card_eq_of_isClassicalMember_sl {F : Type} [Field F] [Finite F]
    (hFodd : Odd (Nat.card F)) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n)
    {L : Subgroup SL(n, F)} {z : SL(n, F)} (h : IsClassicalMember p f L z) :
    Nat.card F = p ^ f := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    refine Ring.two_ne_zero fun hc => ?_
    have h1 := FiniteField.even_card_iff_char_two.mp hc
    rw [← Nat.card_eq_fintype_card] at h1
    obtain ⟨k, hk⟩ := hFodd
    omega
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  set D : Matrix (Fin n) (Fin n) F := (z : Matrix (Fin n) (Fin n) F) with hDdef
  have hD : D * D = 1 := by
    rw [hDdef, ← Matrix.SpecialLinearGroup.coe_mul, hzz, Matrix.SpecialLinearGroup.coe_one]
  have hD' : (-D) * (-D) = 1 := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hD]
  have hz1 : z ≠ 1 := h.ne_one
  have hLC : ∀ x ∈ L, (x : Matrix (Fin n) (Fin n) F) * D = D * x := fun x hx => by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
    have h2' := congrArg Subtype.val h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2'
    exact h2'
  have hperf : Group.IsPerfect ↥L := h.perfect
  have hLsup : L ≤ longRootGroup D ⊔ longRootGroup (-D) :=
    le_sup_longRootGroup_of_perfect h2 hD hperf hLC
  obtain ⟨a, ha, P, hP, hAm⟩ := exists_longRootGroup_data h2 (by omega) hD
  obtain ⟨b, hb, P', hP', hAp⟩ := exists_longRootGroup_data h2 (by omega) hD'
  set Am : Subgroup SL(n, F) := longRootGroup D with hAmdef
  set Ap : Subgroup SL(n, F) := longRootGroup (-D) with hApdef
  have hcomm : ∀ x ∈ Am, ∀ y ∈ Ap, x * y = y * x := fun x hx y hy =>
    commute_longRootGroup_neg h2 hD hx hy
  have hzAm : z ∈ Am := by
    refine ⟨rfl, ?_⟩
    show D * (1 + D) = 1 + D
    rw [Matrix.mul_add, Matrix.mul_one, hD, add_comm]
  have hzAp : z ∉ Ap := by
    intro hz
    have h3 : D * (1 + -D) = 1 + -D := hz.2
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, hD] at h3
    have h4 : D + D = 1 + 1 := by
      calc D + D = (D + -1) + (D + 1) := by abel
        _ = (1 + -D) + (D + 1) := by rw [h3]
        _ = 1 + 1 := by abel
    have h5 : D = 1 := by
      have : (2 : F) • D = (2 : F) • (1 : Matrix (Fin n) (Fin n) F) := by
        rw [two_smul, two_smul, h4]
      exact smul_right_injective _ h2 this
    exact hz1 (Subtype.ext h5)
  obtain ⟨eAm⟩ := nonempty_mulEquiv_longRootGroup ha hAm
  obtain ⟨eAp⟩ := nonempty_mulEquiv_longRootGroup hb hAp
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have hsub : Subsingleton SL(a, F) := subsingleton_sl_of_le_one (by omega)
    have : Subsingleton Am := eAm.surjective.subsingleton
    exact hz1 (congrArg Subtype.val (Subsingleton.elim (⟨z, hzAm⟩ : Am) 1))
  have hAmC : Am ≤ Subgroup.centralizer ({z} : Set SL(n, F)) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hx.1
  have hApqs : CFSG.Open.IsQuasisimple ↥Ap ∨ Group.IsSolvable ↥Ap := by
    rcases quasisimple_or_solvable_sl (F := F) b with hqs | hs
    · exact Or.inl (Components.quasisimple_of_equiv eAp.symm hqs)
    · exact Or.inr (Group.isSolvable_of_surjective (f := eAp.toMonoidHom) eAp.surjective)
  have hAmqs : CFSG.Open.IsQuasisimple ↥Am ∨ Group.IsSolvable ↥Am := by
    rcases quasisimple_or_solvable_sl (F := F) a with hqs | hs
    · exact Or.inl (Components.quasisimple_of_equiv eAm.symm hqs)
    · exact Or.inr (Group.isSolvable_of_surjective (f := eAm.toMonoidHom) eAm.surjective)
  have hq4 : 4 ≤ p ^ f := by omega
  by_cases ha3 : 3 ≤ a
  ·
    exfalso
    obtain ⟨-, hLeq⟩ := quasisimple_and_eq_of_isClassicalMember hq4 h hcomm hLsup hzAp hAmC
      hAmqs hApqs
    obtain ⟨s, t, hs2, ht2, hs1, ht1, hst, hne⟩ := exists_two_commuting_involutions_sl h2 ha3
    obtain ⟨e2⟩ := h.nonempty_equiv
    let eL : SL(a, F) ≃* ↥L := eAm.trans (MulEquiv.subgroupCongr hLeq.symm)
    have hord : ∀ x : SL(a, F), x * x = 1 → x ≠ 1 → orderOf (eL x) = 2 := fun x hx hx1 => by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
    exact false_of_two_commuting_involutions hodd e2 (hord s hs2 hs1) (hord t ht2 ht1)
      (by rw [← map_mul, ← map_mul, hst]) (fun hab => hne (eL.injective hab))
  · obtain rfl : a = 2 := by omega
    by_cases hF4 : 4 ≤ Nat.card F
    · obtain ⟨-, hLeq⟩ := quasisimple_and_eq_of_isClassicalMember hq4 h hcomm hLsup hzAp hAmC
        hAmqs hApqs
      exact card_eq_of_isClassicalMember_equiv_sl2 h hq hF4
        (eAm.trans (MulEquiv.subgroupCongr hLeq.symm))
    ·
      exfalso
      have := isSolvable_sl_two_of_card_lt (F := F) (by omega)
      have hsolv : Group.IsSolvable ↥Am :=
        Group.isSolvable_of_surjective (f := eAm.toMonoidHom) eAm.surjective
      exact hzAp (le_of_perfect_of_solvable_commuting hcomm hsolv hLsup hperf h.mem)

theorem classicalMemberParametersAt_psl : ClassicalMemberParametersAt p f .PSL := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have hn : 2 ≤ n := hadm.2.2.1
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Fact r.Prime := ⟨hr⟩
  have hcard : Nat.card (GaloisField r e) = r ^ e := GaloisField.card r e (by omega)
  have hodd : Odd (Nat.card (GaloisField r e)) := by
    rw [hcard]
    exact (hr.odd_of_ne_two hr2).pow
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h1 := card_eq_of_isClassicalMember_sl hodd hp2 hq hn (L := L) (z := z) hL
  rw [hcard] at h1
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hr Fact.out (by omega) hf h1
  exact ⟨rfl, Or.inl rfl⟩

end Main

end CFSG.ClassicalInvolution.Upgrade
