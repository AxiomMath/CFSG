module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit
public import CFSG.ClassicalInvolution.RouteD.TypeABridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ComponentClassification
open CFSG.ClassicalInvolution.WeakCT (blockSL blockSL_injective)
open scoped MatrixGroups

section Factors

variable {F : Type} [Field F] {n : ℕ}

theorem nonempty_mulEquiv_longRootGroup {a : ℕ} (ha : a ≤ n) {P : SL(n, F)}
    {D : Matrix (Fin n) (Fin n) F}
    (h : longRootGroup D =
      ((blockSL F n a 0 (by omega)).range).map (MulAut.conj P).toMonoidHom) :
    Nonempty (SL(a, F) ≃* longRootGroup D) := by
  let φ : SL(a, F) →* SL(n, F) := (MulAut.conj P).toMonoidHom.comp (blockSL F n a 0 (by omega))
  have hφ : Function.Injective φ := (MulAut.conj P).injective.comp (blockSL_injective _)
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr (by
    rw [h, MonoidHom.range_comp]))⟩

theorem open_isQuasisimple_sl [Finite F] {a : ℕ} (ha : 2 ≤ a) (hF : 4 ≤ Nat.card F) :
    CFSG.Open.IsQuasisimple SL(a, F) := by
  rcases Nat.lt_or_ge a 3 with h | h
  · obtain rfl : a = 2 := by omega
    exact isQuasisimple_specialLinearGroup_two hF
  · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    exact open_isQuasisimple (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F (by omega))

end Factors

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem isLongRootSL2_of_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n)
    {L : Subgroup SL(n, GaloisField p f)} {z : SL(n, GaloisField p f)}
    (h : IsClassicalMember p f L z) : IsLongRootSL2 hn L z := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  set F := GaloisField p f with hFdef
  have hcard : Nat.card F = p ^ f := GaloisField.card p f hf
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have : ringChar F ∣ 2 := ringChar.dvd (by simpa using h0)
    rw [ringChar.eq F p] at this
    have := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this
    exact hp2 this
  have hF5 : 5 ≤ Nat.card F := by rw [hcard]; exact hq
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
  have hAmq : CFSG.Open.IsQuasisimple ↥Am :=
    Components.quasisimple_of_equiv eAm.symm (open_isQuasisimple_sl (F := F) ha2 (by omega))
  have hAmC : Am ≤ Subgroup.centralizer ({z} : Set SL(n, F)) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hx.1
  have hBq : Ap = ⊥ ∨ CFSG.Open.IsQuasisimple ↥Ap := by
    by_cases hb2 : 2 ≤ b
    · exact Or.inr (Components.quasisimple_of_equiv eAp.symm
        (open_isQuasisimple_sl (F := F) hb2 (by omega)))
    · left
      have hsub : Subsingleton SL(b, F) := subsingleton_sl_of_le_one (by omega)
      have : Subsingleton Ap := eAp.surjective.subsingleton
      exact Subgroup.eq_bot_of_subsingleton Ap
  have hLeq : L = Am := eq_of_le_sup_of_isClassicalMember (by omega) h hcomm hLsup hzAp hAmC hAmq hBq
  have ha3 : ¬ 3 ≤ a := by
    intro ha3
    obtain ⟨e2⟩ := h.nonempty_equiv
    exact false_of_sl_equiv_quotient_sl2 hF5 ha3
      (eAm.trans (MulEquiv.subgroupCongr hLeq.symm)) e2
  obtain rfl : a = 2 := by omega
  refine ⟨P, ?_, ?_⟩
  · rw [hLeq]
    exact hAm
  · have hdiag : negBlock F n 0 =
        Matrix.diagonal (fun j : Fin n => if j.val < 2 then (-1 : F) else 1) := by
      rw [negBlock_eq_diagonal]
      congr 1
      funext j
      simp
    have hPP : (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
        1 := coe_mul_coe_inv P
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootInv, hdiag,
      ← hP, Matrix.mul_assoc, hPP, Matrix.mul_one]

theorem classicalMembersFundamental_psl (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 2 ≤ n) : ClassicalMembersFundamental p f .PSL n f hp := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro L z hL
  exact RouteD.longRootSet_subset_fundamentalSubgroups_psl hn
    ⟨z, isLongRootSL2_of_isClassicalMember hp2 hq hn hL⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts
