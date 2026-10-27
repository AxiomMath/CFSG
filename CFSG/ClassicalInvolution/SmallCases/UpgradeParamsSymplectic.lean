module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsBasic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeReduce

public section

namespace CFSG.ClassicalInvolution.Upgrade

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ComponentClassification
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Components

variable {r e : ℕ} [Fact r.Prime] {F : Type} [Field F] [Finite F]

theorem quasisimple_or_solvable_sp (hr2 : r ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = r ^ e) (k : ℕ) :
    CFSG.Open.IsQuasisimple (StatedSp k F) ∨ Group.IsSolvable (StatedSp k F) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases Nat.lt_or_ge k 1 with hk0 | hk1
    · right
      obtain rfl : k = 0 := by omega
      have := ModelFacts.subsingleton_statedSp_zero (F := F)
      infer_instance
    · obtain rfl : k = 1 := by omega
      rcases Nat.lt_or_ge (Nat.card F) 4 with hF4 | hF4
      · right
        have := isSolvable_sl_two_of_card_lt (F := F) hF4
        exact Group.isSolvable_of_surjective (f := (longBlockEquivOne F).toMonoidHom)
          (longBlockEquivOne F).surjective
      · left
        exact Components.quasisimple_of_equiv (longBlockEquivOne F).symm
          (isQuasisimple_specialLinearGroup_two hF4)
  · left
    have hodd : r ^ e ≠ 2 := by
      intro h2
      have := (Nat.Prime.pow_eq_iff Nat.prime_two).1 (by rw [← h2] : (r : ℕ) ^ e = 2)
      exact hr2 this.1
    exact ModelFacts.open_isQuasisimple
      (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible k F
        (p := r) (f := e) ⟨Fact.out, he, hk, fun h' => hodd (by simpa using congrArg Prod.snd h')⟩
        hF)

theorem card_eq_of_isClassicalMember_equiv_sp {p f : ℕ} [Fact p.Prime] (h2 : (2 : F) ≠ 0)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) {a : ℕ} (ha : 1 ≤ a) (eL : StatedSp a F ≃* ↥L) :
    Nat.card F = p ^ f := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · obtain rfl : a = 1 := by omega
    exact card_eq_of_isClassicalMember_equiv_sl2' h hq ((longBlockEquivOne F).trans eL)
  · exfalso
    let k₁ : Fin a := ⟨0, by omega⟩
    let k₂ : Fin a := ⟨1, by omega⟩
    have hk : k₁ ≠ k₂ := by simp [k₁, k₂, Fin.ext_iff]
    have hord : ∀ k : Fin a, orderOf (longInv F a k) = 2 := fun k =>
      (isClassicalSL2_longRootSp2 h2 k).orderOf_eq_two
    have hc : longInv F a k₁ * longInv F a k₂ = longInv F a k₂ * longInv F a k₁ := by
      apply mat_injective
      rw [map_mul, map_mul, mat_longInv, mat_longInv, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext t
      exact mul_comm _ _
    obtain ⟨e2⟩ := h.nonempty_equiv
    exact ModelFacts.false_of_two_commuting_involutions hodd e2 (a := eL (longInv F a k₁))
      (b := eL (longInv F a k₂)) (by rw [MulEquiv.orderOf_eq]; exact hord k₁)
      (by rw [MulEquiv.orderOf_eq]; exact hord k₂) (by rw [← map_mul, ← map_mul, hc])
      (fun hab => longInv_ne_of_ne h2 hk (eL.injective hab))

end Components

section Main

variable {p f r e : ℕ} [Fact p.Prime] [Fact r.Prime]

open CFSG.ClassicalInvolution.ModelFacts in
theorem card_eq_of_isClassicalMember_sp (hr2 : r ≠ 2) (he : 1 ≤ e) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = r ^ e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ}
    {L : Subgroup (StatedSp m F)} {z : StatedSp m F} (h : IsClassicalMember p f L z) :
    Nat.card F = p ^ f := by
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    refine Ring.two_ne_zero fun hc => ?_
    have h1 := FiniteField.even_card_iff_char_two.mp hc
    rw [← Nat.card_eq_fintype_card, hF] at h1
    have hodd : Odd (r ^ e) := (Nat.Prime.odd_of_ne_two Fact.out hr2).pow
    rw [Nat.odd_iff.mp hodd] at h1
    omega
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := h.ne_one
  obtain ⟨S, g, hg⟩ := exists_mul_eq_stdInv h2 hzz
  have hzg : z = g * stdInv F S * g⁻¹ := by rw [← hg]; group
  have hLC : ∀ x ∈ L, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
  have hLsup : L ≤ longRootGroup z ⊔ complGroup z := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute h2 hzz (hLC x hx)
    exact Subgroup.mul_mem_sup ha hb
  have hcomm : ∀ x ∈ longRootGroup z, ∀ y ∈ complGroup z, x * y = y * x :=
    fun x hx y hy => commute_of_mem_longRootGroup_of_mem_complGroup h2 hzz hx hy
  have hzAp : z ∉ complGroup z := fun hz => hz1 (eq_one_of_mem_complGroup_self h2 hzz hz)
  have hAmC : longRootGroup z ≤ Subgroup.centralizer ({z} : Set (StatedSp m F)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroup h2 hzz hx)
  have hSa : 1 ≤ S.card := by
    by_contra hlt
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS
    rw [stdInv_empty, mul_one] at hg
    exact hz1 (mul_right_cancel (hg.trans (one_mul g).symm))
  obtain ⟨eAm⟩ := nonempty_mulEquiv_longRootGroup_sp h2 hzg
  obtain ⟨eAp⟩ := nonempty_mulEquiv_complGroup_sp h2 hzg
  have hAmqs : CFSG.Open.IsQuasisimple ↥(longRootGroup z) ∨
      Group.IsSolvable ↥(longRootGroup z) := by
    rcases quasisimple_or_solvable_sp hr2 he hF S.card with hqs | hs
    · exact Or.inl (Components.quasisimple_of_equiv eAm.symm hqs)
    · exact Or.inr (Group.isSolvable_of_surjective (f := eAm.toMonoidHom) eAm.surjective)
  have hApqs : CFSG.Open.IsQuasisimple ↥(complGroup z) ∨ Group.IsSolvable ↥(complGroup z) := by
    rcases quasisimple_or_solvable_sp hr2 he hF (Sᶜ).card with hqs | hs
    · exact Or.inl (Components.quasisimple_of_equiv eAp.symm hqs)
    · exact Or.inr (Group.isSolvable_of_surjective (f := eAp.toMonoidHom) eAp.surjective)
  obtain ⟨-, hLeq⟩ := quasisimple_and_eq_of_isClassicalMember (by omega) h hcomm hLsup hzAp hAmC
    hAmqs hApqs
  exact card_eq_of_isClassicalMember_equiv_sp h2 hp2 hq h hSa
    (eAm.trans (MulEquiv.subgroupCongr hLeq.symm))

theorem classicalMemberParametersAt_psp : ClassicalMemberParametersAt p f .PSp := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have : Fact r.Prime := ⟨hr⟩
  have hcard : Nat.card (GaloisField r e) = r ^ e := GaloisField.card r e (by omega)
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h1 := card_eq_of_isClassicalMember_sp hr2 he hcard hp2 hq (L := L) (z := z) hL
  rw [hcard] at h1
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hr Fact.out (by omega) hf h1
  exact ⟨rfl, Or.inl rfl⟩

end Main

end CFSG.ClassicalInvolution.Upgrade
