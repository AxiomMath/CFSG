module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsBasic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeReduce

public section

namespace CFSG.ClassicalInvolution.Upgrade

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification
open scoped MatrixGroups

section Components

variable {F : Type} [Field F] [Finite F] {r e : ℕ} [Fact r.Prime] [CharP F r]

theorem quasisimple_or_solvable_su (hF : Nat.card F = (r ^ e) ^ 2) (hr2 : r ≠ 2) (k : ℕ) :
    CFSG.Open.IsQuasisimple (Su F r e k) ∨ Group.IsSolvable (Su F r e k) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · right
    have := ModelFacts.subsingleton_su_of_le_one (F := F) (p := r) (f := e) (a := k) (by omega)
    infer_instance
  · rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · obtain rfl : k = 2 := by omega
      obtain ⟨eSL⟩ := nonempty_sl2_mulEquiv_su_two (K := F) (p := r) (f := e) hF
      have hfix : Nat.card (fixedSubfield F r e) = r ^ e := card_fixedSubfield hF
      rcases Nat.lt_or_ge (r ^ e) 4 with hq | hq
      · right
        have := isSolvable_sl_two_of_card_lt (F := fixedSubfield F r e) (by omega)
        exact Group.isSolvable_of_surjective (f := eSL.toMonoidHom) eSL.surjective
      · left
        exact Components.quasisimple_of_equiv eSL.symm
          (isQuasisimple_specialLinearGroup_two (by omega))
    · left
      have hnq : (k, r ^ e) ≠ (3, 2) := fun h' => by
        have h2 := congrArg Prod.snd h'
        simp only at h2
        have := (Nat.Prime.pow_eq_iff Nat.prime_two).1 (by rw [← h2] : (r : ℕ) ^ e = 2)
        exact hr2 this.1
      have hq' := isQuasisimple_statedSU_of_card hF hk3 hnq
      let eSU : Su F r e k ≃* CFSG.Assembly.LowTwoRank.StatedSU k (r ^ e) F :=
        MulEquiv.subgroupCongr (SUid_eq_statedSU hF k)
      exact ModelFacts.open_isQuasisimple (isQuasisimple_of_mulEquiv eSU.symm hq'.1)

end Components

section Main

variable {F : Type} [Field F] [Finite F] {r e : ℕ} [Fact r.Prime] [CharP F r]
  {p f : ℕ} [Fact p.Prime]

open CFSG.ClassicalInvolution.ModelFacts in
theorem eq_of_isClassicalMember_su (hF : Nat.card F = (r ^ e) ^ 2) (hr2 : r ≠ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n) {L : Subgroup (Su F r e n)} {z : Su F r e n}
    (h : IsClassicalMember p f L z) : r ^ e = p ^ f := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hr2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := h.ne_one
  have hLz : ∀ x ∈ L, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
  obtain ⟨a, ha, g, hg, hAm, hAp⟩ := exists_longRootGroupSU_data hF h2 (by omega) hzz
  set Am : Subgroup (Su F r e n) := longRootGroupSU F r e (suMat z) with hAmdef
  set Ap : Subgroup (Su F r e n) := longRootGroupSU F r e (-suMat z) with hApdef
  have hLsup : L ≤ Am ⊔ Ap := fun x hx => by
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_perfect_su h2 hzz h.perfect hLz x hx
    exact Subgroup.mul_mem_sup ha' hb'
  have hcomm : ∀ x ∈ Am, ∀ y ∈ Ap, x * y = y * x := fun x hx y hy =>
    commute_of_mem_longRootGroupSU_neg h2 hzz hx hy
  have hzAm : z ∈ Am := mem_longRootGroupSU_self hzz
  have hzAp : z ∉ Ap := not_mem_longRootGroupSU_neg_self h2 hzz hz1
  have hAmC : Am ≤ Subgroup.centralizer ({z} : Set (Su F r e n)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroupSU hx)
  obtain ⟨eAm0⟩ := nonempty_mulEquiv_map_blockEmb (F := F) (p := r) (f := e)
    (by omega : 0 + a ≤ n) g
  obtain ⟨eAp0⟩ := nonempty_mulEquiv_map_blockEmb (F := F) (p := r) (f := e)
    (by omega : a + (n - a) ≤ n) g
  let eAm : Su F r e a ≃* ↥Am := eAm0.trans (MulEquiv.subgroupCongr hAm.symm)
  let eAp : Su F r e (n - a) ≃* ↥Ap := eAp0.trans (MulEquiv.subgroupCongr hAp.symm)
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have hsub : Subsingleton (Su F r e a) :=
      subsingleton_su_of_le_one (F := F) (p := r) (f := e) (by omega)
    have : Subsingleton Am := eAm.surjective.subsingleton
    exact hz1 (congrArg Subtype.val (Subsingleton.elim (⟨z, hzAm⟩ : Am) 1))
  have hAmqs : CFSG.Open.IsQuasisimple ↥Am ∨ Group.IsSolvable ↥Am := by
    rcases quasisimple_or_solvable_su hF hr2 a with hqs | hs
    · exact Or.inl (Components.quasisimple_of_equiv eAm.symm hqs)
    · exact Or.inr (Group.isSolvable_of_surjective (f := eAm.toMonoidHom) eAm.surjective)
  have hApqs : CFSG.Open.IsQuasisimple ↥Ap ∨ Group.IsSolvable ↥Ap := by
    rcases quasisimple_or_solvable_su hF hr2 (n - a) with hqs | hs
    · exact Or.inl (Components.quasisimple_of_equiv eAp.symm hqs)
    · exact Or.inr (Group.isSolvable_of_surjective (f := eAp.toMonoidHom) eAp.surjective)
  obtain ⟨-, hLeq⟩ := quasisimple_and_eq_of_isClassicalMember (by omega) h hcomm hLsup hzAp hAmC
    hAmqs hApqs
  by_cases ha3 : 3 ≤ a
  · exfalso
    obtain ⟨s, t, hs2, ht2, hs1, ht1, hst, hne⟩ :=
      exists_two_commuting_involutions (F := F) (p := r) (f := e) h2 ha3
    obtain ⟨e2⟩ := h.nonempty_equiv
    let eL : Su F r e a ≃* ↥L := eAm.trans (MulEquiv.subgroupCongr hLeq.symm)
    have hord : ∀ x : Su F r e a, x * x = 1 → x ≠ 1 → orderOf (eL x) = 2 := fun x hx hx1 => by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
    exact false_of_two_commuting_involutions_sl2 hodd e2 (hord s hs2 hs1) (hord t ht2 ht1)
      (by rw [← map_mul, ← map_mul, hst]) (fun hab => hne (eL.injective hab))
  · obtain rfl : a = 2 := by omega
    obtain ⟨eSL⟩ := nonempty_sl2_mulEquiv_su_two (K := F) (p := r) (f := e) hF
    have hfix : Nat.card (fixedSubfield F r e) = r ^ e := card_fixedSubfield hF
    rw [← hfix]
    exact card_eq_of_isClassicalMember_equiv_sl2' h hq
      (eSL.trans (eAm.trans (MulEquiv.subgroupCongr hLeq.symm)))

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal in
theorem classicalMemberParametersAt_psu : ClassicalMemberParametersAt p f .PSU := by
  intro hp2 hq n r e hr hr2 hadm L z hL
  have he : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero (2 * e) := ⟨by omega⟩
  have hF : Nat.card (GaloisField r (2 * e)) = (r ^ e) ^ 2 :=
    card_galoisField_two_mul r e he
  have hM : modelUniv .PSU n r e hr =
      ⟨↥(SU (unitaryInvolution (GaloisField r (2 * e)) r e) n),
        Unitary.rootDatum (card_galoisField_two_mul r e he) n⟩ :=
    (rfl : Generic.modelUniv .PSU n r e hr = ModelFacts.modelUniv .PSU n r e hr).trans
      (ModelFacts.modelUniv_PSU he)
  suffices h : ∀ M : LieUniversal, M =
      ⟨↥(SU (unitaryInvolution (GaloisField r (2 * e)) r e) n),
        Unitary.rootDatum (card_galoisField_two_mul r e he) n⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember p f L z →
        r = p ∧ (e = f ∨ (StatedLieTag.PSU = .trialityD4 ∧ 3 * e = f)) from h _ hM L z hL
  intro M hM' L z hL
  subst hM'
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  have hL' := ModelFacts.isClassicalMember_map_mulEquiv hL (conjEquiv P hP)
  have h1 := eq_of_isClassicalMember_su hF hr2 hp2 hq (by omega) hL'
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hr Fact.out (by omega) hf h1
  exact ⟨rfl, Or.inl rfl⟩

end Main

end CFSG.ClassicalInvolution.Upgrade
