module

public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (relIndex_inner_linearAutGroup_dvd)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_inner_of_elemAbelian_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (D : Subgroup (MulAut (projectiveSL n K)))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range, x ≠ 1 := by
  classical
  set Dl := linearAutGroup n K with hDl
  set Es := semilinearAutGroup n K with hEs
  have hgen := (automorphism_generation (K := K) hn).1
  obtain ⟨hID, -, hDnorm, -, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := K)
  rw [hgen] at hDnorm
  have hDlN : Dl.Normal := ⟨fun d hd x =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨x, Subgroup.mem_top x⟩⟩
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, zpow_neg, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  have hDE : D ≤ Es := fun x hx => by
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hexp x hx)
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  let α : D →* Es ⧸ Dl.subgroupOf Es :=
    (QuotientGroup.mk' (Dl.subgroupOf Es)).comp (Subgroup.inclusion hDE)
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    have : (x : D) ^ p = 1 := Subtype.ext (hexp x x.2)
    rw [← map_pow, this, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card D = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hrle : Nat.card α.range ≤ p := Nat.le_of_dvd hp.pos hexpα
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle
    have h1 : Nat.card D ≤ p * 1 := by
      rw [hsplit]
      exact Nat.mul_le_mul hrle (by omega)
    omega
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  set x : MulAut (projectiveSL n K) := (d : MulAut (projectiveSL n K)) with hx
  have hxD : x ∈ D := d.2
  have hxDl : x ∈ Dl := by
    have h : α d = 1 := hdk
    change QuotientGroup.mk (Subgroup.inclusion hDE d) = (1 : Es ⧸ Dl.subgroupOf Es) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  have hIN : (inner (projectiveSL n K)).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hIl : (inner (projectiveSL n K)).relIndex Dl ∣ Nat.gcd n (Nat.card K - 1) :=
    relIndex_inner_linearAutGroup_dvd (by omega)
  have hmq : (inner (projectiveSL n K)).relIndex Dl ∣ Nat.card K - 1 :=
    hIl.trans (Nat.gcd_dvd_right _ _)
  have hcop : Nat.Coprime p ((inner (projectiveSL n K)).relIndex Dl) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpq (h.trans hmq)
  have hxI : x ∈ inner (projectiveSL n K) := by
    have : ((inner (projectiveSL n K)).subgroupOf Dl).Normal := hIN.subgroupOf Dl
    set y : Dl ⧸ (inner (projectiveSL n K)).subgroupOf Dl := QuotientGroup.mk ⟨x, hxDl⟩ with hy
    have hyp : y ^ p = 1 := by
      rw [hy, ← QuotientGroup.mk_pow]
      have : (⟨x, hxDl⟩ : Dl) ^ p = 1 := Subtype.ext (hexp x hxD)
      rw [this]; rfl
    have hcardQ : Nat.card (Dl ⧸ (inner (projectiveSL n K)).subgroupOf Dl) =
        (inner (projectiveSL n K)).relIndex Dl := by
      rw [← Subgroup.index_eq_card]; rfl
    have hyd : orderOf y ∣ (inner (projectiveSL n K)).relIndex Dl := by
      rw [← hcardQ]; exact orderOf_dvd_natCard y
    have hyo : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
    have : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.symm hcop |>.symm) hyo hyd
    have hy1 : y = 1 := orderOf_eq_one_iff.1 this
    rw [hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
    exact hy1
  exact ⟨x, ⟨hxD, hxI⟩, fun h => hd1' (Subtype.ext h)⟩

theorem defCharOuterRankFamA_of_two_le :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, (∃ r q, idx.1 = .A r q ∧ 2 ≤ r) →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
          ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 3 →
            ∃ x ∈ D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, x ≠ 1 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨r, q, hr, hr2⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  let e : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e0.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  set φ : MulAut S ≃* MulAut (LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent)) :=
    MulAut.congr e with hφ
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hndvd : ¬ q.p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    intro h
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    rw [hKq] at h
    have h2 : q.p ∣ q.p ^ q.exponent - (q.p ^ q.exponent - 1) := Nat.dvd_sub h1 h
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ hp.pos
    rw [Nat.sub_sub_self hpos] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hcardD : Nat.card (D.map φ.toMonoidHom) = q.p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := exists_inner_of_elemAbelian_projectiveSL
    (K := GaloisField q.p q.exponent) (n := r + 1) (by omega) hp hp2 hndvd (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ q.p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by
      rw [hcardD]
      simpa using Nat.pow_lt_pow_right hp.one_lt (show 1 < 3 by norm_num))
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

end CFSG.HardMathSupport.Timmesfeld.DefChar
