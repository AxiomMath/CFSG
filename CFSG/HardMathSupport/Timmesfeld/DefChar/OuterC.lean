module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

theorem exists_inner_of_elemAbelian_projectiveSp {K : Type} [Field K] [Finite K] {r : ℕ}
    (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K - 1)
    (D : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range, x ≠ 1 := by
  classical
  have : NeZero r := ⟨by omega⟩
  set Dl := spLinearAutGroup r K with hDl
  set Es := spSemilinearAutGroup r K with hEs
  have hgen := (automorphism_generation (K := K) hr).1
  obtain ⟨-, -, hDnorm, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotient (K := K) (r := r) (by omega)
  have hDE : D ≤ Es := fun x hx => by rw [hEs, hgen]; exact Subgroup.mem_top x
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, zpow_neg, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
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
  set x : MulAut (StatedProj (StatedSp r K)) := (d : MulAut (StatedProj (StatedSp r K))) with hx
  have hxD : x ∈ D := d.2
  have hxDl : x ∈ Dl := by
    have h : α d = 1 := hdk
    change QuotientGroup.mk (Subgroup.inclusion hDE d) = (1 : Es ⧸ Dl.subgroupOf Es) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  have hxp : x ^ p = 1 := hexp x hxD
  obtain ⟨A, hA⟩ := mem_spLinearAutGroup_iff.mp hxDl
  set m := Nat.card K - 1 with hm
  have hmc : Nat.card Kˣ = m := Nat.card_units K
  have hBker : A ^ m ∈ (multiplier r K).ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hmc]
    exact pow_card_eq_one'
  have hxm : x ^ m ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range := by
    rw [ker_multiplier, Subgroup.mem_subgroupOf] at hBker
    have : x ^ m = conjAut r K (A ^ m) := by rw [map_pow, hA]
    rw [this]
    have h2 : (A ^ m : gsp r K) = ⟨((⟨_, hBker⟩ : StatedSp r K) :
        GL (Fin r ⊕ Fin r) K), statedSp_le_gsp hBker⟩ := rfl
    rw [h2, conjAut_statedSp]
    exact ⟨_, rfl⟩
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
  have hbez := Nat.gcd_eq_gcd_ab p m
  rw [hcop.gcd_eq_one] at hbez
  have hxI : x ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range := by
    have hx1 : x = (x ^ m) ^ (Nat.gcdB p m) := by
      calc x = x ^ (1 : ℤ) := (zpow_one x).symm
        _ = x ^ ((p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m) := by
          rw [← hbez]; norm_cast
        _ = _ := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hxp, one_zpow, one_mul]
    rw [hx1]
    exact Subgroup.zpow_mem _ hxm _
  exact ⟨x, ⟨hxD, hxI⟩, fun h => hd1' (Subtype.ext h)⟩

theorem defCharOuterRankFamC : DefCharOuterRankFam .C := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hpq : p = q.p := by simpa using hch.symm
  have hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField (⟨.C r q, hv⟩ :
    TauCeti.ValidLieTypeIndex)
  let K := ↥(TauCeti.ValidLieTypeIndex.fixedField (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex))
  let e : S ≃* StatedProj (StatedSp r K) :=
    e0.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
  set φ : MulAut S ≃* MulAut (StatedProj (StatedSp r K)) := MulAut.congr e with hφ
  have hKq : Nat.card K = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hndvd : ¬ p ∣ Nat.card K - 1 := by
    intro h
    have h1 : p ∣ q.p ^ q.exponent := by
      rw [← hpq]; exact dvd_pow_self _ q.exponent_pos.ne'
    rw [hKq] at h
    have h2 : p ∣ q.p ^ q.exponent - (q.p ^ q.exponent - 1) := Nat.dvd_sub h1 h
    have hpos : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    rw [Nat.sub_sub_self hpos] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := exists_inner_of_elemAbelian_projectiveSp
    (K := K) (r := r) hrange.1 hp hndvd (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
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
