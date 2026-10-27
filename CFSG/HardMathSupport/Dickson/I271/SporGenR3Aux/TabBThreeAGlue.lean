module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeATri

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Dickson.I271.TabBThreeTri

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tabBThree_card_le_three_mul {G : Type*} [Group G] [Finite G] {C Q : Subgroup G} {s : G}
    (hsC : s ∈ C) (hQC : Q ≤ C) (hs3 : s ^ 3 = 1)
    (h : ∀ g ∈ C, ∃ k : ℕ, ∃ q ∈ Q, g = s ^ k * q) : Nat.card C ≤ 3 * Nat.card Q := by
  let f : Fin 3 × Q → C := fun p =>
    ⟨s ^ (p.1 : ℕ) * p.2, C.mul_mem (C.pow_mem hsC _) (hQC p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨k, q, hq, rfl⟩ := h g hg
    refine ⟨(⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨q, hq⟩), Subtype.ext ?_⟩
    show s ^ (k % 3) * q = s ^ k * q
    conv_rhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hs3, one_pow, mul_one]
  have hc := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at hc


theorem tabBThree_bThreeABound : BThreeABound := by
  intro v w hw
  have hamb := ambientRootOrbitsHyp
  have hL := labelsInput_of_ambient hamb
  have hO := outerInput_of_ambient hamb
  have hP := pathInput_of_ambient hamb
  have hT := typeThreeBoundInput_of_ambient hamb
  have hdiam := CTIB.dist_le_three_of_inputs hL hO hP hT
  have hinj0 := CTIB.clabel_injective_of_inputs hL hO hP hT
  have hinj : Function.Injective clabelS := fun x y h => hinj0 (congrArg Subtype.val h)
  have hpq : ∀ p q : CVert, Commute (clabelS p) (clabelS q) ∨
      orderOf (clabelS p * clabelS q) = 3 ∨ orderOf (clabelS p * clabelS q) = 4 := fun p q => by
    rcases CTIB.commute_or_three_or_four hdiam hL p q with h | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  let H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have hs : orderOf (clabelS v * clabelS w) = 3 := by
    rw [CTIB.orderOf_clabelS_mul]
    exact ((native_order_three_label_products_and_dihedral_triples v).1 w hw).1
  have hs3 : (clabelS v * clabelS w) ^ 3 = 1 := hs ▸ pow_orderOf_eq_one _
  have hsimp := (native_three_transposition_group_simple v w hw).1
  have hne : ∃ x₁ ∈ cgraph.commonNeighbors v w, ∃ x₂ ∈ cgraph.commonNeighbors v w,
      clabelS x₁ ≠ clabelS x₂ := by
    have hc := (native_three_transposition_group_simple v w hw).2.2.2.2.2.1
    obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 (by rw [hc]; norm_num)
    obtain ⟨x₁, h1, rfl⟩ := ha
    obtain ⟨x₂, h2, rfl⟩ := hb
    exact ⟨x₁, h1, x₂, h2, hab⟩
  have hcen : ∀ d : CVert, Inverts (clabelS v * clabelS w) d →
      ∃ y : CVert, IsCentre (clabelS v * clabelS w) d y := by
    intro d hd
    have hl : clabelS (cvMul d ((clabelS v * clabelS w) ^ 2)) =
        clabelS d * (clabelS v * clabelS w) := by
      rw [clabelS_cvMul_pow hd 2, show 2 * 2 = 3 + 1 by norm_num, pow_add, hs3, one_mul, pow_one]
    have h3 : orderOf (clabelS d * clabelS (cvMul d ((clabelS v * clabelS w) ^ 2))) = 3 := by
      rw [hl, ← mul_assoc, mul_self_clabelS, one_mul]
      exact hs
    have hd1 : cvMul d ((clabelS v * clabelS w) ^ 2) ∈ sphereThree d := by
      rcases CTIB.commute_or_three_or_four hdiam hL d (cvMul d ((clabelS v * clabelS w) ^ 2))
        with hc | ⟨h, -⟩ | ⟨-, h4⟩
      · exfalso
        have h2 := orderOf_dvd_of_pow_eq_one (CTIB.sq_clabelS_mul_of_commute hc)
        rw [h3] at h2
        norm_num at h2
      · exact h
      · omega
    have hcard := (native_order_three_common_neighbors_exact_3510.1 d _ hd1).2.2.1
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcard]; norm_num)
    obtain ⟨h1, h2⟩ := cgraph.mem_commonNeighbors.1 hy
    exact ⟨y, h1.symm, _, hl, h2.symm⟩
  have hv : Inverts (clabelS v * clabelS w) v := by
    show clabelS v * (clabelS v * clabelS w) * clabelS v = (clabelS v * clabelS w)⁻¹
    rw [mul_inv_rev, inv_clabelS, inv_clabelS, ← mul_assoc, mul_self_clabelS, one_mul]
  refine tabBThree_card_le_three_mul (Subgroup.mem_centralizer_singleton_iff.2 rfl) ?_ hs3 ?_
  · intro q hq
    obtain ⟨hqv, hqw⟩ := Subgroup.mem_inf.1 hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc q * (clabelS v * clabelS w) = q * clabelS v * clabelS w := (mul_assoc _ _ _).symm
      _ = clabelS v * (q * clabelS w) := by rw [commute_of_mem_vStab hqv, mul_assoc]
      _ = clabelS v * clabelS w * q := by rw [commute_of_mem_vStab hqw, mul_assoc]
  · intro g hg
    have hgs : Commute g (clabelS v * clabelS w) := Subgroup.mem_centralizer_singleton_iff.1 hg
    obtain ⟨k, hk⟩ := sameTri_of_inverts hinj hpq H hs rfl hsimp hne hcen (hv.map hgs)
    have hl : clabelS (cvMul v g) = clabelS v * (clabelS v * clabelS w) ^ k := by
      rw [← hk, ← mul_assoc, mul_self_clabelS, one_mul]
    have he : cvMul v g = cvMul v ((clabelS v * clabelS w) ^ (2 * k)) := hinj (by
      rw [clabelS_cvMul_pow hv (2 * k), hl, show 2 * (2 * k) = k + 3 * k by ring, pow_add,
        pow_mul _ 3 k, hs3, one_pow, mul_one])
    have hqv : cvMul v (g * ((clabelS v * clabelS w) ^ (2 * k))⁻¹) = v := by
      rw [cvMul_mul, he, ← cvMul_mul, mul_inv_cancel, cvMul_one]
    have hq1 : Commute (g * ((clabelS v * clabelS w) ^ (2 * k))⁻¹) (clabelS v) :=
      commute_of_mem_vStab (mem_vStab.2 hqv)
    have hq2 : Commute (g * ((clabelS v * clabelS w) ^ (2 * k))⁻¹) (clabelS v * clabelS w) :=
      hgs.mul_left (((Commute.refl _).pow_left _).inv_left)
    have hqw : Commute (g * ((clabelS v * clabelS w) ^ (2 * k))⁻¹) (clabelS w) := by
      have e : clabelS w = clabelS v * (clabelS v * clabelS w) := by
        rw [← mul_assoc, mul_self_clabelS, one_mul]
      have h := hq1.mul_right hq2
      rwa [← e] at h
    refine ⟨2 * k, g * ((clabelS v * clabelS w) ^ (2 * k))⁻¹,
      Subgroup.mem_inf.2 ⟨mem_vStab.2 hqv, mem_vStab.2 (hinj ?_)⟩, ?_⟩
    · rw [clabelS_cvMul, mul_assoc, ← hqw.eq, inv_mul_cancel_left]
    · rw [← mul_assoc, ← (hgs.pow_right (2 * k)).eq, mul_inv_cancel_right]

theorem tabBThreeACard_thm : TabBThreeACard :=
  tabBThreeACard_of_bThreeABound tabBThree_bThreeABound

end CFSG.HardMathSupport.Dickson.I271
