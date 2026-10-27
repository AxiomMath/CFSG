module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGLS3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.OddStandard.ChildL34

public section

namespace CFSG.OddStandard

open CFSG Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem oddLieNoStandardL34_holds :
    OddLieNoStandardL34 := by
  intro G _ _ _ hOdd L hL h34
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hG⟩ := hOdd
  have hO : CatLeaf.LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  have hcardL : Nat.card (↥L ⧸ center ↥L) = 20160 := by
    obtain ⟨-, h1, -⟩ := hO _ .PSL 3 2 2
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩ h34
    have h2 : CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide
    have h3 : CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by decide
    rw [h2, h3] at h1
    omega
  have hstd : Assembly.ComponentType.IsStandardSubgroup L := hL
  obtain ⟨hq, heven, -, -, -⟩ := hL
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (L : Set G))) 2
    (even_iff_two_dvd.mp heven)
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨-, hLt, hLn, -, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd t.2 ht'
  have hnab : ∃ u v : ↥L ⧸ center ↥L, u * v ≠ v * u := by
    by_contra hab
    push Not at hab
    have : IsMulCommutative (↥L ⧸ center ↥L) := ⟨⟨hab⟩⟩
    have hpr := Group.is_simple_iff_prime_card.mp hq.2
    rw [hcardL] at hpr
    norm_num at hpr
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hnab
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
      apply huv
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      have hv : (v : G) ∈ center G := h ▸ mem_top _
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hv) (u : G))
  have hα2 : MulAut.conj (t : G) ^ 2 = 1 := by
    rw [← map_pow, ← ht', pow_orderOf_eq_one, map_one]
  have hα1 : MulAut.conj (t : G) ≠ 1 := by
    intro h1
    have htc : (t : G) ∈ center G := mem_center_iff.mpr fun g => by
      have h2 := congrArg (fun φ : MulAut G => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * t = t * g * (t : G)⁻¹ * t := by rw [h2]
        _ = t * g := by group
    rw [hZ, mem_bot] at htc
    rw [htc, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have hF : fixedSubgroup (MulAut.conj (t : G)) = centralizer ({(t : G)} : Set G) := by
    ext g
    rw [mem_centralizer_singleton_iff]
    show (MulAut.conj (t : G)) g = g ↔ g * t = t * g
    rw [MulAut.conj_apply]
    constructor
    · intro h
      calc g * t = t * g * (t : G)⁻¹ * t := by rw [h]
        _ = t * g := by group
    · intro h
      rw [← h, mul_inv_cancel_right]
  have hLF : L ≤ fixedSubgroup (MulAut.conj (t : G)) := hF ▸ hLt
  have hKq : IsQuasisimple ↥(L.subgroupOf (fixedSubgroup (MulAut.conj (t : G)))) := by
    refine (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hLF)).2 ?_
    exact ⟨⟨hq.1⟩, hq.2, hnab⟩
  have hKn : (L.subgroupOf (fixedSubgroup (MulAut.conj (t : G)))).Normal := by
    rw [hF]
    exact hLn
  have hK : IsComponent (L.subgroupOf (fixedSubgroup (MulAut.conj (t : G)))) :=
    ⟨hKq, hKn.isSubnormal⟩
  have hKL : Nat.card (↥(L.subgroupOf (fixedSubgroup (MulAut.conj (t : G)))) ⧸
      center ↥(L.subgroupOf (fixedSubgroup (MulAut.conj (t : G))))) =
        Nat.card (↥L ⧸ center ↥L) :=
    Nat.card_congr (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLF)
      (Subgroup.map_center_eq _)).toEquiv
  rw [hcardL] at hKL
  rcases GrSLit.gls3OddLieAutComponentsInput_holds G τ n p f hp hp2 hadm hG
      (MulAut.conj (t : G)) (orderOf_eq_prime hα2 hα1) _ hK with
    ⟨τ', n', f', hadm', hK'⟩ | ⟨-, -, -, hK8⟩
  · exact CatLeaf.lieModel_odd_card_ne_L34 hO hp2 hadm' hK' hKL
  · obtain ⟨-, h1, -⟩ := hO _ .PSL 2 2 3
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩ hK8
    have h2 : CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
    have h3 : CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
    rw [h2, h3, mul_one] at h1
    have h4 := card_eq_card_quotient_mul_card_subgroup
      (center ↥(L.subgroupOf (fixedSubgroup (MulAut.conj (t : G)))))
    rw [h1, hKL] at h4
    have h5 : 0 < Nat.card
        ↥(center ↥(L.subgroupOf (fixedSubgroup (MulAut.conj (t : G))))) := Nat.card_pos
    nlinarith

end CFSG.OddStandard
