module

public import CFSG.LocalAnalysis.GH72.Vocabulary
public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.Dihedral.DihedralFusionAutomorphisms

public section

namespace CFSG.GH72

open Subgroup
open CFSG.GorensteinWalter (HasDihedralSylowTwo)

theorem kleinFour_mulAut_eq_one_of_odd {K : Type*} [Group K] [IsKleinFour K] (α : MulAut K)
    {u : K} (hu : u ≠ 1) (hfix : α u = u) (hodd : Odd (orderOf α)) : α = 1 := by
  have hsq : α ^ 2 = 1 := by
    ext x
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    by_cases hx1 : x = 1
    · rw [hx1, map_one, map_one]
    by_cases hxu : x = u
    · rw [hxu, hfix, hfix]
    have hαx1 : α x ≠ 1 := fun h => hx1 (α.injective (h.trans (map_one α).symm))
    have hαxu : α x ≠ u := fun h => hxu (α.injective (h.trans hfix.symm))
    by_cases hαx : α x = x
    · rw [hαx, hαx]
    have h := IsKleinFour.eq_mul_of_ne_all hu hx1 (Ne.symm hxu) hαx1 hαxu hαx
    rw [h, map_mul, hfix, h, ← mul_assoc, IsKleinFour.mul_self, one_mul]
  have hdvd : orderOf α ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

variable {G : Type*} [Group G] [Finite G]

theorem mem_centralizer_of_odd_of_mem_normalizer {R : Subgroup G} {m : G}
    (hm : m ∈ normalizer (R : Set G)) (hodd : Odd (orderOf m))
    (hR : IsPGroup 2 (MulAut R) ∨
      (IsKleinFour R ∧ ∃ u ∈ R, u ≠ 1 ∧ m * u * m⁻¹ = u)) :
    m ∈ centralizer (R : Set G) := by
  let N := normalizer (R : Set G)
  haveI : (R.subgroupOf N).Normal := normal_in_normalizer
  let n : N := ⟨m, hm⟩
  let σ : MulAut (R.subgroupOf N) := MulAut.conjNormal n
  let eR : R.subgroupOf N ≃* R := subgroupOfEquivOfLe le_normalizer
  have hσodd : Odd (orderOf σ) := by
    have h1 : orderOf σ ∣ orderOf n :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hσ : σ = 1 := by
    rcases hR with hR | ⟨hK, u, huR, hu1, hmu⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hR' : IsPGroup 2 (MulAut (R.subgroupOf N)) := hR.of_equiv (MulAut.congr eR).symm
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR' σ
      rcases k with _ | k
      · exact orderOf_eq_one_iff.mp (by rw [hk, pow_zero])
      · exfalso
        rw [hk, pow_succ] at hσodd
        exact (Nat.not_even_iff_odd.mpr hσodd) (even_two.mul_left _)
    · haveI : IsKleinFour (R.subgroupOf N) :=
        IsKleinFour.mk (by rw [Nat.card_congr eR.toEquiv]; exact IsKleinFour.card_four)
          (by rw [Monoid.exponent_eq_of_mulEquiv eR]; exact IsKleinFour.exponent_two)
      let u' : R.subgroupOf N := ⟨⟨u, le_normalizer huR⟩, by simpa [mem_subgroupOf] using huR⟩
      refine kleinFour_mulAut_eq_one_of_odd σ (u := u') ?_ ?_ hσodd
      · intro h
        exact hu1 (congrArg (fun x : R.subgroupOf N => ((x : N) : G)) h)
      · apply Subtype.ext
        apply Subtype.ext
        change m * u * m⁻¹ = u
        exact hmu
  rw [mem_centralizer_iff]
  intro r hr
  have h := congrArg (fun φ : MulAut (R.subgroupOf N) =>
    (((φ ⟨⟨r, le_normalizer hr⟩, by simpa [mem_subgroupOf] using hr⟩ : R.subgroupOf N) : N) : G))
    hσ
  change m * r * m⁻¹ = r at h
  calc r * m = m * r * m⁻¹ * m := by rw [h]
    _ = m * r := by group

theorem mem_centralizer_of_odd_of_hasDihedralSylowTwo (hD : HasDihedralSylowTwo G) {t : G}
    (ht : orderOf t = 2) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQt : Q ≤ centralizer ({t} : Set G)) {m : G} (hmt : m ∈ centralizer ({t} : Set G))
    (hmQ : m ∈ normalizer (Q : Set G)) (hodd : Odd (orderOf m)) :
    m ∈ centralizer (Q : Set G) := by
  have hT : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have htQ : t ∈ centralizer (Q : Set G) := by
    rw [mem_centralizer_iff]
    intro q hq
    exact mem_centralizer_singleton_iff.mp (hQt hq)
  have hR2 : IsPGroup 2 (Q ⊔ zpowers t : Subgroup G) := IsPGroup.to_sup_of_normal_left' hQ hT
    ((zpowers_le).mpr (centralizer_le_normalizer _ htQ))
  obtain ⟨S, hRS⟩ := hR2.exists_le_sylow
  obtain ⟨k, hk, ⟨e⟩⟩ := hD S
  have hmt' : m * t * m⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hmt]
    group
  have hmZ : m ∈ centralizer ((zpowers t : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp hmt).symm j).eq
  have hmR : m ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup Q (zpowers t)
      ⟨hmQ, centralizer_le_normalizer _ hmZ⟩
  have hcR : m ∈ centralizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
    by_cases hK : IsKleinFour (Q ⊔ zpowers t : Subgroup G)
    · refine mem_centralizer_of_odd_of_mem_normalizer hmR hodd
        (Or.inr ⟨hK, t, mem_sup_right (mem_zpowers t), fun h => ?_, hmt'⟩)
      rw [h, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · exact mem_centralizer_of_odd_of_mem_normalizer hmR hodd
        (Or.inl (CFSG.GorensteinWalter.dihedral_subgroup_automorphism_isTwoGroup S hk e _ hRS hK))
  exact centralizer_le (by exact_mod_cast (le_sup_left : Q ≤ Q ⊔ zpowers t)) hcR

theorem hasNormalPComplement_centralizer_of_hasDihedralSylowTwo (hD : HasDihedralSylowTwo G)
    {t : G} (ht : orderOf t = 2) :
    CFSG.HasNormalPComplement 2 (centralizer ({t} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G)
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  refine ⟨a, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
  set y := n ^ 2 ^ a with hy
  have hyodd : Odd (orderOf ((y : C) : G)) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy,
      orderOf_pow_of_dvd (by positivity) (by rw [hab]; exact dvd_mul_right _ _), hab,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hb
  have hyN : ((y : C) : G) ∈ normalizer ((Q.map C.subtype : Subgroup G) : Set G) :=
    le_normalizer_map C.subtype ⟨(y : C), y.2, rfl⟩
  have hc := mem_centralizer_of_odd_of_hasDihedralSylowTwo hD ht (hQ.map C.subtype)
    (map_subtype_le Q) (y : C).2 hyN hyodd
  rw [mem_centralizer_iff] at hc ⊢
  intro q hq
  exact Subtype.ext (hc (q : G) ⟨q, hq, rfl⟩)

theorem hasNormalTwoComplement_of_hasNormalPComplement {H : Subgroup G}
    (h : CFSG.HasNormalPComplement 2 H) : HasNormalTwoComplement H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hcop, hP⟩ := h
  have hsub : (N.map H.subtype).subgroupOf H = N := by
    rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  refine ⟨N.map H.subtype, map_subtype_le N, by rw [hsub]; exact hN, ?_, n, ?_⟩
  · rw [card_map_of_injective H.subtype_injective]
    exact Nat.coprime_two_left.mp hcop
  · unfold relIndex
    rw [hsub]
    exact hn

theorem hasNormalTwoComplement_C_of_hasDihedralSylowTwo (hD : HasDihedralSylowTwo G) {t : G}
    (ht : orderOf t = 2) : HasNormalTwoComplement (C t) :=
  hasNormalTwoComplement_of_hasNormalPComplement
    (hasNormalPComplement_centralizer_of_hasDihedralSylowTwo hD ht)

end CFSG.GH72
