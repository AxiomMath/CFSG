module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCoreBasic
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.RankThree.PartOne.S12.LinAlg

public section

namespace CFSG.ComponentClassification.AS81.Sec2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.RankTwoSporadic

variable {G : Type} [Group G]

section Conj

variable (W : Subgroup G)

@[expose] noncomputable def normConj : ↥(normalizer (W : Set G)) →* MulAut ↥W where
  toFun n :=
    { toFun := fun w => ⟨(n : G) * w * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 w).mp w.2⟩
      invFun := fun w => ⟨(n : G)⁻¹ * w * n, by
        simpa using (mem_normalizer_iff.mp (inv_mem n.2) w).mp w.2⟩
      left_inv := fun w => Subtype.ext (by simp [mul_assoc])
      right_inv := fun w => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp only [coe_mul]; group) }
  map_one' := MulEquiv.ext fun w => Subtype.ext (by simp)
  map_mul' a b := MulEquiv.ext fun w => Subtype.ext (by
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, coe_mul]
    group)

theorem normConj_apply (n : ↥(normalizer (W : Set G))) (w : ↥W) :
    ((normConj W n w : ↥W) : G) = n * w * (n : G)⁻¹ :=
  rfl

theorem mem_centralizer_of_mem_ker {n : ↥(normalizer (W : Set G))} (hn : n ∈ (normConj W).ker) :
    (n : G) ∈ centralizer (W : Set G) := by
  rw [mem_centralizer_iff]
  intro w hw
  have h := congrArg (fun σ : MulAut ↥W => ((σ ⟨w, hw⟩ : ↥W) : G)) (MonoidHom.mem_ker.mp hn)
  simp only [normConj_apply, MulAut.one_apply] at h
  calc w * n = (n * w * (n : G)⁻¹) * n := by rw [h]
    _ = n * w := by group

abbrev normQuot : Type := ↥(normalizer (W : Set G)) ⧸ W.subgroupOf (normalizer (W : Set G))

abbrev normOddQuot : Type := normQuot W ⧸ standardComponentOddCore (normQuot W)

@[expose] noncomputable def oddQuotMap : ↥(normalizer (W : Set G)) →* normOddQuot W :=
  (QuotientGroup.mk' (standardComponentOddCore (normQuot W))).comp
    (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))

theorem oddQuotMap_surjective : Function.Surjective (oddQuotMap W) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

end Conj

section Odd

variable [Finite G] {W : Subgroup G} (hW : IsElemAbelian 2 W)
  (hCW : ∀ x ∈ centralizer (W : Set G), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ W)
include hW hCW

theorem oddQuotMap_eq_one_of_mem_ker {n : ↥(normalizer (W : Set G))}
    (hn : n ∈ (normConj W).ker) : oddQuotMap W n = 1 := by
  let π₁ := QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
  let C := ((normConj W).ker).map π₁
  have hCn : C.Normal := (MonoidHom.normal_ker _).map π₁ (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card C) := by
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    obtain ⟨c, hc, hcy⟩ := mem_map.mp y.2
    have hy2 : (y : normQuot W) ^ 2 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      exact congrArg Subtype.val this
    have hc2 : ((c : G) ^ 2) ∈ W := by
      rw [← hcy, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
        at hy2
      simpa using hy2
    have hc4 : (c : G) ^ 2 ^ 2 = 1 := by
      have e : (c : G) ^ 2 ^ 2 = ((c : G) ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
      rw [e]
      exact hW.2 _ hc2
    have hcW : (c : G) ∈ W := hCW _ (mem_centralizer_of_mem_ker W hc) ⟨2, hc4⟩
    have hy1 : (y : normQuot W) = 1 := by
      rw [← hcy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hcW
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hy1', orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hle := le_standardComponentOddCore hCn hodd
  show (QuotientGroup.mk' _) (π₁ n) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hle (mem_map_of_mem π₁ hn)

theorem card_dvd_card_mulAut : Nat.card (normOddQuot W) ∣ Nat.card (MulAut ↥W) := by
  have hle : (normConj W).ker ≤ (oddQuotMap W).ker := fun n hn =>
    oddQuotMap_eq_one_of_mem_ker hW hCW hn
  have h1 : Nat.card ↥(normalizer (W : Set G)) =
      Nat.card (normOddQuot W) * Nat.card (oddQuotMap W).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (oddQuotMap W).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (oddQuotMap_surjective W)).toEquiv]
  have h2 : Nat.card ↥(normalizer (W : Set G)) =
      Nat.card (normConj W).range * Nat.card (normConj W).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (normConj W).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card (normConj W).ker := Nat.card_pos
  have h3 : Nat.card (normOddQuot W) * t = Nat.card (normConj W).range := by
    rw [ht] at h1
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← h2, h1]
    ring
  exact (Dvd.intro t h3).trans (Subgroup.card_subgroup_dvd_card _)

end Odd

section GeneralLinear

variable {W : Subgroup G}

theorem isElementaryAbelian_of {p : ℕ} (hW : IsElemAbelian p W) : IsElementaryAbelian p ↥W where
  toIsMulCommutative := hW.1
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by simpa using hW.2 g g.2)

theorem card_GL_eight_two : Nat.card (GL (Fin 8) (ZMod 2)) = 5348063769211699200 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_eight]

theorem card_mulAut_dvd [Finite G] (hW : IsElemAbelian 2 W) (hW256 : Nat.card W = 256) :
    Nat.card (MulAut ↥W) ∣ 5348063769211699200 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isElementaryAbelian_of hW
  obtain ⟨f⟩ := RankThree.PartOne.LinAlg.exists_coords (p := 2) W (n := 8) (by rw [hW256]; norm_num)
  have h := Subgroup.card_dvd_of_injective _ (RankThree.PartOne.LinAlg.coordGL_injective f)
  rwa [card_GL_eight_two] at h

theorem card_le_twentyfive_of_isPGroup [Finite G] (hW : IsElemAbelian 2 W)
    (hW256 : Nat.card W = 256) {A : Subgroup (MulAut ↥W)} (hA : IsPGroup 5 A) :
    Nat.card A ≤ 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hd : 5 ^ k ∣ 5348063769211699200 :=
    hk ▸ (Subgroup.card_subgroup_dvd_card A).trans (card_mulAut_dvd hW hW256)
  rw [hk]
  by_contra hlt
  have h3 : 3 ≤ k := by
    by_contra h
    have : k ≤ 2 := by omega
    interval_cases k <;> simp_all
  have h125 : 5 ^ 3 ∣ 5348063769211699200 := (pow_dvd_pow 5 h3).trans hd
  exact absurd h125 (by norm_num)

end GeneralLinear

theorem not_isSporadic_M12_of_elem256 [Finite G] {W : Subgroup G}
    (hW : IsElemAbelian 2 W) (hW256 : Nat.card W = 256)
    (hCW : ∀ x ∈ centralizer (W : Set G), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ W) :
    let N := normalizer (W : Set G); let Q := ↥N ⧸ W.subgroupOf N;
    ∀ X : Subgroup (Q ⧸ standardComponentOddCore Q), ¬ NativeSporadic.IsSporadic ↥X .M12 := by
  intro N Q X ⟨e⟩
  have hX : Nat.card X = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
  have h1 : Nat.card X ∣ Nat.card (normOddQuot W) := Subgroup.card_subgroup_dvd_card X
  have h := (h1.trans (card_dvd_card_mulAut hW hCW)).trans (card_mulAut_dvd hW hW256)
  rw [hX] at h
  exact absurd h (by norm_num)

end CFSG.ComponentClassification.AS81.Sec2
