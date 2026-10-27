module

public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank Polynomial

theorem pow_card_eq_zero_of_isNilpotent {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    {M : Matrix n n K} (h : IsNilpotent M) : M ^ Fintype.card n = 0 := by
  have h1 : M.charpoly = X ^ Fintype.card n :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero
  have h2 := Matrix.aeval_self_charpoly M
  rw [h1] at h2
  simpa using h2

theorem pow_four_eq_one_of_pow_two_pow_eq_one {K : Type} [Field K] [CharP K 2]
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {k : ℕ} (h : M ^ (2 ^ k) = 1) :
    M ^ 4 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) 2 := inferInstance
  have hc : Commute M 1 := Commute.one_right M
  have h1 : (M - 1) ^ (2 ^ k) = 0 := by
    rw [sub_pow_char_pow_of_commute (p := 2) (n := k) hc, h, one_pow, sub_self]
  have hnil : IsNilpotent (M - 1) := ⟨2 ^ k, h1⟩
  have h4 := pow_card_eq_zero_of_isNilpotent hnil
  rw [show Fintype.card (Fin 2 ⊕ Fin 2) = 2 ^ 2 by simp,
    sub_pow_char_pow_of_commute (p := 2) (n := 2) hc, one_pow, sub_eq_zero] at h4
  simpa using h4

theorem pow_four_eq_one_of_lieModel {X : Type} [Group X] {Y : Subgroup X}
    (hY : CFSG.Blueprint.LieModel ↥Y .PSp 2 2 2) {y : X} (hy : y ∈ Y) {k : ℕ}
    (hk : y ^ (2 ^ k) = 1) : y ^ 4 = 1 := by
  obtain ⟨⟨-, hf1, -, -⟩, K, _, _, hKcard, ⟨θ⟩⟩ :=
    CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hY
  haveI hch : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hKcard
  set ψ : ↥Y ≃* StatedSp 2 K := θ.trans (projSpEquiv K).symm with hψ
  set g : StatedSp 2 K := ψ ⟨y, hy⟩ with hg
  have hg1 : g ^ (2 ^ k) = 1 := by
    rw [hg, ← map_pow]
    have : (⟨y, hy⟩ : ↥Y) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hM : (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ^ (2 ^ k) =
      1 := by
    have := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hg1
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
  have hM4 := pow_four_eq_one_of_pow_two_pow_eq_one hM
  have hg4 : g ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using hM4
  have hy4 : (⟨y, hy⟩ : ↥Y) ^ 4 = 1 := by
    apply ψ.injective
    rw [map_pow, ← hg, hg4, map_one]
  simpa using congrArg Subtype.val hy4

open CFSG.ABGLocalTools in
theorem pow_four_eq_one_of_isSylowOf {X : Type} [Group X] [Finite X] {Y U L : Subgroup X}
    (hY : CFSG.Blueprint.LieModel ↥Y .PSp 2 2 2) (hUY : U ≤ Y) (hU : IsSylowOf 2 U L)
    {x : X} (hx : x ∈ L) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x ^ 4 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  set x' : L := ⟨x, hx⟩ with hx'
  have hx'pg : IsPGroup 2 (Subgroup.zpowers x') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have hdvd : orderOf x' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  obtain ⟨R, hR⟩ := hx'pg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q R
  have hxR : x' ∈ (R : Subgroup L) := hR (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxR
  obtain ⟨s, hsQ, hsx⟩ := hxR
  have hsx' : g * s * g⁻¹ = x' := by simpa [MulAut.smul_def, MulAut.conj_apply] using hsx
  have hsU : (s : X) ∈ U := by
    have : s ∈ (Q : Subgroup L) := hsQ
    rw [hQ] at this
    exact this
  have hs : s = g⁻¹ * x' * g := by rw [← hsx']; group
  have hx'pow : x' ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have hspow : s ^ (2 ^ k) = 1 := by
    rw [hs, show g⁻¹ * x' * g = g⁻¹ * x' * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hx'pow]
    group
  have h4 := pow_four_eq_one_of_lieModel hY (hUY hsU) (k := k) (by
    have := congrArg Subtype.val hspow
    simpa using this)
  have hs4 : s ^ 4 = 1 := Subtype.ext (by simpa using h4)
  have hx4 : x' ^ 4 = 1 := by
    have : x' = g * s * g⁻¹ := hsx'.symm
    rw [this, conj_pow, hs4]
    group
  simpa using congrArg Subtype.val hx4

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
