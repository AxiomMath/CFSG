module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaOut
import CFSG.LocalAnalysis.RankThreeTheoremC.ExponentThreeTransvection
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (centerQuotientAction centerQuotientAction_mulVec centerQuotientAction_eq
  KOutTwoGroup exists_mul_eq_of_kOutTwoGroup mem_inf_of_pow_eq_one_of_decomp
  exists_inv_mul_mem_centralizer_of_kOutTwoGroup)

section Elements

variable {X : Type*} [Group X]

theorem exists_pow_not_dvd_isPElement [Finite X] (p : ℕ) [Fact p.Prime] (x : X) :
    ∃ m a : ℕ, ¬ p ∣ m ∧ (x ^ m) ^ (p ^ a) = 1 := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p
    (Fact.out : p.Prime).ne_one
  refine ⟨m, a, hm, ?_⟩
  rw [← pow_mul, mul_comm, ← hord]
  exact pow_orderOf_eq_one x

theorem pow_ne_one_of_not_dvd {p : ℕ} [Fact p.Prime] {y : X} (hy : y ^ p = 1) (hy1 : y ≠ 1)
    {m : ℕ} (hm : ¬ p ∣ m) : y ^ m ≠ 1 := fun h =>
  hm ((orderOf_eq_prime hy hy1) ▸ orderOf_dvd_of_pow_eq_one h)

end Elements

section Exponent

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem pow_eq_one_of_exponent (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hexp : ∀ t ∈ (R : Subgroup X) ⊓ K, t ^ p = 1) {x : X} (hx : x ∈ K) {n : ℕ}
    (hxn : x ^ (p ^ n) = 1) : x ^ p = 1 := by
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := (orderOf x).factorization p) ?_
    rw [Nat.card_zpowers]
    have hdvd : orderOf x ∣ p ^ n := orderOf_dvd_of_pow_eq_one hxn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    rw [hj, Nat.Prime.factorization_pow (Fact.out : p.Prime)]
    simp
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_isPGroup R hxp
  have h1 := hg x (Subgroup.mem_zpowers x)
  have h2 : g⁻¹ * x * g ∈ K := by simpa using ‹K.Normal›.conj_mem x hx g⁻¹
  have h3 := hexp _ ⟨h1, h2⟩
  have h4 : (g⁻¹ * x * g) ^ p = g⁻¹ * x ^ p * g := by
    simpa using conj_pow (a := g⁻¹) (b := x) (i := p)
  rw [h4] at h3
  have h5 : x ^ p = g * (g⁻¹ * x ^ p * g) * g⁻¹ := by group
  rw [h5, h3]
  group

end Exponent

section Cubes

variable {G : Type*} [Group G]

theorem pow_three_mul_mem {E : Subgroup G} {k : G} (hk : k ∈ Subgroup.normalizer (E : Set G))
    (hk3 : k ^ 3 = 1) {b : G} (hb : b ∈ E) : (b * k) ^ 3 ∈ E := by
  have h1 : k * b * k⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hk b).mp hb
  have h2 : k * (k * b * k⁻¹) * k⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hk _).mp h1
  have : (b * k) ^ 3 = b * (k * b * k⁻¹) * (k * (k * b * k⁻¹) * k⁻¹) * k ^ 3 := by
    rw [pow_three', pow_three']
    group
  rw [this, hk3, mul_one]
  exact E.mul_mem (E.mul_mem hb h1) h2

theorem pow_three_inv_mul_mem {E : Subgroup G} {k : G} (hk : k ∈ Subgroup.normalizer (E : Set G))
    (hk3 : k ^ 3 = 1) {b : G} (hb : b ∈ E) : (k⁻¹ * b) ^ 3 ∈ E := by
  have hk' : k⁻¹ ∈ Subgroup.normalizer (E : Set G) := inv_mem hk
  have hk3' : (k⁻¹) ^ 3 = 1 := by rw [inv_pow, hk3, inv_one]
  have h1 := pow_three_mul_mem hk' hk3' hb
  have h2 : (k⁻¹ * b) ^ 3 = k⁻¹ * (b * k⁻¹) ^ 3 * k⁻¹⁻¹ := by
    rw [pow_three', pow_three']
    group
  rw [h2]
  exact (Subgroup.mem_normalizer_iff.mp hk' _).mp h1

end Cubes

private theorem upper_ne_one : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := by
  decide

private theorem upper_pow_three : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 = 1 := by
  decide

theorem exists_statedSL_orderOf_three : ∃ A ∈ StatedSL 2 (ZMod 3), A ≠ 1 ∧ A ^ 3 = 1 := by
  obtain ⟨A, hA, hAeq⟩ := exists_statedSL_upper (p := 3) 1
  refine ⟨A, hA, fun h => upper_ne_one (by rw [← hAeq, h]; rfl), ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hAeq]
  exact upper_pow_three

section Main

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_isPElement_transvection_of_outTwo {K : Subgroup Y} [K.Normal] (hout : KOutTwoGroup K)
    {E L : Subgroup Y} (hEK : E ≤ K)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod 3))
    (hSL : StatedSL 2 (ZMod 3) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set Y))).map (centerQuotientAction E e)) :
    ∃ (κ : Y) (hκN : κ ∈ Subgroup.normalizer (E : Set Y)), κ ∈ K ∧
      centerQuotientAction E e ⟨κ, hκN⟩ ≠ 1 ∧ ∃ b : ℕ, κ ^ (3 ^ b) = 1 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨A, hA, hA1, hA3⟩ := exists_statedSL_orderOf_three
  obtain ⟨g, -, hgA⟩ := Subgroup.mem_map.mp (hSL hA)
  obtain ⟨m, a, hm, hu⟩ := exists_pow_not_dvd_isPElement 3 g
  obtain ⟨u, hugm⟩ : ∃ u : Subgroup.normalizer (E : Set Y), u = g ^ m := ⟨_, rfl⟩
  have hu' : u ^ (3 ^ a) = 1 := by rw [hugm]; exact hu
  have hψu : centerQuotientAction E e u = A ^ m := by rw [hugm, map_pow, hgA]
  have hAm1 : A ^ m ≠ 1 := pow_ne_one_of_not_dvd hA3 hA1 hm
  have hAm3 : (A ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hA3, one_pow]
  obtain ⟨κ, hκK, hκC⟩ := exists_inv_mul_mem_centralizer_of_kOutTwoGroup hp (by norm_num) hout
    (r := (u : Y)) (n := a) (by
      have := congrArg Subtype.val hu'
      simpa using this)
  have hκu : ∀ x ∈ E, κ * x * κ⁻¹ = (u : Y) * x * (u : Y)⁻¹ := by
    intro x hx
    have hcomm := Subgroup.mem_centralizer_iff.mp hκC x (hEK hx)
    calc κ * x * κ⁻¹ = κ * (x * (κ⁻¹ * (u : Y))) * (u : Y)⁻¹ := by group
      _ = (u : Y) * x * (u : Y)⁻¹ := by rw [hcomm]; group
  have hκN : κ ∈ Subgroup.normalizer (E : Set Y) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [hκu x hx]
    exact (Subgroup.mem_normalizer_iff.mp u.2 x).mp hx
  have hψκ : centerQuotientAction E e ⟨κ, hκN⟩ = A ^ m := by
    rw [← hψu]
    refine centerQuotientAction_eq E e ⟨κ, hκN⟩ _ fun x y hxy => ?_
    refine (centerQuotientAction_mulVec E e u (u := x) (v := y) ?_).symm
    rw [hxy]
    exact hκu x x.2
  obtain ⟨m₂, b, hm₂, hκ₁⟩ := exists_pow_not_dvd_isPElement 3
    (⟨κ, hκN⟩ : Subgroup.normalizer (E : Set Y))
  refine ⟨κ ^ m₂, (⟨κ, hκN⟩ ^ m₂ : Subgroup.normalizer (E : Set Y)).2, K.pow_mem hκK m₂, ?_,
    b, by simpa using congrArg Subtype.val hκ₁⟩
  show centerQuotientAction E e (⟨κ, hκN⟩ ^ m₂) ≠ 1
  rw [map_pow, hψκ]
  exact pow_ne_one_of_not_dvd hAm3 hAm1 hm₂

theorem false_of_outTwo_exponent_three (R : Sylow 3 Y) {K : Subgroup Y} [K.Normal]
    (hout : KOutTwoGroup K) (hexp : ∀ t ∈ (R : Subgroup Y) ⊓ K, t ^ 3 = 1) {zb : Y}
    (hzbK : zb ∈ K)
    (hC : ∀ c ∈ (R : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = 3 →
      c ∈ Subgroup.zpowers zb)
    {E L : Subgroup Y} (hER : E ≤ (R : Subgroup Y)) (hEexp : ∀ x ∈ E, x ^ 3 = 1)
    (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers zb)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod 3))
    (hSL : StatedSL 2 (ZMod 3) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set Y))).map (centerQuotientAction E e)) :
    False := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hdec : ∀ r ∈ (R : Subgroup Y), ∃ t ∈ (R : Subgroup Y) ⊓ K,
      ∃ c ∈ (R : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), t * c = r :=
    fun r hr => exists_mul_eq_of_kOutTwoGroup hp (by norm_num) R hout hr
  have hzbE : zb ∈ E := Subgroup.map_subtype_le _ (hEZ ▸ Subgroup.mem_zpowers zb)
  have hEK : E ≤ K := fun x hx =>
    (mem_inf_of_pow_eq_one_of_decomp hp (hER hzbE) hzbK hC hdec hexp (hER hx) (hEexp x hx)).2
  obtain ⟨κ, hκN, hκK, hψ, b, hκb⟩ := exists_isPElement_transvection_of_outTwo hout hEK e hSL
  have hκ3 : κ ^ 3 = 1 := pow_eq_one_of_exponent R hexp hκK hκb
  have key : ∀ w ∈ K, w ^ 3 ∈ E → w ^ 3 = 1 := by
    intro w hwK hwE
    refine pow_eq_one_of_exponent R hexp hwK (n := 2) ?_
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]
    exact hEexp _ hwE
  exact false_of_pow_three_transvection e hκN hψ hκ3
    (fun x hx => key _ (K.mul_mem (hEK hx) hκK) (pow_three_mul_mem hκN hκ3 hx))
    (fun x hx => key _ (K.mul_mem (K.inv_mem hκK) (hEK hx)) (pow_three_inv_mul_mem hκN hκ3 hx))

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC
