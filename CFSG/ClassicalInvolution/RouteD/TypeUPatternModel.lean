module

public import CFSG.ClassicalInvolution.RouteD.TypeUPatternBasic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.RouteD.TypeUModel

public section

namespace CFSG.ClassicalInvolution.RouteD

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

section StandardPair

theorem eq_map_zEltU_of_involution (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {X : Type}
    [Group X] {θ : Su K p f 3 →* X} {e : Su K p f 2 →* Su K p f 3}
    (he : Function.Injective (θ.comp e)) {T : Pair 3} (hT : e.range = LcU K p f T) {c : X}
    (hc : c ∈ (θ.comp e).range) (hc2 : orderOf c = 2) : c = θ (zEltU K p f T) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp2
  obtain ⟨A, rfl⟩ := hc
  have hcc : (θ.comp e) A * (θ.comp e) A = 1 := by
    have := pow_orderOf_eq_one ((θ.comp e) A)
    rwa [hc2, pow_two] at this
  have hAA : A * A = 1 := he (by rw [map_mul, map_one]; exact hcc)
  have ht : e A * e A = 1 := by rw [← map_mul, hAA, map_one]
  have ht1 : e A ≠ 1 := by
    intro h1
    have : (θ.comp e) A = 1 := by simp [h1]
    rw [this, orderOf_one] at hc2
    omega
  have ht2 : orderOf (e A) = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
  have htL : e A ∈ LcU K p f T := hT ▸ ⟨A, rfl⟩
  have := (isLongRootSU2_LcU h2 (by norm_num : 2 ≤ 3) T).eq_of_orderOf_eq_two hK hp2 htL ht2
  exact congrArg θ this

theorem unitaryStandardPair_involutions_commute (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {X : Type} [Group X] {W U V : Subgroup X} (h : UnitaryBlockStandardPair K p f W U V)
    {a b : X} (ha : a ∈ U) (hb : b ∈ V) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    a * b = b * a := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp2
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  obtain ⟨hi₂, hr₂, hi₀, hr₀⟩ := pair_block_inj hK hker hU hV
  let T₀ : Pair 3 := ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (by simp)⟩
  let T₁ : Pair 3 := ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  have e₀ : (embSUid (unitaryInvolution K p f) 2).range = LcU K p f T₀ := by
    rw [embSUid_two_eq_blockEmb]
    exact range_blockEmb_two_eq_LcU h2 (by omega) rfl
  have e₁ : (embSUid (unitaryInvolution K p f) 0).range = LcU K p f T₁ := by
    rw [embSUid_zero_eq_blockEmb]
    exact range_blockEmb_two_eq_LcU h2 (by omega) rfl
  have ha' := eq_map_zEltU_of_involution hK hp2 hi₂ e₀ (by rw [hr₂]; exact ha) ha2
  have hb' := eq_map_zEltU_of_involution hK hp2 hi₀ e₁ (by rw [hr₀]; exact hb) hb2
  rw [ha', hb', ← map_mul, ← map_mul,
    signGroupU_comm (zEltU_mem_signGroupU T₀) (zEltU_mem_signGroupU T₁)]

end StandardPair

section Perp

theorem exists_perp_not_commutes_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 4 ≤ n) {R₀ Rβ : Subgroup (Su K p f n)} {i₀ iβ : Su K p f n}
    (h₀ : IsLongRootSU2 K p f (by omega : 2 ≤ n) R₀ i₀)
    (hβ : IsLongRootSU2 K p f (by omega : 2 ≤ n) Rβ iβ) (hc : Commute i₀ iβ) (hne : i₀ ≠ iβ)
    (hnc : ¬ Commutes R₀ Rβ) :
    ∃ (R : Subgroup (Su K p f n)) (i : Su K p f n),
      IsLongRootSU2 K p f (by omega : 2 ≤ n) R i ∧ Commutes R R₀ ∧ ¬ Commutes R Rβ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp2
  rcases inf_eq_bot_or_exists_conj_su hK hp2 (by omega : 3 ≤ n) h₀ hβ hc hne with
    hbot | ⟨g, e₁, e₂, -, -⟩
  · exact absurd hbot (inf_ne_bot_of_not_commutes_su h2 h₀ hβ hc hnc)
  · have hcinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    let T₀ : Pair n := ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
    let T₁ : Pair n := ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
    let T₂ : Pair n := ⟨{⟨2, by omega⟩, ⟨3, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
    have hb0 : (blockEmb K p f n 2 0 (by omega)).range = LcU K p f T₀ :=
      range_blockEmb_two_eq_LcU h2 (by omega) rfl
    have hb1 : (blockEmb K p f n 2 1 (by omega)).range = LcU K p f T₁ :=
      range_blockEmb_two_eq_LcU h2 (by omega) rfl
    have eR₀ : R₀ = (LcU K p f T₀).map (MulAut.conj g).toMonoidHom := by rw [e₁, hb0]
    have eRβ : Rβ = (LcU K p f T₁).map (MulAut.conj g).toMonoidHom := by rw [e₂, hb1]
    refine ⟨(LcU K p f T₂).map (MulAut.conj g).toMonoidHom, g * zEltU K p f T₂ * g⁻¹,
      (isLongRootSU2_LcU h2 (by omega) T₂).conj g, ?_, ?_⟩
    · rw [eR₀, commutes_map_iff _ hcinj]
      refine commutes_LcU_of_disjoint h2 ?_
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [T₀, T₂, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx hx'
      omega
    · rw [eRβ, commutes_map_iff _ hcinj]
      intro hcomm
      exact not_commutes_LcU_overlap hK hp2 (by omega : 3 ≤ n) (i := ⟨1, by omega⟩)
        (j := ⟨2, by omega⟩) (k := ⟨3, by omega⟩) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) fun a ha b hb => (hcomm b hb a ha).symm

end Perp

section Nodes

theorem range_blockEmb2_eq_LcU_nodePair (h2 : (2 : K) ≠ 0) {m a : ℕ} (ha : a < m) :
    (blockEmb2 K p f m ⟨a, ha⟩).range = LcU K p f (nodePair m a ha) :=
  range_blockEmb2_eq_LcU h2 ⟨a, ha⟩ rfl

theorem conjSign_partnerSigns_four (hK : Nat.card K = (p ^ f) ^ 2) (x : Su K p f (4 + 1)) :
    conjSign hK (partnerSigns 4 1) x =
      zEltU K p f (nodePair 4 1 (by norm_num)) * x *
        (zEltU K p f (nodePair 4 1 (by norm_num)))⁻¹ := by
  set T := nodePair 4 1 (by norm_num) with hT
  have hinv : (zEltU K p f T)⁻¹ = zEltU K p f T :=
    inv_eq_of_mul_eq_one_right (zEltU_mul_self T)
  rw [hinv]
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  rw [coe_coe_conjSign_apply]
  have hmem : ∀ i : Fin (4 + 1), i ∈ T.1 ↔ (i.val = 1 ∨ i.val = 2) := by
    intro i
    simp only [hT, nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  have hsgn : ∀ i : Fin (4 + 1),
      signVal K (partnerSigns 4 1 i) = -(if i ∈ T.1 then (-1 : K) else 1) := by
    intro i
    fin_cases i <;> simp [partnerSigns, signVal, hmem]
  have e : suMat (zEltU K p f T * x * zEltU K p f T) a b =
      (if a ∈ T.1 then (-1 : K) else 1) * suMat x a b * (if b ∈ T.1 then (-1 : K) else 1) := by
    rw [suMat_mul, suMat_mul, suMat_zEltU]
    simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  show signVal K (partnerSigns 4 1 a) * suMat x a b * signVal K (partnerSigns 4 1 b) =
    suMat (zEltU K p f T * x * zEltU K p f T) a b
  rw [e, hsgn a, hsgn b]
  ring

end Nodes

end CFSG.ClassicalInvolution.RouteD
