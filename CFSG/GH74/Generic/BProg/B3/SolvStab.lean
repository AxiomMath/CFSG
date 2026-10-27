module

public import CFSG.GH74.Generic.BProg.Stability
public import CFSG.GH74.GLS.Balance.SL23Ext
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

theorem stability_DE [Finite G] {D E I : Subgroup G}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hE : CFSG.IsElementaryAbelian 2 ↥E) (hk : 2 ≤ pRank 2 ↥E)
    (hDE : ∀ d ∈ D, ∀ e ∈ E, d * e = e * d)
    (hI : I ≤ centralizer ((D ⊔ E : Subgroup G) : Set G)) (hI2 : oPrimeResidualOf 2 I = I)
    (h2C : ∀ d ∈ D, d ≠ 1 → ∀ e ∈ E, e ≠ 1 →
       ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
         pPrimeCoreOf 2 (centralizer ({e} : Set G))) :
    (∀ d ∈ D, d ≠ 1 → ⁅I, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥) ∨
      ⁅I, thetaHalf (pRank 2 ↥E - 1) E⁆ ≠ ⊥ := by
  have _hD := hD
  by_cases hθ : ⁅I, thetaHalf (pRank 2 ↥E - 1) E⁆ = ⊥
  · left
    intro d hd hd1
    have hIE : I ≤ centralizer (E : Set G) :=
      hI.trans (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
    refine commutator_eq_bot_of_stability hE hk hIE hI2 ?_ ?_ ?_ ?_ hθ
    · exact Nat.coprime_two_left.mpr (TwoThin.card_pPrimeCoreOf_odd _)
    · exact fun e he => TwoThin.mem_normalizer_pPrimeCoreOf
        (le_normalizer (mem_centralizer_singleton_iff.mpr (hDE d hd e he).symm))
    · exact fun i hi => TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer
        (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_left hd)) (hI hi)))
    · exact fun e he he1 => h2C d hd hd1 e he he1
  · exact Or.inr hθ

namespace SolvStab

theorem odd_orderOf_of_mem_pPrimeCoreOf [Finite G] {C : Subgroup G} {o : G}
    (ho : o ∈ pPrimeCoreOf 2 C) : Odd (orderOf o) :=
  Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd C) (Subgroup.orderOf_dvd_natCard _ ho)

theorem mem_pPrimeCoreOf_of_mem_pPrimePCore [Finite G] {C : Subgroup G} {t : G}
    (ht : t ∈ (pPrimePCore 2 ↥C).map C.subtype) (hodd : Odd (orderOf t)) : t ∈ pPrimeCoreOf 2 C := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : QuotientGroup.mk' (pPrimeCore 2 ↥C) c ∈ pCore 2 (↥C ⧸ pPrimeCore 2 ↥C) := hc
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥C ⧸ pPrimeCore 2 ↥C)) ⟨_, hcore⟩
  have hk' : (QuotientGroup.mk' (pPrimeCore 2 ↥C) c) ^ (2 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have hodd' : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥C) c)) :=
    Odd.of_dvd_nat (by simpa [Subgroup.orderOf_coe] using hodd) (orderOf_map_dvd _ c)
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥C) c = 1 := Balance.SL23.eq_one_of_odd_of_two_pow hodd' hk'
  exact ⟨c, (QuotientGroup.eq_one_iff c).1 h1, rfl⟩

end SolvStab

theorem not_le_O22_of_unstable [Finite G] {d e : G} {I0 : Subgroup G}
    (hI0 : I0 ≤ centralizer ({d} : Set G) ⊓ centralizer ({e} : Set G))
    (hn : ¬ ⁅I0, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
      pPrimeCoreOf 2 (centralizer ({e} : Set G))) :
    ¬ I0 ≤ (pPrimePCore 2 ↥(centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype := by
  intro hle
  refine hn ?_
  set C : Subgroup G := centralizer ({e} : Set G) with hC
  set Xe : Subgroup G := pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ C with hXe
  set N : Subgroup G := (pPrimePCore 2 ↥C).map C.subtype with hN
  have hnorm : I0 ≤ normalizer (Xe : Set G) := fun i hi =>
    inf_normalizer_le_normalizer_inf ⟨TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer (hI0 hi).1),
      le_normalizer (hI0 hi).2⟩
  have hTle : ⁅I0, Xe⁆ ≤ Xe := by
    rw [commutator_comm]
    exact Balance.SL23.comm_le_of_le_normalizer hnorm
  have hNn : ∀ x ∈ C, ∀ m ∈ N, x * m * x⁻¹ ∈ N := by
    intro x hx m hm
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hm
    exact ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, (pPrimePCore_normal 2 ↥C).conj_mem n hn ⟨x, hx⟩, by simp⟩
  have hTN : ⁅I0, Xe⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro i hi x hx
    have e1 : ⁅i, x⁆ = i * (x * i⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [e1]
    exact N.mul_mem (hle hi) (hNn x hx.2 i⁻¹ (N.inv_mem (hle hi)))
  intro t ht
  exact SolvStab.mem_pPrimeCoreOf_of_mem_pPrimePCore (hTN ht)
    (SolvStab.odd_orderOf_of_mem_pPrimeCoreOf (hTle ht).1)

namespace SolvStab

theorem map_two_element_eq_one {I M : Type*} [Group I] [Group M] (π : I →* SL(2, ZMod 3))
    (hπs : Function.Surjective π) (hπo : Odd (Nat.card π.ker)) (φ : I →* M)
    (hM : ∀ a b : M, a * b = b * a) {a : I} {k : ℕ} (ha : a ^ (2 ^ k) = 1) : φ a = 1 := by
  obtain ⟨t₀, ht₀, ht₁⟩ := Balance.SL23.S3_exists_order_three
  have hq : π a ^ 4 = 1 :=
    Balance.SL23.pow_four_of_pow_two_pow (k := k) (by rw [← map_pow, ha, map_one])
  obtain ⟨h₁, -, h₂, -, hπa⟩ := Balance.SL23.S3_comm_gen t₀ ht₀ ht₁ (π a) hq
  obtain ⟨u₁, rfl⟩ := hπs h₁
  obtain ⟨u₂, rfl⟩ := hπs h₂
  obtain ⟨v, rfl⟩ := hπs t₀
  set c : I := ⁅u₁, v⁆ * ⁅u₂, v⁆ with hc
  have hπc : π c = π a := by
    rw [hc, map_mul, map_commutatorElement, map_commutatorElement]
    exact hπa.symm
  have hφc : φ c = 1 := by
    rw [hc, map_mul, map_commutatorElement, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.2 (hM _ _),
      commutatorElement_eq_one_iff_mul_comm.2 (hM _ _), one_mul]
  have hn : c⁻¹ * a ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπc, inv_mul_cancel]
  have hodd : Odd (orderOf (c⁻¹ * a)) :=
    (Balance.SL23.Ext.mk π hπs hπo).odd_orderOf_of_mem_ker hn
  have hφn : φ (c⁻¹ * a) = φ a := by rw [map_mul, map_inv, hφc, inv_one, one_mul]
  have hodd' : Odd (orderOf (φ a)) := by
    rw [← hφn]
    exact Odd.of_dvd_nat hodd (orderOf_map_dvd φ _)
  exact Balance.SL23.eq_one_of_odd_of_two_pow hodd' (by rw [← map_pow, ha, map_one])

end SolvStab

end CFSG.GH74.Generic.BProg.B3
