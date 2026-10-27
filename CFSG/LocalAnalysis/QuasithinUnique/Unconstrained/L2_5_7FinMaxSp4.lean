module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxRank
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent

public section

namespace CFSG.QuasithinUnique.Fin257

namespace Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b CFSG.Open

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {K : Type} [Field K] [CharP K 2]

theorem card_lt_of_outer
    [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (E : Subgroup (MulAut (antiSp K))) (h2 : ∀ α ∈ E, α * α = 1)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α)
    (hout : ∃ θ ∈ E, θ ∉ (MulAut.conj : antiSp K →* MulAut (antiSp K)).range) :
    Nat.card E < Nat.card (radA1 K) := by
  obtain ⟨θ, hθE, hθinn⟩ := hout
  obtain ⟨-, hcyc, -, hrank⟩ := even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK
  obtain ⟨-, hbound, -⟩ := hrank θ (h2 θ hθE) hθinn
  set c : antiSp K →* MulAut (antiSp K) := MulAut.conj with hcdef
  have hinj : Function.Injective c := conj_injective
  set E₀ : Subgroup (MulAut (antiSp K)) := E ⊓ c.range with hE₀
  set B := E.comap c with hB
  have hEB : B.map c = E₀ := by
    rw [Subgroup.map_comap_eq, inf_comm]
  have hcardB : Nat.card E₀ = Nat.card B := by
    rw [← hEB]
    exact Subgroup.card_map_of_injective hinj
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    apply hinj
    rw [map_mul, map_one]
    exact h2 _ hx
  have hBfix : B ≤ fixedSubgroup θ := by
    intro x hx
    rw [mem_fixedSubgroup]
    have hx' : (MulAut.conj x : MulAut (antiSp K)) ∈ E := hx
    have h1 : c (θ x) = c x := by
      have := conj_apply_eq' θ x
      rw [hcdef]
      show MulAut.conj (θ x) = MulAut.conj x
      rw [this]
      have hcomm := hc θ hθE _ hx'
      calc θ * MulAut.conj x * θ⁻¹ = (θ * MulAut.conj x) * θ⁻¹ := rfl
        _ = (MulAut.conj x * θ) * θ⁻¹ := by rw [hcomm]
        _ = MulAut.conj x := by group
    exact hinj h1
  have hBcard : Nat.card B ≤ 2 ^ (if Even n then 3 * (n / 2) else 2 * n) :=
    hbound B hBfix hB2
  have hEcard : Nat.card E = E₀.relIndex E * Nat.card E₀ := by
    have := Subgroup.relIndex_mul_card (H := E₀) (K := E)
    rw [inf_of_le_left inf_le_left] at this
    exact this.symm
  have hidx : E₀.relIndex E ≤ 2 := by
    let Θ : ↥E →* Outer (antiSp K) :=
      (QuotientGroup.mk' (inner (antiSp K))).comp E.subtype
    have hker : Θ.ker = E₀.subgroupOf E := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show (QuotientGroup.mk (x : MulAut (antiSp K)) : Outer (antiSp K)) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff]
      constructor
      · intro hx
        exact ⟨x.2, hx⟩
      · intro hx
        exact hx.2
    have hsq : ∀ y : Outer (antiSp K), y ∈ Θ.range → y ^ 2 = 1 := by
      rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        exact h2 (x : MulAut (antiSp K)) x.2)
      rw [this, map_one]
    have hcard2 : Nat.card Θ.range ≤ 2 := by
      have := Fintype.ofFinite (Outer (antiSp K))
      classical
      calc Nat.card Θ.range
          ≤ Nat.card {y : Outer (antiSp K) // y ^ 2 = 1} :=
            Nat.card_le_card_of_injective (fun y => ⟨y.1, hsq y.1 y.2⟩)
              (fun a b h => Subtype.ext (by
                have := congrArg Subtype.val h
                simpa using this))
        _ ≤ 2 := by
          have h1 := IsCyclic.card_pow_eq_one_le (α := Outer (antiSp K)) (n := 2) (by norm_num)
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          exact h1
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact hcard2
  obtain ⟨-, h1, -, -⟩ := card_radicals (K := K)
  rw [h1, hK, hEcard, hcardB]
  calc E₀.relIndex E * Nat.card B ≤ 2 * 2 ^ (if Even n then 3 * (n / 2) else 2 * n) :=
        Nat.mul_le_mul hidx hBcard
    _ < (2 ^ n) ^ 3 := by
      by_cases hev : Even n
      · obtain ⟨m, hm⟩ := hev
        have hm1 : 1 ≤ m := by omega
        have e1 : (if Even n then 3 * (n / 2) else 2 * n) = 3 * m := by
          have hE : Even n := ⟨m, hm⟩
          simp only [hE, ↓reduceIte]
          omega
        rw [e1, ← pow_succ', ← pow_mul]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · have e2 : (if Even n then 3 * (n / 2) else 2 * n) = 2 * n := by
          simp only [hev, ↓reduceIte]
        rw [e2, ← pow_succ', ← pow_mul]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem maxRankModel_Sp
    [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    MaxRankModel (antiSp K) (antiUnipotent K) (radA1 K) (radA2 K) := by
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  refine maxRankModel_of_outer (modelData_Sp hn hK) (h1.trans h2.symm)
    (fun B hBU hB => elementary_le_radA1_or_radA2 hBU fun x hx => hB x hx)
    (fun E h2 hc _ hout => card_lt_of_outer hn hK E h2 hc hout)

end Sp4

end CFSG.QuasithinUnique.Fin257
