module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_card_CLP_of_not_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om)
    (hk : ∃ k ∈ q13CLP t tau x₁ x₂ rho om, ⁅t, k⁆ ∉ q13AN t tau x₁ x₂ rho) :
    Nat.card (q13CLP t tau x₁ x₂ rho om) = 2 ^ 9 := by
  let K : Subgroup G := q13CLP t tau x₁ x₂ rho om
  let L0 : Subgroup G := q13L t tau x₁ x₂ rho om
  have hKL : K ≤ L0 := fun k hk => (Subgroup.mem_inf.mp hk).1
  let φ : ↥K →* G :=
    { toFun := fun k => ⁅t, (k : G)⁆
      map_one' := by simp
      map_mul' := by
        intro a b
        show ⁅t, ((a * b : ↥K) : G)⁆ = ⁅t, (a : G)⁆ * ⁅t, (b : G)⁆
        rw [Subgroup.coe_mul]
        exact q13e_kap_mul_CLP h hD (a : G) a.2 (b : G) (hKL b.2) }
  let W : Subgroup G := φ.range
  have hWP : W ≤ q13P t tau x₁ x₂ rho om := by
    intro w hw
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hw
    exact q13e_kap_mem_P h hD (k : G) (hKL k.2)
  have hNW : ctxN tau x₁ x₂ ≤ W := by
    intro n hn
    obtain ⟨p, hpP, hpn⟩ := q13e_kap_onto_N h hD n hn
    exact MonoidHom.mem_range.mpr ⟨⟨p, q13e_P_le_CLP h hD hpP⟩, hpn⟩
  have hWM : ∀ g ∈ ctxM t tau x₁ x₂, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hgM w hw
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hw
    have hgL : g ∈ L0 := hD.M_le_L hgM
    refine MonoidHom.mem_range.mpr
      ⟨⟨g * (k : G) * g⁻¹, q13e_CLP_normal_L h hD g hgL (k : G) k.2⟩, ?_⟩
    exact q13e_kap_conj_CLP h hD g hgL (k : G) k.2
  obtain ⟨k, hkK, hkA⟩ := hk
  have hwW : (⁅t, k⁆ : G) ∈ W := MonoidHom.mem_range.mpr ⟨⟨k, hkK⟩, rfl⟩
  have hwA : (⁅t, k⁆ : G) ∉ q13AN t tau x₁ x₂ rho := hkA
  have hPW : ∀ p ∈ q13P t tau x₁ x₂ rho om, p ∈ W :=
    q13e_M1 h hD hWP hNW hWM hwW hwA
  have hrange : φ.range = q13P t tau x₁ x₂ rho om :=
    le_antisymm hWP (fun p hp => hPW p hp)
  have hNK : ctxN tau x₁ x₂ ≤ K := fun n hn => q13e_P_le_CLP h hD (q13d_N_le_P h hn)
  have hker : ∀ k ∈ K, ⁅t, k⁆ = 1 ↔ k ∈ ctxN tau x₁ x₂ := by
    intro k hk
    constructor
    · intro h1
      exact q13e_kap_ker_CLP h hB hD k hk h1
    · intro hkN
      rw [q13e_kap_P h hD k (q13d_N_le_P h hkN)]
      have h2 : k ^ 2 = 1 := (q13b_N_elemAbelian h).2 k hkN
      rw [h2, inv_one]
  have hker_eq : φ.ker = (ctxN tau x₁ x₂).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker (k : G) k.2
  have hker_card : Nat.card φ.ker = Nat.card (ctxN tau x₁ x₂) := by
    rw [hker_eq]
    exact Nat.card_congr (subgroupOfEquivOfLe hNK).toEquiv
  have hcard : Nat.card K = 2 ^ 9 := by
    have hh := Subgroup.card_ker_mul_card_range φ
    rw [hker_card, hrange, q13b_card_N h, q13d_card_P h hD.A_cent] at hh
    norm_num at hh ⊢
    exact hh.symm
  show Nat.card K = 2 ^ 9
  exact hcard

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
