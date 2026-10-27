module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

section Pair

theorem eq_one_of_torus_pow_eq_one {r : ℕ} [Fact r.Prime] [CharP K r] {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) {n : ℕ} (hn : h ^ (r ^ n) = 1) : h = 1 := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have h1 : rootDiagUnit τ (b ^ (r ^ n)) = rootDiagUnit τ (1 : Fin τ.rank → Kˣ) := by
    rw [show rootDiagUnit τ (b ^ (r ^ n)) = (rootDiagUnit τ b) ^ (r ^ n) from
      map_pow (rootDiagUnitHom τ K) b (r ^ n), hn]
    exact (map_one (rootDiagUnitHom τ K)).symm
  have h2 : b ^ (r ^ n) = 1 := rootDiagUnit_injective h1
  have h3 : b = 1 := by
    funext i
    have h4 : ((b i : Kˣ) : K) ^ (r ^ n) = 1 := by
      have := congrFun h2 i
      simpa using congrArg (fun u : Kˣ => (u : K)) this
    have h5 : (((b i : Kˣ) : K) - 1) ^ (r ^ n) = 0 := by
      rw [sub_pow_char_pow, h4, one_pow, sub_self]
    have h6 : ((b i : Kˣ) : K) = 1 := sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n (Fact.out : r.Prime).ne_zero) |>.1 h5)
    exact Units.ext h6
  rw [h3]
  exact map_one (rootDiagUnitHom τ K)

end Pair

end CFSG.LieType.Chevalley
