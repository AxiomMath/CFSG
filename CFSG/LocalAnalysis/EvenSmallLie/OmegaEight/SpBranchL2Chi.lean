module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillSpec
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSetting

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G] {T : Subgroup G} {N : ℕ} {mul : ℕ → ℕ → ℕ}
  (Φ : CodeIso T N mul) {inv : ℕ → ℕ} {gens : List ℕ} (h0 : mul 0 0 = 0)
  (hinv : invOK mul inv N = true) (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N)

include Φ h0 hinv hgens hG in
theorem chi_conj {b : List Bool} {χ : Array Bool} (hchi : chiOK mul gens N b χ = true) {y : G}
    (hyN : y ∈ normalizer (T : Set G)) {B : ℕ → ℕ}
    (hB : ∀ g : T, Φ.f (conjEquiv hyN g) = B (Φ.f g)) (hgen : ∀ g ∈ gens, χ[B g]! = χ[g]!) :
    ∀ x : T, χ[Φ.f (conjEquiv hyN x)]! = χ[Φ.f x]! := by
  refine Φ.induction h0 hgens hG ?_ ?_
  · rw [map_one]
  · intro x hx g hg
    have hgl := hgens g hg
    rw [map_mul, Φ.map_mul, Φ.map_mul,
      chi_mul Φ h0 hinv hgens hG hchi (Φ.lt _) (Φ.lt _),
      chi_mul Φ h0 hinv hgens hG hchi (Φ.lt _) (Φ.lt _), hx, hB, Φ.f_g hgl, hgen g hg]

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
