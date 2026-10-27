module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixOne

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

structure TwelveSixKbar (M H : Subgroup G) (p n₁ n₂ n₃ : ℕ) : Prop where
  n₁_eq_one : n₁ = 1
  n₂_eq_one : n₂ = 1
  n₃_eq_one : n₃ = 1
  p_eq_three : p = 3
  kbar_type : CFSG.Blueprint.LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
    Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9))
  k_inter : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H ⊓ M) →
    kSub p M H ⊓ M =
      (kSub p M H ⊓ normalizer (thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub p M H)

theorem twelveSix_of_twelveCtx {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (h812 : Section15.O812sixGen)
    (h124 : TwelveFour M H)
    (h125 : ∀ q : ℕ, q ∈ sigmaSet G M → TwelveFive M H q)
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L))
    (hdvdL : ∀ q : ℕ, q ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      q ∣ Nat.card L)
    (hcard : (weakBlockSet M H).ncard = 3)
    {d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}
    (hK : TwelveSixKbar M H p n₁ n₂ n₃)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃ :=
  twelveSix_of_parts
    (fun W hW hWL =>
      centralizer_le_of_mem_weakBlockSet h h812 hd.mem_sigma hL3
        (hdvdL d hd.mem_sigma) (le_of_eq hcard.symm) hd.mem₁ hW hWL)
    (fun W hW hWL =>
      centralizer_le_of_mem_weakBlockSet h h812 hd.mem_sigma hL3
        (hdvdL d hd.mem_sigma) (le_of_eq hcard.symm) hd.mem₂ hW hWL)
    (fun W hW hWL =>
      centralizer_le_of_mem_weakBlockSet h h812 hd.mem_sigma hL3
        (hdvdL d hd.mem_sigma) (le_of_eq hcard.symm) hd.mem₃ hW hWL)
    hK.n₁_eq_one hK.n₂_eq_one hK.n₃_eq_one
    (twelveSix_part_three_of_odd_prime_divisors h124 h.sigma_nonempty
      (fun q hq => (h125 q hq).1)
      (odd_prime_divisors_of_n_eq_one hd hK.n₁_eq_one hK.n₂_eq_one hK.n₃_eq_one))
    hK.p_eq_three hK.kbar_type hK.k_inter

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
