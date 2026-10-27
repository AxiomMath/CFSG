module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Chart
public import CFSG.ClassicalInvolution.Models.LinearFrames.Generation

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Sets

variable (K : Type) [Field K] (n : ℕ)

variable {K n} in
@[expose] def longRootSet (hn : 2 ≤ n) : Set (Subgroup SL(n, K)) :=
  {L | ∃ i, IsLongRootSL2 hn L i}

abbrev coordSet : Set (Subgroup SL(n, K)) := Set.range (Lc K (n := n))

variable {K n}

theorem mem_coordSet {L : Subgroup SL(n, K)} : L ∈ coordSet K n ↔ ∃ T : Pair n, Lc K T = L :=
  Iff.rfl

theorem Lc_mem_coordSet (T : Pair n) : Lc K T ∈ coordSet K n := ⟨T, rfl⟩

theorem mem_longRootSet_iff (hn : 2 ≤ n) {L : Subgroup SL(n, K)} :
    L ∈ longRootSet hn ↔ ∃ g : SL(n, K), L = (rootSL2 K hn).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨i, g, hL, -⟩
    exact ⟨g, hL⟩
  · rintro ⟨g, hL⟩
    exact ⟨g * rootInv K hn * g⁻¹, g, hL, rfl⟩

theorem longRootSet_conjInvariant (hn : 2 ≤ n) : ConjInvariant (longRootSet (K := K) hn) := by
  rintro g L ⟨i, hi⟩
  exact ⟨g * i * g⁻¹, hi.conj g⟩

theorem Lc_mem_longRootSet (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    Lc K T ∈ longRootSet hn :=
  ⟨zElt K T, isLongRootSL2_Lc h2 hn T⟩

theorem coordSet_eq_sigmaSet (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    coordSet K n = sigmaSet K (longRootSet (K := K) (by omega : 2 ≤ n)) (signGroup K n) := by
  ext L
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨Lc_mem_longRootSet h2 _ T, inSigma_Lc h2 hn T⟩
  · rintro ⟨⟨i, hi⟩, hS⟩
    obtain ⟨T, rfl⟩ := exists_pair_of_inSigma h2 hi hS
    exact ⟨T, rfl⟩

theorem Lc_injective (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) : Function.Injective (Lc K (n := n)) := by
  intro T T' h
  have h1 := isLongRootSL2_Lc h2 hn T
  have h1' : IsLongRootSL2 hn (Lc K T) (zElt K T') := h ▸ isLongRootSL2_Lc h2 hn T'
  exact zElt_injective h2 (h1.involution_unique h2 h1')

end Sets

section Generation

variable {K : Type} [Field K] {n : ℕ}

theorem zElt_ne_one (h2 : (2 : K) ≠ 0) (T : Pair n) : zElt K T ≠ 1 :=
  z_ne_one (mat := slMat K n) (z := zElt K (n := n)) h2 (fun _ => rfl) T

theorem isUniqueInvolution_Lc (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    IsUniqueInvolution (Lc K T) (zElt K T) := by
  have hL := isLongRootSL2_Lc h2 hn T
  refine ⟨hL.mem, zElt_ne_one h2 T, zElt_mul_self T, fun y hy hy2 => ?_⟩
  by_cases h1 : y = 1
  · exact Or.inl h1
  · exact Or.inr (hL.eq_of_orderOf_eq_two h2 hy (orderOf_eq_prime (by rwa [pow_two]) h1))

theorem zSet_coordSet (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    zSet (coordSet K n) = Set.range (zElt K (n := n)) := by
  ext z
  constructor
  · rintro ⟨L, ⟨T, rfl⟩, hz⟩
    exact ⟨T, (isUniqueInvolution_Lc h2 hn T).eq hz⟩
  · rintro ⟨T, rfl⟩
    exact ⟨Lc K T, Lc_mem_coordSet T, isUniqueInvolution_Lc h2 hn T⟩

theorem closure_range_zElt (h2 : (2 : K) ≠ 0) :
    Subgroup.closure (Set.range (zElt K (n := n))) = signGroup K n :=
  closure_range_z (mat := slMat K n) (z := zElt K (n := n)) h2 slMat_injective (fun x => x.2)
    (fun _ => rfl)

theorem card_signGroup [Finite K] (h2 : (2 : K) ≠ 0) (hn : 4 ≤ n) :
    8 ≤ Nat.card (signGroup K n) :=
  card_signSubgroup (mat := slMat K n) (z := zElt K (n := n)) h2 (fun _ => rfl) hn

end Generation

section TheFrame

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem toralFrame (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn : 4 ≤ n) :
    ToralFrame K (longRootSet (K := K) (by omega : 2 ≤ n)) (signGroup K n) (coordSet K n) := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  exact
    { odd := hodd
      five := h5
      inv := longRootSet_conjInvariant _
      elem := fun x hx => signGroup_sq hx
      eq_sigma := coordSet_eq_sigmaSet h2 (by omega)
      gen := by
        rw [zSet_coordSet h2 (by omega)]
        exact closure_range_zElt h2
      card := card_signGroup h2 hn }

end TheFrame

end CFSG.ClassicalInvolution.Models
