module

public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart
public import CFSG.ClassicalInvolution.Models.LinearFrames.Generation

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open scoped MatrixGroups

section SetsU

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)

variable {K p f n} in
@[expose] def longRootSetU (hn : 2 ≤ n) : Set (Subgroup (Su K p f n)) :=
  {L | ∃ i, IsLongRootSU2 K p f hn L i}

noncomputable abbrev coordSetU : Set (Subgroup (Su K p f n)) :=
  Set.range (LcU K p f (n := n))

variable {K p f n}

theorem mem_coordSetU {L : Subgroup (Su K p f n)} :
    L ∈ coordSetU K p f n ↔ ∃ T : Pair n, LcU K p f T = L :=
  Iff.rfl

theorem LcU_mem_coordSetU (T : Pair n) : LcU K p f T ∈ coordSetU K p f n := ⟨T, rfl⟩

theorem mem_longRootSetU_iff (hn : 2 ≤ n) {L : Subgroup (Su K p f n)} :
    L ∈ longRootSetU (K := K) (p := p) (f := f) hn ↔
      ∃ g : Su K p f n, L = (rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨i, g, hL, -⟩
    exact ⟨g, hL⟩
  · rintro ⟨g, hL⟩
    exact ⟨g * rootInvSU K p f hn * g⁻¹, g, hL, rfl⟩

theorem longRootSetU_conjInvariant (hn : 2 ≤ n) :
    ConjInvariant (longRootSetU (K := K) (p := p) (f := f) hn) := by
  rintro g L ⟨i, hi⟩
  exact ⟨g * i * g⁻¹, hi.conj g⟩

theorem LcU_mem_longRootSetU (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    LcU K p f T ∈ longRootSetU hn :=
  ⟨zEltU K p f T, isLongRootSU2_LcU h2 hn T⟩

theorem coordSetU_eq_sigmaSet (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n) :
    coordSetU K p f n = sigmaSet (fixedSubfield K p f)
      (longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ n)) (signGroupU K p f n) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  ext L
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨LcU_mem_longRootSetU h2 _ T, inSigma_LcU hK hp hn T⟩
  · rintro ⟨⟨i, hi⟩, hS⟩
    obtain ⟨T, rfl⟩ := exists_pair_of_inSigmaU hK hp hi hS
    exact ⟨T, rfl⟩

theorem LcU_injective (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n) :
    Function.Injective (LcU K p f (n := n)) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  intro T T' h
  have h1 := isLongRootSU2_LcU (p := p) (f := f) h2 hn T
  have h1' : IsLongRootSU2 K p f hn (LcU K p f T) (zEltU K p f T') := h ▸ isLongRootSU2_LcU h2 hn T'
  have := h1.involution_unique hK hp h1'
  exact Subtype.ext (zMat_inj h2 (congrArg suMat this))

end SetsU

section GenerationU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem zEltU_ne_one (h2 : (2 : K) ≠ 0) (T : Pair n) : zEltU K p f T ≠ 1 :=
  z_ne_one (mat := suMatHom K p f n) (z := zEltU K p f (n := n)) h2 (fun _ => rfl) T

theorem isUniqueInvolution_LcU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n)
    (T : Pair n) : IsUniqueInvolution (LcU K p f T) (zEltU K p f T) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hL := isLongRootSU2_LcU (p := p) (f := f) h2 hn T
  refine ⟨hL.mem, zEltU_ne_one h2 T, zEltU_mul_self T, fun y hy hy2 => ?_⟩
  by_cases h1 : y = 1
  · exact Or.inl h1
  · exact Or.inr (hL.eq_of_orderOf_eq_two hK hp hy (orderOf_eq_prime (by rwa [pow_two]) h1))

theorem zSet_coordSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 2 ≤ n) :
    zSet (coordSetU K p f n) = Set.range (zEltU K p f (n := n)) := by
  ext z
  constructor
  · rintro ⟨L, ⟨T, rfl⟩, hz⟩
    exact ⟨T, (isUniqueInvolution_LcU hK hp hn T).eq hz⟩
  · rintro ⟨T, rfl⟩
    exact ⟨LcU K p f T, LcU_mem_coordSetU T, isUniqueInvolution_LcU hK hp hn T⟩

theorem closure_range_zEltU (h2 : (2 : K) ≠ 0) :
    Subgroup.closure (Set.range (zEltU K p f (n := n))) = signGroupU K p f n :=
  closure_range_z (mat := suMatHom K p f n) (z := zEltU K p f (n := n)) h2 suMatHom_injective
    (fun x => det_suMat x) (fun _ => rfl)

theorem card_signGroupU (h2 : (2 : K) ≠ 0) (hn : 4 ≤ n) : 8 ≤ Nat.card (signGroupU K p f n) :=
  card_signSubgroup (mat := suMatHom K p f n) (z := zEltU K p f (n := n)) h2 (fun _ => rfl) hn

end GenerationU

section TheFrameU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem toralFrameU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hn : 4 ≤ n) :
    ToralFrame (fixedSubfield K p f) (longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ n))
      (signGroupU K p f n) (coordSetU K p f n) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  exact
    { odd := odd_natCard_fixedSubfield hK hp
      five := by rw [card_fixedSubfield hK]; exact h5
      inv := longRootSetU_conjInvariant _
      elem := fun x hx => signGroupU_sq hx
      eq_sigma := coordSetU_eq_sigmaSet hK hp (by omega)
      gen := by
        rw [zSet_coordSetU hK hp (by omega)]
        exact closure_range_zEltU h2
      card := card_signGroupU h2 hn }

end TheFrameU

end CFSG.ClassicalInvolution.Models
