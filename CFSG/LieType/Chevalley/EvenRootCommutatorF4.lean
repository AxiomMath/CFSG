module

public import CFSG.LieType.Chevalley.F4FieldTwoRootPairs

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootOps
open scoped commutatorElement

@[expose] def f4OddCommutatorFactors : List ((ℕ × ℕ) × List (ℕ × ℕ × ℕ)) := [
  ((24, 25), [(1, 1, 26)]), ((24, 26), []), ((24, 27), []), ((24, 28), [(1, 1, 29)]),
  ((24, 29), []), ((24, 30), [(1, 1, 31), (2, 1, 32)]), ((24, 31), []), ((24, 32), []),
  ((24, 33), []), ((24, 34), []), ((24, 35), [(1, 1, 36)]), ((24, 36), []),
  ((24, 37), [(1, 1, 38), (2, 1, 39)]), ((24, 38), []), ((24, 39), []),
  ((24, 40), [(1, 1, 41), (2, 1, 42)]), ((24, 41), []), ((24, 42), []), ((24, 43), [(1, 1, 44)]),
  ((24, 44), []), ((24, 45), []), ((24, 46), []), ((24, 47), []), ((25, 24), [(1, 1, 26)]),
  ((25, 26), []), ((25, 27), [(1, 1, 28), (2, 1, 30)]), ((25, 28), []), ((25, 29), [(1, 1, 31)]),
  ((25, 30), []), ((25, 31), []), ((25, 32), []), ((25, 33), []),
  ((25, 34), [(1, 1, 35), (2, 1, 37)]), ((25, 35), []), ((25, 36), [(1, 1, 38)]), ((25, 37), []),
  ((25, 38), []), ((25, 39), []), ((25, 40), []), ((25, 41), [(1, 1, 43)]),
  ((25, 42), [(1, 1, 44), (2, 1, 45)]), ((25, 43), []), ((25, 44), []), ((25, 45), []),
  ((25, 46), []), ((25, 47), []), ((26, 24), []), ((26, 25), []),
  ((26, 27), [(1, 1, 29), (2, 1, 32)]), ((26, 28), [(1, 1, 31)]), ((26, 29), []), ((26, 30), []),
  ((26, 31), []), ((26, 32), []), ((26, 33), []), ((26, 34), [(1, 1, 36), (2, 1, 39)]),
  ((26, 35), [(1, 1, 38)]), ((26, 36), []), ((26, 37), []), ((26, 38), []), ((26, 39), []),
  ((26, 40), [(1, 1, 43), (2, 1, 45)]), ((26, 41), [(1, 1, 44)]), ((26, 42), []), ((26, 43), []),
  ((26, 44), []), ((26, 45), []), ((26, 46), []), ((26, 47), []), ((27, 24), []),
  ((27, 25), [(1, 1, 28), (1, 2, 30)]), ((27, 26), [(1, 1, 29), (1, 2, 32)]), ((27, 28), []),
  ((27, 29), []), ((27, 30), []), ((27, 31), []), ((27, 32), []), ((27, 33), [(1, 1, 34)]),
  ((27, 34), []), ((27, 35), []), ((27, 36), []), ((27, 37), [(1, 1, 40)]),
  ((27, 38), [(1, 1, 41), (1, 2, 47)]), ((27, 39), [(1, 1, 42)]), ((27, 40), []), ((27, 41), []),
  ((27, 42), []), ((27, 43), []), ((27, 44), []), ((27, 45), [(1, 1, 46)]), ((27, 46), []),
  ((27, 47), []), ((28, 24), [(1, 1, 29)]), ((28, 25), []), ((28, 26), [(1, 1, 31)]),
  ((28, 27), []), ((28, 29), []), ((28, 30), []), ((28, 31), []), ((28, 32), []),
  ((28, 33), [(1, 1, 35), (2, 1, 40)]), ((28, 34), []), ((28, 35), []), ((28, 36), [(1, 1, 41)]),
  ((28, 37), []), ((28, 38), [(1, 1, 43)]), ((28, 39), [(1, 1, 44), (2, 1, 46)]), ((28, 40), []),
  ((28, 41), []), ((28, 42), []), ((28, 43), []), ((28, 44), []), ((28, 45), []), ((28, 46), []),
  ((28, 47), []), ((29, 24), []), ((29, 25), [(1, 1, 31)]), ((29, 26), []), ((29, 27), []),
  ((29, 28), []), ((29, 30), []), ((29, 31), []), ((29, 32), []),
  ((29, 33), [(1, 1, 36), (2, 1, 42)]), ((29, 34), []), ((29, 35), [(1, 1, 41)]), ((29, 36), []),
  ((29, 37), [(1, 1, 43), (2, 1, 46)]), ((29, 38), [(1, 1, 44)]), ((29, 39), []), ((29, 40), []),
  ((29, 41), []), ((29, 42), []), ((29, 43), []), ((29, 44), []), ((29, 45), []), ((29, 46), []),
  ((29, 47), []), ((30, 24), [(1, 1, 31), (1, 2, 32)]), ((30, 25), []), ((30, 26), []),
  ((30, 27), []), ((30, 28), []), ((30, 29), []), ((30, 31), []), ((30, 32), []),
  ((30, 33), [(1, 1, 37)]), ((30, 34), [(1, 1, 40)]), ((30, 35), []),
  ((30, 36), [(1, 1, 43), (1, 2, 47)]), ((30, 37), []), ((30, 38), []), ((30, 39), [(1, 1, 45)]),
  ((30, 40), []), ((30, 41), []), ((30, 42), [(1, 1, 46)]), ((30, 43), []), ((30, 44), []),
  ((30, 45), []), ((30, 46), []), ((30, 47), []), ((31, 24), []), ((31, 25), []), ((31, 26), []),
  ((31, 27), []), ((31, 28), []), ((31, 29), []), ((31, 30), []), ((31, 32), []),
  ((31, 33), [(1, 1, 38), (2, 1, 45)]), ((31, 34), [(1, 1, 41), (2, 1, 46)]),
  ((31, 35), [(1, 1, 43)]), ((31, 36), [(1, 1, 44)]), ((31, 37), []), ((31, 38), []),
  ((31, 39), []), ((31, 40), []), ((31, 41), []), ((31, 42), []), ((31, 43), []), ((31, 44), []),
  ((31, 45), []), ((31, 46), []), ((31, 47), []), ((32, 24), []), ((32, 25), []), ((32, 26), []),
  ((32, 27), []), ((32, 28), []), ((32, 29), []), ((32, 30), []), ((32, 31), []),
  ((32, 33), [(1, 1, 39)]), ((32, 34), [(1, 1, 42)]), ((32, 35), [(1, 1, 44), (1, 2, 47)]),
  ((32, 36), []), ((32, 37), [(1, 1, 45)]), ((32, 38), []), ((32, 39), []),
  ((32, 40), [(1, 1, 46)]), ((32, 41), []), ((32, 42), []), ((32, 43), []), ((32, 44), []),
  ((32, 45), []), ((32, 46), []), ((32, 47), []), ((33, 24), []), ((33, 25), []), ((33, 26), []),
  ((33, 27), [(1, 1, 34)]), ((33, 28), [(1, 1, 35), (1, 2, 40)]),
  ((33, 29), [(1, 1, 36), (1, 2, 42)]), ((33, 30), [(1, 1, 37)]),
  ((33, 31), [(1, 1, 38), (1, 2, 45)]), ((33, 32), [(1, 1, 39)]), ((33, 34), []), ((33, 35), []),
  ((33, 36), []), ((33, 37), []), ((33, 38), []), ((33, 39), []), ((33, 40), []), ((33, 41), []),
  ((33, 42), []), ((33, 43), []), ((33, 44), []), ((33, 45), []), ((33, 46), [(1, 1, 47)]),
  ((33, 47), []), ((34, 24), []), ((34, 25), [(1, 1, 35), (1, 2, 37)]),
  ((34, 26), [(1, 1, 36), (1, 2, 39)]), ((34, 27), []), ((34, 28), []), ((34, 29), []),
  ((34, 30), [(1, 1, 40)]), ((34, 31), [(1, 1, 41), (1, 2, 46)]), ((34, 32), [(1, 1, 42)]),
  ((34, 33), []), ((34, 35), []), ((34, 36), []), ((34, 37), []), ((34, 38), []), ((34, 39), []),
  ((34, 40), []), ((34, 41), []), ((34, 42), []), ((34, 43), []), ((34, 44), []),
  ((34, 45), [(1, 1, 47)]), ((34, 46), []), ((34, 47), []), ((35, 24), [(1, 1, 36)]),
  ((35, 25), []), ((35, 26), [(1, 1, 38)]), ((35, 27), []), ((35, 28), []),
  ((35, 29), [(1, 1, 41)]), ((35, 30), []), ((35, 31), [(1, 1, 43)]),
  ((35, 32), [(1, 1, 44), (2, 1, 47)]), ((35, 33), []), ((35, 34), []), ((35, 36), []),
  ((35, 37), []), ((35, 38), []), ((35, 39), []), ((35, 40), []), ((35, 41), []), ((35, 42), []),
  ((35, 43), []), ((35, 44), []), ((35, 45), []), ((35, 46), []), ((35, 47), []), ((36, 24), []),
  ((36, 25), [(1, 1, 38)]), ((36, 26), []), ((36, 27), []), ((36, 28), [(1, 1, 41)]),
  ((36, 29), []), ((36, 30), [(1, 1, 43), (2, 1, 47)]), ((36, 31), [(1, 1, 44)]), ((36, 32), []),
  ((36, 33), []), ((36, 34), []), ((36, 35), []), ((36, 37), []), ((36, 38), []), ((36, 39), []),
  ((36, 40), []), ((36, 41), []), ((36, 42), []), ((36, 43), []), ((36, 44), []), ((36, 45), []),
  ((36, 46), []), ((36, 47), []), ((37, 24), [(1, 1, 38), (1, 2, 39)]), ((37, 25), []),
  ((37, 26), []), ((37, 27), [(1, 1, 40)]), ((37, 28), []), ((37, 29), [(1, 1, 43), (1, 2, 46)]),
  ((37, 30), []), ((37, 31), []), ((37, 32), [(1, 1, 45)]), ((37, 33), []), ((37, 34), []),
  ((37, 35), []), ((37, 36), []), ((37, 38), []), ((37, 39), []), ((37, 40), []), ((37, 41), []),
  ((37, 42), [(1, 1, 47)]), ((37, 43), []), ((37, 44), []), ((37, 45), []), ((37, 46), []),
  ((37, 47), []), ((38, 24), []), ((38, 25), []), ((38, 26), []),
  ((38, 27), [(1, 1, 41), (2, 1, 47)]), ((38, 28), [(1, 1, 43)]), ((38, 29), [(1, 1, 44)]),
  ((38, 30), []), ((38, 31), []), ((38, 32), []), ((38, 33), []), ((38, 34), []), ((38, 35), []),
  ((38, 36), []), ((38, 37), []), ((38, 39), []), ((38, 40), []), ((38, 41), []), ((38, 42), []),
  ((38, 43), []), ((38, 44), []), ((38, 45), []), ((38, 46), []), ((38, 47), []), ((39, 24), []),
  ((39, 25), []), ((39, 26), []), ((39, 27), [(1, 1, 42)]), ((39, 28), [(1, 1, 44), (1, 2, 46)]),
  ((39, 29), []), ((39, 30), [(1, 1, 45)]), ((39, 31), []), ((39, 32), []), ((39, 33), []),
  ((39, 34), []), ((39, 35), []), ((39, 36), []), ((39, 37), []), ((39, 38), []),
  ((39, 40), [(1, 1, 47)]), ((39, 41), []), ((39, 42), []), ((39, 43), []), ((39, 44), []),
  ((39, 45), []), ((39, 46), []), ((39, 47), []), ((40, 24), [(1, 1, 41), (1, 2, 42)]),
  ((40, 25), []), ((40, 26), [(1, 1, 43), (1, 2, 45)]), ((40, 27), []), ((40, 28), []),
  ((40, 29), []), ((40, 30), []), ((40, 31), []), ((40, 32), [(1, 1, 46)]), ((40, 33), []),
  ((40, 34), []), ((40, 35), []), ((40, 36), []), ((40, 37), []), ((40, 38), []),
  ((40, 39), [(1, 1, 47)]), ((40, 41), []), ((40, 42), []), ((40, 43), []), ((40, 44), []),
  ((40, 45), []), ((40, 46), []), ((40, 47), []), ((41, 24), []), ((41, 25), [(1, 1, 43)]),
  ((41, 26), [(1, 1, 44)]), ((41, 27), []), ((41, 28), []), ((41, 29), []), ((41, 30), []),
  ((41, 31), []), ((41, 32), []), ((41, 33), []), ((41, 34), []), ((41, 35), []), ((41, 36), []),
  ((41, 37), []), ((41, 38), []), ((41, 39), []), ((41, 40), []), ((41, 42), []), ((41, 43), []),
  ((41, 44), []), ((41, 45), []), ((41, 46), []), ((41, 47), []), ((42, 24), []),
  ((42, 25), [(1, 1, 44), (1, 2, 45)]), ((42, 26), []), ((42, 27), []), ((42, 28), []),
  ((42, 29), []), ((42, 30), [(1, 1, 46)]), ((42, 31), []), ((42, 32), []), ((42, 33), []),
  ((42, 34), []), ((42, 35), []), ((42, 36), []), ((42, 37), [(1, 1, 47)]), ((42, 38), []),
  ((42, 39), []), ((42, 40), []), ((42, 41), []), ((42, 43), []), ((42, 44), []), ((42, 45), []),
  ((42, 46), []), ((42, 47), []), ((43, 24), [(1, 1, 44)]), ((43, 25), []), ((43, 26), []),
  ((43, 27), []), ((43, 28), []), ((43, 29), []), ((43, 30), []), ((43, 31), []), ((43, 32), []),
  ((43, 33), []), ((43, 34), []), ((43, 35), []), ((43, 36), []), ((43, 37), []), ((43, 38), []),
  ((43, 39), []), ((43, 40), []), ((43, 41), []), ((43, 42), []), ((43, 44), []), ((43, 45), []),
  ((43, 46), []), ((43, 47), []), ((44, 24), []), ((44, 25), []), ((44, 26), []), ((44, 27), []),
  ((44, 28), []), ((44, 29), []), ((44, 30), []), ((44, 31), []), ((44, 32), []), ((44, 33), []),
  ((44, 34), []), ((44, 35), []), ((44, 36), []), ((44, 37), []), ((44, 38), []), ((44, 39), []),
  ((44, 40), []), ((44, 41), []), ((44, 42), []), ((44, 43), []), ((44, 45), []), ((44, 46), []),
  ((44, 47), []), ((45, 24), []), ((45, 25), []), ((45, 26), []), ((45, 27), [(1, 1, 46)]),
  ((45, 28), []), ((45, 29), []), ((45, 30), []), ((45, 31), []), ((45, 32), []), ((45, 33), []),
  ((45, 34), [(1, 1, 47)]), ((45, 35), []), ((45, 36), []), ((45, 37), []), ((45, 38), []),
  ((45, 39), []), ((45, 40), []), ((45, 41), []), ((45, 42), []), ((45, 43), []), ((45, 44), []),
  ((45, 46), []), ((45, 47), []), ((46, 24), []), ((46, 25), []), ((46, 26), []), ((46, 27), []),
  ((46, 28), []), ((46, 29), []), ((46, 30), []), ((46, 31), []), ((46, 32), []),
  ((46, 33), [(1, 1, 47)]), ((46, 34), []), ((46, 35), []), ((46, 36), []), ((46, 37), []),
  ((46, 38), []), ((46, 39), []), ((46, 40), []), ((46, 41), []), ((46, 42), []), ((46, 43), []),
  ((46, 44), []), ((46, 45), []), ((46, 47), []), ((47, 24), []), ((47, 25), []), ((47, 26), []),
  ((47, 27), []), ((47, 28), []), ((47, 29), []), ((47, 30), []), ((47, 31), []), ((47, 32), []),
  ((47, 33), []), ((47, 34), []), ((47, 35), []), ((47, 36), []), ((47, 37), []), ((47, 38), []),
  ((47, 39), []), ((47, 40), []), ((47, 41), []), ((47, 42), []), ((47, 43), []), ((47, 44), []),
  ((47, 45), []), ((47, 46), [])]

@[expose] def f4VecEq (u v : Fin Tag.F4.rank → ℤ) : Bool :=
  List.ofFn u == List.ofFn v

@[expose] def f4OddEntryOK (i j : ℕ) (l : List (ℕ × ℕ × ℕ)) : Bool :=
  l.all (fun f => f4VecEq (orbitCertRoot .F4 f.2.2)
      (f.1 • orbitCertRoot .F4 i + f.2.1 • orbitCertRoot .F4 j) &&
    Nat.ble 24 f.2.2 && Nat.ble f.2.2 47) &&
  (if f4Euclid (orbitCertRoot .F4 i) ⬝ᵥ f4Euclid (orbitCertRoot .F4 i) =
      f4Euclid (orbitCertRoot .F4 j) ⬝ᵥ f4Euclid (orbitCertRoot .F4 j) ∧
      2 * (f4Euclid (orbitCertRoot .F4 i) ⬝ᵥ f4Euclid (orbitCertRoot .F4 j)) =
        -(f4Euclid (orbitCertRoot .F4 i) ⬝ᵥ f4Euclid (orbitCertRoot .F4 i)) then
    l.map (fun f => (f.1, f.2.1)) == [(1, 1)]
  else if f4Euclid (orbitCertRoot .F4 i) ⬝ᵥ f4Euclid (orbitCertRoot .F4 i) = 2 ∧
      f4Euclid (orbitCertRoot .F4 j) ⬝ᵥ f4Euclid (orbitCertRoot .F4 j) = 1 ∧
      f4Euclid (orbitCertRoot .F4 i) ⬝ᵥ f4Euclid (orbitCertRoot .F4 j) = -1 then
    l.map (fun f => (f.1, f.2.1)) == [(1, 1), (1, 2)]
  else if f4Euclid (orbitCertRoot .F4 i) ⬝ᵥ f4Euclid (orbitCertRoot .F4 i) = 1 ∧
      f4Euclid (orbitCertRoot .F4 j) ⬝ᵥ f4Euclid (orbitCertRoot .F4 j) = 2 ∧
      f4Euclid (orbitCertRoot .F4 i) ⬝ᵥ f4Euclid (orbitCertRoot .F4 j) = -1 then
    l.map (fun f => (f.1, f.2.1)) == [(1, 1), (2, 1)]
  else l.isEmpty)

@[expose] def f4PosPairs : List (ℕ × ℕ) :=
  (List.range' 24 24).flatMap fun i => ((List.range' 24 24).filter (· != i)).map fun j => (i, j)

@[expose] def f4OddTableCheck : Bool :=
  f4OddCommutatorFactors.map Prod.fst == f4PosPairs &&
    f4OddCommutatorFactors.all fun e => f4OddEntryOK e.1.1 e.1.2 e.2

theorem f4OddTableCheck_eq : f4OddTableCheck = true := by
  decide +kernel

theorem f4PosPairs_length : f4PosPairs.length = 552 := by
  decide +kernel

theorem mem_f4PosPairs {i j : ℕ} :
    (i, j) ∈ f4PosPairs ↔ 24 ≤ i ∧ i ≤ 47 ∧ 24 ≤ j ∧ j ≤ 47 ∧ i ≠ j := by
  simp only [f4PosPairs, List.mem_flatMap, List.mem_range'_1, List.mem_map, List.mem_filter,
    bne_iff_ne, ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i', ⟨hi₁, hi₂⟩, j', ⟨⟨hj₁, hj₂⟩, hne⟩, rfl, rfl⟩
    exact ⟨hi₁, by omega, hj₁, by omega, fun h => hne h.symm⟩
  · rintro ⟨hi₁, hi₂, hj₁, hj₂, hne⟩
    exact ⟨i, ⟨hi₁, by omega⟩, j, ⟨⟨hj₁, by omega⟩, fun h => hne h.symm⟩, rfl, rfl⟩

theorem f4_posRoot_positions : ∀ k : Fin 48, 0 < height (Tag.F4.rootCertificate.root k) →
    ∃ i : Fin 48, 24 ≤ (i : ℕ) ∧
      List.ofFn (orbitCertRoot .F4 i) = List.ofFn (Tag.F4.rootCertificate.root k) := by
  decide +kernel

theorem f4_height_orbitCertRoot_pos : ∀ i : Fin 48, 24 ≤ (i : ℕ) →
    0 < height (orbitCertRoot .F4 i) ∧ i.val < Tag.F4.witnesses.roots.length := by
  decide +kernel

theorem isRoot_pos_iff_f4
    (v : Fin Tag.F4.rank → ℤ) :
    IsRoot .F4 v ∧ 0 < height v ↔ ∃ i, 24 ≤ i ∧ i ≤ 47 ∧ orbitCertRoot .F4 i = v := by
  constructor
  · rintro ⟨hv, hh⟩
    obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hv
    obtain ⟨i, hi, he⟩ := f4_posRoot_positions k hh
    exact ⟨i, hi, by omega, List.ofFn_injective he⟩
  · rintro ⟨i, hi, hi', rfl⟩
    obtain ⟨hh, hlt⟩ := f4_height_orbitCertRoot_pos ⟨i, by omega⟩ hi
    exact ⟨isRoot_decodeVec_witness hlt, hh⟩

theorem f4_exists_commutator_factors_params
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s) (hne : r ≠ s)
    (hne' : r ≠ -s) (x y : R) :
    ∃ F : List (ℕ × ℕ × ℤ),
      ⁅pinnedX .F4 R r x, pinnedX .F4 R s y⁆ =
        (F.map fun f => pinnedX .F4 R (f.1 • r + f.2.1 • s)
          ((f.2.2 : R) * x ^ f.1 * y ^ f.2.1)).prod ∧
      ((f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
          2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r) ∧ F = [(1, 1, -1)]) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1 ∧ F = [(1, 1, 1), (1, 2, 1)]) ∨
        (f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
          f4Euclid r ⬝ᵥ f4Euclid s = -1 ∧ F = [(1, 1, -1), (2, 1, 1)]) ∨
        (¬(f4Euclid r ⬝ᵥ f4Euclid r = f4Euclid s ⬝ᵥ f4Euclid s ∧
            2 * (f4Euclid r ⬝ᵥ f4Euclid s) = -(f4Euclid r ⬝ᵥ f4Euclid r)) ∧
          ¬(f4Euclid r ⬝ᵥ f4Euclid r = 2 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 1 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = -1) ∧
          ¬(f4Euclid r ⬝ᵥ f4Euclid r = 1 ∧ f4Euclid s ⬝ᵥ f4Euclid s = 2 ∧
            f4Euclid r ⬝ᵥ f4Euclid s = -1) ∧
          (F = [] ∨ F = [(1, 1, -2)]))) := by
  obtain ⟨row, hrow, w, hwr, hws, -, hcomm⟩ :=
    exists_pairTable_commutatorElement_of_two_eq_zero hr hs hne hne'
  have eA := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.1)
  have eB := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.2.1) (orbitCertRoot .F4 row.2.1)
  have eC := f4Euclid_smul_dotProduct w (orbitCertRoot .F4 row.1) (orbitCertRoot .F4 row.2.1)
  simp only [hwr, hws] at eA eB eC
  have hcases := f4_pairTable_cases row hrow
  rw [← eA, ← eB, ← eC] at hcases
  refine ⟨row.2.2.2.map fun f => (f.1, f.2.1, f.2.2.2), ?_, hcases⟩
  rw [hcomm R h2 x y, List.map_map]
  rfl

theorem lookup_spec {β : Type*} {l : List ((ℕ × ℕ) × β)} {a : ℕ × ℕ} (h : a ∈ l.map Prod.fst) :
    ∃ b, l.lookup a = some b ∧ (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.lookup_cons]
    by_cases hx : a = x.1
    · subst hx
      exact ⟨x.2, by simp, by simp⟩
    · have h' : a ∈ l.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        exact h.resolve_left hx
      obtain ⟨b, hb, hmem⟩ := ih h'
      refine ⟨b, ?_, List.mem_cons_of_mem _ hmem⟩
      have hne : (a == x.1) = false := by simpa using hx
      rw [hne]
      exact hb

theorem f4_even_positive_root_commutator_table :
    (∀ v : Fin Tag.F4.rank → ℤ,
      IsRoot .F4 v ∧ 0 < height v ↔ ∃ i, 24 ≤ i ∧ i ≤ 47 ∧ orbitCertRoot .F4 i = v) ∧
    f4OddCommutatorFactors.length = 552 ∧
    (∀ i j : ℕ, (i, j) ∈ f4OddCommutatorFactors.map Prod.fst ↔
      24 ≤ i ∧ i ≤ 47 ∧ 24 ≤ j ∧ j ≤ 47 ∧ i ≠ j) ∧
    (∀ e ∈ f4OddCommutatorFactors,
      e.2.Pairwise (fun f g => f.1 + f.2.1 < g.1 + g.2.1 ∨
        (f.1 + f.2.1 = g.1 + g.2.1 ∧ f.1 < g.1)) ∧
      ∀ f ∈ e.2, 24 ≤ f.2.2 ∧ f.2.2 ≤ 47 ∧
        orbitCertRoot .F4 f.2.2 = f.1 • orbitCertRoot .F4 e.1.1 + f.2.1 • orbitCertRoot .F4 e.1.2) ∧
    ∀ (R : Type*) [CommRing R] [CharP R 2] (i j : ℕ), 24 ≤ i → i ≤ 47 → 24 ≤ j → j ≤ 47 →
      i ≠ j → ∀ s t : R,
        ⁅pinnedX .F4 R (orbitCertRoot .F4 i) s, pinnedX .F4 R (orbitCertRoot .F4 j) t⁆ =
          (((f4OddCommutatorFactors.lookup (i, j)).getD []).map fun f =>
            pinnedX .F4 R (orbitCertRoot .F4 f.2.2) (s ^ f.1 * t ^ f.2.1)).prod := by
  have hcheck := f4OddTableCheck_eq
  simp only [f4OddTableCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcheck
  obtain ⟨hkeys, hentries⟩ := hcheck
  have hentry : ∀ e ∈ f4OddCommutatorFactors,
      (∀ f ∈ e.2, 24 ≤ f.2.2 ∧ f.2.2 ≤ 47 ∧
        orbitCertRoot .F4 f.2.2 = f.1 • orbitCertRoot .F4 e.1.1 + f.2.1 • orbitCertRoot .F4 e.1.2) ∧
      (e.2.map (fun f => (f.1, f.2.1)) = [] ∨ e.2.map (fun f => (f.1, f.2.1)) = [(1, 1)] ∨
        e.2.map (fun f => (f.1, f.2.1)) = [(1, 1), (1, 2)] ∨
        e.2.map (fun f => (f.1, f.2.1)) = [(1, 1), (2, 1)]) := by
    intro e he
    have h := hentries e he
    simp only [f4OddEntryOK, Bool.and_eq_true, List.all_eq_true, f4VecEq, beq_iff_eq,
      Nat.ble_eq] at h
    refine ⟨fun f hf => ?_, ?_⟩
    · obtain ⟨⟨hv, h1⟩, h2⟩ := h.1 f hf
      exact ⟨h1, h2, List.ofFn_injective hv⟩
    · have h2 := h.2
      split_ifs at h2 with c1 c2 c3
      · exact Or.inr (Or.inl (by simpa using h2))
      · exact Or.inr (Or.inr (Or.inl (by simpa using h2)))
      · exact Or.inr (Or.inr (Or.inr (by simpa using h2)))
      · left
        simpa using h2
  refine ⟨isRoot_pos_iff_f4, by rw [← List.length_map, hkeys, f4PosPairs_length],
    fun i j => by rw [hkeys, mem_f4PosPairs], fun e he => ⟨?_, (hentry e he).1⟩, ?_⟩
  · rw [← List.pairwise_map (f := fun f : ℕ × ℕ × ℕ => (f.1, f.2.1))
      (R := fun f g => f.1 + f.2 < g.1 + g.2 ∨ (f.1 + f.2 = g.1 + g.2 ∧ f.1 < g.1))]
    rcases (hentry e he).2 with h | h | h | h <;> rw [h] <;> decide
  · intro R _ _ i j hi hi' hj hj' hij s t
    have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    have hneg : ∀ c : R, -c = c := CharTwo.neg_eq
    obtain ⟨l, hl, hmem⟩ := lookup_spec (l := f4OddCommutatorFactors) (a := (i, j))
      (by rw [hkeys, mem_f4PosPairs]; exact ⟨hi, hi', hj, hj', hij⟩)
    rw [hl, Option.getD_some]
    have hok := hentries _ hmem
    obtain ⟨hroots, -⟩ := hentry _ hmem
    simp only at hroots
    obtain ⟨hhi, hlti⟩ := f4_height_orbitCertRoot_pos ⟨i, by omega⟩ hi
    obtain ⟨hhj, hltj⟩ := f4_height_orbitCertRoot_pos ⟨j, by omega⟩ hj
    replace hhi : 0 < height (orbitCertRoot .F4 i) := hhi
    replace hhj : 0 < height (orbitCertRoot .F4 j) := hhj
    replace hlti : i < Tag.F4.witnesses.roots.length := hlti
    replace hltj : j < Tag.F4.witnesses.roots.length := hltj
    have hri : IsRoot .F4 (orbitCertRoot .F4 i) := isRoot_decodeVec_witness hlti
    have hrj : IsRoot .F4 (orbitCertRoot .F4 j) := isRoot_decodeVec_witness hltj
    have hne : orbitCertRoot .F4 i ≠ orbitCertRoot .F4 j := fun h =>
      hij (RootOps.orbitCertRoot_injOn hlti hltj h)
    have hne' : orbitCertRoot .F4 i ≠ -orbitCertRoot .F4 j := fun h => by
      have := congrArg height h
      rw [height_neg] at this
      omega
    obtain ⟨F, hF, hcases⟩ := f4_exists_commutator_factors_params h2 hri hrj hne hne' s t
    have hrhs :
        (l.map fun f => pinnedX .F4 R (orbitCertRoot .F4 f.2.2) (s ^ f.1 * t ^ f.2.1)).prod =
          ((l.map fun f => (f.1, f.2.1)).map fun ab => pinnedX .F4 R
            (ab.1 • orbitCertRoot .F4 i + ab.2 • orbitCertRoot .F4 j)
              (s ^ ab.1 * t ^ ab.2)).prod := by
      rw [List.map_map]
      exact congrArg List.prod (List.map_congr_left fun f hf => by
        simp only [Function.comp_apply, (hroots f hf).2.2])
    rw [hrhs, hF]
    simp only [f4OddEntryOK, Bool.and_eq_true] at hok
    have hpat := hok.2
    rcases hcases with ⟨c1, c2, rfl⟩ | ⟨c1, c2, c3, rfl⟩ | ⟨c1, c2, c3, rfl⟩ | ⟨n1, n2, n3, hF0⟩
    · rw [ite_eq_left ⟨c1, c2⟩] at hpat
      rw [show l.map (fun f => (f.1, f.2.1)) = [(1, 1)] by simpa using hpat]
      simp [hneg]
    · rw [ite_eq_right (fun h => by rw [c1, c2] at h; norm_num at h),
        ite_eq_left ⟨c1, c2, c3⟩] at hpat
      rw [show l.map (fun f => (f.1, f.2.1)) = [(1, 1), (1, 2)] by simpa using hpat]
      simp
    · rw [ite_eq_right (fun h => by rw [c1, c2] at h; norm_num at h),
        ite_eq_right (fun h => by rw [c1] at h; norm_num at h), ite_eq_left ⟨c1, c2, c3⟩] at hpat
      rw [show l.map (fun f => (f.1, f.2.1)) = [(1, 1), (2, 1)] by simpa using hpat]
      simp [hneg]
    · rw [ite_eq_right n1, ite_eq_right n2, ite_eq_right n3] at hpat
      rw [show l.map (fun f => (f.1, f.2.1)) = [] by simpa using hpat]
      rcases hF0 with rfl | rfl
      · rfl
      · simp [h2, pinnedX_zero]

end CFSG.LieType.Chevalley
