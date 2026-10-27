module

public import CFSG.LieType.Chevalley.RootCommutatorOrbitData
public import CFSG.LieType.Chevalley.RootCommutatorOrbitDataE7
public import CFSG.LieType.Chevalley.RootCommutatorOrbitDataE8
public import CFSG.LieType.Chevalley.AllRootWeylSignsDefs

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

@[expose] def pairLabels : Tag → List (List ℕ)
  | .G2 => g2PairLabels
  | .F4 => f4PairLabels
  | .D4 => d4PairLabels
  | .E6 => e6PairLabels
  | .E7 => e7PairLabels
  | .E8 => e8PairLabels

@[expose] def negPos : Tag → List ℕ
  | .G2 => g2NegPos
  | .F4 => f4NegPos
  | .D4 => d4NegPos
  | .E6 => e6NegPos
  | .E7 => e7NegPos
  | .E8 => e8NegPos

@[expose] def pairTable : Tag → List PairRow
  | .G2 => g2PairTable
  | .F4 => f4PairTable
  | .D4 => d4PairTable
  | .E6 => e6PairTable
  | .E7 => e7PairTable
  | .E8 => e8PairTable

@[expose] def orbitCertRoot (τ : Tag) (b : ℕ) : Fin τ.rank → ℤ :=
  decodeVec (τ.witnesses.roots.getD b 0)

@[expose] def pairLab (τ : Tag) (m n : ℕ) : ℕ :=
  (((pairLabels τ).getD m []).getD (n / 16) 0 >>> (4 * (n % 16))) &&& 15

@[expose] def closureCheck (τ : Tag) (i : Fin τ.rank) (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun m =>
    (List.range τ.rootCertificate.roots.length).all fun n =>
      pairLab τ (imgPar τ i m / 2) (imgPar τ i n / 2) == pairLab τ m n

@[expose] def closureCheckAll (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun i => closureCheck τ i 0 τ.rootCertificate.roots.length

@[expose] def negCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun m =>
    Nat.blt ((negPos τ).getD m 0) τ.rootCertificate.roots.length &&
      CFSG.LieType.Ree.vecBEq (τ.rootCertificate.root ((negPos τ).getD m 0))
        (-τ.rootCertificate.root m) &&
      Nat.ble (repsOf τ).length (pairLab τ m m) &&
      Nat.ble (repsOf τ).length (pairLab τ m ((negPos τ).getD m 0))

@[expose] def convertRow
    (τ : Tag) (x : ℕ × ℕ × List Factor) :
    ℕ × ℕ × List (ℕ × ℕ × ℕ × ℤ) :=
  (certWitnessPos τ x.1, certWitnessPos τ x.2.1, x.2.2.map fun f =>
    (f.1, f.2.1, certWitnessPos τ f.2.2.1,
      pinnedSignW τ (certWitnessPos τ f.2.2.1) * pinnedSignW τ (certWitnessPos τ x.1) ^ f.1 *
        pinnedSignW τ (certWitnessPos τ x.2.1) ^ f.2.1 * f.2.2.2))

@[expose] def tableCheck
    (τ : Tag) : Bool :=
  (pairTable τ).map (fun r => (r.1, r.2.1, r.2.2.2)) == (repsOf τ).map (convertRow τ) &&
    (repsOf τ).map (fun x => pairLab τ x.1 x.2.1) == List.range (repsOf τ).length &&
    (pairTable τ).all (fun r => r.2.2.2.all fun f =>
      Nat.ble 1 f.2.2.2.natAbs && Nat.ble f.2.2.2.natAbs 3) &&
    decide τ.witnesses.roots.Nodup

@[expose] def labPairs (τ : Tag) (l : ℕ) : List (ℕ × ℕ) :=
  (List.range τ.rootCertificate.roots.length ×ˢ List.range τ.rootCertificate.roots.length).filter
    fun mn => pairLab τ mn.1 mn.2 == l

@[expose] def countLab (τ : Tag) (l : ℕ) : ℕ :=
  ((List.range τ.rootCertificate.roots.length).map fun m =>
    ((List.range τ.rootCertificate.roots.length).filter fun n => pairLab τ m n == l).length).sum

@[expose] def sizeCheck (τ : Tag) (r : ℕ) : Bool :=
  ((pairTable τ).getD r (0, 0, 0, [])).2.2.1 == countLab τ r

@[expose] def ClosureOK (τ : Tag) : Prop :=
  ∀ (i : Fin τ.rank) (m n : ℕ), m < τ.rootCertificate.roots.length →
    n < τ.rootCertificate.roots.length →
      pairLab τ (imgPar τ i m / 2) (imgPar τ i n / 2) = pairLab τ m n

@[expose] def SizesOK (τ : Tag) : Prop :=
  ∀ r < (pairTable τ).length, sizeCheck τ r = true

variable {τ : Tag}

theorem closureCheck_spec {i : Fin τ.rank} {lo hi : ℕ} (h : closureCheck τ i lo hi = true)
    {m n : ℕ} (hm : lo ≤ m) (hm' : m < hi) (hn : n < τ.rootCertificate.roots.length) :
    pairLab τ (imgPar τ i m / 2) (imgPar τ i n / 2) = pairLab τ m n := by
  simp only [closureCheck, List.all_eq_true, List.mem_range'_1, List.mem_range, beq_iff_eq] at h
  exact h m ⟨hm, by omega⟩ n hn

theorem closureOK_of_closureCheckAll (h : closureCheckAll τ = true) : ClosureOK τ := by
  intro i m n hm hn
  simp only [closureCheckAll, List.all_eq_true, List.mem_finRange, true_implies] at h
  exact closureCheck_spec (h i) (Nat.zero_le m) hm hn

theorem sizesOK_of_all (h : (List.range (pairTable τ).length).all (sizeCheck τ) = true) :
    SizesOK τ := by
  intro r hr
  simp only [List.all_eq_true, List.mem_range] at h
  exact h r hr

end CFSG.LieType.Chevalley.RootOps
