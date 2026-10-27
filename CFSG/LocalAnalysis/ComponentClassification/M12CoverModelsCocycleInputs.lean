module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsSylow

public section
namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover

@[expose] def fIdx (i j : ℕ) : ℕ := packEntry fTable 1 (64 * i + j)

@[expose] def lam0Idx (j : ℕ) : ℕ := packEntry lam0Table 1 j

@[expose] def lamIdx (j : ℕ) : ℕ := packEntry lamTable 1 j

@[expose] def cocycleCheck : Bool :=
  (List.range 64).all (fun j => fIdx 0 j == 0 && fIdx j 0 == 0) &&
    [8, 61, 54, 59].all fun y => [y, invIdx y].all fun y => (List.range 64).all fun j =>
      (List.range 64).all fun k =>
        (fIdx y j + fIdx (mIdx y j) k) % 2 == (fIdx j k + fIdx y (mIdx j k)) % 2

@[expose] def fixCount (j : ℕ) : ℕ := (List.range 12).countP fun p => dCode j p == p

@[expose] def diagCheck : Bool :=
  (List.range 64).all fun j => mIdx j j != 0 || j == 0 ||
    (fixCount j == 4 && fIdx j j == 0) || (fixCount j == 0 && fIdx j j == 1)

@[expose] def autCheck : Bool :=
  (List.range 64).all (fun i => (List.range 64).all fun j =>
    (lam0Idx i + lam0Idx j + lam0Idx (mIdx i j)) % 2 == (fIdx (bIdx i) (bIdx j) + fIdx i j) % 2 &&
      (lamIdx i + lamIdx j + lamIdx (mIdx i j)) % 2 == (fIdx (bIdx i) (bIdx j) + fIdx i j) % 2) &&
    (List.range 64).all fun j =>
      (lam0Idx j + lam0Idx (bIdx j)) % 2 == 0 && (lamIdx j + lamIdx (bIdx j)) % 2 == 0

end CFSG.ComponentClassification.M12Cover.InternalSylow
