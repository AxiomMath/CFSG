module

public import CFSG.HardMathSupport.U4FF.ClassLocBase
public import CFSG.HardMathSupport.U4FF.ClassLocData
public import CFSG.HardMathSupport.U4FF.ClassComb

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix

@[expose] def fsOf (a b c : Bool) : List FK :=
  (if a then [FK.N] else []) ++ (if b then [FK.W] else []) ++ (if c then [FK.S] else [])

@[expose] def hwOf : FK → ℕ
  | .N => 0
  | .W => 0
  | .S => 3

theorem hwOf_lt (K : FK) : hwOf K < K.dim := by cases K <;> decide

@[expose] def hwIdx (fs : List FK) : AmbIdx fs := fun f => ⟨hwOf (fs.get f), hwOf_lt _⟩

@[expose] def hwEnc (fs : List FK) : ℕ := (ambEq fs (hwIdx fs) : ℕ)

@[expose] def yMasks (fs : List FK) (D : LocData) : ℕ :=
  MCols.apply D.pmcols (1 <<< hwEnc fs)

@[expose] def tabD (fs : List FK) (i j : Fin 4) (r : ℕ) : MCols :=
  MCols.tab (ambDF fs i j r)

@[expose] def zrowOf (n zeta : ℕ) : MCols :=
  Array.ofFn fun x : Fin n => if zeta.testBit (x : ℕ) then 1 else 0

@[expose] def piOf (n : ℕ) (D : LocData) : MCols :=
  MCols.add (MCols.mul D.bcols D.pmcols) (MCols.mul (MCols.col D.z) (zrowOf n D.zeta))

@[expose] def LocValid1 (a b c : Bool) : Prop :=
  (locData a b c).bcols.size = locM a b c ∧
  (locData a b c).pmcols.size = ambDim (fsOf a b c) ∧
  MCols.mul (locData a b c).pmcols (locData a b c).bcols = MCols.one (locM a b c) ∧
  MCols.apply (locData a b c).pmcols (locData a b c).z = 0 ∧
  MCols.mul (zrowOf (ambDim (fsOf a b c)) (locData a b c).zeta) (locData a b c).bcols =
    MCols.zero (locM a b c) ∧
  MCols.apply (piOf (ambDim (fsOf a b c)) (locData a b c)) (locData a b c).z =
    (locData a b c).z ∧
  (∀ i j : Fin 4, i ≠ j → ∀ r ∈ Finset.range ((fsOf a b c).length + 1),
    MCols.mul (piOf (ambDim (fsOf a b c)) (locData a b c))
        (MCols.mul (tabD (fsOf a b c) i j r) (locData a b c).bcols) =
      MCols.mul (tabD (fsOf a b c) i j r) (locData a b c).bcols) ∧
  (∀ i j : Fin 4, i ≠ j → ∀ r ∈ Finset.range ((fsOf a b c).length + 1),
    MCols.apply (tabD (fsOf a b c) i j r) (locData a b c).z =
      if r = 0 then (locData a b c).z else 0) ∧
  MCols.apply (piOf (ambDim (fsOf a b c)) (locData a b c)) (1 <<< hwEnc (fsOf a b c)) =
    1 <<< hwEnc (fsOf a b c) ∧
  (∀ i j : Fin 4, i < j → ∀ r ∈ Finset.range ((fsOf a b c).length + 1), 1 ≤ r →
    MCols.apply (tabD (fsOf a b c) i j r) (1 <<< hwEnc (fsOf a b c)) = 0) ∧
  ∃ i ∈ Finset.range (locM a b c), (yMasks (fsOf a b c) (locData a b c)).testBit i = true

instance (a b c : Bool) : Decidable (LocValid1 a b c) := by
  unfold LocValid1
  infer_instance

@[expose] def elemMasks (fs : List FK) (i j : Fin 4) : MCols :=
  (List.range (fs.length + 1)).foldl (fun acc r => MCols.add acc (tabD fs i j r))
    (MCols.zero (ambDim fs))

@[expose] def locOpMasks (D : LocData) (A : MCols) : MCols :=
  MCols.mul D.pmcols (MCols.mul A D.bcols)

@[expose] def a1Masks (fs : List FK) : MCols :=
  MCols.add (elemMasks fs 0 3) (MCols.one (ambDim fs))

@[expose] def a2Masks (fs : List FK) : MCols :=
  MCols.add (MCols.mul (elemMasks fs 0 2) (elemMasks fs 1 3)) (MCols.one (ambDim fs))

@[expose] def RankOK (m : ℕ) (M : MCols) (R : RankData) : Prop :=
  M.size = m ∧ R.x.size = R.r ∧ R.y.size = m ∧ R.xl.size = m ∧ R.yr.size = R.r ∧
  M = MCols.mul R.x R.y ∧ MCols.mul R.xl (MCols.mul M R.yr) = MCols.one R.r

@[expose] def LocValid2 (a b c : Bool) : Prop :=
  RankOK (locM a b c) (locOpMasks (locData a b c) (a1Masks (fsOf a b c))) (locData a b c).rk1 ∧
  RankOK (locM a b c) (locOpMasks (locData a b c) (a2Masks (fsOf a b c))) (locData a b c).rk2 ∧
  2 * (locData a b c).rk1.r + locF1 a b c = locM a b c ∧
  (locData a b c).rk1.r ≤ (locData a b c).rk2.r ∧
  2 * (locData a b c).rk2.r ≤ locM a b c

instance (a b c : Bool) : Decidable (LocValid2 a b c) := by
  unfold LocValid2 RankOK
  infer_instance

@[expose] def dlocMasks (fs : List FK) (D : LocData) (i j : Fin 4) (r : ℕ) : MCols :=
  MCols.mul D.pmcols (MCols.mul (tabD fs i j r) D.bcols)

@[expose] def LocValid3 (a b c : Bool) : Prop :=
  (locData a b c).pic.size = locM true true true ∧
  (locData a b c).pir.size = locM a b c ∧
  (locData a b c).ioc.size = locM a b c ∧
  (locData a b c).iol.size = locM true true true ∧
  MCols.mul (locData a b c).pic (locData a b c).pir = MCols.one (locM a b c) ∧
  MCols.mul (locData a b c).iol (locData a b c).ioc = MCols.one (locM a b c) ∧
  MCols.apply (locData a b c).pic (yMasks (fsOf true true true) (locData true true true)) =
    yMasks (fsOf a b c) (locData a b c) ∧
  (∀ i j : Fin 4, j < i → ∀ r ∈ Finset.range 4,
    MCols.mul (locData a b c).pic
        (dlocMasks (fsOf true true true) (locData true true true) i j r) =
      MCols.mul (dlocMasks (fsOf a b c) (locData a b c) i j r) (locData a b c).pic ∧
    MCols.mul (locData a b c).ioc (dlocMasks (fsOf a b c) (locData a b c) i j r) =
      MCols.mul (dlocMasks (fsOf true true true) (locData true true true) i j r)
        (locData a b c).ioc)

instance (a b c : Bool) : Decidable (LocValid3 a b c) := by
  unfold LocValid3
  infer_instance

@[expose] def LocValid (a b c : Bool) : Prop := LocValid1 a b c ∧ LocValid2 a b c ∧ LocValid3 a b c

instance (a b c : Bool) : Decidable (LocValid a b c) := by
  unfold LocValid
  infer_instance

end CFSG.HardMathSupport.U4FF
