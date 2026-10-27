module

public import Mathlib
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public noncomputable section

namespace CFSG.Blueprint.NativeSporadic

@[expose] def asciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

@[expose] def decode (p d mode : ℕ) (s : String) : Matrix (Fin d) (Fin d) (ZMod p) :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  let entries : List ℕ := if mode = 1 then
    (body.filter fun c => !asciiWhitespace c).map fun c =>
      if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0
    else
      ((String.ofList (body.map fun c => if asciiWhitespace c then ' ' else c)).splitOn " ").filter
        (· != "") |>.map fun token => if token.toList.all (fun c => '0' ≤ c && c ≤ '9') then token.toNat?.getD 0 else 0
  fun i j => (entries[i.val * d + j.val]?.getD 0 : ZMod p)

@[expose] def seedMonoid (p d mode : ℕ) (s₁ s₂ : String) :
    Submonoid (Matrix (Fin d) (Fin d) (ZMod p)) :=
  Submonoid.closure {decode p d mode s₁, decode p d mode s₂}

@[expose] def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure {(List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]),
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8])}

@[expose] def M12 : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure {(List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]),
    (List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6])}

@[expose] def M22 : Subgroup (Equiv.Perm (Fin 22)) :=
  Subgroup.closure {(List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]),
    (List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18])}

@[expose] def M23 : Subgroup (Equiv.Perm (Fin 23)) :=
  Subgroup.closure {(List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]),
    (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16])}

@[expose] def M24 : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure {(List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]),
    (List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] * List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22])}

def J1Seed1 : String := include_str "Data"/"J1G1-f11r7B0.m1"
def J1Seed2 : String := include_str "Data"/"J1G1-f11r7B0.m2"
abbrev J1 : Type := (seedMonoid 11 7 3 J1Seed1 J1Seed2)ˣ

def J2Seed1 : String := include_str "Data"/"J2G1-f5r14B0.m1"
def J2Seed2 : String := include_str "Data"/"J2G1-f5r14B0.m2"
abbrev J2 : Type := (seedMonoid 5 14 1 J2Seed1 J2Seed2)ˣ

def J3Seed1 : String := include_str "Data"/"J3G1-f2r80B0.m1"
def J3Seed2 : String := include_str "Data"/"J3G1-f2r80B0.m2"
abbrev J3 : Type := (seedMonoid 2 80 1 J3Seed1 J3Seed2)ˣ

def J4Seed1 : String := include_str "Data"/"J4G1-f2r112B0.m1"
def J4Seed2 : String := include_str "Data"/"J4G1-f2r112B0.m2"
abbrev J4 : Type := (seedMonoid 2 112 1 J4Seed1 J4Seed2)ˣ

def Co1Seed1 : String := include_str "Data"/"Co1G1-f2r24B0.m1"
def Co1Seed2 : String := include_str "Data"/"Co1G1-f2r24B0.m2"
abbrev Co1 : Type := (seedMonoid 2 24 1 Co1Seed1 Co1Seed2)ˣ

def Co2Seed1 : String := include_str "Data"/"Co2G1-f2r22B0.m1"
def Co2Seed2 : String := include_str "Data"/"Co2G1-f2r22B0.m2"
abbrev Co2 : Type := (seedMonoid 2 22 1 Co2Seed1 Co2Seed2)ˣ

def Co3Seed1 : String := include_str "Data"/"Co3G1-f2r22B0.m1"
def Co3Seed2 : String := include_str "Data"/"Co3G1-f2r22B0.m2"
abbrev Co3 : Type := (seedMonoid 2 22 1 Co3Seed1 Co3Seed2)ˣ

def Fi22Seed1 : String := include_str "Data"/"F22G1-f3r77B0.m1"
def Fi22Seed2 : String := include_str "Data"/"F22G1-f3r77B0.m2"
abbrev Fi22 : Type := (seedMonoid 3 77 1 Fi22Seed1 Fi22Seed2)ˣ

def Fi23Seed1 : String := include_str "Data"/"F23G1-f3r253B0.m1"
def Fi23Seed2 : String := include_str "Data"/"F23G1-f3r253B0.m2"
abbrev Fi23 : Type := (seedMonoid 3 253 1 Fi23Seed1 Fi23Seed2)ˣ

def Fi24primeSeed1 : String := include_str "Data"/"F24G1-f3r781B0.m1"
def Fi24primeSeed2 : String := include_str "Data"/"F24G1-f3r781B0.m2"
abbrev Fi24prime : Type := (seedMonoid 3 781 1 Fi24primeSeed1 Fi24primeSeed2)ˣ

def HSSeed1 : String := include_str "Data"/"HSG1-f2r20B0.m1"
def HSSeed2 : String := include_str "Data"/"HSG1-f2r20B0.m2"
abbrev HS : Type := (seedMonoid 2 20 1 HSSeed1 HSSeed2)ˣ

def McLSeed1 : String := include_str "Data"/"McLG1-f3r21B0.m1"
def McLSeed2 : String := include_str "Data"/"McLG1-f3r21B0.m2"
abbrev McL : Type := (seedMonoid 3 21 1 McLSeed1 McLSeed2)ˣ

def HeSeed1 : String := include_str "Data"/"HeG1-f7r50B0.m1"
def HeSeed2 : String := include_str "Data"/"HeG1-f7r50B0.m2"
abbrev He : Type := (seedMonoid 7 50 1 HeSeed1 HeSeed2)ˣ

def RuSeed1 : String := include_str "Data"/"RuG1-f2r28B0.m1"
def RuSeed2 : String := include_str "Data"/"RuG1-f2r28B0.m2"
abbrev Ru : Type := (seedMonoid 2 28 1 RuSeed1 RuSeed2)ˣ

def SuzSeed1 : String := include_str "Data"/"SuzG1-f3r64B0.m1"
def SuzSeed2 : String := include_str "Data"/"SuzG1-f3r64B0.m2"
abbrev Suz : Type := (seedMonoid 3 64 1 SuzSeed1 SuzSeed2)ˣ

def ONSeed1 : String := include_str "Data"/"ONG1-f3r154B0.m1"
def ONSeed2 : String := include_str "Data"/"ONG1-f3r154B0.m2"
abbrev ON : Type := (seedMonoid 3 154 1 ONSeed1 ONSeed2)ˣ

def HNSeed1 : String := include_str "Data"/"HNG1-f5r133B0.m1"
def HNSeed2 : String := include_str "Data"/"HNG1-f5r133B0.m2"
abbrev HN : Type := (seedMonoid 5 133 1 HNSeed1 HNSeed2)ˣ

def LySeed1 : String := include_str "Data"/"LyG1-f5r111B0.m1"
def LySeed2 : String := include_str "Data"/"LyG1-f5r111B0.m2"
abbrev Ly : Type := (seedMonoid 5 111 1 LySeed1 LySeed2)ˣ

def ThSeed1 : String := include_str "Data"/"ThG1-f2r248B0.m1"
def ThSeed2 : String := include_str "Data"/"ThG1-f2r248B0.m2"
abbrev Th : Type := (seedMonoid 2 248 1 ThSeed1 ThSeed2)ˣ

def BSeed1 : String := include_str "Data"/"BG1-f2r4370B0.m1"
def BSeed2 : String := include_str "Data"/"BG1-f2r4370B0.m2"
abbrev B : Type := (seedMonoid 2 4370 1 BSeed1 BSeed2)ˣ

@[expose] def y443Adjacent (i j : Fin 12) : Prop :=
  (i.val = 0 ∧ j.val ∈ ({1, 5, 9} : Set ℕ)) ∨
  (j.val = 0 ∧ i.val ∈ ({1, 5, 9} : Set ℕ)) ∨
  (i.val + 1 = j.val ∧ i.val ∈ ({1, 2, 3, 5, 6, 7, 9, 10} : Set ℕ)) ∨
  (j.val + 1 = i.val ∧ j.val ∈ ({1, 2, 3, 5, 6, 7, 9, 10} : Set ℕ))

@[expose] def y443Relations : Set (FreeGroup (Fin 12)) := by
  classical
  exact {w | ∃ i : Fin 12, w = FreeGroup.of i ^ 2} ∪
  {w | ∃ i j : Fin 12, i.val < j.val ∧
    w = (FreeGroup.of i * FreeGroup.of j) ^ (if y443Adjacent i j then 3 else 2)} ∪
  {(FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 0 *
    FreeGroup.of 5 * FreeGroup.of 6 * FreeGroup.of 0 * FreeGroup.of 9 * FreeGroup.of 10) ^ 10}

abbrev Y443 : Type := PresentedGroup y443Relations

abbrev M : Type := commutator Y443

@[expose] def Carrier : TauCeti.SporadicName → Type
  | .M11 => M11
  | .M12 => M12
  | .M22 => M22
  | .M23 => M23
  | .M24 => M24
  | .J1 => J1
  | .J2 => J2
  | .J3 => J3
  | .J4 => J4
  | .Co1 => Co1
  | .Co2 => Co2
  | .Co3 => Co3
  | .Fi22 => Fi22
  | .Fi23 => Fi23
  | .Fi24Prime => Fi24prime
  | .HS => HS
  | .McL => McL
  | .He => He
  | .Ru => Ru
  | .Suz => Suz
  | .ONan => ON
  | .HN => HN
  | .Ly => Ly
  | .Th => Th
  | .B => B
  | .M => M

instance carrierGroup (s : TauCeti.SporadicName) : Group (Carrier s) := by
  cases s <;> dsimp [Carrier] <;> infer_instance

@[expose] def SporadicRep (G : Type) [Group G] : Prop :=
  ∃ s : TauCeti.SporadicName, Nonempty (G ≃* Carrier s)

@[expose] def IsSporadic (G : Type) [Group G] (s : TauCeti.SporadicName) : Prop :=
  Nonempty (G ≃* Carrier s)

end CFSG.Blueprint.NativeSporadic
