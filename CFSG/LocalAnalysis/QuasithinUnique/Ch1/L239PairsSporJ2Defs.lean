module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporBFS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import CFSG.Sporadic.Schreier.Enumeration
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public meta import CFSG.Sporadic.Schreier.Enumeration
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Certificate10019
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Th.F2Spec
public meta import Mathlib.Data.Nat.Digits.Lemmas
public meta import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs

open CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open scoped Pointwise

abbrev PermArrOK (t r : Array ℕ) : Prop :=
  ∀ i : Fin 315, t[i.val]! < 315 ∧ r[i.val]! < 315 ∧ r[t[i.val]!]! = i.val ∧
    t[r[i.val]!]! = i.val

@[expose] def invArr (t : Array ℕ) : Array ℕ :=
  ((List.range 315).map fun j => t.toList.findIdx (· == j)).toArray

@[expose] def permC (t r : Array ℕ) (h : PermArrOK t r) : Equiv.Perm (Fin 315) where
  toFun i := ⟨t[i.val]!, (h i).1⟩
  invFun i := ⟨r[i.val]!, (h i).2.1⟩
  left_inv i := Fin.ext (h i).2.2.1
  right_inv i := Fin.ext (h i).2.2.2

theorem permC_eq {t r : Array ℕ} {σ : Equiv.Perm (Fin 315)} (ht : CFSG.Monster.B.Co2.Rep 315 t σ)
    (h : PermArrOK t r) : permC t r h = σ :=
  Equiv.ext fun i => Fin.ext (ht i)

theorem permAc_ok : PermArrOK autStrong[0]! (invArr autStrong[0]!) := by
  decide +kernel

theorem permBc_ok : PermArrOK autStrong[1]! (invArr autStrong[1]!) := by
  decide +kernel

@[expose] def permAc : Equiv.Perm (Fin 315) :=
  permC autStrong[0]! (invArr autStrong[0]!) permAc_ok

@[expose] def permBc : Equiv.Perm (Fin 315) :=
  permC autStrong[1]! (invArr autStrong[1]!) permBc_ok

theorem permAc_eq : permAc = permA :=
  permC_eq (rep_strong (j := 0) (by norm_num)) permAc_ok

theorem permBc_eq : permBc = permB :=
  permC_eq (rep_strong (j := 1) (by norm_num)) permBc_ok

@[expose] def PC : Subgroup (Equiv.Perm (Fin 315)) := Subgroup.closure {permAc, permBc}

theorem PC_eq : PC = P := by
  rw [PC, permAc_eq, permBc_eq]
  rfl

theorem card_PC : Nat.card PC = 604800 := by
  have h := card_P
  rw [← PC_eq] at h
  exact h

abbrev XJ : Type := ↥PC

theorem permAc_mem : permAc ∈ PC := Subgroup.subset_closure (Set.mem_insert _ _)

theorem permBc_mem : permBc ∈ PC := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def paC : XJ := ⟨permAc, permAc_mem⟩

@[expose] def pbC : XJ := ⟨permBc, permBc_mem⟩

theorem closure_paC_pbC : Subgroup.closure ({paC, pbC} : Set XJ) = ⊤ :=
  CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl permAc_mem permBc_mem

@[expose] def enc (x : XJ) : ℕ := encPerm x.1

@[expose] def hkey (x : XJ) : ℕ := enc x % 2305843009213693951

theorem enc_injective : Function.Injective enc := fun x y h =>
  Subtype.ext (encPerm_injective (by norm_num) h)

@[expose] def tabX (x : XJ) : XJ := ⟨tab x.1, by rw [tab_eq]; exact x.2⟩

theorem tabX_eq (x : XJ) : tabX x = x := Subtype.ext (tab_eq x.1)

@[expose] def evalW {G : Type*} [Group G] (S : List G) : List ℤ → G
  | [] => 1
  | z :: w =>
    (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) * evalW S w

@[expose] def genX (w : List ℤ) : XJ := tabX (evalW [paC, pbC] w)

theorem evalW_mem {G : Type*} [Group G] (H : Subgroup G) (S : List G) (hS : ∀ g ∈ S, g ∈ H) :
    ∀ w : List ℤ, evalW S w ∈ H := by
  intro w
  induction w with
  | nil => exact H.one_mem
  | cons z w ih =>
    have hget : ∀ i, S.getD i 1 ∈ H := by
      intro i
      by_cases hi : i < S.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hS _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact H.one_mem
    simp only [evalW]
    refine H.mul_mem ?_ ih
    split_ifs
    · exact hget _
    · exact H.inv_mem (hget _)

theorem arith_index (m : ℕ) (h : 128 * m = 604800) : ¬ 2 ∣ m := by omega

theorem arith_class (n : ℕ) (h : n * 315 ≤ 604800) : n ≤ 1920 := by omega

theorem arith_lines (n : ℕ) (h : n * 525 ≤ 604800) : n ≤ 1152 := by omega

section FixSet

variable {X : Type*} [Group X] {n : ℕ} [MulAction X (Fin n)]

@[expose] def fixSetL (Al : List X) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ a ∈ Al, a • i = i

theorem mem_fixSetL {Al : List X} {i : Fin n} : i ∈ fixSetL Al ↔ ∀ a ∈ Al, a • i = i := by
  simp [fixSetL]

theorem smul_fixSet_eq (A : Subgroup X) (Al : List X) (hA : ∀ y, y ∈ A ↔ y ∈ Al) {x : X}
    (hx : x ∈ Subgroup.normalizer (A : Set X)) : x • fixSetL (n := n) Al = fixSetL Al := by
  classical
  have hxn := Subgroup.mem_normalizer_iff.1 hx
  have hsub : x • fixSetL (n := n) Al ⊆ fixSetL Al := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_smul_finset.1 hj
    rw [mem_fixSetL] at hi ⊢
    intro a ha
    have hmem : x⁻¹ * a * x ∈ Al := by
      rw [← hA, hxn]
      have : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
      rw [this]
      exact (hA a).2 ha
    have h1 := hi _ hmem
    calc a • x • i = x • ((x⁻¹ * a * x) • i) := by simp [mul_smul]
      _ = x • i := by rw [h1]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

end FixSet

@[expose] def maskF (B : Finset (Fin 315)) : ℕ := ∑ i ∈ B, 2 ^ i.val

end CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
