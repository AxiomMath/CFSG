module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Interface
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.MainFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

variable {minus : Bool}

abbrev CertD (minus : Bool) : GrpData := grpData minus ()

abbrev CertL (minus : Bool) : LData := ldata minus ()

theorem array_getElem!_mem_toList {α : Type*} [Inhabited α] {A : Array α} {i : ℕ}
    (h : i < A.size) : A[i]! ∈ A.toList := by
  rw [array_getElem!_eq_getElem_of_lt h]
  exact Array.getElem_mem_toList h

theorem exists_pos_of_mem {α : Type*} [Inhabited α] {A : Array α} {i : α} (hi : i ∈ A) :
    ∃ x, x < A.size ∧ A[x]! = i := by
  have hi' : i ∈ A.toList := Array.mem_toList_iff.mpr hi
  obtain ⟨x, hx, hxl⟩ := List.mem_iff_getElem.mp hi'
  have hx' : x < A.size := by rw [← Array.length_toList]; exact hx
  refine ⟨x, hx', ?_⟩
  rw [array_getElem!_eq_getElem_of_lt hx']
  rw [← Array.getElem_toList (by simpa [Array.length_toList] using hx)]
  exact hxl

@[expose] def Lam (minus : Bool) (j : ℕ) : Set (V₀ ≃ₗ[ZMod 2] V₀) :=
  {x | InCodeList minus ((CertL minus).Llist[j]!) x}

theorem mem_Lam_iff {j : ℕ} {x : V₀ ≃ₗ[ZMod 2] V₀} :
    x ∈ Lam minus j ↔ InIdx (CertD minus) ((CertL minus).Llist[j]!) x :=
  Iff.rfl

theorem elt_mem_Lam_iff (hD : GrpFacts minus (CertD minus)) {j i : ℕ}
    (hi : i < (CertD minus).O.size) :
    hD.elt i ∈ Lam minus j ↔ i ∈ (CertL minus).Llist[j]! := by
  constructor
  · intro hx
    obtain ⟨m, hm, hm', heq⟩ := hD.inIdx_iff.mp (mem_Lam_iff.mp hx)
    have hmi : m = i := hD.elt_injOn hm' hi heq
    rwa [hmi] at hm
  · intro hx
    exact mem_Lam_iff.mpr (hD.inIdx_iff.mpr ⟨i, hx, hi, rfl⟩)

structure CensusBaseFacts (minus : Bool) : Prop where
  grp : GrpFacts minus (CertD minus)
  trans : transOK (CertD minus) (singOf minus) (b0Of minus)
    (transWitOf (CertD minus) (singOf minus) (b0Of minus)) = true
  lsize : (CertL minus).Llist.size = if minus then 17 else 22
  csize : (candidatesOf minus (CertL minus).Llist).size = if minus then 11 else 20
  lOK : ∀ j, j < (CertL minus).Llist.size →
    lOK (CertD minus) minus (b0Of minus) ((CertL minus).Llist[j]!) = true
  l2OK : l2OK (CertD minus) minus (b0Of minus) (CertL minus).Llist
    (a2FixOf (CertD minus) minus (b0Of minus)) (CertL minus).l2wit = true
  l3Complete : l3Complete (CertD minus) (b0Of minus) (CertL minus).Llist
    (CertL minus).l3tasks = true
  l3OK : l3OK (CertD minus) (b0Of minus) (CertL minus).Llist
    (CertL minus).l3tasks (CertL minus).l3wit = true

theorem censusBaseFacts_of (hb : censusBase minus () = true) : CensusBaseFacts minus := by
  have h := hb
  simp only [censusBase, censusBaseOf, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨-, htrans, hlsize, hcsize, hlOK, hl2, hl3c, hl3⟩ := h
  refine ⟨grpFacts_of_censusBase hb, htrans, hlsize, hcsize, ?_,
    hl2, hl3c, hl3⟩
  intro j hj
  have hall := hlOK
  rw [Array.all_eq_true] at hall
  have hthis := hall j hj
  simpa [array_getElem!_eq_getElem_of_lt hj] using hthis

end CFSG.GF2Type.Smith1979W3.Cert690

end
