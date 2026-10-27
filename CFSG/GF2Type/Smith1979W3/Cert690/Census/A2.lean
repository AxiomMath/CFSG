module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Trans
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Good

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.RankThree.OrthogonalInvolutions Module

variable {minus : Bool}

@[expose] def commCode (m v : ℕ) : ℕ := Code.act m v ^^^ v

@[expose] def commCodes (m : ℕ) : List ℕ := (List.range 64).map (commCode m)

theorem commCode_lt (m v : ℕ) (hv : v < 64) : commCode m v < 64 := by
  rw [commCode]
  exact Nat.xor_lt_two_pow (n := 6) (by simpa using Code.act_lt m v) (by omega)

theorem vec_commCode {t : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hcode : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) m) (v : ℕ) :
    Code.vec (commCode m v) = t (Code.vec v) - Code.vec v := by
  rw [commCode, vec_xor, apply_vec_of_hasCode hcode v, CharTwo.sub_eq_add]

theorem qB_commCode_false {t : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hcode : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) m)
    (hvan : ∀ x ∈ commSpace t, qModel minus x = 0) (v : ℕ) :
    qB minus (commCode m v) = false := by
  have hmem : Code.vec (commCode m v) ∈ commSpace t := by
    rw [vec_commCode hcode v]
    exact sub_mem_commSpace t (Code.vec v)
  exact qB_eq_false_of_qModel_eq_zero (hvan _ hmem)

theorem commCodes_all_singular {t : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hcode : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) m)
    (hvan : ∀ x ∈ commSpace t, qModel minus x = 0) :
    (commCodes m).toArray.all (fun x => !(qB minus x)) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < (commCodes m).length := by simpa using hi
  have hiarr : i < (commCodes m).toArray.size := by simpa using hi'
  rw [show (commCodes m).toArray[i] = (commCodes m)[i] from
    List.getElem_toArray hiarr]
  have hmem : (commCodes m)[i] ∈ commCodes m := List.getElem_mem hi'
  obtain ⟨v, hv, hvl⟩ := List.mem_map.mp hmem
  rw [← hvl, qB_commCode_false hcode hvan v]
  rfl

theorem natCard_commSpace_eq_four {t : V₀ ≃ₗ[ZMod 2] V₀}
    (hfr : finrank (ZMod 2) (commSpace t) = 2) :
    Nat.card (commSpace t) = 4 := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2)
    (V := ↥(commSpace t)), ZMod.card, hfr]
  norm_num

theorem hashSet_commCodes {t : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hcode : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) m)
    (hfr : finrank (ZMod 2) (commSpace t) = 2) :
    (hashSetOfArray (commCodes m).toArray).size = 4 := by
  classical
  let S : Finset ℕ := (commCodes m).toFinset
  have h1 : (hashSetOfArray (commCodes m).toArray).size = S.card := by
    rw [hashSetOfArray_size_eq_toFinset_card]
  have hinj : Set.InjOn Code.vec (S : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a < 64 := by
      obtain ⟨v, hv, hva⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      rw [← hva]
      exact commCode_lt m v (List.mem_range.mp hv)
    have hb' : b < 64 := by
      obtain ⟨v, hv, hvb⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
      rw [← hvb]
      exact commCode_lt m v (List.mem_range.mp hv)
    exact vec_injective_of_lt ha' hb' hab
  have hS_eq : (Code.vec '' (S : Set ℕ)) = (commSpace t : Set V₀) := by
    ext y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      obtain ⟨v, _, hxv⟩ := List.mem_map.mp (List.mem_toFinset.mp hxS)
      rw [← hxv, vec_commCode hcode v]
      exact sub_mem_commSpace t (Code.vec v)
    · intro hy
      obtain ⟨x, hx⟩ := mem_commSpace.mp hy
      obtain ⟨v, hv, rfl⟩ := exists_vec x
      refine ⟨commCode m v, ?_, ?_⟩
      · exact List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩)
      · rw [vec_commCode hcode v, hx]
  have hScard : S.card = (S : Set ℕ).ncard := by
    rw [← Fintype.card_coe S, ← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq (S : Set ℕ)
  calc (hashSetOfArray (commCodes m).toArray).size = S.card := h1
    _ = (S : Set ℕ).ncard := hScard
    _ = (Code.vec '' (S : Set ℕ)).ncard := hinj.ncard_image.symm
    _ = (commSpace t : Set V₀).ncard := by rw [hS_eq]
    _ = Nat.card (commSpace t) := (Nat.card_coe_set_eq _).symm
    _ = 4 := natCard_commSpace_eq_four hfr

theorem mem_a2FixOf_iff {b i : ℕ} :
    i ∈ a2FixOf (CertD minus) minus b ↔
      i < (CertD minus).O.size ∧ Code.act (CertD minus).O[i]! b = b ∧
        isA2Of (CertD minus) minus i = true := by
  simp [a2FixOf, Array.mem_toList_iff, List.mem_toArray, List.mem_filter, List.mem_range]

theorem isA2Of_of_isTypeA
    {t : V₀ ≃ₗ[ZMod 2] V₀} {i : ℕ} (hi : i < (CertD minus).O.size)
    (hcode : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) ((CertD minus).O[i]!))
    (hA : IsTypeA (qModel minus) t 2) :
    isA2Of (CertD minus) minus i = true := by
  obtain ⟨_, htne, ht2, hdim, hvan⟩ := hA
  have hne : (CertD minus).O[i]! ≠ Code.one := by
    intro hc
    apply htne
    rw [hc] at hcode
    exact hcode.eq_of_equiv Code.hasCode_one
  have hmul : Code.mul ((CertD minus).O[i]!) ((CertD minus).O[i]!) = Code.one := by
    have h2 : Code.HasCode
        (((t * t : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀))
        (Code.mul ((CertD minus).O[i]!) ((CertD minus).O[i]!)) := hcode.mul hcode
    rw [ht2] at h2
    exact h2.code_eq Code.hasCode_one (Code.mul_lt _ _) Code.one_lt
  have hsize : (hashSetOfArray (commCodes ((CertD minus).O[i]!)).toArray).size = 4 := by
    simpa [commCodes, commCode] using hashSet_commCodes hcode hdim
  have hall : (commCodes ((CertD minus).O[i]!)).toArray.all (fun x => !(qB minus x)) = true :=
    commCodes_all_singular hcode hvan
  simp [isA2Of, hi, hne, hmul, hsize, hall, commCodes, commCode]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [array_getElem!_eq_getElem hi] using hne
  · simpa [array_getElem!_eq_getElem hi] using hmul
  · have hsize' : (hashSetOfArray (commCodes ((CertD minus).O[i])).toArray).size = 4 := by
      rwa [array_getElem!_eq_getElem hi] at hsize
    exact hsize'
  · intro x hx
    have hcode' : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) ((CertD minus).O[i]) := by
      rwa [array_getElem!_eq_getElem hi] at hcode
    exact qB_commCode_false hcode' hvan x

theorem a2FixOf_index (hb : censusBase minus () = true)
    {t : V₀ ≃ₗ[ZMod 2] V₀} {i : ℕ} (hi : i < (CertD minus).O.size)
    (hcode : Code.HasCode (t : V₀ →ₗ[ZMod 2] V₀) ((CertD minus).O[i]!))
    (hfix : t (Code.vec (b0Of minus)) = Code.vec (b0Of minus))
    (hA : IsTypeA (qModel minus) t 2) :
    i ∈ a2FixOf (CertD minus) minus (b0Of minus) := by
  rw [mem_a2FixOf_iff]
  refine ⟨hi, ?_, isA2Of_of_isTypeA hi hcode hA⟩
  have hactvec : Code.vec (Code.act ((CertD minus).O[i]!) (b0Of minus)) =
      Code.vec (b0Of minus) := by
    rw [← apply_vec_of_hasCode hcode (b0Of minus)]
    exact hfix
  exact vec_injective_of_lt (Code.act_lt _ _) (b0Of_lt minus) hactvec

end CFSG.GF2Type.Smith1979W3.Cert690

end