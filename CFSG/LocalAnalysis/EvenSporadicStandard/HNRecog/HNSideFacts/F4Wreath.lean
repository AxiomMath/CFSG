module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Data
public import CFSG.Sporadic.Schreier.ONPermArr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.ONSchreier

@[expose] def pt10 : Fin 10 ≃ Fin 5 × Multiplicative (ZMod 2) where
  toFun i := (⟨i.val % 5, by omega⟩, if i.val < 5 then 1 else Multiplicative.ofAdd 1)
  invFun x := if x.2 = 1 then ⟨x.1.val, by omega⟩ else ⟨x.1.val + 5, by omega⟩
  left_inv := by
    intro i
    revert i
    decide
  right_inv := by
    intro x
    revert x
    decide

noncomputable def a5WrTwoImage : Subgroup (Equiv.Perm (Fin 10)) :=
  (RegularWreathProduct.toPerm (alternatingGroup (Fin 5)) (Multiplicative (ZMod 2))
    (Fin 5)).range.map (Equiv.permCongrHom pt10.symm).toMonoidHom

private def pRev : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 2, 1, 0], ![4, 3, 2, 1, 0], by decide, by decide⟩
private theorem pRev_mem : pRev ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p4A : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 1, 0, 2], ![3, 2, 4, 1, 0], by decide, by decide⟩
private theorem p4A_mem : p4A ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p4B : Equiv.Perm (Fin 5) :=
  ⟨![3, 2, 4, 1, 0], ![4, 3, 1, 0, 2], by decide, by decide⟩
private theorem p4B_mem : p4B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p6A : Equiv.Perm (Fin 5) :=
  ⟨![0, 1, 3, 4, 2], ![0, 1, 4, 2, 3], by decide, by decide⟩
private theorem p6A_mem : p6A ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p6B : Equiv.Perm (Fin 5) :=
  ⟨![2, 0, 1, 3, 4], ![1, 2, 0, 3, 4], by decide, by decide⟩
private theorem p6B_mem : p6B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p7A : Equiv.Perm (Fin 5) :=
  ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide, by decide⟩
private theorem p7A_mem : p7A ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p7B : Equiv.Perm (Fin 5) :=
  ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
private theorem p7B_mem : p7B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p8 : Equiv.Perm (Fin 5) :=
  ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
private theorem p8_mem : p8 ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def p9B : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 0, 2, 1], ![2, 4, 3, 1, 0], by decide, by decide⟩
private theorem p9B_mem : p9B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

private def mkW (A B : Equiv.Perm (Fin 5)) (hA : A ∈ alternatingGroup (Fin 5))
    (hB : B ∈ alternatingGroup (Fin 5)) (s : Bool) : A5WrTwo :=
  if s then ⟨fun q => if q = 1 then ⟨B, hB⟩ else ⟨A, hA⟩, Multiplicative.ofAdd 1⟩
  else ⟨fun q => if q = 1 then ⟨A, hA⟩ else ⟨B, hB⟩, 1⟩

private def wk (k : ℕ) : A5WrTwo :=
  match k with
  | 0 => mkW 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _) false
  | 1 => mkW 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _) false
  | 2 => mkW 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _) false
  | 3 => mkW pRev pRev pRev_mem pRev_mem true
  | 4 => mkW p4A p4B p4A_mem p4B_mem true
  | 5 => mkW pRev pRev pRev_mem pRev_mem true
  | 6 => mkW p6A p6B p6A_mem p6B_mem false
  | 7 => mkW p7A p7B p7A_mem p7B_mem false
  | 8 => mkW p8 p8 p8_mem p8_mem true
  | 9 => mkW pRev p9B pRev_mem p9B_mem false
  | _ => 1

private theorem wk_spec (k : Fin 10) (x : Fin 10) :
    ((pt10.symm (RegularWreathProduct.toPerm (alternatingGroup (Fin 5))
        (Multiplicative (ZMod 2)) (Fin 5) (wk (k : ℕ)) (pt10 x)) : Fin 10) : ℕ)
      = (sigArrs[(k : ℕ)]!)[(x : ℕ)]! := by
  revert k x
  decide

theorem nonempty_mulEquiv_a5WrTwoImage : Nonempty (A5WrTwo ≃* a5WrTwoImage) := by
  let f : A5WrTwo →* Equiv.Perm (Fin 5 × Multiplicative (ZMod 2)) :=
    RegularWreathProduct.toPerm (alternatingGroup (Fin 5)) (Multiplicative (ZMod 2)) (Fin 5)
  let g : Equiv.Perm (Fin 5 × Multiplicative (ZMod 2)) →* Equiv.Perm (Fin 10) :=
    (Equiv.permCongrHom pt10.symm).toMonoidHom
  have hf : Function.Injective f :=
    RegularWreathProduct.toPermInj (D := alternatingGroup (Fin 5))
      (Q := Multiplicative (ZMod 2)) (Λ := Fin 5)
  have hg : Function.Injective g := fun _ _ h => (Equiv.permCongrHom pt10.symm).injective h
  exact ⟨(MonoidHom.ofInjective hf).trans (Subgroup.equivMapOfInjective f.range g hg)⟩

theorem card_a5WrTwoImage : Nat.card a5WrTwoImage = 7200 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_a5WrTwoImage
  rw [← Nat.card_congr e.toEquiv]
  have hD : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hQ : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [RegularWreathProduct.card, hD, hQ]
  norm_num

theorem mem_a5WrTwoImage_of_prep_sigArrs {k : ℕ} (hk : k < 10) {π : Equiv.Perm (Fin 10)}
    (hπ : PRep 10 sigArrs[k]! π) : π ∈ a5WrTwoImage := by
  let f : A5WrTwo →* Equiv.Perm (Fin 5 × Multiplicative (ZMod 2)) :=
    RegularWreathProduct.toPerm (alternatingGroup (Fin 5)) (Multiplicative (ZMod 2)) (Fin 5)
  let g : Equiv.Perm (Fin 5 × Multiplicative (ZMod 2)) →* Equiv.Perm (Fin 10) :=
    (Equiv.permCongrHom pt10.symm).toMonoidHom
  have hw : g (f (wk k)) = π := by
    apply Equiv.ext
    intro x
    apply Fin.ext
    rw [show (g (f (wk k))) x = pt10.symm (f (wk k) (pt10 x)) from rfl]
    rw [← hπ x]
    exact wk_spec ⟨k, hk⟩ x
  show π ∈ f.range.map g
  rw [← hw]
  exact Subgroup.mem_map_of_mem g (MonoidHom.mem_range.mpr ⟨wk k, rfl⟩)

theorem nonempty_quotient_mulEquiv_a5WrTwo {Γ : Type*} [Group Γ] (Q : Subgroup Γ) [Q.Normal]
    (φ : Γ →* Equiv.Perm (Fin 10)) (hker : φ.ker = Q) (hle : φ.range ≤ a5WrTwoImage)
    (hcard : Nat.card φ.range = 7200) : Nonempty (Γ ⧸ Q ≃* A5WrTwo) := by
  haveI : Finite a5WrTwoImage :=
    Nat.finite_of_card_ne_zero (by rw [card_a5WrTwoImage]; norm_num)
  have hrange : φ.range = a5WrTwoImage := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_a5WrTwoImage, hcard]
  obtain ⟨e⟩ := nonempty_mulEquiv_a5WrTwoImage
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans
      ((MulEquiv.subgroupCongr hrange).trans e.symm))⟩

end CFSG.EvenSporadicStandard.HNRecog.SideF4
