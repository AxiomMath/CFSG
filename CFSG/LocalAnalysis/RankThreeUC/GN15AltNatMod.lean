module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatEnd
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv

variable {V : Type*} [CommGroup V]

structure AltNatModule (L : Subgroup (MulAut V)) (M : Subgroup V) (n : ℕ) where
  inv : ∀ l ∈ L, ∀ m ∈ M, l m ∈ M
  α : ↥L →* alternatingGroup (Fin n)
  surj : Function.Surjective α
  e : ↥M ≃* Multiplicative (evenWeight n)
  equivar : ∀ (l : ↥L) (m m' : ↥M), (m' : V) = (l : MulAut V) (m : V) →
    Multiplicative.toAdd (e m') = evenWeightPerm (α l : Perm (Fin n)) (Multiplicative.toAdd (e m))

variable {L : Subgroup (MulAut V)} {M : Subgroup V} {n : ℕ}

namespace AltNatModule

@[expose] def act (D : AltNatModule L M n) (l : ↥L) (m : ↥M) : ↥M := ⟨(l : MulAut V) (m : V), D.inv l l.2 m m.2⟩

@[simp] theorem coe_act (D : AltNatModule L M n) (l : ↥L) (m : ↥M) :
    ((D.act l m : ↥M) : V) = (l : MulAut V) (m : V) := rfl

theorem e_act (D : AltNatModule L M n) (l : ↥L) (m : ↥M) :
    Multiplicative.toAdd (D.e (D.act l m)) =
      evenWeightPerm (D.α l : Perm (Fin n)) (Multiplicative.toAdd (D.e m)) :=
  D.equivar l m _ rfl

theorem simple (D : AltNatModule L M n) (hn : Odd n) (h4 : 4 ≤ n) (S : Subgroup V) (hSM : S ≤ M)
    (hS : ∀ l ∈ L, ∀ s ∈ S, l s ∈ S) : S = ⊥ ∨ S = M := by
  let S' : AddSubgroup (evenWeight n) :=
    AddSubgroup.toSubgroup'.symm ((S.subgroupOf M).map D.e.toMonoidHom)
  have hmem : ∀ x : evenWeight n, x ∈ S' ↔ ∃ m : ↥M, (m : V) ∈ S ∧ Multiplicative.toAdd (D.e m) = x := by
    intro x
    constructor
    · rintro ⟨m, hm, hmx⟩
      exact ⟨m, hm, by rw [show D.e m = Multiplicative.ofAdd x from hmx]; rfl⟩
    · rintro ⟨m, hm, hmx⟩
      exact ⟨m, hm, by rw [← hmx]; rfl⟩
  have hinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ x ∈ S', evenWeightPerm σ x ∈ S' := by
    intro σ hσ x hx
    obtain ⟨m, hmS, hmx⟩ := (hmem x).1 hx
    obtain ⟨l, hl⟩ := D.surj ⟨σ, hσ⟩
    have hσl : (D.α l : Perm (Fin n)) = σ := congrArg Subtype.val hl
    refine (hmem _).2 ⟨D.act l m, hS l l.2 m hmS, ?_⟩
    rw [D.e_act, hσl, hmx]
  rcases evenWeight_irreducible hn h4 S' hinv with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have hvM : v ∈ M := hSM hv
    have h1 : Multiplicative.toAdd (D.e ⟨v, hvM⟩) ∈ S' := (hmem _).2 ⟨⟨v, hvM⟩, hv, rfl⟩
    rw [h, AddSubgroup.mem_bot] at h1
    have h2 : D.e ⟨v, hvM⟩ = 1 := Multiplicative.toAdd.injective (h1.trans toAdd_one.symm)
    have h3 : (⟨v, hvM⟩ : ↥M) = 1 := D.e.injective (h2.trans (map_one D.e).symm)
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val h3)
  · right
    refine le_antisymm hSM fun m hm => ?_
    have h1 : Multiplicative.toAdd (D.e ⟨m, hm⟩) ∈ S' := by rw [h]; trivial
    obtain ⟨m', hm'S, hm'⟩ := (hmem _).1 h1
    have hmm : m' = ⟨m, hm⟩ := D.e.injective (Multiplicative.toAdd.injective hm')
    have hmm' : (m' : V) = m := congrArg Subtype.val hmm
    rw [← hmm']
    exact hm'S

theorem end_eq (D : AltNatModule L M n) (hn : Odd n) (h5 : 5 ≤ n) (φ : ↥M →* ↥M)
    (hφ : ∀ (l : ↥L) (m : ↥M), φ (D.act l m) = D.act l (φ m)) :
    φ = 1 ∨ φ = MonoidHom.id _ := by
  let ψ : evenWeight n →+ evenWeight n :=
    { toFun := fun x => Multiplicative.toAdd (D.e (φ (D.e.symm (Multiplicative.ofAdd x))))
      map_zero' := by
        show Multiplicative.toAdd (D.e (φ (D.e.symm 1))) = 0
        rw [map_one, map_one, map_one]; rfl
      map_add' := fun x y => by
        show Multiplicative.toAdd (D.e (φ (D.e.symm (Multiplicative.ofAdd (x + y))))) = _
        rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul] }
  have hψ : ∀ σ ∈ alternatingGroup (Fin n), ∀ x, ψ (evenWeightPerm σ x) = evenWeightPerm σ (ψ x) := by
    intro σ hσ x
    obtain ⟨l, hl⟩ := D.surj ⟨σ, hσ⟩
    have hσl : (D.α l : Perm (Fin n)) = σ := congrArg Subtype.val hl
    set m : ↥M := D.e.symm (Multiplicative.ofAdd x) with hm
    have hex : Multiplicative.toAdd (D.e m) = x := by rw [hm, MulEquiv.apply_symm_apply]; rfl
    have h1 : D.act l m = D.e.symm (Multiplicative.ofAdd (evenWeightPerm σ x)) := by
      apply D.e.injective
      rw [MulEquiv.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      rw [D.e_act, hσl, hex]; rfl
    have h2 : ψ (evenWeightPerm σ x) = Multiplicative.toAdd (D.e (φ (D.act l m))) := by
      show Multiplicative.toAdd (D.e (φ (D.e.symm (Multiplicative.ofAdd (evenWeightPerm σ x))))) = _
      rw [h1]
    rw [h2, hφ, D.e_act, hσl]
    rfl
  rcases altNat_endo_eq hn h5 ψ hψ with h | h
  · left
    ext m
    have := DFunLike.congr_fun h (Multiplicative.toAdd (D.e m))
    have e1 : D.e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (D.e m))) = m := by
      simp
    simp only [AddMonoidHom.zero_apply] at this
    have h3 : D.e (φ m) = 1 := by
      apply Multiplicative.toAdd.injective
      have : Multiplicative.toAdd (D.e (φ (D.e.symm (Multiplicative.ofAdd
        (Multiplicative.toAdd (D.e m)))))) = 0 := this
      rw [e1] at this
      rw [this]; rfl
    have h4 : φ m = 1 := D.e.injective (h3.trans (map_one D.e).symm)
    rw [h4]; rfl
  · right
    ext m
    have := DFunLike.congr_fun h (Multiplicative.toAdd (D.e m))
    have e1 : D.e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (D.e m))) = m := by
      simp
    have h3 : Multiplicative.toAdd (D.e (φ m)) = Multiplicative.toAdd (D.e m) := by
      have : Multiplicative.toAdd (D.e (φ (D.e.symm (Multiplicative.ofAdd
        (Multiplicative.toAdd (D.e m)))))) = Multiplicative.toAdd (D.e m) := this
      rwa [e1] at this
    have h4 : φ m = m := D.e.injective (Multiplicative.toAdd.injective h3)
    rw [h4]; rfl

theorem two_lt_card [Finite V] (D : AltNatModule L M n) (hn : Odd n) (h2 : 2 ≤ n) :
    2 < Nat.card M := by
  have : Fintype ↥M := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  let x : Fin n := ⟨0, by omega⟩
  let y : Fin n := ⟨1, by omega⟩
  have hxy : x ≠ y := fun h => by simpa [x, y] using congrArg Fin.val h
  have hx0 : altBaumY hn x ≠ 0 := altBaumY_ne_zero hn h2 x
  have hy0 : altBaumY hn y ≠ 0 := altBaumY_ne_zero hn h2 y
  refine Fintype.two_lt_card_iff.2 ⟨1, D.e.symm (Multiplicative.ofAdd (altBaumY hn x)),
    D.e.symm (Multiplicative.ofAdd (altBaumY hn y)), ?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun m => Multiplicative.toAdd (D.e m)) h
    simp only [map_one, MulEquiv.apply_symm_apply, toAdd_one, toAdd_ofAdd] at h1
    exact hx0 h1.symm
  · intro h
    have h1 := congrArg (fun m => Multiplicative.toAdd (D.e m)) h
    simp only [map_one, MulEquiv.apply_symm_apply, toAdd_one, toAdd_ofAdd] at h1
    exact hy0 h1.symm
  · intro h
    have h1 := congrArg (fun m => Multiplicative.toAdd (D.e m)) h
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
    exact hxy (altBaumY_injective hn h1)

end AltNatModule

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
