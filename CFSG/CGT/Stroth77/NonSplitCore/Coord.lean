module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.CGT.Stroth77.Core

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

abbrev U4 : Type := Fin 4 → ZMod 2

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

@[expose] def lift4 (c : U4) (j : Fin 6) : ZMod 2 :=
  if h : j.val < 4 then c ⟨j.val, h⟩ else if j.val = 4 then c 0 + c 1 + c 2 + c 3 else 0

@[expose] def coordFun (x : Fin 6 → ZMod 2) : U4 := fun i => x (Fin.castLE (by omega) i) + x 5

theorem lift4_add (c d : U4) : lift4 (c + d) = lift4 c + lift4 d := by
  funext j; fin_cases j <;> simp [lift4] <;> ring

theorem coordFun_add (x y : Fin 6 → ZMod 2) : coordFun (x + y) = coordFun x + coordFun y := by
  funext i; simp only [coordFun, Pi.add_apply]; ring

theorem mem_evenWeight_iff {x : Fin 6 → ZMod 2} : x ∈ evenWeight 6 ↔ ∑ i, x i = 0 := by
  rw [evenWeight, AddMonoidHom.mem_ker]; rfl

theorem lift4_mem (c : U4) : lift4 c ∈ evenWeight 6 := by
  rw [mem_evenWeight_iff]
  simp only [Fin.sum_univ_succ, lift4, Fin.sum_univ_zero]
  simp
  generalize c 0 = a; generalize c 1 = b; generalize c 2 = d; generalize c 3 = e
  revert a b d e; decide

theorem coordFun_lift4 (c : U4) : coordFun (lift4 c) = c := by
  funext i; fin_cases i <;> simp [coordFun, lift4]

theorem lift4_coordFun {x : Fin 6 → ZMod 2} (hx : x ∈ evenWeight 6) (j : Fin 6) :
    lift4 (coordFun x) j = x j + x 5 := by
  rw [mem_evenWeight_iff] at hx
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hx
  fin_cases j <;> simp [lift4, coordFun] at hx ⊢
  · generalize x 0 = a at hx ⊢; generalize x 1 = b at hx ⊢; generalize x 2 = d at hx ⊢
    generalize x 3 = e at hx ⊢; generalize x 4 = f at hx ⊢; generalize x 5 = g at hx ⊢
    revert a b d e f g; decide
  · exact (zmod2_add_self _).symm

@[expose] def actC (σ : Perm (Fin 6)) : U4 →+ U4 where
  toFun c := coordFun fun i => lift4 c (σ⁻¹ i)
  map_zero' := by
    funext i; simp only [coordFun, Pi.zero_apply]
    rw [show lift4 0 = 0 by funext j; fin_cases j <;> simp [lift4]]; simp
  map_add' c d := by
    rw [lift4_add, ← coordFun_add]; rfl

@[expose] noncomputable def coordHom : altHeart 6 →+ U4 :=
  QuotientAddGroup.lift (evenWeightOnes 6)
    ((AddMonoidHom.mk' coordFun coordFun_add).comp (evenWeight 6).subtype) fun x hx => by
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
    funext i
    simp [coordFun, hc, zmod2_add_self]

@[expose] noncomputable def uncoord (c : U4) : altHeart 6 := ((⟨lift4 c, lift4_mem c⟩ : evenWeight 6) : altHeart 6)

theorem coordHom_uncoord (c : U4) : coordHom (uncoord c) = c := coordFun_lift4 c

theorem uncoord_coordHom (v : altHeart 6) : uncoord (coordHom v) = v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  refine QuotientAddGroup.eq.2 (mem_evenWeightOnes_of_forall_eq (c := (x : Fin 6 → ZMod 2) 5)
    fun j => ?_)
  show -(lift4 (coordFun x) j) + (x : Fin 6 → ZMod 2) j = _
  rw [lift4_coordFun x.2 j]
  generalize (x : Fin 6 → ZMod 2) j = a; generalize (x : Fin 6 → ZMod 2) 5 = b
  revert a b; decide

@[expose] noncomputable def coordE : altHeart 6 ≃+ U4 where
  toFun := coordHom
  invFun := uncoord
  left_inv := uncoord_coordHom
  right_inv := coordHom_uncoord
  map_add' := coordHom.map_add

theorem coordE_altAct (σ : Perm (Fin 6)) (v : altHeart 6) :
    coordE (altAct σ v) = actC σ (coordE v) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  show coordFun (fun i => (x : Fin 6 → ZMod 2) (σ⁻¹ i)) =
    coordFun fun i => lift4 (coordFun x) (σ⁻¹ i)
  simp only [lift4_coordFun x.2]
  funext i
  simp only [coordFun]
  generalize (x : Fin 6 → ZMod 2) (σ⁻¹ (Fin.castLE (by omega) i)) = a
  generalize (x : Fin 6 → ZMod 2) (σ⁻¹ 5) = b; generalize (x : Fin 6 → ZMod 2) 5 = c
  revert a b c; decide

theorem coordE_pairEW (i j : Fin 6) :
    coordE ((pairEW i j : evenWeight 6) : altHeart 6) =
      coordFun fun p => (if p = i then 1 else 0) + (if p = j then 1 else 0) := by
  show coordFun _ = _
  congr 1
  funext p
  exact pairEW_apply i j p

end CFSG.CGT.Stroth77.Core
