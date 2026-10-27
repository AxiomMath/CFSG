module

public import CFSG.CGT.Stroth77.NonSplit.Model

public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
  CFSG.HardMathSupport.Cooperstein.Coordinator

@[expose] def Msp : Type := {p : Vec6 × Perm (Fin 6) // p.1 5 = 0 ∧ par p.1 = 0}

instance : DecidablePred fun p : Vec6 × Perm (Fin 6) => p.1 5 = 0 ∧ par p.1 = 0 :=
  fun _ => instDecidableAnd

namespace Msp

instance : DecidableEq Msp := fun a b =>
  decidable_of_iff
    (a.1.2 0 = b.1.2 0 ∧ a.1.2 1 = b.1.2 1 ∧ a.1.2 2 = b.1.2 2 ∧ a.1.2 3 = b.1.2 3 ∧
      a.1.2 4 = b.1.2 4 ∧ a.1.2 5 = b.1.2 5 ∧ a.1.1 0 = b.1.1 0 ∧ a.1.1 1 = b.1.1 1 ∧
      a.1.1 2 = b.1.1 2 ∧ a.1.1 3 = b.1.1 3 ∧ a.1.1 4 = b.1.1 4)
    (by
      constructor
      · rintro ⟨h0, h1, h2, h3, h4, h5, v0, v1, v2, v3, v4⟩
        refine Subtype.ext (Prod.ext (funext fun i => ?_) (Equiv.ext fun i => ?_))
        · fin_cases i <;> first | assumption | exact a.2.1.trans b.2.1.symm
        · fin_cases i <;> assumption
      · intro h; subst h; simp)

instance : Fintype Msp := Subtype.fintype _

@[expose] def vec (a : Msp) : Vec6 := a.1.1

@[expose] def perm (a : Msp) : Perm (Fin 6) := a.1.2

theorem vec_five (a : Msp) : a.vec 5 = 0 := a.2.1

theorem par_vec (a : Msp) : par a.vec = 0 := a.2.2

@[expose] def mk (v : Vec6) (σ : Perm (Fin 6)) (h : par v = 0) : Msp :=
  ⟨((nrmS v).get, σ), by rw [nrmS_get]; exact nrm_five v, by rw [nrmS_get, par_nrm]; exact h⟩

@[ext] theorem ext {a b : Msp} (hv : a.vec = b.vec) (hp : a.perm = b.perm) : a = b :=
  Subtype.ext (Prod.ext hv hp)

theorem vec_mk (v : Vec6) (σ : Perm (Fin 6)) (h : par v = 0) : (mk v σ h).vec = nrm v :=
  nrmS_get v

instance : One Msp := ⟨⟨(0, 1), rfl, by simp [par]⟩⟩

theorem vec_one : (1 : Msp).vec = 0 := rfl

theorem perm_one : (1 : Msp).perm = 1 := rfl

instance : Mul Msp :=
  ⟨fun a b => mk (fun i => xadd (a.vec i) (b.vec (a.perm.symm i))) (forcePerm (b.perm.trans a.perm))
    (by
    have : (fun i => xadd (a.vec i) (b.vec (a.perm.symm i))) = a.vec + pact a.perm b.vec := rfl
    rw [this, par_add, par_pact, a.par_vec, b.par_vec, add_zero])⟩

instance : Inv Msp :=
  ⟨fun a => mk (fun i => a.vec (a.perm i)) (forcePerm a.perm.symm) (by
    have : (fun i => a.vec (a.perm i)) = pact a.perm⁻¹ a.vec := rfl
    rw [this, par_pact, a.par_vec])⟩

theorem vec_mul (a b : Msp) : (a * b).vec = nrm (a.vec + pact a.perm b.vec) :=
  vec_mk _ _ _

theorem perm_mul (a b : Msp) : (a * b).perm = a.perm * b.perm := forcePerm_eq _

theorem vec_inv (a : Msp) : a⁻¹.vec = nrm (pact a.perm⁻¹ a.vec) :=
  vec_mk _ _ _

theorem perm_inv (a : Msp) : a⁻¹.perm = a.perm⁻¹ := forcePerm_eq _

instance : Group Msp where
  mul_assoc a b c := by
    refine ext ?_ (by rw [perm_mul, perm_mul, perm_mul, perm_mul, mul_assoc])
    rw [vec_mul, vec_mul, vec_mul, vec_mul, perm_mul, nrm_add_nrm_left,
      nrm_add_pact_nrm, pact_add, pact_mul, add_assoc]
  one_mul a := by
    refine ext ?_ (by rw [perm_mul, perm_one, one_mul])
    rw [vec_mul, vec_one, perm_one, pact_one, zero_add, nrm_eq_self a.vec_five]
  mul_one a := by
    refine ext ?_ (by rw [perm_mul, perm_one, mul_one])
    rw [vec_mul, vec_one, pact_zero, add_zero, nrm_eq_self a.vec_five]
  inv_mul_cancel a := by
    refine ext ?_ (by rw [perm_mul, perm_inv, perm_one, inv_mul_cancel])
    rw [vec_mul, vec_inv, perm_inv, nrm_add_nrm_left]
    generalize pact a.perm⁻¹ a.vec = x
    funext i
    simp only [nrm_apply, vec_one, Pi.add_apply, Pi.zero_apply]
    generalize x i = c; generalize x 5 = d
    revert c d; decide

@[expose] def ofPerm (σ : Perm (Fin 6)) : Msp := ⟨(0, σ), rfl, by simp [par]⟩

theorem vec_ofPerm (σ : Perm (Fin 6)) : (ofPerm σ).vec = 0 := rfl

theorem perm_ofPerm (σ : Perm (Fin 6)) : (ofPerm σ).perm = σ := rfl

end Msp

open Msp in
@[expose] def θsp : Msp →* Perm (Fin 6) where
  toFun := Msp.perm
  map_one' := rfl
  map_mul' _ _ := Msp.perm_mul _ _

theorem θsp_apply (a : Msp) : θsp a = a.perm := rfl

@[expose] def sigmaSp : Perm (Fin 6) →* Msp where
  toFun := Msp.ofPerm
  map_one' := rfl
  map_mul' σ τ := Msp.ext (by
    rw [Msp.vec_mul]
    simp only [Msp.vec_ofPerm, pact_zero, add_zero]
    exact (nrm_eq_self rfl).symm) (by rw [Msp.perm_mul]; rfl)

theorem θsp_surjective : Function.Surjective θsp := fun σ => ⟨sigmaSp σ, rfl⟩

@[expose] def Qsp : Subgroup Msp := θsp.ker

theorem mem_Qsp {a : Msp} : a ∈ Qsp ↔ a.perm = 1 := MonoidHom.mem_ker

theorem θsp_ker : θsp.ker = Qsp := rfl

instance : DecidablePred (· ∈ Qsp) := fun a => decidable_of_iff (a.perm = 1) mem_Qsp.symm

instance : Fintype Qsp := Subtype.fintype _

@[expose] def evToMsp (x : evenWeight 6) : Msp := Msp.mk (x : Vec6) 1 x.2

theorem evToMsp_vec (x : evenWeight 6) : (evToMsp x).vec = nrm (x : Vec6) := Msp.vec_mk _ _ _

theorem evToMsp_perm (x : evenWeight 6) : (evToMsp x).perm = 1 := rfl

theorem evToMsp_eq_of_rel {x y : evenWeight 6} (h : -x + y ∈ evenWeightOnes 6) :
    evToMsp x = evToMsp y := by
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes h
  refine Msp.ext ?_ rfl
  funext i
  have h5 : -(x : Vec6) 5 + (y : Vec6) 5 = c := hc 5
  have hi : -(x : Vec6) i + (y : Vec6) i = c := hc i
  rw [evToMsp_vec, evToMsp_vec, nrm_apply, nrm_apply]
  clear hc h
  revert h5 hi
  generalize (x : Vec6) i = a; generalize (x : Vec6) 5 = b
  generalize (y : Vec6) i = c'; generalize (y : Vec6) 5 = d
  revert a b c' d c; decide

@[expose] def heartToMsp (v : altHeart 6) : Msp :=
  Quotient.liftOn' v evToMsp fun _ _ h => evToMsp_eq_of_rel (QuotientAddGroup.leftRel_apply.1 h)

theorem heartToMsp_mk (x : evenWeight 6) : heartToMsp (x : altHeart 6) = evToMsp x := rfl

theorem heartToMsp_add (v w : altHeart 6) :
    heartToMsp (v + w) = heartToMsp v * heartToMsp w := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
  show evToMsp (x + y) = evToMsp x * evToMsp y
  refine Msp.ext ?_ (by simp [evToMsp_perm, Msp.perm_mul])
  rw [Msp.vec_mul, evToMsp_perm, pact_one]
  rw [evToMsp_vec, evToMsp_vec, evToMsp_vec, nrm_add_nrm_left, nrm_add_nrm_right]
  rfl

theorem heartToMsp_perm (v : altHeart 6) : (heartToMsp v).perm = 1 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rfl

@[expose] def heartHomSp : Multiplicative (altHeart 6) →* Msp where
  toFun v := heartToMsp v.toAdd
  map_one' := by
    show evToMsp 0 = 1
    exact Msp.ext (by funext i; simp [evToMsp_vec, nrm_apply, Msp.vec_one]) rfl
  map_mul' v w := heartToMsp_add v.toAdd w.toAdd

theorem heartHomSp_mem (v : Multiplicative (altHeart 6)) : heartHomSp v ∈ Qsp :=
  mem_Qsp.2 (heartToMsp_perm _)

theorem heartHomSp_injective : Function.Injective heartHomSp := by
  rw [injective_iff_map_eq_one]
  intro v hv
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective v.toAdd
  have h : evToMsp x = 1 := by rw [← heartToMsp_mk, hx]; exact hv
  have hvec : nrm (x : Vec6) = 0 := (evToMsp_vec x).symm.trans (congrArg Msp.vec h)
  have : v.toAdd = 0 := by
    rw [← hx, QuotientAddGroup.eq_zero_iff]
    refine mem_evenWeightOnes_of_forall_eq (c := (x : Vec6) 5) fun i => ?_
    have := congrFun hvec i
    simp only [nrm_apply, Pi.zero_apply] at this
    revert this; generalize (x : Vec6) i = a; generalize (x : Vec6) 5 = b; revert a b; decide
  exact this

theorem heartHomSp_surjective : ∀ a : Qsp, ∃ v, heartHomSp v = (a : Msp) := by
  rintro ⟨a, ha⟩
  rw [mem_Qsp] at ha
  refine ⟨Multiplicative.ofAdd ((⟨a.vec, a.par_vec⟩ : evenWeight 6) : altHeart 6), ?_⟩
  refine Msp.ext ?_ ha.symm
  exact (evToMsp_vec ⟨a.vec, a.par_vec⟩).trans (nrm_eq_self a.vec_five)

@[expose] noncomputable def ψsp : Multiplicative (altHeart 6) ≃* Qsp :=
  MulEquiv.ofBijective (heartHomSp.codRestrict Qsp heartHomSp_mem)
    ⟨fun _ _ h => heartHomSp_injective (congrArg Subtype.val h), fun a => by
      obtain ⟨v, hv⟩ := heartHomSp_surjective a
      exact ⟨v, Subtype.ext hv⟩⟩

theorem card_Qsp : Nat.card Qsp = 16 := by
  rw [← Nat.card_congr ψsp.toEquiv, Nat.card_congr (Multiplicative.toAdd.trans Core.coordE.toEquiv),
    Nat.card_eq_fintype_card]
  rfl

theorem card_Msp : Nat.card Msp = 11520 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Qsp, card_Qsp, ← θsp_ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θsp θsp_surjective).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end CFSG.CGT.Stroth77
