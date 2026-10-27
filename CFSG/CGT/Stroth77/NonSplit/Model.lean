module

public import CFSG.CGT.Stroth77.NonSplitCore.Coord

public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
  CFSG.HardMathSupport.Cooperstein.Coordinator

abbrev Vec6 : Type := Fin 6 → ZMod 2

@[expose] def pact (σ : Perm (Fin 6)) (x : Vec6) : Vec6 := fun i => x (σ⁻¹ i)

@[expose] def par (x : Vec6) : ZMod 2 := ∑ i, x i

@[expose] def sg (σ : Perm (Fin 6)) : ZMod 2 := if Perm.sign σ = 1 then 0 else 1

@[expose] def xadd (a b : ZMod 2) : ZMod 2 := Fin.add (n := 2) a b

@[expose, noinline] def tab6 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) : Fin 6 → α := fun i =>
  if i.val = 0 then a0 else if i.val = 1 then a1 else if i.val = 2 then a2
    else if i.val = 3 then a3 else if i.val = 4 then a4 else a5

structure Tbl (α : Type*) where
  get : Fin 6 → α

@[expose] def tabS {α : Type*} (f : Fin 6 → α) : Tbl α :=
  ⟨tab6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)⟩

theorem tabS_get {α : Type*} (f : Fin 6 → α) (i : Fin 6) : (tabS f).get i = f i := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;> rfl

@[expose] def nrm (x : Vec6) : Vec6 := fun i => x i + x 5

@[expose] def nrmS (x : Vec6) : Tbl (ZMod 2) := tabS fun i => xadd (x i) (x 5)

theorem nrmS_get (x : Vec6) : (nrmS x).get = nrm x := funext fun i => tabS_get _ i

@[expose] def forcePerm (σ : Perm (Fin 6)) : Perm (Fin 6) where
  toFun := (tabS σ).get
  invFun := (tabS σ.symm).get
  left_inv i := by simp [tabS_get]
  right_inv i := by simp [tabS_get]

theorem forcePerm_eq (σ : Perm (Fin 6)) : forcePerm σ = σ :=
  Equiv.ext fun i => tabS_get σ i

theorem pact_apply (σ : Perm (Fin 6)) (x : Vec6) (i : Fin 6) : pact σ x i = x (σ⁻¹ i) := rfl

theorem nrm_apply (x : Vec6) (i : Fin 6) : nrm x i = x i + x 5 := rfl

theorem pact_add (σ : Perm (Fin 6)) (x y : Vec6) : pact σ (x + y) = pact σ x + pact σ y := rfl

theorem pact_zero (σ : Perm (Fin 6)) : pact σ 0 = 0 := rfl

theorem pact_one (x : Vec6) : pact 1 x = x := rfl

theorem pact_mul (σ τ : Perm (Fin 6)) (x : Vec6) : pact (σ * τ) x = pact σ (pact τ x) := by
  funext i
  simp [pact, mul_inv_rev, Perm.mul_apply]

theorem pact_pact_inv (σ : Perm (Fin 6)) (x : Vec6) : pact σ (pact σ⁻¹ x) = x := by
  rw [← pact_mul, mul_inv_cancel, pact_one]

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem nrm_five (x : Vec6) : nrm x 5 = 0 := zmod2_add_self _

theorem nrm_eq_self {x : Vec6} (h : x 5 = 0) : nrm x = x := by
  funext i; simp [nrm_apply, h]

theorem nrm_add_nrm_left (x y : Vec6) : nrm (nrm x + y) = nrm (x + y) := by
  funext i
  simp only [nrm_apply, Pi.add_apply]
  generalize x i = a; generalize x 5 = b; generalize y i = c; generalize y 5 = d
  revert a b c d; decide

theorem nrm_add_pact_nrm (x y : Vec6) (σ : Perm (Fin 6)) :
    nrm (x + pact σ (nrm y)) = nrm (x + pact σ y) := by
  funext i
  simp only [nrm_apply, Pi.add_apply, pact_apply]
  generalize x i = a; generalize x 5 = b; generalize y (σ⁻¹ i) = c; generalize y (σ⁻¹ 5) = d
  generalize y 5 = e
  revert a b c d e; decide

theorem nrm_add_nrm_right (x y : Vec6) : nrm (x + nrm y) = nrm (x + y) := by
  have := nrm_add_pact_nrm x y 1
  simpa [pact_one] using this

theorem par_add (x y : Vec6) : par (x + y) = par x + par y := by
  simp [par, Finset.sum_add_distrib]

theorem par_pact (σ : Perm (Fin 6)) (x : Vec6) : par (pact σ x) = par x := by
  simp only [par, pact]
  exact Equiv.sum_comp σ⁻¹ x

theorem par_nrm (x : Vec6) : par (nrm x) = par x := by
  simp only [par, nrm_apply, Fin.sum_univ_six]
  generalize x 0 = a0; generalize x 1 = a1; generalize x 2 = a2; generalize x 3 = a3
  generalize x 4 = a4; generalize x 5 = a5
  revert a0 a1 a2 a3 a4 a5; decide

theorem sg_mul (σ τ : Perm (Fin 6)) : sg (σ * τ) = sg σ + sg τ := by
  unfold sg
  rw [map_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;>
  rcases Int.units_eq_one_or (Perm.sign τ) with h' | h' <;> simp [h, h'] <;> decide

theorem sg_one : sg (1 : Perm (Fin 6)) = 0 := by simp [sg]

theorem sg_inv (σ : Perm (Fin 6)) : sg σ⁻¹ = sg σ := by
  have := sg_mul σ σ⁻¹
  rw [mul_inv_cancel, sg_one] at this
  revert this; generalize sg σ = a; generalize sg σ⁻¹ = b; revert a b; decide

@[expose] def Mns : Type := {p : Vec6 × Perm (Fin 6) // p.1 5 = 0 ∧ par p.1 = sg p.2}

instance : DecidablePred fun p : Vec6 × Perm (Fin 6) => p.1 5 = 0 ∧ par p.1 = sg p.2 :=
  fun _ => instDecidableAnd

namespace Mns

instance : DecidableEq Mns := fun a b =>
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

instance : Fintype Mns := Subtype.fintype _

@[expose] def vec (a : Mns) : Vec6 := a.1.1

@[expose] def perm (a : Mns) : Perm (Fin 6) := a.1.2

theorem vec_five (a : Mns) : a.vec 5 = 0 := a.2.1

theorem par_vec (a : Mns) : par a.vec = sg a.perm := a.2.2

@[expose] def mk (v : Vec6) (σ : Perm (Fin 6)) (h : par v = sg σ) : Mns :=
  ⟨((nrmS v).get, σ), by rw [nrmS_get]; exact nrm_five v, by rw [nrmS_get, par_nrm]; exact h⟩

@[ext] theorem ext {a b : Mns} (hv : a.vec = b.vec) (hp : a.perm = b.perm) : a = b :=
  Subtype.ext (Prod.ext hv hp)

theorem vec_mk (v : Vec6) (σ : Perm (Fin 6)) (h : par v = sg σ) : (mk v σ h).vec = nrm v :=
  nrmS_get v

theorem perm_mk (v : Vec6) (σ : Perm (Fin 6)) (h : par v = sg σ) : (mk v σ h).perm = σ := rfl

instance : One Mns := ⟨⟨(0, 1), rfl, by simp [par, sg]⟩⟩

theorem vec_one : (1 : Mns).vec = 0 := rfl

theorem perm_one : (1 : Mns).perm = 1 := rfl

instance : Mul Mns :=
  ⟨fun a b => mk (fun i => xadd (a.vec i) (b.vec (a.perm.symm i))) (forcePerm (b.perm.trans a.perm))
    (by
    have : (fun i => xadd (a.vec i) (b.vec (a.perm.symm i))) = a.vec + pact a.perm b.vec := rfl
    have h2 : b.perm.trans a.perm = a.perm * b.perm := rfl
    rw [this, h2, forcePerm_eq, par_add, par_pact, a.par_vec, b.par_vec, sg_mul])⟩

instance : Inv Mns :=
  ⟨fun a => mk (fun i => a.vec (a.perm i)) (forcePerm a.perm.symm) (by
    have : (fun i => a.vec (a.perm i)) = pact a.perm⁻¹ a.vec := rfl
    have h2 : a.perm.symm = a.perm⁻¹ := rfl
    rw [this, h2, forcePerm_eq, par_pact, a.par_vec, sg_inv])⟩

theorem vec_mul (a b : Mns) : (a * b).vec = nrm (a.vec + pact a.perm b.vec) :=
  vec_mk _ _ _

theorem perm_mul (a b : Mns) : (a * b).perm = a.perm * b.perm := forcePerm_eq _

theorem vec_inv (a : Mns) : a⁻¹.vec = nrm (pact a.perm⁻¹ a.vec) :=
  vec_mk _ _ _

theorem perm_inv (a : Mns) : a⁻¹.perm = a.perm⁻¹ := forcePerm_eq _

instance : Group Mns where
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

end Mns

open Mns in
@[expose] def θns : Mns →* Perm (Fin 6) where
  toFun := Mns.perm
  map_one' := rfl
  map_mul' _ _ := Mns.perm_mul _ _

theorem θns_surjective : Function.Surjective θns := by
  intro σ
  refine ⟨Mns.mk (Pi.single 0 (sg σ)) σ ?_, rfl⟩
  simp [par, Finset.sum_pi_single']

@[expose] def Qns : Subgroup Mns := θns.ker

theorem mem_Qns {a : Mns} : a ∈ Qns ↔ a.perm = 1 := MonoidHom.mem_ker

theorem θns_ker : θns.ker = Qns := rfl

instance : DecidablePred (· ∈ Qns) := fun a => decidable_of_iff (a.perm = 1) mem_Qns.symm

instance : Fintype Qns := Subtype.fintype _

@[expose] def evToMns (x : evenWeight 6) : Mns :=
  Mns.mk (x : Vec6) 1 (by
    have : par (x : Vec6) = 0 := x.2
    rw [this, sg_one])

theorem evToMns_vec (x : evenWeight 6) : (evToMns x).vec = nrm (x : Vec6) := Mns.vec_mk _ _ _

theorem evToMns_perm (x : evenWeight 6) : (evToMns x).perm = 1 := rfl

theorem evToMns_eq_of_rel {x y : evenWeight 6} (h : -x + y ∈ evenWeightOnes 6) :
    evToMns x = evToMns y := by
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes h
  refine Mns.ext ?_ rfl
  funext i
  have h5 : -(x : Vec6) 5 + (y : Vec6) 5 = c := hc 5
  have hi : -(x : Vec6) i + (y : Vec6) i = c := hc i
  rw [evToMns_vec, evToMns_vec, nrm_apply, nrm_apply]
  clear hc h
  revert h5 hi
  generalize (x : Vec6) i = a; generalize (x : Vec6) 5 = b
  generalize (y : Vec6) i = c'; generalize (y : Vec6) 5 = d
  revert a b c' d c; decide

@[expose] def heartToMns (v : altHeart 6) : Mns :=
  Quotient.liftOn' v evToMns fun _ _ h => evToMns_eq_of_rel (QuotientAddGroup.leftRel_apply.1 h)

theorem heartToMns_mk (x : evenWeight 6) : heartToMns (x : altHeart 6) = evToMns x := rfl

theorem heartToMns_add (v w : altHeart 6) :
    heartToMns (v + w) = heartToMns v * heartToMns w := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
  show evToMns (x + y) = evToMns x * evToMns y
  refine Mns.ext ?_ (by simp [evToMns_perm, Mns.perm_mul])
  rw [Mns.vec_mul, evToMns_perm, pact_one]
  rw [evToMns_vec, evToMns_vec, evToMns_vec, nrm_add_nrm_left, nrm_add_nrm_right]
  rfl

theorem heartToMns_perm (v : altHeart 6) : (heartToMns v).perm = 1 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rfl

@[expose] def heartHom : Multiplicative (altHeart 6) →* Mns where
  toFun v := heartToMns v.toAdd
  map_one' := by
    show evToMns 0 = 1
    exact Mns.ext (by funext i; simp [evToMns_vec, nrm_apply, Mns.vec_one]) rfl
  map_mul' v w := heartToMns_add v.toAdd w.toAdd

theorem heartHom_mem (v : Multiplicative (altHeart 6)) : heartHom v ∈ Qns :=
  mem_Qns.2 (heartToMns_perm _)

theorem heartHom_injective : Function.Injective heartHom := by
  rw [injective_iff_map_eq_one]
  intro v hv
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective v.toAdd
  have h : evToMns x = 1 := by rw [← heartToMns_mk, hx]; exact hv
  have hvec : nrm (x : Vec6) = 0 := (evToMns_vec x).symm.trans (congrArg Mns.vec h)
  have : v.toAdd = 0 := by
    rw [← hx, QuotientAddGroup.eq_zero_iff]
    refine mem_evenWeightOnes_of_forall_eq (c := (x : Vec6) 5) fun i => ?_
    have := congrFun hvec i
    simp only [nrm_apply, Pi.zero_apply] at this
    revert this; generalize (x : Vec6) i = a; generalize (x : Vec6) 5 = b; revert a b; decide
  exact this

theorem heartHom_surjective : ∀ a : Qns, ∃ v, heartHom v = (a : Mns) := by
  rintro ⟨a, ha⟩
  rw [mem_Qns] at ha
  have hp : par a.vec = 0 := by rw [a.par_vec, ha, sg_one]
  refine ⟨Multiplicative.ofAdd ((⟨a.vec, hp⟩ : evenWeight 6) : altHeart 6), ?_⟩
  refine Mns.ext ?_ ha.symm
  exact (evToMns_vec ⟨a.vec, hp⟩).trans (nrm_eq_self a.vec_five)

@[expose] noncomputable def ψns : Multiplicative (altHeart 6) ≃* Qns :=
  MulEquiv.ofBijective (heartHom.codRestrict Qns heartHom_mem)
    ⟨fun _ _ h => heartHom_injective (congrArg Subtype.val h), fun a => by
      obtain ⟨v, hv⟩ := heartHom_surjective a
      exact ⟨v, Subtype.ext hv⟩⟩

theorem ψns_coe (v : Multiplicative (altHeart 6)) : (ψns v : Mns) = heartHom v := rfl

theorem ψns_conj (g : Mns) (v : Multiplicative (altHeart 6)) :
    g * (ψns v : Mns) * g⁻¹ = (ψns (Multiplicative.ofAdd (altAct (θns g) v.toAdd)) : Mns) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective v.toAdd
  rw [ψns_coe, ψns_coe]
  show g * heartToMns v.toAdd * g⁻¹ = heartToMns (altAct g.perm v.toAdd)
  rw [← hx, altAct_mk, heartToMns_mk, heartToMns_mk]
  refine Mns.ext ?_ (by simp [Mns.perm_mul, Mns.perm_inv, evToMns_perm])
  rw [Mns.vec_mul, Mns.vec_mul, Mns.perm_mul, evToMns_perm, mul_one, Mns.vec_inv, evToMns_vec,
    nrm_add_nrm_left, nrm_add_pact_nrm, pact_pact_inv]
  funext i
  have e1 : (evToMns (evenWeightPerm g.perm x)).vec = nrm (pact g.perm (x : Vec6)) :=
    Mns.vec_mk _ _ _
  rw [e1]
  simp only [nrm_apply, Pi.add_apply, pact_apply]
  generalize (x : Vec6) (g.perm⁻¹ i) = a
  generalize (x : Vec6) (g.perm⁻¹ 5) = b
  generalize g.vec i = c
  generalize g.vec 5 = d
  generalize (x : Vec6) 5 = e
  revert a b c d e; decide

theorem card_Qns : Nat.card Qns = 16 := by
  rw [← Nat.card_congr ψns.toEquiv, Nat.card_congr (Multiplicative.toAdd.trans Core.coordE.toEquiv),
    Nat.card_eq_fintype_card]
  rfl

theorem card_Mns : Nat.card Mns = 11520 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Qns, card_Qns, ← θns_ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θns θns_surjective).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end CFSG.CGT.Stroth77
