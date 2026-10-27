module

public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LieType.RootSystem.Cartan
public import CFSG.LieType.CurtisTits.Reduction
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm
public import CFSG.Open.Defs

public section

namespace CFSG.LieType.Universal.SpecialLinear

open Matrix CFSG.LieType.RootSystem

variable (m : ℕ) (F : Type) [Field F]

theorem isFiniteType_A : TauCeti.IsFiniteType (CartanMatrix.A m) :=
  TauCeti.isFiniteType_cartanMatrix_A m

@[expose] def toStd (v : Fin m → ℤ) : Fin (m + 1) → ℤ := fun a =>
  (if h : a.val < m then v ⟨a.val, h⟩ else 0) -
    (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0)

@[expose] noncomputable def rootGroup (γ : Fin m → ℤ) :
    Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
  ⨆ (i : Fin (m + 1)) (j : Fin (m + 1)) (h : i ≠ j)
    (_ : toStd m γ = Pi.single i 1 - Pi.single j 1), rootSubgroup m F h

@[expose] noncomputable def weylRep (k : Fin m) : SpecialLinearGroup (Fin (m + 1)) F :=
  SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne'
      (-1) *
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1

@[expose] noncomputable def torus (k : Fin m) : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
  Subgroup.closure {h | ∃ t : Fˣ, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
    Matrix.diagonal (Function.update (Function.update 1 k.castSucc (t : F)) k.succ
      ((t⁻¹ : Fˣ) : F))}

private def toStdLin : (Fin m → ℤ) →ₗ[ℤ] (Fin (m + 1) → ℤ) where
  toFun := toStd m
  map_add' v w := by
    funext a
    simp only [toStd, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext a
    simp only [toStd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private theorem toStdLin_apply (v : Fin m → ℤ) : toStdLin m v = toStd m v := rfl

theorem toStd_zero : toStd m 0 = 0 :=
  map_zero (toStdLin m)

theorem toStd_sub (v w : Fin m → ℤ) : toStd m (v - w) = toStd m v - toStd m w :=
  map_sub (toStdLin m) v w

theorem toStd_neg (v : Fin m → ℤ) : toStd m (-v) = -toStd m v :=
  map_neg (toStdLin m) v

theorem toStd_smul (c : ℤ) (v : Fin m → ℤ) : toStd m (c • v) = c • toStd m v :=
  map_zsmul (toStdLin m) c v

theorem toStd_single (k : Fin m) :
    toStd m (Pi.single k 1) = Pi.single k.castSucc 1 - Pi.single k.succ 1 := by
  funext a
  simp only [toStd, Pi.sub_apply, Pi.single_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

private theorem toStd_castSucc (v : Fin m → ℤ) (k : Fin m) :
    toStd m v k.castSucc = v k - if h : 0 < k.val then v ⟨k.val - 1, by omega⟩ else 0 := by
  simp only [toStd, Fin.val_castSucc, k.isLt, dite_true, Fin.eta]

theorem toStd_injective : Function.Injective (toStd m) := by
  intro v w h
  have key : ∀ n (k : Fin m), k.val = n → v k = w k := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have := congrFun h k.castSucc
      rw [toStd_castSucc, toStd_castSucc, dite_eq_right (by omega),
        dite_eq_right (by omega)] at this
      simpa using this
    | succ n ih =>
      intro k hk
      have := congrFun h k.castSucc
      rw [toStd_castSucc, toStd_castSucc, dite_eq_left (by omega), dite_eq_left (by omega),
        ih ⟨k.val - 1, by omega⟩ (by simp only; omega)] at this
      simpa using this
  funext k
  exact key k.val k rfl

private theorem sum_cartanMatrix_A_mul_single (k l : Fin m) :
    ∑ j, CartanMatrix.A m k j * (Pi.single l 1 : Fin m → ℤ) j = CartanMatrix.A m k l := by
  simp [Pi.single_apply]

private theorem toStdLin_comp_reflection (k : Fin m) :
    (toStdLin m).comp (reflection (CartanMatrix.A m) k) =
      (LinearMap.funLeft ℤ ℤ (Equiv.swap k.castSucc k.succ)).comp (toStdLin m) := by
  ext l a
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, toStdLin_apply, reflection_apply,
    LinearMap.coe_single, sum_cartanMatrix_A_mul_single, toStd_sub, toStd_smul, toStd_single]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, CartanMatrix.A, Matrix.of_apply,
    Equiv.swap_apply_def, smul_eq_mul]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem toStd_reflection (k : Fin m) (v : Fin m → ℤ) :
    toStd m (reflection (CartanMatrix.A m) k v) = toStd m v ∘ Equiv.swap k.castSucc k.succ :=
  LinearMap.congr_fun (toStdLin_comp_reflection m k) v

private theorem toStd_reflection_of_eq (k : Fin m) {v : Fin m → ℤ} {i j : Fin (m + 1)}
    (h : toStd m v = Pi.single i 1 - Pi.single j 1) :
    toStd m (reflection (CartanMatrix.A m) k v) =
      Pi.single (Equiv.swap k.castSucc k.succ i) 1 -
        Pi.single (Equiv.swap k.castSucc k.succ j) 1 := by
  rw [toStd_reflection, h]
  funext a
  simp only [Function.comp_apply, Pi.sub_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]

private theorem reflection_A_single_self (k : Fin m) :
    reflection (CartanMatrix.A m) k (Pi.single k 1) = -Pi.single k 1 := by
  rw [reflection_apply, sum_cartanMatrix_A_mul_single,
    show CartanMatrix.A m k k = 2 by simp [CartanMatrix.A], two_smul, sub_add_cancel_left]

private theorem exists_toStd_weylAction (w : (coxeterMatrix (isFiniteType_A m)).Group)
    {v : Fin m → ℤ}
    (hv : ∃ i j : Fin (m + 1), i ≠ j ∧ toStd m v = Pi.single i 1 - Pi.single j 1) :
    ∃ i j : Fin (m + 1), i ≠ j ∧
      toStd m (weylAction (isFiniteType_A m) w v) = Pi.single i 1 - Pi.single j 1 := by
  obtain ⟨ω, rfl⟩ := (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.wordProd_surjective w
  induction ω with
  | nil => simpa using hv
  | cons k ω ih =>
    obtain ⟨i, j, hij, h⟩ := ih
    rw [CoxeterSystem.wordProd_cons, map_mul, Module.End.mul_apply, weylAction_simple]
    exact ⟨_, _, (Equiv.swap _ _).injective.ne hij, toStd_reflection_of_eq m k h⟩

private theorem exists_weylAction_of_lt (d : ℕ) : ∀ i j : Fin (m + 1), j.val = i.val + d + 1 →
    ∃ (w : (coxeterMatrix (isFiniteType_A m)).Group) (k : Fin m),
      toStd m (weylAction (isFiniteType_A m) w (Pi.single k 1)) =
        Pi.single i 1 - Pi.single j 1 := by
  induction d with
  | zero =>
    intro i j hij
    refine ⟨1, ⟨i.val, by omega⟩, ?_⟩
    rw [map_one, Module.End.one_apply, toStd_single]
    congr 2
    ext
    simp only [Fin.val_succ]
    omega
  | succ d ih =>
    intro i j hij
    obtain ⟨w, k, h⟩ := ih ⟨i.val + 1, by omega⟩ j (by simp only; omega)
    refine ⟨(coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ⟨i.val, by omega⟩ * w, k,
      ?_⟩
    rw [map_mul, Module.End.mul_apply, weylAction_simple, toStd_reflection_of_eq m _ h]
    congr 2
    · rw [Equiv.swap_apply_def]
      split_ifs with h₁ h₂ <;> simp [Fin.ext_iff] at *
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
        (Fin.ne_of_val_ne (by simp; omega))]

private theorem exists_weylAction_single {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ (w : (coxeterMatrix (isFiniteType_A m)).Group) (k : Fin m),
      toStd m (weylAction (isFiniteType_A m) w (Pi.single k 1)) =
        Pi.single i 1 - Pi.single j 1 := by
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact exists_weylAction_of_lt m (j.val - i.val - 1) i j (by omega)
  · obtain ⟨w, k, hw⟩ := exists_weylAction_of_lt m (i.val - j.val - 1) j i (by omega)
    refine ⟨w * (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k, k, ?_⟩
    rw [map_mul, Module.End.mul_apply, weylAction_simple, reflection_A_single_self, map_neg,
      toStd_neg, hw, neg_sub]

theorem roots_eq : roots (isFiniteType_A m) ∅ =
    {γ | ∃ i j : Fin (m + 1), i ≠ j ∧ toStd m γ = Pi.single i 1 - Pi.single j 1} := by
  ext γ
  constructor
  · rintro (⟨w, k, rfl⟩ | ⟨w, k, hk, -⟩)
    · exact exists_toStd_weylAction m w ⟨_, _, Fin.castSucc_lt_succ.ne, toStd_single m k⟩
    · exact absurd hk (Set.notMem_empty k)
  · rintro ⟨i, j, hij, h⟩
    obtain ⟨w, k, hw⟩ := exists_weylAction_single m hij
    exact Or.inl ⟨w, k, toStd_injective m (h.trans hw.symm)⟩

private theorem eq_of_single_sub_single {ι : Type*} [DecidableEq ι] {i j i' j' : ι} (hij : i ≠ j)
    (h : (Pi.single i 1 - Pi.single j 1 : ι → ℤ) = Pi.single i' 1 - Pi.single j' 1) :
    i = i' ∧ j = j' := by
  have h₁ := congrFun h i
  have h₂ := congrFun h j
  simp only [Pi.sub_apply, Pi.single_apply] at h₁ h₂
  grind

theorem rootGroup_eq {i j : Fin (m + 1)} (hij : i ≠ j) {γ : Fin m → ℤ}
    (hγ : toStd m γ = Pi.single i 1 - Pi.single j 1) : rootGroup m F γ = rootSubgroup m F hij := by
  refine le_antisymm (iSup_le fun i' => iSup_le fun j' => iSup_le fun hij' => iSup_le fun h => ?_)
    (le_iSup_of_le i <| le_iSup_of_le j <| le_iSup_of_le hij <| le_iSup_of_le hγ le_rfl)
  obtain ⟨rfl, rfl⟩ := eq_of_single_sub_single hij (hγ.symm.trans h)
  exact le_rfl

variable {m} in
private theorem castSucc_ne_succ (k : Fin m) : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne

private theorem rootGroup_single (k : Fin m) :
    rootGroup m F (Pi.single k 1) = fundamentalRootSubgroup m F k true :=
  rootGroup_eq m F (castSucc_ne_succ k) (toStd_single m k)

private theorem rootGroup_neg_single (k : Fin m) :
    rootGroup m F (-Pi.single k 1) = fundamentalRootSubgroup m F k false :=
  rootGroup_eq m F (castSucc_ne_succ k).symm (by rw [toStd_neg, toStd_single, neg_sub])

theorem rankOne_rootGroup (k : Fin m) :
    CFSG.LieType.CurtisTits.rankOne (rootGroup m F) k =
      fundamentalRootSubgroup m F k true ⊔ fundamentalRootSubgroup m F k false := by
  rw [CurtisTits.rankOne, rootGroup_single, rootGroup_neg_single]

theorem levi_rootGroup (J : Finset (Fin m)) :
    CFSG.LieType.CurtisTits.levi (rootGroup m F) J = SpecialLinear.levi m F J := by
  simp only [CurtisTits.levi, SpecialLinear.levi, rankOne_rootGroup, iSup_bool_eq]

private theorem single_mem_roots (k : Fin m) : Pi.single k 1 ∈ roots (isFiniteType_A m) ∅ := by
  rw [roots_eq]
  exact ⟨_, _, castSucc_ne_succ k, toStd_single m k⟩

private theorem neg_single_mem_roots (k : Fin m) :
    -Pi.single k 1 ∈ roots (isFiniteType_A m) ∅ := by
  rw [roots_eq]
  exact ⟨_, _, (castSucc_ne_succ k).symm, by rw [toStd_neg, toStd_single, neg_sub]⟩

private theorem iSup_rootGroup_eq_top :
    ⨆ γ ∈ roots (isFiniteType_A m) ∅, rootGroup m F γ = ⊤ := by
  rw [eq_top_iff, ← iSup_fundamentalRootSubgroup_eq_top]
  refine iSup_le fun k => iSup_le fun s => ?_
  cases s
  · rw [← rootGroup_neg_single]
    exact le_iSup₂_of_le (f := fun γ _ => rootGroup m F γ) _ (neg_single_mem_roots m k) le_rfl
  · rw [← rootGroup_single]
    exact le_iSup₂_of_le (f := fun γ _ => rootGroup m F γ) _ (single_mem_roots m k) le_rfl

private theorem rootGroup_le_rankOne (i : Fin m) (γ : Fin m → ℤ)
    (hγ : γ ∈ roots (isFiniteType_A m) ∅) (hsupp : ∀ k, k ≠ i → γ k = 0) :
    rootGroup m F γ ≤ CurtisTits.rankOne (rootGroup m F) i := by
  rw [roots_eq] at hγ
  obtain ⟨p, q, hpq, hγ⟩ := hγ
  have hγi : γ = γ i • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hsupp k hk, hk]
  have hval : toStd m (γ i • Pi.single i 1) i.castSucc = γ i := by
    rw [toStd_smul, toStd_single]
    simp [castSucc_ne_succ i]
  rw [← hγi, hγ] at hval
  have hcases : γ i = 1 ∨ γ i = -1 ∨ γ i = 0 := by
    rw [← hval]
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> simp
  rcases hcases with h | h | h
  · rw [hγi, h, one_smul]
    exact le_sup_left
  · rw [hγi, h, neg_one_zsmul]
    exact le_sup_right
  · have h0 : toStd m γ = 0 := by rw [hγi, h, zero_smul, toStd_zero]
    have := congrFun (hγ.symm.trans h0) p
    simp [hpq] at this

private theorem coe_weylRep (k : Fin m) :
    (weylRep m F k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = weylMatrix k.castSucc k.succ :=
  coe_transvection_mul_transvection_mul_transvection (castSucc_ne_succ k)

private theorem weylRep_mem_rankOne (k : Fin m) :
    weylRep m F k ∈ CurtisTits.rankOne (rootGroup m F) k := by
  rw [rankOne_rootGroup]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (transvection_mem_rootSubgroup _ _))
    (Subgroup.mem_sup_right (transvection_mem_rootSubgroup _ _)))
    (Subgroup.mem_sup_left (transvection_mem_rootSubgroup _ _))

private theorem weylRep_conj_mem (k : Fin m) (γ : Fin m → ℤ)
    (hγ : γ ∈ roots (isFiniteType_A m) ∅) (x : SpecialLinearGroup (Fin (m + 1)) F)
    (hx : x ∈ rootGroup m F γ) :
    weylRep m F k * x * (weylRep m F k)⁻¹ ∈ rootGroup m F
      (weylAction (isFiniteType_A m) ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k)
        γ) := by
  rw [roots_eq] at hγ
  obtain ⟨p, q, hpq, hγ⟩ := hγ
  rw [rootGroup_eq m F hpq hγ, mem_rootSubgroup] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [weylAction_simple, rootGroup_eq m F ((Equiv.swap _ _).injective.ne hpq)
      (toStd_reflection_of_eq m k hγ),
    conj_transvection_of_coe_eq_signedPerm (coe_weylRep m F k) (weylSign_mul_self _) hpq c]
  exact transvection_mem_rootSubgroup _ _

private theorem coxeterMatrix_A_of_adj {i j : Fin m} (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    coxeterMatrix (isFiniteType_A m) i j = 3 := by
  have hij : i ≠ j := fun e => by subst e; omega
  simp [CartanMatrix.A, hij, Ne.symm hij, h, h.symm]

private theorem coxeterMatrix_A_of_far {i j : Fin m} (hij : i ≠ j)
    (h : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    coxeterMatrix (isFiniteType_A m) i j = 2 := by
  have h' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := fun h'' => h h''.symm
  simp [CartanMatrix.A, hij, Ne.symm hij, h, h']

private theorem weylRep_braid (i j : Fin m) :
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_A m)) i j).map (weylRep m F)).prod =
      ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_A m)) j i).map
        (weylRep m F)).prod := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterMatrix_A_of_adj m h,
      coxeterMatrix_A_of_adj m h.symm]
    show ([j, i, j].map (weylRep m F)).prod = ([i, j, i].map (weylRep m F)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    apply SpecialLinearGroup.coeMonoidHom_injective
    simp only [map_mul, SpecialLinearGroup.coeMonoidHom_apply, coe_weylRep]
    rcases h with h | h
    · rw [show i.succ = j.castSucc from Fin.ext (by simp; omega)]
      exact (weylMatrix_braid (Fin.ne_of_val_ne (by simp; omega)) (castSucc_ne_succ j)
        (Fin.ne_of_val_ne (by simp; omega))).symm
    · rw [show j.succ = i.castSucc from Fin.ext (by simp; omega)]
      exact weylMatrix_braid (Fin.ne_of_val_ne (by simp; omega)) (castSucc_ne_succ i)
        (Fin.ne_of_val_ne (by simp; omega))
  · rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, coxeterMatrix_A_of_far m hij h,
      coxeterMatrix_A_of_far m hij.symm (fun h' => h h'.symm)]
    show ([i, j].map (weylRep m F)).prod = ([j, i].map (weylRep m F)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    apply SpecialLinearGroup.coeMonoidHom_injective
    simp only [map_mul, SpecialLinearGroup.coeMonoidHom_apply, coe_weylRep]
    have hv : i.val ≠ j.val := Fin.val_ne_of_ne hij
    exact weylMatrix_comm (Fin.ne_of_val_ne (by simpa using hv)) (Fin.ne_of_val_ne (by simp; omega))
      (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simpa using hv))

private theorem update_update_one {a b : Fin (m + 1)} (hab : a ≠ b) (x y : F) :
    Function.update (Function.update (1 : Fin (m + 1) → F) a x) b y =
      fun r => if r = a then x else if r = b then y else 1 := by
  funext r
  simp only [Function.update_apply, Pi.one_apply]
  grind

private theorem torus_eq (k : Fin m) :
    torus m F k =
      Subgroup.closure (Set.range (SpecialLinearGroup.diag2nUnit (castSucc_ne_succ k))) := by
  rw [torus]
  congr 1
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_range, update_update_one m F (castSucc_ne_succ k)]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, SpecialLinearGroup.coeMonoidHom_injective (by
      simp only [SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.diag2nUnit_coe, ht])⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, SpecialLinearGroup.diag2nUnit_coe _ t⟩

private theorem diag2nUnit_mem_torus (k : Fin m) {i j : Fin (m + 1)} (hij : i ≠ j)
    (hi : i = k.castSucc) (hj : j = k.succ) (t : Fˣ) :
    SpecialLinearGroup.diag2nUnit hij t ∈ torus m F k := by
  subst hi hj
  rw [torus_eq]
  exact Subgroup.subset_closure ⟨t, rfl⟩

private theorem torus_le_rankOne (k : Fin m) :
    torus m F k ≤ CurtisTits.rankOne (rootGroup m F) k := by
  rw [torus_eq, Subgroup.closure_le, rankOne_rootGroup]
  rintro _ ⟨t, rfl⟩
  exact diag2nUnit_mem (castSucc_ne_succ k)
    (fun c => Subgroup.mem_sup_left (transvection_mem_rootSubgroup _ c))
    (fun c => Subgroup.mem_sup_right (transvection_mem_rootSubgroup _ c)) t

private theorem weylRep_sq_mem (k : Fin m) : weylRep m F k ^ 2 ∈ torus m F k := by
  have h : weylRep m F k ^ 2 = SpecialLinearGroup.diag2nUnit (castSucc_ne_succ k) (-1) := by
    apply SpecialLinearGroup.coeMonoidHom_injective
    rw [pow_two, map_mul, SpecialLinearGroup.coeMonoidHom_apply, coe_weylRep,
      weylMatrix_mul_self (castSucc_ne_succ k), SpecialLinearGroup.coeMonoidHom_apply,
      SpecialLinearGroup.diag2nUnit_coe]
    simp
  rw [h]
  exact diag2nUnit_mem_torus m F k _ rfl rfl _

private theorem torus_le_diagonalTorus (k : Fin m) :
    torus m F k ≤ SpecialLinearGroup.diagonalTorus F (m + 1) := by
  rw [torus, Subgroup.closure_le]
  rintro h ⟨t, ht⟩
  exact SpecialLinearGroup.mem_diagonalTorus_iff.mpr (by rw [ht]; exact isDiag_diagonal _)

private theorem torus_conj_mem (k : Fin m) (γ : Fin m → ℤ)
    (hγ : γ ∈ roots (isFiniteType_A m) ∅) (h : SpecialLinearGroup (Fin (m + 1)) F)
    (hh : h ∈ torus m F k) (x : SpecialLinearGroup (Fin (m + 1)) F)
    (hx : x ∈ rootGroup m F γ) : h * x * h⁻¹ ∈ rootGroup m F γ := by
  rw [roots_eq] at hγ
  obtain ⟨p, q, hpq, hγ⟩ := hγ
  rw [rootGroup_eq m F hpq hγ, mem_rootSubgroup] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  have hdiag := SpecialLinearGroup.mem_diagonalTorus_iff.mp (torus_le_diagonalTorus m F k hh)
  exact ⟨_, (conj_transvection_of_coe_eq_diagonal hdiag.diagonal_diag.symm hpq c).symm⟩

private theorem weylRep_conj_torus (j k : Fin m) (h : SpecialLinearGroup (Fin (m + 1)) F)
    (hh : h ∈ torus m F k) :
    weylRep m F j * h * (weylRep m F j)⁻¹ ∈ torus m F j ⊔ torus m F k := by
  rw [torus_eq m F k] at hh
  refine (Subgroup.closure_le ((torus m F j ⊔ torus m F k).comap
    (MulAut.conj (weylRep m F j)).toMonoidHom)).mpr ?_ hh
  rintro _ ⟨t, rfl⟩
  have hconj : ∀ {i' j' : Fin (m + 1)} (hij' : i' ≠ j'),
      Equiv.swap j.castSucc j.succ k.castSucc = i' → Equiv.swap j.castSucc j.succ k.succ = j' →
      weylRep m F j * SpecialLinearGroup.diag2nUnit (castSucc_ne_succ k) t *
        (weylRep m F j)⁻¹ = SpecialLinearGroup.diag2nUnit hij' t :=
    fun hij' hi hj =>
      conj_diag2nUnit_of_coe_eq_signedPerm (coe_weylRep m F j) (castSucc_ne_succ k) hij' hi hj t
  show weylRep m F j * SpecialLinearGroup.diag2nUnit (castSucc_ne_succ k) t *
    (weylRep m F j)⁻¹ ∈ torus m F j ⊔ torus m F k
  rcases eq_or_ne j k with rfl | hjk
  · rw [hconj (castSucc_ne_succ j).symm (Equiv.swap_apply_left _ _)
      (Equiv.swap_apply_right _ _), diag2nUnit_symm (castSucc_ne_succ j)]
    exact Subgroup.mem_sup_left (diag2nUnit_mem_torus m F j _ rfl rfl t⁻¹)
  have hv : j.val ≠ k.val := Fin.val_ne_of_ne hjk
  by_cases h₁ : j.val + 1 = k.val
  · have e : j.succ = k.castSucc := Fin.ext (by simp; omega)
    have hne : j.castSucc ≠ k.succ := Fin.ne_of_val_ne (by simp; omega)
    rw [hconj hne (by rw [← e, Equiv.swap_apply_right])
        (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
          (Fin.ne_of_val_ne (by simp; omega))),
      ← diag2nUnit_mul_diag2nUnit (castSucc_ne_succ j) (Fin.ne_of_val_ne (by simp; omega)) hne]
    exact mul_mem (Subgroup.mem_sup_left (diag2nUnit_mem_torus m F j _ rfl rfl t))
      (Subgroup.mem_sup_right (diag2nUnit_mem_torus m F k _ e rfl t))
  by_cases h₂ : k.val + 1 = j.val
  · have e : k.succ = j.castSucc := Fin.ext (by simp; omega)
    have hne : k.castSucc ≠ j.succ := Fin.ne_of_val_ne (by simp; omega)
    rw [hconj hne (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
          (Fin.ne_of_val_ne (by simp; omega))) (by rw [e, Equiv.swap_apply_left]),
      ← diag2nUnit_mul_diag2nUnit (castSucc_ne_succ k) (Fin.ne_of_val_ne (by simp; omega)) hne]
    exact mul_mem (Subgroup.mem_sup_right (diag2nUnit_mem_torus m F k _ rfl rfl t))
      (Subgroup.mem_sup_left (diag2nUnit_mem_torus m F j _ e rfl t))
  · rw [hconj (castSucc_ne_succ k)
        (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
          (Fin.ne_of_val_ne (by simp; omega)))
        (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp; omega))
          (Fin.ne_of_val_ne (by simp; omega)))]
    exact Subgroup.mem_sup_right (diag2nUnit_mem_torus m F k _ rfl rfl t)

theorem isCTGroupDatum :
    CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem
      (weylAction (isFiniteType_A m)) (roots (isFiniteType_A m) ∅) (rootGroup m F)
      (weylRep m F) (torus m F) where
  n_mem := weylRep_mem_rankOne m F
  conj_mem := weylRep_conj_mem m F
  braid := weylRep_braid m F
  H_le := torus_le_rankOne m F
  sq_mem := weylRep_sq_mem m F
  H_conj_mem := torus_conj_mem m F
  conj_H_mem := weylRep_conj_torus m F
  le_rankOne := rootGroup_le_rankOne m F
  iSup_eq_top := iSup_rootGroup_eq_top m F

end CFSG.LieType.Universal.SpecialLinear
