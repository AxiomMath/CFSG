module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section ListLemmas

variable {M : Type*} [Monoid M]

theorem list_prod_ofFn_mul {n : ℕ} (f g : Fin n → M)
    (hfg : ∀ i j, i ≠ j → Commute (g i) (f j)) :
    (List.ofFn f).prod * (List.ofFn g).prod = (List.ofFn fun j => f j * g j).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcomm : Commute (g 0) (List.ofFn fun i : Fin n => f i.succ).prod :=
      Commute.list_prod_right _ _ fun a ha => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
        exact hfg 0 i.succ (Fin.succ_ne_zero i).symm
    have ih' := ih (fun i => f i.succ) (fun i => g i.succ)
      fun i j hij => hfg _ _ fun e => hij (Fin.succ_injective _ e)
    simp only [List.ofFn_succ, List.prod_cons]
    rw [← ih']
    set F' := (List.ofFn fun i : Fin n => f i.succ).prod
    set G' := (List.ofFn fun i : Fin n => g i.succ).prod
    calc f 0 * F' * (g 0 * G') = f 0 * (F' * g 0) * G' := by simp only [mul_assoc]
      _ = f 0 * (g 0 * F') * G' := by rw [← hcomm.eq]
      _ = f 0 * g 0 * (F' * G') := by simp only [mul_assoc]

theorem list_prod_ofFn_eq_of_eq_one {n : ℕ} (f : Fin n → M) (i : Fin n)
    (hf : ∀ j, j ≠ i → f j = 1) : (List.ofFn f).prod = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      have h1 : (List.ofFn fun j : Fin n => f j.succ).prod = 1 :=
        List.prod_eq_one fun a ha => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
          exact hf _ (Fin.succ_ne_zero j)
      rw [h1, mul_one]
    | succ i =>
      rw [hf 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih (fun j => f j.succ) i fun j hj => hf _ fun e => hj (Fin.succ_injective _ e)

end ListLemmas

section ZModPow

variable {M : Type*} [Monoid M] {g : M}

theorem pow_val_add (hg : g ^ 3 = 1) (a b : ZMod 3) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem pow_val_mul (hg : g ^ 3 = 1) (a b : ZMod 3) : g ^ (a * b).val = g ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ hg]

theorem list_prod_ofFn_pow_val (hg : g ^ 3 = 1) {n : ℕ} (t : Fin n → ZMod 3) :
    (List.ofFn fun j => g ^ (t j).val).prod = g ^ (∑ j, t j).val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => t j.succ), Fin.sum_univ_succ,
      pow_val_add hg]

end ZModPow

theorem zmod3_val_one : (1 : ZMod 3).val = 1 := rfl

theorem zmod3_val_two : (2 : ZMod 3).val = 2 := rfl

theorem zmod3_add_two_mul_add (c a : ZMod 3) : c + 2 * a + a = c := by revert c a; decide

theorem zmod3_add_two_mul_add' (c b : ZMod 3) : c + 2 * (c + b) + b = 0 := by revert c b; decide

theorem zmod3_add_add_self (c : ZMod 3) : c + (c + c) = 0 := by revert c; decide

theorem pow_two_eq_inv {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) : g ^ 2 = g⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← pow_succ' g 2, hg])

theorem pow_mul_pow_of_mul_eq {M : Type*} [Monoid M] {X Y W : M} (hYX : Y * X = X * Y * W)
    (hWX : Commute W X) (hWY : Commute W Y) (b a : ℕ) :
    Y ^ b * X ^ a = X ^ a * Y ^ b * W ^ (b * a) := by
  have h1 : ∀ a : ℕ, Y * X ^ a = X ^ a * Y * W ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      calc Y * X ^ (a + 1) = (Y * X ^ a) * X := by rw [pow_succ, mul_assoc]
        _ = X ^ a * Y * (W ^ a * X) := by rw [ih, mul_assoc]
        _ = X ^ a * Y * (X * W ^ a) := by rw [(hWX.pow_left a).eq]
        _ = X ^ a * (Y * X) * W ^ a := by simp only [mul_assoc]
        _ = X ^ a * (X * Y * W) * W ^ a := by rw [hYX]
        _ = X ^ (a + 1) * Y * W ^ (a + 1) := by
          rw [pow_succ, pow_succ' W]; simp only [mul_assoc]
  induction b with
  | zero => simp
  | succ b ih =>
    calc Y ^ (b + 1) * X ^ a = Y * (Y ^ b * X ^ a) := by rw [pow_succ', mul_assoc]
      _ = Y * (X ^ a * Y ^ b * W ^ (b * a)) := by rw [ih]
      _ = (Y * X ^ a) * Y ^ b * W ^ (b * a) := by simp only [mul_assoc]
      _ = X ^ a * Y * W ^ a * Y ^ b * W ^ (b * a) := by rw [h1]
      _ = X ^ a * Y * (W ^ a * Y ^ b) * W ^ (b * a) := by simp only [mul_assoc]
      _ = X ^ a * Y * (Y ^ b * W ^ a) * W ^ (b * a) := by
          rw [((hWY.pow_left a).pow_right b).eq]
      _ = X ^ a * (Y * Y ^ b) * (W ^ a * W ^ (b * a)) := by simp only [mul_assoc]
      _ = X ^ a * Y ^ (b + 1) * W ^ ((b + 1) * a) := by
          rw [pow_succ' Y, ← pow_add, add_mul, one_mul, add_comm a]

theorem local_mul {G : Type*} [Group G] {X Y Z : G} (hX : X ^ 3 = 1) (hY : Y ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hXY : X * Y = Y * X * Z) (hZX : Commute Z X) (hZY : Commute Z Y)
    (a b a' b' : ZMod 3) :
    (X ^ a.val * Y ^ b.val) * (X ^ a'.val * Y ^ b'.val) =
      (X ^ (a + a').val * Y ^ (b + b').val) * Z ^ (2 * (b * a')).val := by
  have hZ2 : Z ^ 2 = Z⁻¹ := pow_two_eq_inv hZ
  have hZ23 : (Z ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hZ, one_pow]
  have hYX : Y * X = X * Y * Z ^ 2 := by rw [hZ2, hXY, mul_inv_cancel_right]
  have h1 := pow_mul_pow_of_mul_eq hYX (hZX.pow_left 2) (hZY.pow_left 2) b.val a'.val
  have hW : (Z ^ 2) ^ (b.val * a'.val) = Z ^ (2 * (b * a')).val := by
    rw [pow_val_mul hZ, zmod3_val_two, pow_mul Z 2, pow_val_mul hZ23]
  rw [← hW, pow_val_add hX, pow_val_add hY]
  calc X ^ a.val * Y ^ b.val * (X ^ a'.val * Y ^ b'.val)
      = X ^ a.val * (Y ^ b.val * X ^ a'.val) * Y ^ b'.val := by simp only [mul_assoc]
    _ = X ^ a.val * (X ^ a'.val * Y ^ b.val * (Z ^ 2) ^ (b.val * a'.val)) * Y ^ b'.val := by
        rw [h1]
    _ = X ^ a.val * X ^ a'.val * Y ^ b.val * ((Z ^ 2) ^ (b.val * a'.val) * Y ^ b'.val) := by
        simp only [mul_assoc]
    _ = X ^ a.val * X ^ a'.val * Y ^ b.val * (Y ^ b'.val * (Z ^ 2) ^ (b.val * a'.val)) := by
        rw [(((hZY.pow_left 2).pow_left _).pow_right b'.val).eq]
    _ = X ^ a.val * X ^ a'.val * (Y ^ b.val * Y ^ b'.val) * (Z ^ 2) ^ (b.val * a'.val) := by
        simp only [mul_assoc]

theorem comm_eq_of_mul_eq {G : Type*} [Group G] {a b t : G} (hta : Commute t a)
    (htb : Commute t b) (h : a * b = b * a * t) : a * b * a⁻¹ * b⁻¹ = t := by
  have h1 : a * t * a⁻¹ = t := by rw [← hta.eq]; group
  have h2 : b * t * b⁻¹ = t := by rw [← htb.eq]; group
  calc a * b * a⁻¹ * b⁻¹ = b * a * t * a⁻¹ * b⁻¹ := by rw [h]
    _ = b * (a * t * a⁻¹) * b⁻¹ := by simp only [mul_assoc]
    _ = t := by rw [h1, h2]

variable {G : Type*} [Group G] {n : ℕ} {x y : Fin n → G} {z : G}

@[expose] def heisSub (x y : Fin n → G) : Subgroup G :=
  Subgroup.closure (Set.range x ∪ Set.range y)

@[expose] def heisNF (x y : Fin n → G) (z : G) (v : Fin (n + n) → ZMod 3) (c : ZMod 3) : G :=
  (List.ofFn fun j : Fin n => x j ^ (v (Fin.castAdd n j)).val).prod *
    (List.ofFn fun j : Fin n => y j ^ (v (Fin.natAdd n j)).val).prod * z ^ c.val

@[expose] def heisBasis (x y : Fin n → G) : Fin (n + n) → G := Fin.addCases x y

@[expose] def heisCocycle (v v' : Fin (n + n) → ZMod 3) : ZMod 3 :=
  2 * ∑ j : Fin n, v (Fin.natAdd n j) * v' (Fin.castAdd n j)

@[expose] def heisLoc (x y : Fin n → G) (v : Fin (n + n) → ZMod 3) (j : Fin n) : G :=
  x j ^ (v (Fin.castAdd n j)).val * y j ^ (v (Fin.natAdd n j)).val

theorem x_mem_heisSub (i : Fin n) : x i ∈ heisSub x y :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

theorem y_mem_heisSub (i : Fin n) : y i ∈ heisSub x y :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem heisBasis_castAdd (j : Fin n) : heisBasis x y (Fin.castAdd n j) = x j :=
  Fin.addCases_left j

theorem heisBasis_natAdd (j : Fin n) : heisBasis x y (Fin.natAdd n j) = y j :=
  Fin.addCases_right j

theorem heisBasis_mem (k : Fin (n + n)) : heisBasis x y k ∈ heisSub x y := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [heisBasis_castAdd]; exact x_mem_heisSub i
  · rw [heisBasis_natAdd]; exact y_mem_heisSub i

theorem castAdd_ne_natAdd (i j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n j := by
  intro e
  have := congrArg Fin.val e
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
  omega

theorem natAdd_ne_castAdd (j i : Fin n) : Fin.natAdd n j ≠ Fin.castAdd n i :=
  (castAdd_ne_natAdd i j).symm

theorem orderOf_z (h : HeisCfg 3 n x y z) : orderOf z = 3 :=
  orderOf_eq_prime h.zp h.z1

theorem z_mem (h : HeisCfg 3 n x y z) (hn : 0 < n) : z ∈ heisSub x y := by
  have h0 := h.yx ⟨0, hn⟩
  have : z = (x ⟨0, hn⟩)⁻¹ * ((y ⟨0, hn⟩)⁻¹ * x ⟨0, hn⟩ * y ⟨0, hn⟩) := by rw [h0]; group
  rw [this]
  exact mul_mem (inv_mem (x_mem_heisSub _))
    (mul_mem (mul_mem (inv_mem (y_mem_heisSub _)) (x_mem_heisSub _)) (y_mem_heisSub _))

theorem heisNF_mem (h : HeisCfg 3 n x y z) (hn : 0 < n) (v : Fin (n + n) → ZMod 3) (c : ZMod 3) :
    heisNF x y z v c ∈ heisSub x y := by
  unfold heisNF
  refine mul_mem (mul_mem (list_prod_mem fun a ha => ?_) (list_prod_mem fun a ha => ?_))
    (pow_mem (z_mem h hn) _)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    exact pow_mem (x_mem_heisSub j) _
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    exact pow_mem (y_mem_heisSub j) _

theorem heisNF_zero_left (c : ZMod 3) : heisNF x y z 0 c = z ^ c.val := by
  simp [heisNF]

theorem heisNF_add_right (hz3 : z ^ 3 = 1) (v : Fin (n + n) → ZMod 3) (c t : ZMod 3) :
    heisNF x y z v (c + t) = heisNF x y z v c * z ^ t.val := by
  unfold heisNF
  rw [pow_val_add hz3, ← mul_assoc]

theorem heisNF_single_x (i : Fin n) :
    heisNF x y z (Pi.single (Fin.castAdd n i) 1) 0 = x i := by
  unfold heisNF
  have h1 : (List.ofFn fun j : Fin n => x j ^
      ((Pi.single (Fin.castAdd n i) (1 : ZMod 3) : Fin (n + n) → ZMod 3)
        (Fin.castAdd n j)).val).prod = x i := by
    rw [list_prod_ofFn_eq_of_eq_one _ i]
    · simp only [Pi.single_eq_same, zmod3_val_one, pow_one]
    · intro j hj
      rw [Pi.single_eq_of_ne (fun e => hj (Fin.castAdd_injective _ _ e)), ZMod.val_zero, pow_zero]
  have h2 : (List.ofFn fun j : Fin n => y j ^
      ((Pi.single (Fin.castAdd n i) (1 : ZMod 3) : Fin (n + n) → ZMod 3)
        (Fin.natAdd n j)).val).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    rw [Pi.single_eq_of_ne (natAdd_ne_castAdd j i), ZMod.val_zero, pow_zero]
  rw [h1, h2]
  simp

theorem heisNF_single_y (i : Fin n) :
    heisNF x y z (Pi.single (Fin.natAdd n i) 1) 0 = y i := by
  unfold heisNF
  have h1 : (List.ofFn fun j : Fin n => x j ^
      ((Pi.single (Fin.natAdd n i) (1 : ZMod 3) : Fin (n + n) → ZMod 3)
        (Fin.castAdd n j)).val).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    rw [Pi.single_eq_of_ne (castAdd_ne_natAdd j i), ZMod.val_zero, pow_zero]
  have h2 : (List.ofFn fun j : Fin n => y j ^
      ((Pi.single (Fin.natAdd n i) (1 : ZMod 3) : Fin (n + n) → ZMod 3)
        (Fin.natAdd n j)).val).prod = y i := by
    rw [list_prod_ofFn_eq_of_eq_one _ i]
    · simp only [Pi.single_eq_same, zmod3_val_one, pow_one]
    · intro j hj
      rw [Pi.single_eq_of_ne (fun e => hj (Fin.natAdd_injective _ _ e)), ZMod.val_zero, pow_zero]
  rw [h1, h2]
  simp

theorem heisCfg_xy_same (h : HeisCfg 3 n x y z) (j : Fin n) : x j * y j = y j * x j * z := by
  calc x j * y j = y j * ((y j)⁻¹ * x j * y j) := by group
    _ = y j * (x j * z) := by rw [h.yx j]
    _ = y j * x j * z := by rw [mul_assoc]

theorem heisCfg_commute_z_x (h : HeisCfg 3 n x y z) (i : Fin n) : Commute z (x i) :=
  (h.zx i).symm

theorem heisCfg_commute_z_y (h : HeisCfg 3 n x y z) (i : Fin n) : Commute z (y i) :=
  (h.zy i).symm

theorem heisCfg_commute_z_loc (h : HeisCfg 3 n x y z) (v : Fin (n + n) → ZMod 3) (j : Fin n) :
    Commute z (heisLoc x y v j) :=
  Commute.mul_right ((heisCfg_commute_z_x h j).pow_right _)
    ((heisCfg_commute_z_y h j).pow_right _)

theorem heisCfg_commute_z_prod_loc (h : HeisCfg 3 n x y z) (v : Fin (n + n) → ZMod 3) :
    Commute z (List.ofFn (heisLoc x y v)).prod :=
  Commute.list_prod_right _ _ fun a ha => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    exact heisCfg_commute_z_loc h v j

theorem heisCfg_commute_loc (h : HeisCfg 3 n x y z) (w v : Fin (n + n) → ZMod 3) {i j : Fin n}
    (hij : i ≠ j) : Commute (heisLoc x y w i) (heisLoc x y v j) := by
  unfold heisLoc
  have hxx : Commute (x i) (x j) := h.xx i j
  have hyy : Commute (y i) (y j) := h.yy i j hij
  have hxy : Commute (x i) (y j) := h.xy i j hij
  have hyx : Commute (y i) (x j) := (h.xy j i hij.symm).symm
  exact Commute.mul_left (Commute.mul_right (hxx.pow_pow _ _) (hxy.pow_pow _ _))
    (Commute.mul_right (hyx.pow_pow _ _) (hyy.pow_pow _ _))

theorem heisNF_eq (h : HeisCfg 3 n x y z) (v : Fin (n + n) → ZMod 3) (c : ZMod 3) :
    heisNF x y z v c = (List.ofFn (heisLoc x y v)).prod * z ^ c.val := by
  unfold heisNF heisLoc
  rw [list_prod_ofFn_mul]
  intro i j hij
  exact Commute.pow_pow (h.xy j i hij.symm).symm _ _

theorem heisCfg_commute_z_heisNF (h : HeisCfg 3 n x y z) (v : Fin (n + n) → ZMod 3) (c : ZMod 3) :
    Commute z (heisNF x y z v c) := by
  rw [heisNF_eq h]
  exact Commute.mul_right (heisCfg_commute_z_prod_loc h v) ((Commute.refl z).pow_right _)

theorem heisNF_mul (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)
    (v v' : Fin (n + n) → ZMod 3) (c c' : ZMod 3) :
    heisNF x y z v c * heisNF x y z v' c' = heisNF x y z (v + v') (c + c' + heisCocycle v v') := by
  have hz3 := h.zp
  have hz23 : (z ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz3, one_pow]
  have e3 : ∀ s : ZMod 3, z ^ (2 * s).val = (z ^ 2) ^ s.val := fun s => by
    rw [pow_val_mul hz3, zmod3_val_two, pow_mul]
  have key : (List.ofFn (heisLoc x y v)).prod * (List.ofFn (heisLoc x y v')).prod =
      (List.ofFn (heisLoc x y (v + v'))).prod * z ^ (heisCocycle v v').val := by
    rw [list_prod_ofFn_mul _ _ fun i j hij => heisCfg_commute_loc h v' v hij]
    have e2 : (fun j => heisLoc x y v j * heisLoc x y v' j) = fun j =>
        heisLoc x y (v + v') j * (z ^ 2) ^ (v (Fin.natAdd n j) * v' (Fin.castAdd n j)).val := by
      funext j
      rw [← e3]
      unfold heisLoc
      exact local_mul (h.xp j) (hy3 j) hz3 (heisCfg_xy_same h j) (heisCfg_commute_z_x h j)
        (heisCfg_commute_z_y h j) _ _ _ _
    rw [e2, ← list_prod_ofFn_mul (heisLoc x y (v + v'))
      (fun j => (z ^ 2) ^ (v (Fin.natAdd n j) * v' (Fin.castAdd n j)).val)
      fun i j _ => ((heisCfg_commute_z_loc h _ j).pow_left 2).pow_left _,
      list_prod_ofFn_pow_val hz23, heisCocycle, e3]
  rw [heisNF_eq h, heisNF_eq h, heisNF_eq h]
  have hcomm : Commute (z ^ c.val) (List.ofFn (heisLoc x y v')).prod :=
    (heisCfg_commute_z_prod_loc h v').pow_left _
  calc (List.ofFn (heisLoc x y v)).prod * z ^ c.val *
        ((List.ofFn (heisLoc x y v')).prod * z ^ c'.val)
      = (List.ofFn (heisLoc x y v)).prod * (z ^ c.val * (List.ofFn (heisLoc x y v')).prod) *
          z ^ c'.val := by simp only [mul_assoc]
    _ = (List.ofFn (heisLoc x y v)).prod * ((List.ofFn (heisLoc x y v')).prod * z ^ c.val) *
          z ^ c'.val := by rw [hcomm.eq]
    _ = ((List.ofFn (heisLoc x y v)).prod * (List.ofFn (heisLoc x y v')).prod) * z ^ c.val *
          z ^ c'.val := by simp only [mul_assoc]
    _ = (List.ofFn (heisLoc x y (v + v'))).prod * z ^ (heisCocycle v v').val * z ^ c.val *
          z ^ c'.val := by rw [key]
    _ = (List.ofFn (heisLoc x y (v + v'))).prod *
          z ^ (c + c' + heisCocycle v v').val := by
        rw [show c + c' + heisCocycle v v' = heisCocycle v v' + c + c' by ring, pow_val_add hz3,
          pow_val_add hz3]
        simp only [mul_assoc]

theorem exists_heisNF_aux (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) :
    ∀ q ∈ heisSub x y, ∃ v c, q = heisNF x y z v c := by
  intro q hq
  unfold heisSub at hq
  induction hq using Subgroup.closure_induction with
  | mem q hq =>
    rcases hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨_, _, (heisNF_single_x i).symm⟩
    · exact ⟨_, _, (heisNF_single_y i).symm⟩
  | one => exact ⟨0, 0, by rw [heisNF_zero_left, ZMod.val_zero, pow_zero]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, c, rfl⟩ := ha
    obtain ⟨v', c', rfl⟩ := hb
    exact ⟨_, _, heisNF_mul h hy3 v v' c c'⟩
  | inv a _ ha =>
    obtain ⟨v, c, rfl⟩ := ha
    refine ⟨v + v, 2 * (c + heisCocycle v (v + v)), ?_⟩
    have h1 := heisNF_mul h hy3 v (v + v) c (2 * (c + heisCocycle v (v + v)))
    have h2 : v + (v + v) = 0 := by
      funext i
      exact zmod3_add_add_self (v i)
    rw [h2, zmod3_add_two_mul_add', heisNF_zero_left, ZMod.val_zero, pow_zero] at h1
    exact (eq_inv_of_mul_eq_one_right h1).symm

theorem exists_heisNF (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (_hn : 0 < n) :
    ∀ q ∈ heisSub x y, ∃ v c, q = heisNF x y z v c :=
  exists_heisNF_aux h hy3

theorem heisCocycle_single_natAdd_right (v : Fin (n + n) → ZMod 3) (j : Fin n) :
    heisCocycle v (Pi.single (Fin.natAdd n j) 1) = 0 := by
  unfold heisCocycle
  have : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      v (Fin.natAdd n k) * (Pi.single (Fin.natAdd n j) (1 : ZMod 3) : Fin (n + n) → ZMod 3)
        (Fin.castAdd n k) = 0 := fun k _ => by
    rw [Pi.single_eq_of_ne (castAdd_ne_natAdd k j), mul_zero]
  rw [Finset.sum_eq_zero this, mul_zero]

theorem heisCocycle_single_natAdd_left (j : Fin n) (v : Fin (n + n) → ZMod 3) :
    heisCocycle (Pi.single (Fin.natAdd n j) 1) v = 2 * v (Fin.castAdd n j) := by
  unfold heisCocycle
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_mul]
  · intro k _ hk
    rw [Pi.single_eq_of_ne (fun e => hk (Fin.natAdd_injective _ _ e)), zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem heisCocycle_single_castAdd_left (j : Fin n) (v : Fin (n + n) → ZMod 3) :
    heisCocycle (Pi.single (Fin.castAdd n j) 1) v = 0 := by
  unfold heisCocycle
  have : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      (Pi.single (Fin.castAdd n j) (1 : ZMod 3) : Fin (n + n) → ZMod 3) (Fin.natAdd n k) *
        v (Fin.castAdd n k) = 0 := fun k _ => by
    rw [Pi.single_eq_of_ne (natAdd_ne_castAdd k j), zero_mul]
  rw [Finset.sum_eq_zero this, mul_zero]

theorem heisCocycle_single_castAdd_right (v : Fin (n + n) → ZMod 3) (j : Fin n) :
    heisCocycle v (Pi.single (Fin.castAdd n j) 1) = 2 * v (Fin.natAdd n j) := by
  unfold heisCocycle
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro k _ hk
    rw [Pi.single_eq_of_ne (fun e => hk (Fin.castAdd_injective _ _ e)), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem comm_y (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (v : Fin (n + n) → ZMod 3)
    (c : ZMod 3) (j : Fin n) :
    heisNF x y z v c * y j * (heisNF x y z v c)⁻¹ * (y j)⁻¹ =
      z ^ (v (Fin.castAdd n j)).val := by
  have hz3 := h.zp
  have hy : y j = heisNF x y z (Pi.single (Fin.natAdd n j) 1) 0 := (heisNF_single_y j).symm
  have h1 : heisNF x y z v c * y j =
      heisNF x y z (v + Pi.single (Fin.natAdd n j) 1) c := by
    rw [hy, heisNF_mul h hy3, heisCocycle_single_natAdd_right]
    simp only [add_zero]
  have h2 : y j * heisNF x y z v c =
      heisNF x y z (v + Pi.single (Fin.natAdd n j) 1) (c + 2 * v (Fin.castAdd n j)) := by
    rw [hy, heisNF_mul h hy3, heisCocycle_single_natAdd_left,
      add_comm (Pi.single (Fin.natAdd n j) (1 : ZMod 3) : Fin (n + n) → ZMod 3) v]
    simp only [zero_add]
  have h3 : heisNF x y z (v + Pi.single (Fin.natAdd n j) 1) c =
      heisNF x y z (v + Pi.single (Fin.natAdd n j) 1) (c + 2 * v (Fin.castAdd n j)) *
        z ^ (v (Fin.castAdd n j)).val := by
    rw [← heisNF_add_right hz3, zmod3_add_two_mul_add]
  have key : heisNF x y z v c * y j = y j * heisNF x y z v c * z ^ (v (Fin.castAdd n j)).val := by
    rw [h1, h2]
    exact h3
  exact comm_eq_of_mul_eq ((heisCfg_commute_z_heisNF h v c).pow_left _)
    ((heisCfg_commute_z_y h j).pow_left _) key

theorem comm_x (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (v : Fin (n + n) → ZMod 3)
    (c : ZMod 3) (j : Fin n) :
    x j * heisNF x y z v c * (x j)⁻¹ * (heisNF x y z v c)⁻¹ =
      z ^ (v (Fin.natAdd n j)).val := by
  have hz3 := h.zp
  have hx : x j = heisNF x y z (Pi.single (Fin.castAdd n j) 1) 0 := (heisNF_single_x j).symm
  have h1 : x j * heisNF x y z v c =
      heisNF x y z (v + Pi.single (Fin.castAdd n j) 1) c := by
    rw [hx, heisNF_mul h hy3, heisCocycle_single_castAdd_left,
      add_comm (Pi.single (Fin.castAdd n j) (1 : ZMod 3) : Fin (n + n) → ZMod 3) v]
    simp only [zero_add, add_zero]
  have h2 : heisNF x y z v c * x j =
      heisNF x y z (v + Pi.single (Fin.castAdd n j) 1) (c + 2 * v (Fin.natAdd n j)) := by
    rw [hx, heisNF_mul h hy3, heisCocycle_single_castAdd_right]
    simp only [add_zero]
  have h3 : heisNF x y z (v + Pi.single (Fin.castAdd n j) 1) c =
      heisNF x y z (v + Pi.single (Fin.castAdd n j) 1) (c + 2 * v (Fin.natAdd n j)) *
        z ^ (v (Fin.natAdd n j)).val := by
    rw [← heisNF_add_right hz3, zmod3_add_two_mul_add]
  have key : x j * heisNF x y z v c = heisNF x y z v c * x j * z ^ (v (Fin.natAdd n j)).val := by
    rw [h1, h2]
    exact h3
  exact comm_eq_of_mul_eq ((heisCfg_commute_z_x h j).pow_left _)
    ((heisCfg_commute_z_heisNF h v c).pow_left _) key

theorem zpow_val_inj {z : G} (hz : orderOf z = 3) {a b : ZMod 3} (h : z ^ a.val = z ^ b.val) :
    a = b :=
  ZMod.val_injective 3 (pow_injOn_Iio_orderOf
    (by rw [Set.mem_Iio, hz]; exact ZMod.val_lt a) (by rw [Set.mem_Iio, hz]; exact ZMod.val_lt b) h)

@[expose] noncomputable def zlog (z g : G) : ZMod 3 :=
  open Classical in if hg : ∃ e : ZMod 3, z ^ e.val = g then hg.choose else 0

theorem zlog_pow {z : G} (hz : orderOf z = 3) (e : ZMod 3) : zlog z (z ^ e.val) = e := by
  have hex : ∃ e' : ZMod 3, z ^ e'.val = z ^ e.val := ⟨e, rfl⟩
  unfold zlog
  rw [dif_pos hex]
  exact zpow_val_inj hz hex.choose_spec

theorem zlog_one {z : G} (hz : orderOf z = 3) : zlog z 1 = 0 := by
  have := zlog_pow hz 0
  rwa [ZMod.val_zero, pow_zero] at this

theorem mem_zpowers_iff_exists_val {z : G} (hz : orderOf z = 3) {g : G} :
    g ∈ Subgroup.zpowers z ↔ ∃ e : ZMod 3, z ^ e.val = g := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨(k : ZMod 3), ?_⟩
    have h1 : (((k : ZMod 3).val : ℕ) : ℤ) = k % 3 := ZMod.val_intCast k
    have h2 : z ^ (k % (3 : ℤ)) = z ^ k := by
      have := zpow_mod_orderOf z k
      rwa [hz, Nat.cast_ofNat] at this
    rw [← zpow_natCast, h1, h2]
  · rintro ⟨e, rfl⟩
    exact (Subgroup.zpowers z).pow_mem (Subgroup.mem_zpowers z) _

@[expose] noncomputable def heisCoordFun (x y : Fin n → G) (z q : G) : Fin (n + n) → ZMod 3 :=
  Fin.addCases (motive := fun _ => ZMod 3) (fun j => zlog z (q * y j * q⁻¹ * (y j)⁻¹))
    fun j => zlog z (x j * q * (x j)⁻¹ * q⁻¹)

theorem heisCoordFun_castAdd (q : G) (j : Fin n) :
    heisCoordFun x y z q (Fin.castAdd n j) = zlog z (q * y j * q⁻¹ * (y j)⁻¹) :=
  Fin.addCases_left j

theorem heisCoordFun_natAdd (q : G) (j : Fin n) :
    heisCoordFun x y z q (Fin.natAdd n j) = zlog z (x j * q * (x j)⁻¹ * q⁻¹) :=
  Fin.addCases_right j

theorem heisCoordFun_heisNF (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)
    (v : Fin (n + n) → ZMod 3) (c : ZMod 3) : heisCoordFun x y z (heisNF x y z v c) = v := by
  have hz := orderOf_z h
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [heisCoordFun_castAdd, comm_y h hy3, zlog_pow hz]
  · rw [heisCoordFun_natAdd, comm_x h hy3, zlog_pow hz]

theorem heisNF_inj (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)
    {v v' : Fin (n + n) → ZMod 3} {c c' : ZMod 3}
    (e : heisNF x y z v c = heisNF x y z v' c') : v = v' ∧ c = c' := by
  have hv : v = v' := by
    have := congrArg (heisCoordFun x y z) e
    rwa [heisCoordFun_heisNF h hy3, heisCoordFun_heisNF h hy3] at this
  subst hv
  refine ⟨rfl, zpow_val_inj (orderOf_z h) ?_⟩
  unfold heisNF at e
  exact mul_left_cancel e

theorem heisCoordFun_one (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) :
    heisCoordFun x y z 1 = 0 := by
  have : (1 : G) = heisNF x y z 0 0 := by rw [heisNF_zero_left, ZMod.val_zero, pow_zero]
  rw [this, heisCoordFun_heisNF h hy3]

theorem heisCoordFun_mul (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q q' : G}
    (hq : q ∈ heisSub x y) (hq' : q' ∈ heisSub x y) :
    heisCoordFun x y z (q * q') = heisCoordFun x y z q + heisCoordFun x y z q' := by
  obtain ⟨v, c, rfl⟩ := exists_heisNF_aux h hy3 q hq
  obtain ⟨v', c', rfl⟩ := exists_heisNF_aux h hy3 q' hq'
  rw [heisNF_mul h hy3, heisCoordFun_heisNF h hy3, heisCoordFun_heisNF h hy3,
    heisCoordFun_heisNF h hy3]

theorem heisCoordFun_eq_zero_iff (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q : G}
    (hq : q ∈ heisSub x y) : heisCoordFun x y z q = 0 ↔ q ∈ Subgroup.zpowers z := by
  obtain ⟨v, c, rfl⟩ := exists_heisNF_aux h hy3 q hq
  rw [heisCoordFun_heisNF h hy3]
  constructor
  · intro h0
    rw [h0, heisNF_zero_left]
    exact (Subgroup.zpowers z).pow_mem (Subgroup.mem_zpowers z) _
  · intro h1
    obtain ⟨e, he⟩ := (mem_zpowers_iff_exists_val (orderOf_z h)).1 h1
    have e1 : heisNF x y z v c = heisNF x y z 0 e := by rw [heisNF_zero_left, he]
    calc v = heisCoordFun x y z (heisNF x y z v c) := (heisCoordFun_heisNF h hy3 v c).symm
      _ = heisCoordFun x y z (heisNF x y z 0 e) := by rw [e1]
      _ = 0 := heisCoordFun_heisNF h hy3 0 e

@[expose] noncomputable def heisCoord (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) :
    ↥(heisSub x y) →* Multiplicative (Fin (n + n) → ZMod 3) where
  toFun q := Multiplicative.ofAdd (heisCoordFun x y z q.1)
  map_one' := by
    show Multiplicative.ofAdd (heisCoordFun x y z 1) = 1
    rw [heisCoordFun_one h hy3]
    rfl
  map_mul' q q' := by
    show Multiplicative.ofAdd (heisCoordFun x y z (q.1 * q'.1)) =
      Multiplicative.ofAdd (heisCoordFun x y z q.1) * Multiplicative.ofAdd (heisCoordFun x y z q'.1)
    rw [heisCoordFun_mul h hy3 q.2 q'.2]
    rfl

theorem heisCoord_eq_one_iff (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1)
    (q : ↥(heisSub x y)) : heisCoord h hy3 q = 1 ↔ (q : G) ∈ Subgroup.zpowers z := by
  rw [← heisCoordFun_eq_zero_iff h hy3 q.2]
  exact ⟨fun h1 => congrArg Multiplicative.toAdd h1, fun h1 => congrArg Multiplicative.ofAdd h1⟩

theorem heisCoord_surjective (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (hn : 0 < n) :
    Function.Surjective (heisCoord h hy3) := fun w =>
  ⟨⟨heisNF x y z (Multiplicative.toAdd w) 0, heisNF_mem h hn _ _⟩,
    congrArg Multiplicative.ofAdd (heisCoordFun_heisNF h hy3 _ _)⟩

@[expose] noncomputable def heisCoordG (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (q : G) :
    Fin (n + n) → ZMod 3 :=
  open Classical in
  if hq : q ∈ heisSub x y then Multiplicative.toAdd (heisCoord h hy3 ⟨q, hq⟩) else 0

theorem heisCoordG_of_mem (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q : G}
    (hq : q ∈ heisSub x y) : heisCoordG h hy3 q = heisCoordFun x y z q := by
  unfold heisCoordG
  rw [dif_pos hq]
  rfl

theorem heisCoordG_mul (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q q' : G}
    (hq : q ∈ heisSub x y) (hq' : q' ∈ heisSub x y) :
    heisCoordG h hy3 (q * q') = heisCoordG h hy3 q + heisCoordG h hy3 q' := by
  rw [heisCoordG_of_mem h hy3 (mul_mem hq hq'), heisCoordG_of_mem h hy3 hq,
    heisCoordG_of_mem h hy3 hq']
  exact heisCoordFun_mul h hy3 hq hq'

theorem heisCoordG_one (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) :
    heisCoordG h hy3 1 = 0 := by
  rw [heisCoordG_of_mem h hy3 (one_mem _), heisCoordFun_one h hy3]

theorem heisCoordG_pow (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q : G}
    (hq : q ∈ heisSub x y) (k : ℕ) : heisCoordG h hy3 (q ^ k) = k • heisCoordG h hy3 q := by
  induction k with
  | zero => rw [pow_zero, heisCoordG_one h hy3, zero_nsmul]
  | succ k ih =>
    rw [pow_succ, heisCoordG_mul h hy3 (pow_mem hq k) hq, ih, succ_nsmul]

theorem heisCoordG_inv_add (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q : G}
    (hq : q ∈ heisSub x y) : heisCoordG h hy3 q⁻¹ + heisCoordG h hy3 q = 0 := by
  rw [← heisCoordG_mul h hy3 (inv_mem hq) hq, inv_mul_cancel, heisCoordG_one h hy3]

theorem heisCoordG_conj_of_mem (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q b : G}
    (hq : q ∈ heisSub x y) (hb : b ∈ heisSub x y) :
    heisCoordG h hy3 (q * b * q⁻¹) = heisCoordG h hy3 b := by
  rw [heisCoordG_mul h hy3 (mul_mem hq hb) (inv_mem hq), heisCoordG_mul h hy3 hq hb,
    add_comm (heisCoordG h hy3 q) (heisCoordG h hy3 b), add_assoc, add_comm (heisCoordG h hy3 q),
    heisCoordG_inv_add h hy3 hq, add_zero]

theorem heisCoordG_heisNF (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (hn : 0 < n)
    (v : Fin (n + n) → ZMod 3) (c : ZMod 3) : heisCoordG h hy3 (heisNF x y z v c) = v := by
  rw [heisCoordG_of_mem h hy3 (heisNF_mem h hn v c), heisCoordFun_heisNF h hy3]

theorem heisCoordG_x (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (i : Fin n) :
    heisCoordG h hy3 (x i) = Pi.single (Fin.castAdd n i) 1 := by
  rw [heisCoordG_of_mem h hy3 (x_mem_heisSub i), ← heisNF_single_x (x := x) (y := y) (z := z) i,
    heisCoordFun_heisNF h hy3]

theorem heisCoordG_y (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (i : Fin n) :
    heisCoordG h hy3 (y i) = Pi.single (Fin.natAdd n i) 1 := by
  rw [heisCoordG_of_mem h hy3 (y_mem_heisSub i), ← heisNF_single_y (x := x) (y := y) (z := z) i,
    heisCoordFun_heisNF h hy3]

theorem heisCoordG_basis (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (k : Fin (n + n)) :
    heisCoordG h hy3 (heisBasis x y k) = Pi.single k 1 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [heisBasis_castAdd, heisCoordG_x h hy3]
  · rw [heisBasis_natAdd, heisCoordG_y h hy3]

theorem heisCoordG_eq_zero_iff (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q : G}
    (hq : q ∈ heisSub x y) : heisCoordG h hy3 q = 0 ↔ q ∈ Subgroup.zpowers z := by
  rw [heisCoordG_of_mem h hy3 hq]
  exact heisCoordFun_eq_zero_iff h hy3 hq

theorem mem_zpowers_of_forall_commute (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) {q : G}
    (hq : q ∈ heisSub x y) (hc : ∀ i, q * x i = x i * q ∧ q * y i = y i * q) :
    q ∈ Subgroup.zpowers z := by
  rw [← heisCoordFun_eq_zero_iff h hy3 hq]
  have hz := orderOf_z h
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [heisCoordFun_castAdd]
    have : q * y j * q⁻¹ * (y j)⁻¹ = 1 := by rw [(hc j).2]; group
    rw [this, zlog_one hz]
    rfl
  · rw [heisCoordFun_natAdd]
    have : x j * q * (x j)⁻¹ * q⁻¹ = 1 := by rw [← (hc j).1]; group
    rw [this, zlog_one hz]
    rfl

theorem zpowers_le_heisSub (h : HeisCfg 3 n x y z) (hn : 0 < n) :
    Subgroup.zpowers z ≤ heisSub x y :=
  Subgroup.zpowers_le.2 (z_mem h hn)

theorem relIndex_zpowers_heisSub (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (hn : 0 < n) :
    (Subgroup.zpowers z).relIndex (heisSub x y) = 3 ^ (2 * n) := by
  have hker : (Subgroup.zpowers z).subgroupOf (heisSub x y) = (heisCoord h hy3).ker := by
    ext q
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, heisCoord_eq_one_iff h hy3]
  rw [Subgroup.relIndex, hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (heisCoord_surjective h hy3 hn), Subgroup.card_top,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin (n + n) → ZMod 3) ≃ _),
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, two_mul]

theorem card_heisSub (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (hn : 0 < n) :
    Nat.card (heisSub x y) = 3 ^ (2 * n + 1) := by
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers z) (K := heisSub x y)
  rw [inf_of_le_left (zpowers_le_heisSub h hn), Nat.card_zpowers, orderOf_z h,
    relIndex_zpowers_heisSub h hy3 hn] at h1
  rw [← h1, pow_succ]

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
