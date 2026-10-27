module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices
import all CFSG.LieType.Universal.SymplecticRoots
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic

public section

namespace CFSG.LieType.Universal.Symplectic.SpExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

section Block

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ}

def IsBlk (p q : κ) (M : Matrix κ κ F) : Prop :=
  ∀ a b, (a ≠ p ∧ a ≠ q) ∨ (b ≠ p ∧ b ≠ q) → M a b = (1 : Matrix κ κ F) a b

def toBlock (p q : κ) (M : Matrix κ κ F) : Matrix (Fin 2) (Fin 2) F :=
  !![M p p, M p q; M q p, M q q]

theorem mul_apply_blk (hpq : p ≠ q) {M N : Matrix κ κ F} (hM : IsBlk p q M) {a : κ}
    (ha : a = p ∨ a = q) (b : κ) : (M * N) a b = M a p * N p b + M a q * N q b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add p q hpq]
  · intro c _ ⟨hcp, hcq⟩
    have hac : a ≠ c := by
      rintro rfl
      rcases ha with rfl | rfl <;> contradiction
    rw [hM a c (Or.inr ⟨hcp, hcq⟩), Matrix.one_apply_ne hac, zero_mul]
  · simp
  · simp

omit [Fintype κ] in
theorem isBlk_one : IsBlk p q (1 : Matrix κ κ F) := fun _ _ _ => rfl

theorem isBlk_mul {M N : Matrix κ κ F} (hM : IsBlk p q M) (hN : IsBlk p q N) :
    IsBlk p q (M * N) := by
  intro a b hab
  rcases hab with hab | hab
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hM a a (Or.inl hab), Matrix.one_apply_eq, one_mul, hN a b (Or.inl hab)]
    · intro c _ hca
      rw [hM a c (Or.inl hab), Matrix.one_apply_ne (Ne.symm hca), zero_mul]
    · simp
  · rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [hN b b (Or.inr hab), Matrix.one_apply_eq, mul_one, hM a b (Or.inr hab)]
    · intro c _ hcb
      rw [hN c b (Or.inr hab), Matrix.one_apply_ne hcb, mul_zero]
    · simp

theorem toBlock_mul (hpq : p ≠ q) {M N : Matrix κ κ F} (hM : IsBlk p q M) :
    toBlock p q (M * N) = toBlock p q M * toBlock p q N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toBlock, Matrix.mul_apply, Fin.sum_univ_two, mul_apply_blk hpq hM (Or.inl rfl),
      mul_apply_blk hpq hM (Or.inr rfl)]

omit [Fintype κ] in
theorem toBlock_one (hpq : p ≠ q) : toBlock p q (1 : Matrix κ κ F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, hpq, hpq.symm]

omit [Fintype κ] in
theorem eq_of_toBlock_eq {M N : Matrix κ κ F} (hM : IsBlk p q M) (hN : IsBlk p q N)
    (h : toBlock p q M = toBlock p q N) : M = N := by
  ext a b
  by_cases ha : a = p ∨ a = q
  · by_cases hb : b = p ∨ b = q
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · simpa [toBlock] using congrFun (congrFun h 0) 0
      · simpa [toBlock] using congrFun (congrFun h 0) 1
      · simpa [toBlock] using congrFun (congrFun h 1) 0
      · simpa [toBlock] using congrFun (congrFun h 1) 1
    · rw [not_or] at hb
      rw [hM a b (Or.inr hb), hN a b (Or.inr hb)]
  · rw [not_or] at ha
    rw [hM a b (Or.inl ha), hN a b (Or.inl ha)]

omit [Fintype κ] in
theorem isBlk_transvection {a b : κ} (hab : (a = p ∧ b = q) ∨ (a = q ∧ b = p)) (c : F) :
    IsBlk p q (Matrix.transvection a b c) := by
  intro x y hxy
  have : ¬ (a = x ∧ b = y) := by
    rintro ⟨rfl, rfl⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      contradiction
  simp [Matrix.transvection, this]

omit [Fintype κ] in
theorem toBlock_transvection_pq (hpq : p ≠ q) (c : F) :
    toBlock p q (Matrix.transvection p q c) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, Matrix.transvection, hpq, hpq.symm]

omit [Fintype κ] in
theorem toBlock_transvection_qp (hpq : p ≠ q) (c : F) :
    toBlock p q (Matrix.transvection q p c) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, Matrix.transvection, hpq, hpq.symm]

omit [Fintype κ] in
theorem isBlk_diagonal {d : κ → F} (hd : ∀ a, a ≠ p → a ≠ q → d a = 1) :
    IsBlk p q (Matrix.diagonal d) := by
  intro a b hab
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [hd _ h1 h2]
  · simp [h]

omit [Fintype κ] in
theorem toBlock_diagonal (hpq : p ≠ q) (d : κ → F) :
    toBlock p q (Matrix.diagonal d) = !![d p, 0; 0, d q] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, hpq, hpq.symm]

end Block

section Generic

variable {L X Y H : Subgroup (StatedSp n F)} {w : StatedSp n F}
  {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F → Prop}
  {β : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F → Matrix (Fin 2) (Fin 2) F}

theorem bruhat_of_block
    (hPmul : ∀ M N, P M → P N → P (M * N))
    (hβmul : ∀ M N, P M → P N → β (M * N) = β M * β N)
    (hβinj : ∀ M N, P M → P N → β M = β N → M = N)
    (hL : ∀ g ∈ L, P (mat n F g) ∧ (β (mat n F g)).det = 1)
    (hX : ∀ c : F, ∃ u ∈ X, P (mat n F u) ∧ β (mat n F u) = !![1, c; 0, 1])
    (hH : ∀ t : Fˣ, ∃ h ∈ H, P (mat n F h) ∧ β (mat n F h) = !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)])
    (hw : P (mat n F w) ∧ β (mat n F w) = !![0, 1; -1, 0]) (g : StatedSp n F) (hg : g ∈ L) :
    (∃ h ∈ H, ∃ u ∈ X, g = h * u) ∨ ∃ u ∈ X, ∃ h ∈ H, ∃ v ∈ X, g = u * w * h * v := by
  obtain ⟨hPg, hdet⟩ := hL g hg
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨a, ha'⟩ : ∃ a, β (mat n F g) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, β (mat n F g) 0 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, β (mat n F g) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd'⟩ : ∃ d, β (mat n F g) 1 1 = d := ⟨_, rfl⟩
  rw [ha', hb', hc', hd'] at hdet
  have hβg : β (mat n F g) = !![a, b; c, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha', hb', hc', hd']
  by_cases hc : c = 0
  · left
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, hc] at hdet
      simp at hdet
    obtain ⟨h, hh, hPh, hβh⟩ := hH (Units.mk0 a ha)
    obtain ⟨u, hu, hPu, hβu⟩ := hX (b / a)
    refine ⟨h, hh, u, hu, mat_injective ?_⟩
    rw [map_mul]
    refine hβinj _ _ hPg (hPmul _ _ hPh hPu) ?_
    rw [hβmul _ _ hPh hPu, hβg, hβh, hβu]
    have hd : d = a⁻¹ := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    field_simp
  · right
    obtain ⟨u, hu, hPu, hβu⟩ := hX (a / c)
    obtain ⟨h, hh, hPh, hβh⟩ := hH (Units.mk0 (-c) (neg_ne_zero.mpr hc))
    obtain ⟨v, hv, hPv, hβv⟩ := hX (d / c)
    refine ⟨u, hu, h, hh, v, hv, mat_injective ?_⟩
    rw [map_mul, map_mul, map_mul]
    have h1 := hPmul _ _ hPu hw.1
    have h2 := hPmul _ _ h1 hPh
    refine hβinj _ _ hPg (hPmul _ _ h2 hPv) ?_
    rw [hβmul _ _ h2 hPv, hβmul _ _ h1 hPh, hβmul _ _ hPu hw.1, hβg, hβu, hw.2, hβh, hβv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · field_simp
    · field_simp
      linear_combination -hdet
    · field_simp

theorem eq_one_of_block (hP1 : P 1) (hβ1 : β 1 = 1)
    (hPmul : ∀ M N, P M → P N → P (M * N))
    (hβmul : ∀ M N, P M → P N → β (M * N) = β M * β N)
    (hβinj : ∀ M N, P M → P N → β M = β N → M = N)
    (hX : ∀ u ∈ X, ∃ c : F, P (mat n F u) ∧ β (mat n F u) = !![1, c; 0, 1])
    (hY : ∃ y ∈ Y, P (mat n F y) ∧ β (mat n F y) = !![1, 0; 1, 1])
    (hY' : ∀ y ∈ Y, ∃ c : F, P (mat n F y) ∧ β (mat n F y) = !![1, 0; c, 1])
    (u : StatedSp n F) (hu : u ∈ X) (hn : u ∈ Subgroup.normalizer (Y : Set (StatedSp n F))) :
    u = 1 := by
  obtain ⟨c, hPu, hβu⟩ := hX u hu
  obtain ⟨c', hPu', hβu'⟩ := hX u⁻¹ (inv_mem hu)
  have hcc' : c' = -c := by
    have h := hβmul _ _ hPu hPu'
    rw [← map_mul, mul_inv_cancel, map_one, hβ1, hβu, hβu'] at h
    have := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this
  obtain ⟨y, hy, hPy, hβy⟩ := hY
  have hz := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
  obtain ⟨d, hPz, hβz⟩ := hY' _ hz
  have hP1' := hPmul _ _ hPu hPy
  rw [map_mul, map_mul, hβmul _ _ hP1' hPu', hβmul _ _ hPu hPy, hβu, hβy, hβu', hcc'] at hβz
  have h00 := congrFun (congrFun hβz 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hc : c = 0 := by linear_combination h00
  apply mat_injective
  refine hβinj _ _ hPu (by rw [map_one]; exact hP1) ?_
  rw [hβu, map_one, hβ1, hc]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Generic

theorem rankOne_induction {k : Fin n} {C : StatedSp n F → Prop} {g : StatedSp n F}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k)
    (hpos : ∀ x ∈ rootGroup n F (Pi.single k 1), C x)
    (hneg : ∀ x ∈ rootGroup n F (-Pi.single k 1), C x)
    (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x * y)) : C g := by
  rw [CFSG.LieType.CurtisTits.rankOne, sup_eq_iSup] at hg
  refine Subgroup.iSup_induction _ hg (C := C) (fun b x hx => ?_) h1 hmul
  cases b
  · exact hneg x hx
  · exact hpos x hx

section Long

variable {k : Fin n}

theorem stdVec_positiveLong_eq (hk : ¬k.val + 1 < n) :
    stdVec (.positiveLong k) = toStd n (Pi.single k 1) := by
  rw [toStd_single_of_not_lt' hk]
  rfl

theorem stdVec_negativeLong_eq (hk : ¬k.val + 1 < n) :
    stdVec (.negativeLong k) = toStd n (-Pi.single k 1) := by
  rw [toStd_neg', toStd_single_of_not_lt' hk]
  rfl

theorem mat_elt_positiveLong (k : Fin n) (c : F) :
    mat n F (elt (.positiveLong k) c) = Matrix.transvection (.inl k) (.inr k) c := by
  rw [mat_elt, Matrix.transvection, E, Matrix.smul_single, smul_eq_mul, mul_one]

theorem mat_elt_negativeLong (k : Fin n) (c : F) :
    mat n F (elt (.negativeLong k) c) = Matrix.transvection (.inr k) (.inl k) c := by
  rw [mat_elt, Matrix.transvection, E, Matrix.smul_single, smul_eq_mul, mul_one]

theorem weylRep_eq_long (hk : ¬k.val + 1 < n) :
    weylRep n F k = elt (.positiveLong k) 1 * elt (.negativeLong k) (-1) *
      elt (.positiveLong k) 1 := by
  rw [weylRep_eq, weylElt_of_not_lt n F hk, positiveLongRootWeylElement]
  simp only [map_mul, elt, RootSubgroupIndex.hom_positiveLong,
    RootSubgroupIndex.hom_negativeLong, positiveLongRootTransvectionHom_apply,
    negativeLongRootTransvectionHom_apply, toAdd_ofAdd]

theorem torus_mat_long (hk : ¬k.val + 1 < n) (t : Fˣ) :
    IsBlk (.inl k) (.inr k)
        (mat n F (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k t)))) ∧
      toBlock (.inl k) (.inr k)
        (mat n F (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k t)))) =
        !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] := by
  rw [corootVec_of_not_lt n F hk, mat_equiv_diagonal]
  refine ⟨isBlk_diagonal fun a ha hb => ?_, ?_⟩
  · rcases a with i | i
    · have : i ≠ k := fun h => ha (by rw [h])
      simp [Pi.mulSingle_apply, this]
    · have : i ≠ k := fun h => hb (by rw [h])
      simp [Pi.mulSingle_apply, this]
  · rw [toBlock_diagonal Sum.inl_ne_inr]
    simp

theorem rankOne_long_mem (hk : ¬k.val + 1 < n) {g : StatedSp n F}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k) :
    IsBlk (.inl k) (.inr k) (mat n F g) ∧ (toBlock (.inl k) (.inr k) (mat n F g)).det = 1 := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  refine rankOne_induction hg (C := fun g => IsBlk (.inl k) (.inr k) (mat n F g) ∧
    (toBlock (.inl k) (.inr k) (mat n F g)).det = 1) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_positiveLong_eq hk)).1 hx
    rw [mat_elt_positiveLong]
    exact ⟨isBlk_transvection (Or.inl ⟨rfl, rfl⟩) c, by
      rw [toBlock_transvection_pq hpq, Matrix.det_fin_two_of]
      ring⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_negativeLong_eq hk)).1 hx
    rw [mat_elt_negativeLong]
    exact ⟨isBlk_transvection (Or.inr ⟨rfl, rfl⟩) c, by
      rw [toBlock_transvection_qp hpq, Matrix.det_fin_two_of]
      ring⟩
  · rw [map_one]
    exact ⟨isBlk_one, by rw [toBlock_one hpq, Matrix.det_one]⟩
  · intro x y hx hy
    rw [map_mul]
    exact ⟨isBlk_mul hx.1 hy.1, by rw [toBlock_mul hpq hx.1, Matrix.det_mul, hx.2, hy.2, one_mul]⟩

theorem weylRep_block_long (hk : ¬k.val + 1 < n) :
    IsBlk (.inl k) (.inr k) (mat n F (weylRep n F k)) ∧
      toBlock (.inl k) (.inr k) (mat n F (weylRep n F k)) = !![0, 1; -1, 0] := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  have h1 := isBlk_transvection (F := F) (p := (Sum.inl k : Fin n ⊕ Fin n)) (q := Sum.inr k)
    (Or.inl ⟨rfl, rfl⟩) 1
  have h2 := isBlk_transvection (F := F) (p := (Sum.inl k : Fin n ⊕ Fin n)) (q := Sum.inr k)
    (Or.inr ⟨rfl, rfl⟩) (-1)
  rw [weylRep_eq_long hk, map_mul, map_mul, mat_elt_positiveLong, mat_elt_negativeLong]
  refine ⟨isBlk_mul (isBlk_mul h1 h2) h1, ?_⟩
  rw [toBlock_mul hpq (isBlk_mul h1 h2), toBlock_mul hpq h1, toBlock_transvection_pq hpq,
    toBlock_transvection_qp hpq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rankOne_bruhat_long (hk : ¬k.val + 1 < n) (g : StatedSp n F)
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k) :
    (∃ h ∈ torus n F k, ∃ u ∈ rootGroup n F (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ rootGroup n F (Pi.single k 1), ∃ h ∈ torus n F k,
        ∃ v ∈ rootGroup n F (Pi.single k 1), g = u * weylRep n F k * h * v := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  refine bruhat_of_block (P := IsBlk (.inl k) (.inr k)) (β := toBlock (.inl k) (.inr k))
    (fun M N hM hN => isBlk_mul hM hN) (fun M N hM _ => toBlock_mul hpq hM)
    (fun M N hM hN h => eq_of_toBlock_eq hM hN h) (fun g hg => rankOne_long_mem hk hg)
    (fun c => ⟨elt (.positiveLong k) c, elt_mem_rootGroup (stdVec_positiveLong_eq hk) c, ?_⟩)
    (fun t => ⟨_, diagonal_mem_torus n F k t, torus_mat_long hk t⟩) (weylRep_block_long hk) g hg
  rw [mat_elt_positiveLong]
  exact ⟨isBlk_transvection (Or.inl ⟨rfl, rfl⟩) c, toBlock_transvection_pq hpq c⟩

theorem eq_one_of_mem_normalizer_long (hk : ¬k.val + 1 < n) (u : StatedSp n F)
    (hu : u ∈ rootGroup n F (Pi.single k 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup n F (-Pi.single k 1) : Set (StatedSp n F))) :
    u = 1 := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  refine eq_one_of_block (P := IsBlk (.inl k) (.inr k)) (β := toBlock (.inl k) (.inr k))
    isBlk_one (toBlock_one hpq) (fun M N hM hN => isBlk_mul hM hN)
    (fun M N hM _ => toBlock_mul hpq hM) (fun M N hM hN h => eq_of_toBlock_eq hM hN h)
    (fun x hx => ?_) ⟨elt (.negativeLong k) 1, elt_mem_rootGroup (stdVec_negativeLong_eq hk) 1, ?_⟩
    (fun y hy => ?_) u hu hn
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_positiveLong_eq hk)).1 hx
    rw [mat_elt_positiveLong]
    exact ⟨c, isBlk_transvection (Or.inl ⟨rfl, rfl⟩) c, toBlock_transvection_pq hpq c⟩
  · rw [mat_elt_negativeLong]
    exact ⟨isBlk_transvection (Or.inr ⟨rfl, rfl⟩) 1, toBlock_transvection_qp hpq 1⟩
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_negativeLong_eq hk)).1 hy
    rw [mat_elt_negativeLong]
    exact ⟨c, isBlk_transvection (Or.inr ⟨rfl, rfl⟩) c, toBlock_transvection_qp hpq c⟩

end Long

section Short

variable {k : Fin n}

theorem stdVec_shortPos_eq (hk : k.val + 1 < n) :
    stdVec (.difference k ⟨k.val + 1, hk⟩ (ne_succ' hk)) = toStd n (Pi.single k 1) := by
  rw [toStd_single_of_lt' hk]
  rfl

theorem stdVec_shortNeg_eq (hk : k.val + 1 < n) :
    stdVec (.difference ⟨k.val + 1, hk⟩ k (ne_succ' hk).symm) = toStd n (-Pi.single k 1) := by
  rw [toStd_neg', toStd_single_of_lt' hk, neg_sub]
  rfl

theorem elt_difference_eq_leviHom {i j : Fin n} (hij : i ≠ j) (c : F) :
    elt (.difference i j hij) c = equivStatedSp n F (leviHom (TauCeti.transvectionUnit hij c)) := by
  rw [elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd,
    ← leviHom_transvection, TauCeti.toGL_transvection_eq_transvectionUnit]

theorem mat_equiv_leviHom (A : GL (Fin n) F) :
    mat n F (equivStatedSp n F (leviHom A)) =
      fromBlocks (A : Matrix (Fin n) (Fin n) F) 0 0
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := by
  rw [mat_equivStatedSp, coe_leviHom, Matrix.submatrix_submatrix]
  simp

def PShort (k k' : Fin n) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  ∃ A : GL (Fin n) F, IsBlk k k' (A : Matrix (Fin n) (Fin n) F) ∧
    M = mat n F (equivStatedSp n F (leviHom A))

theorem toBlock_mat_leviHom (k k' : Fin n) (A : GL (Fin n) F) :
    toBlock (.inl k) (.inl k') (mat n F (equivStatedSp n F (leviHom A))) =
      toBlock k k' (A : Matrix (Fin n) (Fin n) F) := by
  rw [mat_equiv_leviHom]
  rfl

theorem pShort_mul {k k' : Fin n} {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hM : PShort k k' M) (hN : PShort k k' N) : PShort k k' (M * N) := by
  obtain ⟨A, hA, rfl⟩ := hM
  obtain ⟨B, hB, rfl⟩ := hN
  refine ⟨A * B, by rw [Units.val_mul]; exact isBlk_mul hA hB, ?_⟩
  rw [map_mul, map_mul, map_mul]

theorem toBlock_mul_short {k k' : Fin n} (hkk' : k ≠ k')
    {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hM : PShort k k' M) (hN : PShort k k' N) :
    toBlock (.inl k) (.inl k') (M * N) =
      toBlock (.inl k) (.inl k') M * toBlock (.inl k) (.inl k') N := by
  obtain ⟨A, hA, rfl⟩ := hM
  obtain ⟨B, hB, rfl⟩ := hN
  rw [← map_mul, ← map_mul, ← map_mul, toBlock_mat_leviHom, toBlock_mat_leviHom,
    toBlock_mat_leviHom, Units.val_mul, toBlock_mul hkk' hA]

theorem eq_of_toBlock_eq_short {k k' : Fin n} {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hM : PShort k k' M) (hN : PShort k k' N)
    (h : toBlock (.inl k) (.inl k') M = toBlock (.inl k) (.inl k') N) : M = N := by
  obtain ⟨A, hA, rfl⟩ := hM
  obtain ⟨B, hB, rfl⟩ := hN
  rw [toBlock_mat_leviHom, toBlock_mat_leviHom] at h
  rw [Units.ext (eq_of_toBlock_eq hA hB h)]

theorem pShort_one (k k' : Fin n) : PShort k k' (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
  ⟨1, isBlk_one, by rw [map_one, map_one, map_one]⟩

theorem pShort_elt {k k' : Fin n} (hkk' : k ≠ k') (c : F) :
    PShort k k' (mat n F (elt (.difference k k' hkk') c)) ∧
      toBlock (.inl k) (.inl k') (mat n F (elt (.difference k k' hkk') c)) = !![1, c; 0, 1] := by
  rw [elt_difference_eq_leviHom]
  refine ⟨⟨_, ?_, rfl⟩, ?_⟩
  · rw [TauCeti.coe_transvectionUnit]
    exact isBlk_transvection (Or.inl ⟨rfl, rfl⟩) c
  · rw [toBlock_mat_leviHom, TauCeti.coe_transvectionUnit, toBlock_transvection_pq hkk']

theorem pShort_elt' {k k' : Fin n} (hkk' : k ≠ k') (c : F) :
    PShort k k' (mat n F (elt (.difference k' k hkk'.symm) c)) ∧
      toBlock (.inl k) (.inl k') (mat n F (elt (.difference k' k hkk'.symm) c)) =
        !![1, 0; c, 1] := by
  rw [elt_difference_eq_leviHom]
  refine ⟨⟨_, ?_, rfl⟩, ?_⟩
  · rw [TauCeti.coe_transvectionUnit]
    exact isBlk_transvection (Or.inr ⟨rfl, rfl⟩) c
  · rw [toBlock_mat_leviHom, TauCeti.coe_transvectionUnit, toBlock_transvection_qp hkk']

theorem weylRep_eq_short (hk : k.val + 1 < n) :
    weylRep n F k = elt (.difference k ⟨k.val + 1, hk⟩ (ne_succ' hk)) 1 *
      elt (.difference ⟨k.val + 1, hk⟩ k (ne_succ' hk).symm) (-1) *
      elt (.difference k ⟨k.val + 1, hk⟩ (ne_succ' hk)) 1 := by
  rw [weylRep_eq, weylElt_of_lt n F hk, differenceShortRootWeylElement]
  simp only [map_mul, elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply,
    toAdd_ofAdd]

theorem torus_mat_short (hk : k.val + 1 < n) (t : Fˣ) :
    PShort k ⟨k.val + 1, hk⟩
        (mat n F (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k t)))) ∧
      toBlock (.inl k) (.inl ⟨k.val + 1, hk⟩)
        (mat n F (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k t)))) =
        !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] := by
  have hkk' := ne_succ' hk
  have hdiag : TauCeti.GLSymplecticFin.diagonal (corootVec n F k t) =
      leviHom (TauCeti.diagGL (corootVec n F k t)) := rfl
  rw [hdiag]
  refine ⟨⟨_, ?_, rfl⟩, ?_⟩
  · rw [TauCeti.diagGL_coe]
    refine isBlk_diagonal fun a ha hb => ?_
    rw [corootVec_of_lt n F hk]
    simp [ha, hb]
  · rw [toBlock_mat_leviHom, TauCeti.diagGL_coe, toBlock_diagonal hkk', corootVec_of_lt n F hk]
    simp [hkk'.symm]

theorem rankOne_short_mem (hk : k.val + 1 < n) {g : StatedSp n F}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k) :
    PShort k ⟨k.val + 1, hk⟩ (mat n F g) ∧
      (toBlock (.inl k) (.inl ⟨k.val + 1, hk⟩) (mat n F g)).det = 1 := by
  have hkk' := ne_succ' hk
  refine rankOne_induction hg (C := fun g => PShort k ⟨k.val + 1, hk⟩ (mat n F g) ∧
    (toBlock (.inl k) (.inl ⟨k.val + 1, hk⟩) (mat n F g)).det = 1) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_shortPos_eq hk)).1 hx
    obtain ⟨h1, h2⟩ := pShort_elt hkk' c
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.det_fin_two_of]
    ring
  · intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_shortNeg_eq hk)).1 hx
    obtain ⟨h1, h2⟩ := pShort_elt' hkk' c
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.det_fin_two_of]
    ring
  · rw [map_one]
    exact ⟨pShort_one _ _, by rw [toBlock_one (Sum.inl_injective.ne hkk'), Matrix.det_one]⟩
  · intro x y hx hy
    rw [map_mul]
    exact ⟨pShort_mul hx.1 hy.1, by
      rw [toBlock_mul_short hkk' hx.1 hy.1, Matrix.det_mul, hx.2, hy.2, one_mul]⟩

theorem weylRep_block_short (hk : k.val + 1 < n) :
    PShort k ⟨k.val + 1, hk⟩ (mat n F (weylRep n F k)) ∧
      toBlock (.inl k) (.inl ⟨k.val + 1, hk⟩) (mat n F (weylRep n F k)) = !![0, 1; -1, 0] := by
  have hkk' := ne_succ' hk
  obtain ⟨p1, b1⟩ := pShort_elt (F := F) hkk' 1
  obtain ⟨p2, b2⟩ := pShort_elt' (F := F) hkk' (-1)
  rw [weylRep_eq_short hk, map_mul, map_mul]
  refine ⟨pShort_mul (pShort_mul p1 p2) p1, ?_⟩
  rw [toBlock_mul_short hkk' (pShort_mul p1 p2) p1, toBlock_mul_short hkk' p1 p2, b1, b2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rankOne_bruhat_short (hk : k.val + 1 < n) (g : StatedSp n F)
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k) :
    (∃ h ∈ torus n F k, ∃ u ∈ rootGroup n F (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ rootGroup n F (Pi.single k 1), ∃ h ∈ torus n F k,
        ∃ v ∈ rootGroup n F (Pi.single k 1), g = u * weylRep n F k * h * v := by
  have hkk' := ne_succ' hk
  exact bruhat_of_block (P := PShort k ⟨k.val + 1, hk⟩)
    (β := toBlock (.inl k) (.inl ⟨k.val + 1, hk⟩))
    (fun M N hM hN => pShort_mul hM hN) (fun M N hM hN => toBlock_mul_short hkk' hM hN)
    (fun M N hM hN h => eq_of_toBlock_eq_short hM hN h) (fun g hg => rankOne_short_mem hk hg)
    (fun c => ⟨_, elt_mem_rootGroup (stdVec_shortPos_eq hk) c, pShort_elt hkk' c⟩)
    (fun t => ⟨_, diagonal_mem_torus n F k t, torus_mat_short hk t⟩) (weylRep_block_short hk) g hg

theorem eq_one_of_mem_normalizer_short (hk : k.val + 1 < n) (u : StatedSp n F)
    (hu : u ∈ rootGroup n F (Pi.single k 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup n F (-Pi.single k 1) : Set (StatedSp n F))) :
    u = 1 := by
  have hkk' := ne_succ' hk
  refine eq_one_of_block (P := PShort k ⟨k.val + 1, hk⟩)
    (β := toBlock (.inl k) (.inl ⟨k.val + 1, hk⟩))
    (pShort_one _ _) (toBlock_one (Sum.inl_injective.ne hkk')) (fun M N hM hN => pShort_mul hM hN)
    (fun M N hM hN => toBlock_mul_short hkk' hM hN)
    (fun M N hM hN h => eq_of_toBlock_eq_short hM hN h) (fun x hx => ?_)
    ⟨_, elt_mem_rootGroup (stdVec_shortNeg_eq hk) 1, pShort_elt' hkk' 1⟩ (fun y hy => ?_) u hu hn
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_shortPos_eq hk)).1 hx
    exact ⟨c, pShort_elt hkk' c⟩
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_shortNeg_eq hk)).1 hy
    exact ⟨c, pShort_elt' hkk' c⟩

end Short

theorem rankOne_bruhat (k : Fin n) (g : StatedSp n F)
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k) :
    (∃ h ∈ torus n F k, ∃ u ∈ rootGroup n F (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ rootGroup n F (Pi.single k 1), ∃ h ∈ torus n F k,
        ∃ v ∈ rootGroup n F (Pi.single k 1), g = u * weylRep n F k * h * v := by
  by_cases hk : k.val + 1 < n
  · exact rankOne_bruhat_short hk g hg
  · exact rankOne_bruhat_long hk g hg

theorem eq_one_of_mem_normalizer (k : Fin n) (u : StatedSp n F)
    (hu : u ∈ rootGroup n F (Pi.single k 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup n F (-Pi.single k 1) : Set (StatedSp n F))) :
    u = 1 := by
  by_cases hk : k.val + 1 < n
  · exact eq_one_of_mem_normalizer_short hk u hu hn
  · exact eq_one_of_mem_normalizer_long hk u hu hn

end CFSG.LieType.Universal.Symplectic.SpExtras
