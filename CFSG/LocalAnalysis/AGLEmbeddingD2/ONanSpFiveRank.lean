module

public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.AGLEmbeddingD2.SpFive

open Matrix CFSG.LieType.SteinbergBR.EvenSp CFSG.Assembly.LowTwoRank CFSG.Open

section Embed

variable {K : Type*} [CommRing K] {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
  [DecidableEq X]

open Classical in
@[expose] noncomputable def embedEquiv (c : X → I) (hc : Function.Injective c) :
    X ⊕ ↥(Set.range c)ᶜ ≃ I :=
  (Equiv.sumCongr (Equiv.ofInjective c hc) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range c))

omit [Fintype I] [DecidableEq X] in
theorem embedEquiv_inl (c : X → I) (hc : Function.Injective c) (x : X) :
    embedEquiv c hc (Sum.inl x) = c x := by
  simp [embedEquiv]

omit [Fintype I] [DecidableEq X] in
theorem embedEquiv_inr (c : X → I) (hc : Function.Injective c) (y : ↥(Set.range c)ᶜ) :
    embedEquiv c hc (Sum.inr y) = y.1 := by
  simp [embedEquiv]

@[expose] noncomputable def embedMat (c : X → I) (hc : Function.Injective c) (N : Matrix X X K) :
    Matrix I I K :=
  Matrix.reindexAlgEquiv K K (embedEquiv c hc) (fromBlocks N 0 0 1)

theorem embedMat_mul (c : X → I) (hc : Function.Injective c) (N N' : Matrix X X K) :
    embedMat c hc (N * N') = embedMat c hc N * embedMat c hc N' := by
  unfold embedMat
  rw [← map_mul, fromBlocks_multiply]
  simp

theorem embedMat_one (c : X → I) (hc : Function.Injective c) :
    embedMat c hc (1 : Matrix X X K) = 1 := by
  unfold embedMat
  rw [fromBlocks_one]
  exact map_one _

theorem embedMat_injective (c : X → I) (hc : Function.Injective c) :
    Function.Injective (embedMat (K := K) c hc) := by
  intro N N' h
  have h1 := (Matrix.reindexAlgEquiv K K (embedEquiv c hc)).injective h
  have h2 := congrArg Matrix.toBlocks₁₁ h1
  simpa using h2

theorem reindexAlgEquiv_transpose' {R : Type*} [Fintype R] [DecidableEq R]
    (e : R ≃ I) (P : Matrix R R K) :
    (Matrix.reindexAlgEquiv K K e P)ᵀ = Matrix.reindexAlgEquiv K K e Pᵀ := by
  simp [Matrix.coe_reindexAlgEquiv]

theorem embedMat_symplectic (c : X → I) (hc : Function.Injective c) (J : Matrix I I K)
    (hJ : ∀ (x : X) (y : ↥(Set.range c)ᶜ), J (c x) y.1 = 0 ∧ J y.1 (c x) = 0)
    {N : Matrix X X K} (hN : Nᵀ * J.submatrix c c * N = J.submatrix c c) :
    (embedMat c hc N)ᵀ * J * embedMat c hc N = J := by
  have hJ' : J = Matrix.reindexAlgEquiv K K (embedEquiv c hc)
      (fromBlocks (J.submatrix c c) 0 0
        (J.submatrix (fun y : ↥(Set.range c)ᶜ => y.1) (fun y => y.1))) := by
    ext a b
    obtain ⟨u, rfl⟩ := (embedEquiv c hc).surjective a
    obtain ⟨w, rfl⟩ := (embedEquiv c hc).surjective b
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]
    rcases u with x | y <;> rcases w with x' | y' <;>
      simp [embedEquiv_inl, embedEquiv_inr, (hJ _ _).1, (hJ _ _).2]
  set Jb : Matrix (X ⊕ ↥(Set.range c)ᶜ) (X ⊕ ↥(Set.range c)ᶜ) K :=
    fromBlocks (J.submatrix c c) 0 0
      (J.submatrix (fun y : ↥(Set.range c)ᶜ => y.1) (fun y => y.1)) with hJb
  have hM : fromBlocks Nᵀ 0 0 1 * Jb * fromBlocks N 0 0 1 = Jb := by
    rw [hJb, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, hN]
  have key : (embedMat c hc N)ᵀ * Matrix.reindexAlgEquiv K K (embedEquiv c hc) Jb *
      embedMat c hc N = Matrix.reindexAlgEquiv K K (embedEquiv c hc)
        (fromBlocks Nᵀ 0 0 1 * Jb * fromBlocks N 0 0 1) := by
    unfold embedMat
    rw [reindexAlgEquiv_transpose', ← map_mul, ← map_mul, fromBlocks_transpose]
    simp
  rw [← hJ', hM] at key
  exact key.trans hJ'.symm

end Embed

section Instance

@[expose] def A2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 0, 1, 1; 1, 1, 0, 1; 1, 0, 1, 1]

@[expose] def J2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem A2_symp : A2ᵀ * J2 * A2 = J2 := by decide +kernel

theorem A2_pow : A2 ^ 5 = 1 := by decide +kernel

variable (K : Type) [Field K] [CharP K 2]

@[expose] def f2 : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

@[expose] def AK : Matrix (Fin 4) (Fin 4) K := A2.map (f2 K)

@[expose] def J4 : Matrix (Fin 4) (Fin 4) K := J2.map (f2 K)

theorem AK_symp : (AK K)ᵀ * J4 K * AK K = J4 K := by
  have := congrArg (RingHom.mapMatrix (f2 K)) A2_symp
  simpa [AK, J4, RingHom.mapMatrix_apply, Matrix.transpose_map, Matrix.map_mul] using this

theorem AK_pow : AK K ^ 5 = 1 := by
  have := congrArg (RingHom.mapMatrix (f2 K)) A2_pow
  simpa [AK, RingHom.mapMatrix_apply, map_pow] using this

theorem AK_ne : AK K ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 3
  simp [AK, A2, f2] at this

theorem orderOf_AK : orderOf (AK K) = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  orderOf_eq_prime (AK_pow K) (AK_ne K)

theorem AK_pow_symp (m : ℕ) : (AK K ^ m)ᵀ * J4 K * AK K ^ m = J4 K := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc (AK K ^ (m + 1))ᵀ * J4 K * AK K ^ (m + 1)
        = (AK K)ᵀ * ((AK K ^ m)ᵀ * J4 K * AK K ^ m) * AK K := by
          rw [pow_succ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = J4 K := by rw [ih, AK_symp K]

end Instance

section Blocks

variable {k : ℕ} (K : Type) [Field K] [CharP K 2]

@[expose] def blkIdx (hk : 6 ≤ k) (p : Fin 4 × Fin 3) : Fin k ⊕ Fin k :=
  if h : p.1.1 < 2 then Sum.inl ⟨2 * p.2.1 + p.1.1, by have := p.2.2; omega⟩
  else Sum.inr ⟨2 * p.2.1 + (p.1.1 - 2), by have := p.2.2; have := p.1.2; omega⟩

theorem blkIdx_injective (hk : 6 ≤ k) : Function.Injective (blkIdx hk) := by
  rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ ⟨⟨r', hr'⟩, ⟨i', hi'⟩⟩ h
  simp only [blkIdx] at h
  split_ifs at h with h1 h2 h2 <;> simp at h ⊢ <;> omega

theorem Jk_submatrix (hk : 6 ≤ k) :
    (fromBlocks (0 : Matrix (Fin k) (Fin k) K) 1 (-1) 0).submatrix (blkIdx hk) (blkIdx hk) =
      Matrix.blockDiagonal (fun _ : Fin 3 => J4 K) := by
  ext ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ ⟨⟨s, hs⟩, ⟨j, hj⟩⟩
  rw [Matrix.blockDiagonal_apply]
  simp only [Matrix.submatrix_apply, blkIdx]
  interval_cases r <;> interval_cases s <;>
    simp (config := {decide := true}) [J4, J2, f2, Matrix.one_apply, Fin.ext_iff,
      CharTwo.neg_eq] <;> omega

theorem blkIdx_inl (hk : 6 ≤ k) {r i : ℕ} (hr : r < 4) (hi : i < 3) (h : r < 2) :
    blkIdx hk (⟨r, hr⟩, ⟨i, hi⟩) = Sum.inl ⟨2 * i + r, by omega⟩ := by
  simp [blkIdx, h]

theorem blkIdx_inr (hk : 6 ≤ k) {r i : ℕ} (hr : r < 4) (hi : i < 3) (h : ¬ r < 2) :
    blkIdx hk (⟨r, hr⟩, ⟨i, hi⟩) = Sum.inr ⟨2 * i + (r - 2), by omega⟩ := by
  simp [blkIdx, h]

omit [CharP K 2] in
theorem Jk_closed (hk : 6 ≤ k) (x : Fin 4 × Fin 3) (y : ↥(Set.range (blkIdx hk))ᶜ) :
    (fromBlocks (0 : Matrix (Fin k) (Fin k) K) 1 (-1) 0) (blkIdx hk x) y.1 = 0 ∧
    (fromBlocks (0 : Matrix (Fin k) (Fin k) K) 1 (-1) 0) y.1 (blkIdx hk x) = 0 := by
  obtain ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ := x
  obtain ⟨y, hy⟩ := y
  have hy' : ∀ z, blkIdx hk z ≠ y := fun z h => hy ⟨z, h⟩
  by_cases hr2 : r < 2
  · rw [blkIdx_inl hk hr hi hr2]
    rcases y with b | b
    · simp
    · by_cases hab : (⟨2 * i + r, by omega⟩ : Fin k) = b
      · exfalso
        refine hy' (⟨r + 2, by omega⟩, ⟨i, hi⟩) ?_
        rw [blkIdx_inr hk (r := r + 2) (by omega) hi (by omega)]
        exact congrArg Sum.inr (by simpa using hab)
      · have hba : b ≠ ⟨2 * i + r, by omega⟩ := fun h => hab h.symm
        simp [hab, hba]
  · rw [blkIdx_inr hk hr hi hr2]
    rcases y with b | b
    · by_cases hab : (⟨2 * i + (r - 2), by omega⟩ : Fin k) = b
      · exfalso
        refine hy' (⟨r - 2, by omega⟩, ⟨i, hi⟩) ?_
        rw [blkIdx_inl hk (r := r - 2) (by omega) hi (by omega)]
        exact congrArg Sum.inl hab
      · have hba : b ≠ ⟨2 * i + (r - 2), by omega⟩ := fun h => hab h.symm
        simp [hab, hba]
    · simp

end Blocks

section Hom

variable {k : ℕ} (K : Type) [Field K] [CharP K 2]

@[expose] noncomputable def blockMat (v : Multiplicative (Fin 3 → ZMod 5)) :
    Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) K :=
  Matrix.blockDiagonal fun i => AK K ^ (Multiplicative.toAdd v i).val

theorem AK_pow_val_add (a b : ZMod 5) : AK K ^ (a + b).val = AK K ^ a.val * AK K ^ b.val := by
  have h := pow_mod_orderOf (AK K) (a.val + b.val)
  rw [orderOf_AK] at h
  rw [ZMod.val_add, h, pow_add]

theorem blockMat_mul (u v : Multiplicative (Fin 3 → ZMod 5)) :
    blockMat K (u * v) = blockMat K u * blockMat K v := by
  simp only [blockMat, toAdd_mul, Matrix.blockDiagonal_mul, Pi.add_apply, AK_pow_val_add]

theorem blockMat_one : blockMat K (1 : Multiplicative (Fin 3 → ZMod 5)) = 1 := by
  simp only [blockMat, toAdd_one, Pi.zero_apply, ZMod.val_zero, pow_zero]
  exact Matrix.blockDiagonal_one

@[expose] noncomputable def sp5Mat (hk : 6 ≤ k) :
    Multiplicative (Fin 3 → ZMod 5) →* Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) K where
  toFun v := embedMat (blkIdx hk) (blkIdx_injective hk) (blockMat K v)
  map_one' := by rw [blockMat_one, embedMat_one]
  map_mul' u v := by rw [blockMat_mul, embedMat_mul]

theorem sp5Mat_symplectic (hk : 6 ≤ k) (v : Multiplicative (Fin 3 → ZMod 5)) :
    (sp5Mat K hk v)ᵀ * fromBlocks (0 : Matrix (Fin k) (Fin k) K) 1 (-1) 0 * sp5Mat K hk v =
      fromBlocks 0 1 (-1) 0 := by
  refine embedMat_symplectic (blkIdx hk) (blkIdx_injective hk) _ (Jk_closed K hk) ?_
  rw [Jk_submatrix K hk]
  unfold blockMat
  rw [Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  simp only [AK_pow_symp]

end Hom

section Final

variable {k : ℕ} (K : Type) [Field K] [CharP K 2]

@[expose] noncomputable def sp5Hom (hk : 6 ≤ k) :
    Multiplicative (Fin 3 → ZMod 5) →* GL (Fin k ⊕ Fin k) K :=
  (sp5Mat K hk).toHomUnits

theorem coe_sp5Hom (hk : 6 ≤ k) (v : Multiplicative (Fin 3 → ZMod 5)) :
    ((sp5Hom K hk v : GL (Fin k ⊕ Fin k) K) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) K) =
      sp5Mat K hk v := rfl

theorem sp5Hom_mem (hk : 6 ≤ k) (v : Multiplicative (Fin 3 → ZMod 5)) :
    sp5Hom K hk v ∈ StatedSp k K := by
  rw [mem_statedSp_iff', coe_sp5Hom]
  exact sp5Mat_symplectic K hk v

@[expose] noncomputable def sp5Proj (hk : 6 ≤ k) :
    Multiplicative (Fin 3 → ZMod 5) →* StatedProj (StatedSp k K) :=
  (projEquiv (K := K) (n := k) (by omega)).symm.toMonoidHom.comp
    ((sp5Hom K hk).codRestrict (StatedSp k K) (sp5Hom_mem K hk))

theorem sp5Proj_injective (hk : 6 ≤ k) : Function.Injective (sp5Proj K hk) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have h1 : (projEquiv (K := K) (n := k) (by omega)).symm
      ((sp5Hom K hk).codRestrict (StatedSp k K) (sp5Hom_mem K hk) v) = 1 := hv
  have h2 := (projEquiv (K := K) (n := k) (by omega)).symm.injective (h1.trans (map_one _).symm)
  have h3 : sp5Mat K hk v = 1 := by
    have := congrArg (fun g : StatedSp k K =>
      ((g : GL (Fin k ⊕ Fin k) K) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) K)) h2
    exact this
  have h4 : blockMat K v = 1 := by
    apply embedMat_injective (blkIdx hk) (blkIdx_injective hk)
    rw [embedMat_one]
    exact h3
  have h4' : (fun i => AK K ^ (Multiplicative.toAdd v i).val) =
      fun _ => (1 : Matrix (Fin 4) (Fin 4) K) := by
    apply Matrix.blockDiagonal_injective
    have h1 : (Matrix.blockDiagonal fun _ : Fin 3 => (1 : Matrix (Fin 4) (Fin 4) K)) = 1 :=
      Matrix.blockDiagonal_one
    rw [h1]
    exact h4
  apply Multiplicative.toAdd.injective
  funext i
  have h5 : AK K ^ (Multiplicative.toAdd v i).val = 1 := congrFun h4' i
  have h6 := orderOf_dvd_of_pow_eq_one h5
  rw [orderOf_AK] at h6
  have h7 : (Multiplicative.toAdd v i).val = 0 :=
    Nat.eq_zero_of_dvd_of_lt h6 (ZMod.val_lt _)
  exact (ZMod.val_eq_zero _).1 h7

theorem exists_elemAbelian_five_cube (hk : 6 ≤ k) :
    ∃ A : Subgroup (StatedProj (StatedSp k K)), CFSG.IsElementaryAbelian 5 A ∧
      Nat.card A = 5 ^ 3 := by
  refine ⟨(sp5Proj K hk).range, isElementaryAbelian_range _
    (fun (x y : Multiplicative (Fin 3 → ZMod 5)) => mul_comm x y) ?_, ?_⟩
  · intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp [show (5 : ZMod 5) = 0 by decide]
  · rw [← Nat.card_congr (MonoidHom.ofInjective (sp5Proj_injective K hk)).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

end Final

theorem not_dvd_ordBC {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 6) : ¬ 125 ∣ ordBC k 2 := by
  interval_cases k <;> (unfold ordBC; decide +kernel)

theorem three_le_pRank_five_catSp (k : ℕ) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group] (hk : 3 ≤ k)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q)
    (h125 : 125 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group) :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨q, hq2, hd⟩ := hd
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hdvd : q.p ∣ 2 := hpe ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
  have hqe : q.exponent = 1 := by
    rw [hqp] at hpe
    exact Nat.pow_right_injective le_rfl (by simpa using hpe)
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B k q := hd
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hqp hk
    (MulEquiv.refl _)
  rw [hqp, hqe] at hm
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.1 rfl
  rw [hcard, pow_one] at h125
  have hk6 : 6 ≤ k := by
    by_contra h
    exact not_dvd_ordBC hk (by omega) h125
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ := hm
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hFcard)
  obtain ⟨A, hA, hAc⟩ := exists_elemAbelian_five_cube F hk6
  have hA' : IsElemAbelian 5 A := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 A).1 hA
  have hE : IsElemAbelian 5 (A.map e.symm.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hA' _
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE
    (by rw [Subgroup.card_map_of_injective e.symm.injective, hAc])

end CFSG.AGLEmbeddingD2.SpFive
