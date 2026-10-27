module

public import CFSG.Adapters.TauCetiExceptional.BigCellEndgameE

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

structure BlockCarrier
    (τ : Tag) (L : Type) [Field L] (n m : ℕ) where
  C : Subgroup (Matrix.GeneralLinearGroup (Fin n) L)
  π : C →* ModGL τ L
  u : Fin τ.rank → L → C
  v : Fin τ.rank → L → C
  E : Fin τ.rank → Matrix (Fin n) (Fin n) L
  F : Fin τ.rank → Matrix (Fin n) (Fin n) L
  coe_u : ∀ i c, (((u i c : C) : Matrix.GeneralLinearGroup (Fin n) L) :
    Matrix (Fin n) (Fin n) L) = 1 + c • E i
  coe_v : ∀ i c, (((v i c : C) : Matrix.GeneralLinearGroup (Fin n) L) :
    Matrix (Fin n) (Fin n) L) = 1 + c • F i
  u_add : ∀ i c d, u i (c + d) = u i c * u i d
  v_add : ∀ i c d, v i (c + d) = v i c * v i d
  π_u : ∀ i c, π (u i c) = xUnit τ L i c
  π_v : ∀ i c, π (v i c) = yUnit τ L i c
  blk : Fin n → Fin m
  block : ∀ (z : C) (a b : Fin n), blk a ≠ blk b →
    ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) a b = 0
  ker_diag : ∀ z : C, π z = 1 → ∀ a b : Fin n, a ≠ b →
    ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) a b = 0
  ker_center : ∀ z : C, π z = 1 → z ∈ Subgroup.center C
  wt : Fin n → Fin τ.rank → ℤ
  wt_mem : ∀ a i, wt a i = -1 ∨ wt a i = 0 ∨ wt a i = 1
  comm : ∀ i, E i * F i - F i * E i = Matrix.diagonal fun a => (wt a i : L)
  comm_HE : ∀ i j, Matrix.diagonal (fun a => (wt a i : L)) * E j -
    E j * Matrix.diagonal (fun a => (wt a i : L)) = ((τ.cartan i j : ℤ) : L) • E j
  E_ne : ∀ j, E j ≠ 0
  cartan_off : ∀ i j, i ≠ j → τ.cartan i j = 0 ∨ τ.cartan i j = -1
  excl : ∀ π' : Equiv.Perm (Fin τ.rank),
    (∀ ij : Fin τ.rank × Fin τ.rank, τ.cartan (π' ij.1) (π' ij.2) = τ.cartan ij.1 ij.2) →
    (∀ a, ∃ b, blk b = blk a ∧ ∀ j, wt b (π' j) = wt a j) → π' = 1

theorem eq_of_cast_eq {L : Type} [Field L] (h2 : (2 : L) ≠ 0) {x y : ℤ}
    (hx : x = -1 ∨ x = 0 ∨ x = 1) (hy : y = -1 ∨ y = 0 ∨ y = 1) (h : (x : L) = y) : x = y := by
  have h1 : (1 : L) ≠ -1 := fun e => h2 (by linear_combination e)
  have h0 : (1 : L) ≠ 0 := one_ne_zero
  have h0' : (-1 : L) ≠ 0 := neg_ne_zero.2 one_ne_zero
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> push_cast at h <;>
    first | rfl | exact absurd h h1 | exact absurd h.symm h1 | exact absurd h h0 |
      exact absurd h.symm h0 | exact absurd h h0' | exact absurd h.symm h0'

theorem eq_one_of_pow_eq_one {L : Type} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p] {n : ℕ}
    (ζ : Matrix.GeneralLinearGroup (Fin n) L)
    (hd : ∀ a b, a ≠ b → (ζ : Matrix (Fin n) (Fin n) L) a b = 0) (hp : ζ ^ p = 1) : ζ = 1 := by
  obtain ⟨d, hdiag⟩ : ∃ d : Fin n → L,
      (ζ : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d := by
    refine ⟨fun a => ζ a a, ?_⟩
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [hd a b hab, Matrix.diagonal_apply_ne _ hab]
  have hpow : ((ζ ^ p : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (d ^ p) := by
    rw [Units.val_pow_eq_pow_val, hdiag, Matrix.diagonal_pow]
  have h1 : ∀ a, d a = 1 := by
    intro a
    have e := congrArg (fun M : Matrix.GeneralLinearGroup (Fin n) L =>
      (M : Matrix (Fin n) (Fin n) L) a a) hp
    simp only [hpow, Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq,
      Pi.pow_apply] at e
    have e' : (d a - 1) ^ p = 0 := by
      rw [sub_pow_char, e, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 e')
  refine Units.ext ?_
  rw [hdiag, Units.val_one, show d = fun _ => 1 from funext h1, Matrix.diagonal_one]

namespace BlockCarrier

variable {τ : Tag} {L : Type} [Field L] {n m : ℕ} (B : BlockCarrier τ L n m)

abbrev mat (z : B.C) : Matrix (Fin n) (Fin n) L :=
  ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem mat_mul (z w : B.C) : B.mat (z * w) = B.mat z * B.mat w := rfl

theorem mat_mul_inv (z : B.C) : B.mat z * B.mat z⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel]
  rfl

theorem mat_inv_mul (z : B.C) : B.mat z⁻¹ * B.mat z = 1 := by
  rw [← mat_mul, inv_mul_cancel]
  rfl

abbrev liftErr (E : Subfield L) (z' : B.C) (w w' : L → B.C) (φ : E → L) (c : E) : B.C :=
  z' * w c * z'⁻¹ * (w' (φ c))⁻¹

theorem liftErr_add (E : Subfield L) (z' : B.C) (w w' : L → B.C)
    (hw : ∀ c d, w (c + d) = w c * w d) (hw' : ∀ c d, w' (c + d) = w' c * w' d) (φ : E → L)
    (hφ : ∀ c d, φ (c + d) = φ c + φ d) (c d : E)
    (hd : B.liftErr E z' w w' φ d ∈ Subgroup.center B.C) :
    B.liftErr E z' w w' φ (c + d) = B.liftErr E z' w w' φ c * B.liftErr E z' w w' φ d := by
  have hc := Subgroup.mem_center_iff.1 hd
  have e : B.liftErr E z' w w' φ (c + d) =
      z' * w c * z'⁻¹ * B.liftErr E z' w w' φ d * (w' (φ c))⁻¹ := by
    simp only [liftErr, hφ, Subfield.coe_add, hw, hw', mul_inv_rev, mul_assoc,
      inv_mul_cancel_left]
  rw [e, hc (z' * w c * z'⁻¹), hc (B.liftErr E z' w w' φ c)]
  simp only [liftErr, mul_assoc]

theorem conj_eq_of_π_eq {p : ℕ} [Fact p.Prime] [CharP L p] (E : Subfield L)
    (w w' : L → B.C) (hw : ∀ c d, w (c + d) = w c * w d)
    (hw' : ∀ c d, w' (c + d) = w' c * w' d) (φ : E → L) (hφ : ∀ c d, φ (c + d) = φ c + φ d)
    (z' : B.C) (h : ∀ c : E, B.π (z' * w c * z'⁻¹) = B.π (w' (φ c))) (c : E) :
    z' * w c * z'⁻¹ = w' (φ c) := by
  have hker : ∀ c, B.π (B.liftErr E z' w w' φ c) = 1 := fun c => by
    rw [liftErr, map_mul, map_inv, h c, mul_inv_cancel]
  have hφ0 : φ 0 = 0 := by
    have := hφ 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hw0 : ∀ {w : L → B.C}, (∀ c d, w (c + d) = w c * w d) → w 0 = 1 := fun {w} hw =>
    mul_left_cancel (a := w 0) (by rw [← hw, add_zero, mul_one])
  have h0 : B.liftErr E z' w w' φ 0 = 1 := by
    simp only [liftErr, hφ0, ZeroMemClass.coe_zero, hw0 hw, hw0 hw', mul_one, mul_inv_cancel,
      inv_one]
  have hnsmul : ∀ k : ℕ, B.liftErr E z' w w' φ (k • c) = B.liftErr E z' w w' φ c ^ k := by
    intro k
    induction k with
    | zero => rw [zero_smul, h0, pow_zero]
    | succ k ih =>
      rw [succ_nsmul, B.liftErr_add E z' w w' hw hw' φ hφ _ _ (B.ker_center _ (hker c)), ih,
        pow_succ]
  have hp : B.liftErr E z' w w' φ c ^ p = 1 := by
    rw [← hnsmul, nsmul_eq_mul, CharP.cast_eq_zero E p, zero_mul, h0]
  have hp' : ((B.liftErr E z' w w' φ c : B.C) : Matrix.GeneralLinearGroup (Fin n) L) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hp, Subgroup.coe_one]
  have h1 := eq_one_of_pow_eq_one _ (B.ker_diag _ (hker c)) hp'
  exact mul_inv_eq_one.1 (Subtype.ext h1)

theorem conj_E_eq (z' : B.C) {i j : Fin τ.rank} {a : L} (h : z' * B.u i 1 * z'⁻¹ = B.u j a) :
    B.mat z' * B.E i * B.mat z'⁻¹ = a • B.E j := by
  have e := congrArg B.mat h
  have hZ := B.mat_mul_inv z'
  simp only [mat, Subgroup.coe_mul, Units.val_mul, B.coe_u, one_smul] at e hZ ⊢
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hZ] at e
  exact add_left_cancel e

theorem conj_F_eq (z' : B.C) {i j : Fin τ.rank} {a : L} (h : z' * B.v i 1 * z'⁻¹ = B.v j a) :
    B.mat z' * B.F i * B.mat z'⁻¹ = a • B.F j := by
  have e := congrArg B.mat h
  have hZ := B.mat_mul_inv z'
  simp only [mat, Subgroup.coe_mul, Units.val_mul, B.coe_v, one_smul] at e hZ ⊢
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hZ] at e
  exact add_left_cancel e

theorem conj_diag_eq (z' : B.C) {i j : Fin τ.rank} {a : L} (ha : a ≠ 0)
    (hE : B.mat z' * B.E i * B.mat z'⁻¹ = a • B.E j)
    (hF : B.mat z' * B.F i * B.mat z'⁻¹ = a⁻¹ • B.F j) :
    B.mat z' * Matrix.diagonal (fun b => (B.wt b i : L)) * B.mat z'⁻¹ =
      Matrix.diagonal fun b => (B.wt b j : L) := by
  have key : ∀ X Y : Matrix (Fin n) (Fin n) L, B.mat z' * (X * Y) * B.mat z'⁻¹ =
      (B.mat z' * X * B.mat z'⁻¹) * (B.mat z' * Y * B.mat z'⁻¹) := by
    intro X Y
    have e : (B.mat z' * X * B.mat z'⁻¹) * (B.mat z' * Y * B.mat z'⁻¹) =
        B.mat z' * X * (B.mat z'⁻¹ * B.mat z') * Y * B.mat z'⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [e, mat_inv_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [← B.comm i, ← B.comm j, Matrix.mul_sub, Matrix.sub_mul, key, key, hE, hF,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul,
    mul_inv_cancel₀ ha, inv_mul_cancel₀ ha, one_smul, one_smul]

theorem cartan_perm (z' : B.C) (π' : Equiv.Perm (Fin τ.rank)) (a : Fin τ.rank → L)
    (ha : ∀ j, a j ≠ 0)
    (hH : ∀ i, B.mat z' * Matrix.diagonal (fun b => (B.wt b i : L)) * B.mat z'⁻¹ =
      Matrix.diagonal fun b => (B.wt b (π' i) : L))
    (hE : ∀ j, B.mat z' * B.E j * B.mat z'⁻¹ = a j • B.E (π' j)) (i j : Fin τ.rank) :
    τ.cartan (π' i) (π' j) = τ.cartan i j := by
  by_cases hij : i = j
  · subst hij
    rw [τ.cartan_self, τ.cartan_self]
  have key : ∀ X Y : Matrix (Fin n) (Fin n) L, B.mat z' * (X * Y) * B.mat z'⁻¹ =
      (B.mat z' * X * B.mat z'⁻¹) * (B.mat z' * Y * B.mat z'⁻¹) := by
    intro X Y
    have e : (B.mat z' * X * B.mat z'⁻¹) * (B.mat z' * Y * B.mat z'⁻¹) =
        B.mat z' * X * (B.mat z'⁻¹ * B.mat z') * Y * B.mat z'⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [e, mat_inv_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hL : B.mat z' * (Matrix.diagonal (fun b => (B.wt b i : L)) * B.E j -
      B.E j * Matrix.diagonal (fun b => (B.wt b i : L))) * B.mat z'⁻¹ =
      a j • (((τ.cartan (π' i) (π' j) : ℤ) : L) • B.E (π' j)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, key, key, hH, hE, Matrix.mul_smul, Matrix.smul_mul,
      ← smul_sub, B.comm_HE]
  rw [B.comm_HE i j, Matrix.mul_smul, Matrix.smul_mul, hE, smul_smul, smul_smul] at hL
  have h0 : ((((τ.cartan i j : ℤ) : L) * a j - a j * ((τ.cartan (π' i) (π' j) : ℤ) : L)) •
      B.E (π' j)) = 0 := by
    rw [sub_smul, hL, sub_self]
  have h3 := (smul_eq_zero.1 h0).resolve_right (B.E_ne _)
  have hcast : ((τ.cartan (π' i) (π' j) : ℤ) : L) = ((τ.cartan i j : ℤ) : L) := by
    have h4 : a j * (((τ.cartan i j : ℤ) : L) - ((τ.cartan (π' i) (π' j) : ℤ) : L)) = 0 := by
      rw [← h3]
      ring
    exact (sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left (ha j))).symm
  have hne : π' i ≠ π' j := π'.injective.ne hij
  rcases B.cartan_off _ _ hne with h1 | h1 <;> rcases B.cartan_off _ _ hij with h2 | h2 <;>
    rw [h1, h2] at hcast ⊢ <;> first | rfl | (exfalso; norm_num at hcast)

theorem perm_eq_one (h2 : (2 : L) ≠ 0) (z' : B.C) (π' : Equiv.Perm (Fin τ.rank))
    (hcart : ∀ i j, τ.cartan (π' i) (π' j) = τ.cartan i j)
    (hH : ∀ i, B.mat z' * Matrix.diagonal (fun b => (B.wt b i : L)) * B.mat z'⁻¹ =
      Matrix.diagonal fun b => (B.wt b (π' i) : L)) : π' = 1 := by
  refine B.excl π' (fun ij => hcart ij.1 ij.2) fun a => ?_
  obtain ⟨b, hb⟩ : ∃ b, B.mat z' b a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e := congrArg (fun M : Matrix (Fin n) (Fin n) L => M a a) (B.mat_inv_mul z')
    simp only [Matrix.mul_apply, hcon, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at e
    exact zero_ne_one e
  refine ⟨b, ?_, fun j => ?_⟩
  · by_contra hne
    exact hb (B.block z' b a hne)
  · have e : B.mat z' * Matrix.diagonal (fun b => (B.wt b j : L)) =
        Matrix.diagonal (fun b => (B.wt b (π' j) : L)) * B.mat z' := by
      rw [← hH j, Matrix.mul_assoc _ (B.mat z'⁻¹), mat_inv_mul, Matrix.mul_one]
    have e' := congrArg (fun M : Matrix (Fin n) (Fin n) L => M b a) e
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e'
    have e'' : ((B.wt a j : ℤ) : L) = (B.wt b (π' j) : L) :=
      mul_left_cancel₀ hb (by rw [e', mul_comm])
    exact (eq_of_cast_eq h2 (B.wt_mem a j) (B.wt_mem b (π' j)) e'').symm

theorem adjointGroup_le_range : adjointGroup τ L ≤ B.π.range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hx | hy⟩
  · exact ⟨B.u i c, by rw [B.π_u]; exact Units.ext hx.symm⟩
  · exact ⟨B.v i c, by rw [B.π_v]; exact Units.ext hy.symm⟩

theorem exactPerm_zero (τ : Tag) : exactPerm τ 0 = 1 := by
  cases τ <;> rfl

theorem exactQ_zero (τ : Tag) (K : Type) [Field K] : exactQ τ K 0 = 1 := by
  cases τ <;> rfl

theorem exists_eq_diag_entrywise
    {K : Type} [Field K] [Finite K] {β : MulAut (adjointGroup τ K)}
    (hβ : β ∈ rootPairAut τ K) :
    ∃ (a : Fin τ.rank → Kˣ) (σ : K ≃+* K), ∀ x : adjointGroup τ K, (β x : ModGL τ K) =
      rootDiagUnit τ a * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
        (rootDiagUnit τ a)⁻¹ := by
  obtain ⟨q, hq, -⟩ := (ordinary_Chevalley_root_pair_common_field_parameter τ K).1 β hβ
  have e : β = exactNormalAut τ K q.1 q.2 0 := by
    refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
    · rw [(hq i).1, exactNormalAut_adjX, exactPerm_zero, Equiv.Perm.one_apply]
    · rw [(hq i).2.1, exactNormalAut_adjY, exactPerm_zero, Equiv.Perm.one_apply]
  refine ⟨q.1, q.2, fun x => ?_⟩
  rw [e, coe_exactNormalAut, exactQ_zero, mul_one, inv_one, mul_one]

end BlockCarrier

section Endgame

variable {τ : Tag} {L : Type} [Field L] {n m : ℕ} (B : BlockCarrier τ L n m)
  {p : ℕ} [Fact p.Prime] [CharP L p]

theorem BlockCarrier.π_mem_of_conj
    [IsAlgClosed L] (hτ : τ ≠ .G2) (hp2 : p ≠ 2)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (B.π z : Module.End L (RootModule τ L))) P = 0) (z : B.C)
    (E : Subfield L) [Finite E] (t : Eˣ) (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1)
    (α : MulAut (adjointGroup τ E))
    (hα : ∀ x : adjointGroup τ E, baseChangeGL E.subtype (α x : ModGL τ E) =
      B.π z * baseChangeGL E.subtype (x : ModGL τ E) * (B.π z)⁻¹) :
    B.π z ∈ adjointGroup τ L := by
  have h2 : (2 : L) ≠ 0 := two_ne_zero_of_charP hp2
  have hHr : ∀ h ∈ B.π.range, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0 := by
    rintro _ ⟨w, rfl⟩ P hP
    exact hH w P hP
  have hcharE : ringChar E ≠ 2 := by
    rw [ringChar.eq E p]
    exact hp2
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  obtain ⟨c, β, hU, hV, hαβ⟩ :=
    (exceptional_ordinary_Sylow_opposition τ E p w₀ hw₀).2.2.2.2.2 α
  have hβ : β ∈ unipotentPairAut τ E := ⟨hU, hV⟩
  obtain ⟨π', hπ'⟩ := exists_perm_map_simple hβ
  choose prm hprm using fun i => exists_params_of_map_simple hcharE (hπ' i).1 (hπ' i).2
  obtain ⟨c', hc'⟩ := B.adjointGroup_le_range
    (map_baseChangeGL_adjointGroup_le E.subtype ⟨(c : ModGL τ E), c.2, rfl⟩)
  have hαx : ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (c : ModGL τ E) * (β x : ModGL τ E) * (c : ModGL τ E)⁻¹ := fun x => by
    rw [hαβ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
  have hz' : ∀ x : adjointGroup τ E, B.π (c'⁻¹ * z) * baseChangeGL E.subtype (x : ModGL τ E) *
      (B.π (c'⁻¹ * z))⁻¹ = baseChangeGL E.subtype (β x : ModGL τ E) := by
    intro x
    have e1 : baseChangeGL E.subtype (β x : ModGL τ E) =
        (baseChangeGL E.subtype (c : ModGL τ E))⁻¹ * baseChangeGL E.subtype (α x : ModGL τ E) *
          baseChangeGL E.subtype (c : ModGL τ E) := by
      rw [hαx x, map_mul, map_mul, map_inv]
      group
    rw [e1, hα x, map_mul, map_inv, hc']
    group
  have hu : ∀ i (c₀ : E), (c'⁻¹ * z) * B.u i c₀ * (c'⁻¹ * z)⁻¹ =
      B.u (π' i) (((prm i).1 * (prm i).2 c₀ : E) : L) := by
    intro i
    refine B.conj_eq_of_π_eq E (B.u i) (B.u (π' i)) (B.u_add i) (B.u_add (π' i)) _
      (fun c d => by rw [map_add, mul_add, Subfield.coe_add]) _ fun c₀ => ?_
    rw [map_mul, map_mul, map_inv, B.π_u, B.π_u]
    have e := hz' (adjX τ E i c₀)
    rw [(hprm i).1 c₀] at e
    simpa only [adjX, baseChangeGL_xUnit, Subfield.coe_subtype] using e
  have hv : ∀ i (c₀ : E), (c'⁻¹ * z) * B.v i c₀ * (c'⁻¹ * z)⁻¹ =
      B.v (π' i) (((((prm i).1⁻¹ : Eˣ) : E) * (prm i).2 c₀ : E) : L) := by
    intro i
    refine B.conj_eq_of_π_eq E (B.v i) (B.v (π' i)) (B.v_add i) (B.v_add (π' i)) _
      (fun c d => by rw [map_add, mul_add, Subfield.coe_add]) _ fun c₀ => ?_
    rw [map_mul, map_mul, map_inv, B.π_v, B.π_v]
    have e := hz' (adjY τ E i c₀)
    rw [(hprm i).2.1 c₀] at e
    simpa only [adjY, baseChangeGL_yUnit, Subfield.coe_subtype] using e
  have ha : ∀ i, (((prm i).1 : E) : L) ≠ 0 := fun i h0 =>
    (prm i).1.ne_zero (Subtype.ext (by rw [h0]; rfl))
  have hEq : ∀ i, B.mat (c'⁻¹ * z) * B.E i * B.mat (c'⁻¹ * z)⁻¹ =
      (((prm i).1 : E) : L) • B.E (π' i) := fun i =>
    B.conj_E_eq _ (by simpa only [OneMemClass.coe_one, map_one, mul_one] using hu i 1)
  have hFq : ∀ i, B.mat (c'⁻¹ * z) * B.F i * B.mat (c'⁻¹ * z)⁻¹ =
      (((prm i).1 : E) : L)⁻¹ • B.F (π' i) := by
    intro i
    refine B.conj_F_eq _ ?_
    have e := hv i 1
    rwa [OneMemClass.coe_one, map_one, mul_one, Units.val_inv_eq_inv_val, Subfield.coe_inv] at e
  have hdiag : ∀ i, B.mat (c'⁻¹ * z) * Matrix.diagonal (fun b => (B.wt b i : L)) *
      B.mat (c'⁻¹ * z)⁻¹ = Matrix.diagonal fun b => (B.wt b (π' i) : L) := fun i =>
    B.conj_diag_eq _ (ha i) (hEq i) (hFq i)
  have hπ1 : π' = 1 :=
    B.perm_eq_one h2 _ π' (B.cartan_perm _ π' (fun i => (((prm i).1 : E) : L)) ha hdiag hEq) hdiag
  have hβ' : β ∈ rootPairAut τ E := mem_rootPairAut.2 fun i => by
    have h := hπ' i
    rw [hπ1, Equiv.Perm.one_apply] at h
    exact h
  obtain ⟨a, σ, hβx⟩ := BlockCarrier.exists_eq_diag_entrywise hβ'
  refine mem_adjointGroup_of_diag_entrywise hτ h2 E σ t ht B.adjointGroup_le_range hHr ⟨z, rfl⟩
    c a α hα fun x => ?_
  rw [hαx x, hβx x]
  simp only [mul_assoc]

theorem BlockCarrier.π_mem_adjointGroup
    [IsAlgClosed L] [Algebra (ZMod p) L]
    [Algebra.IsAlgebraic (ZMod p) L] (hτ : τ ≠ .G2) (hp2 : p ≠ 2)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (B.π z : Module.End L (RootModule τ L))) P = 0) (z : B.C) :
    B.π z ∈ adjointGroup τ L := by
  have hHr : ∀ h ∈ B.π.range, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0 := by
    rintro _ ⟨w, rfl⟩ P hP
    exact hH w P hP
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ :=
    exists_conj_mulAut hp2 B.π.range B.adjointGroup_le_range hHr ⟨z, rfl⟩
  have : Finite (frobeniusFixedSubfield L p k) := finite_frobeniusFixedSubfield L p k hk
  exact B.π_mem_of_conj hτ hp2 hH z _ t ht α hα

end Endgame

end CFSG.TauCetiBridge.Twisted
