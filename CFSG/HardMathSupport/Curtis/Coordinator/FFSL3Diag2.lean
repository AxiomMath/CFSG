module

public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Diag

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Quasithin CFSG.Quasithin.MS93.S32 CFSG.Assembly.LowTwoRank
open scoped Matrix

section Normalizing

variable {V : Type} [CommGroup V] {F : Type} [Field F]

theorem dg_mul (g h : GL (Fin 3) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    dg (g * h) w = dg g (dg h w) := by
  simp [dg, Matrix.mulVec_mulVec]

theorem dg_one (w : (Fin 3 → F) × (Fin 3 → F)) : dg (1 : GL (Fin 3) F) w = w := by
  simp [dg]

theorem dg_dg_inv (g : GL (Fin 3) F) (w : (Fin 3 → F) × (Fin 3 → F)) : dg g (dg g⁻¹ w) = w := by
  rw [← dg_mul, mul_inv_cancel, dg_one]

@[expose] def bm (M : Matrix (Fin 2) (Fin 2) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    (Fin 3 → F) × (Fin 3 → F) :=
  blockSmul (M 0 0) (M 0 1) (M 1 0) (M 1 1) w

theorem bm_one (w : (Fin 3 → F) × (Fin 3 → F)) : bm (1 : Matrix (Fin 2) (Fin 2) F) w = w := by
  simp [bm, blockSmul]

theorem bm_mul (M N : Matrix (Fin 2) (Fin 2) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    bm M (bm N w) = bm (M * N) w := by
  simp only [bm, blockSmul, Prod.mk.injEq, Matrix.mul_apply, Fin.sum_univ_two, smul_add,
    smul_smul, add_smul]
  constructor <;> abel

theorem bm_dg (M : Matrix (Fin 2) (Fin 2) F) (g : GL (Fin 3) F) (w : (Fin 3 → F) × (Fin 3 → F)) :
    bm M (dg g w) = dg g (bm M w) :=
  blockSmul_dg _ _ _ _ g w

theorem conj_mem_statedSL (g : GL (Fin 3) F) {γ : GL (Fin 3) F} (hγ : γ ∈ StatedSL 3 F) :
    g * γ * g⁻¹ ∈ StatedSL 3 F := by
  unfold StatedSL at hγ ⊢
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    have hx' : Matrix.GeneralLinearGroup.det x = 1 := Units.ext hx
    have : Matrix.GeneralLinearGroup.det (g * x * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hx', mul_one]
      exact mul_inv_cancel _
    exact congrArg Units.val this
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem eq_zero_of_mulVec_eq_zero (h : GL (Fin 3) F) {x : Fin 3 → F}
    (hx : (h : Matrix (Fin 3) (Fin 3) F) *ᵥ x = 0) : x = 0 := by
  have := congrArg (fun y => ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) hx
  simpa [Matrix.mulVec_mulVec] using this

theorem det_ne_zero_of_dg_bm (h : GL (Fin 3) F) (N : Matrix (Fin 2) (Fin 2) F)
    (hN : ∀ w, dg h (bm N w) = w) : N.det ≠ 0 := by
  have h1 := hN (fun _ => 1, 0)
  have h2 := hN (0, fun _ => 1)
  simp only [bm, blockSmul, dg, smul_zero, add_zero, zero_add,
    Prod.mk.injEq] at h1 h2
  have hN10 : N 1 0 = 0 := by
    have := eq_zero_of_mulVec_eq_zero h h1.2
    simpa using congrFun this 0
  have hN01 : N 0 1 = 0 := by
    have := eq_zero_of_mulVec_eq_zero h h2.1
    simpa using congrFun this 0
  have hN00 : N 0 0 ≠ 0 := by
    intro h0
    have := congrFun h1.1 0
    rw [h0, zero_smul, Matrix.mulVec_zero] at this
    simp at this
  have hN11 : N 1 1 ≠ 0 := by
    intro h0
    have := congrFun h2.2 0
    rw [h0, zero_smul, Matrix.mulVec_zero] at this
    simp at this
  rw [Matrix.det_fin_two, hN10, hN01]
  simpa using mul_ne_zero hN00 hN11

variable {K P : Subgroup (MulAut V)} {π : ↥(StatedSL 3 F) →* ↥K}

namespace Coord

variable (c : Coord K π)

@[expose] def Rep2 (p : MulAut V) (g : GL (Fin 3) F) (M : Matrix (Fin 2) (Fin 2) F) : Prop :=
  ∀ w, c.T (dg g (bm M w)) = p (c.T w)

theorem rep2_one : c.Rep2 1 1 1 := fun w => by
  rw [bm_one, dg_one]; rfl

theorem rep2_mul {p q : MulAut V} {g h : GL (Fin 3) F} {M N : Matrix (Fin 2) (Fin 2) F}
    (hp : c.Rep2 p g M) (hq : c.Rep2 q h N) : c.Rep2 (p * q) (g * h) (M * N) := fun w => by
  have : dg (g * h) (bm (M * N) w) = dg g (bm M (dg h (bm N w))) := by
    rw [dg_mul, ← bm_mul, bm_dg]
  rw [this, hp, hq]
  rfl

theorem rep2_inv {p : MulAut V} {g : GL (Fin 3) F} {M : GL (Fin 2) F}
    (hp : c.Rep2 p g (M : Matrix (Fin 2) (Fin 2) F)) :
    c.Rep2 p⁻¹ g⁻¹ ((M⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := fun w => by
  have h1 := hp (dg g⁻¹ (bm ((M⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) w))
  rw [bm_dg, bm_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, bm_one, dg_dg_inv] at h1
  rw [h1]
  simp

end Coord

theorem map_mem_commV_of_normalizes {K : Subgroup (MulAut V)} {p : MulAut V}
    (hp : ∀ k ∈ K, p * k * p⁻¹ ∈ K) {u : V} (hu : u ∈ commV K) : p u ∈ commV K :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hp hu

theorem Coord.exists_rep2 (c : Coord K π) (hπ : Function.Surjective π) {p : MulAut V}
    {g : GL (Fin 3) F}
    (hconj : ∀ γ γ' : ↥(StatedSL 3 F), (γ' : GL (Fin 3) F) = g * (γ : GL (Fin 3) F) * g⁻¹ →
      p * (π γ : MulAut V) * p⁻¹ = (π γ' : MulAut V)) :
    ∃ M : Matrix (Fin 2) (Fin 2) F, c.Rep2 p g M := by
  classical
  have hconj' : ∀ γ : ↥(StatedSL 3 F), ∃ γ' : ↥(StatedSL 3 F),
      (γ' : GL (Fin 3) F) = g * (γ : GL (Fin 3) F) * g⁻¹ :=
    fun γ => ⟨⟨_, conj_mem_statedSL g γ.2⟩, rfl⟩
  have hnorm : ∀ k ∈ K, p * k * p⁻¹ ∈ K := by
    intro k hk
    obtain ⟨γ, hγ⟩ := hπ ⟨k, hk⟩
    obtain ⟨γ', hγ'⟩ := hconj' γ
    have h1 := hconj γ γ' hγ'
    rw [hγ] at h1
    rw [show p * k * p⁻¹ = (π γ' : MulAut V) from h1]
    exact (π γ').2
  have hmem : ∀ w, p (c.T w) ∈ commV K := fun w =>
    map_mem_commV_of_normalizes hnorm (c.mem w)
  choose D hD using fun w => c.surj _ (hmem w)
  let D' : ((Fin 3 → F) × (Fin 3 → F)) →+ ((Fin 3 → F) × (Fin 3 → F)) :=
    AddMonoidHom.mk' D fun w w' => c.inj (by
      rw [hD, c.add, c.add, hD, hD, map_mul])
  let E : ((Fin 3 → F) × (Fin 3 → F)) →+ ((Fin 3 → F) × (Fin 3 → F)) :=
    AddMonoidHom.mk' (fun w => dg g⁻¹ (D w)) fun w w' => by
      rw [show D (w + w') = D w + D w' from D'.map_add w w', dg_add]
  have hcomm : ∀ γ ∈ StatedSL 3 F, ∀ w, E (dg γ w) = dg γ (E w) := by
    intro γ hγ w
    obtain ⟨γ', hγ'⟩ := hconj' ⟨γ, hγ⟩
    have h1 := hconj ⟨γ, hγ⟩ γ' hγ'
    have hD1 : D (dg γ w) = dg (γ' : GL (Fin 3) F) (D w) := by
      apply c.inj
      rw [hD, c.equiv ⟨γ, hγ⟩ w, c.equiv γ' (D w), hD]
      have h2 : p (((π ⟨γ, hγ⟩ : ↥K) : MulAut V) (c.T w)) =
          (p * ((π ⟨γ, hγ⟩ : ↥K) : MulAut V) * p⁻¹) (p (c.T w)) := by simp
      rw [h2, h1]
    change dg g⁻¹ (D (dg γ w)) = dg γ (dg g⁻¹ (D w))
    rw [hD1, hγ', ← dg_mul, ← dg_mul]
    congr 1
    group
  obtain ⟨a, b, d, e, h⟩ := exists_blockSmul_of_commute E hcomm
  refine ⟨!![a, b; d, e], fun w => ?_⟩
  have : bm !![a, b; d, e] w = E w := (h w).symm
  rw [this]
  change c.T (dg g (dg g⁻¹ (D w))) = _
  rw [dg_dg_inv, hD]

theorem Coord.exists_rep2_unit (c : Coord K π) (hπ : Function.Surjective π) {p : MulAut V}
    {g g' : GL (Fin 3) F}
    (hconj : ∀ γ γ' : ↥(StatedSL 3 F), (γ' : GL (Fin 3) F) = g * (γ : GL (Fin 3) F) * g⁻¹ →
      p * (π γ : MulAut V) * p⁻¹ = (π γ' : MulAut V))
    (hconj' : ∀ γ γ' : ↥(StatedSL 3 F), (γ' : GL (Fin 3) F) = g' * (γ : GL (Fin 3) F) * g'⁻¹ →
      p⁻¹ * (π γ : MulAut V) * p⁻¹⁻¹ = (π γ' : MulAut V)) :
    ∃ M : GL (Fin 2) F, c.Rep2 p g (M : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨M, hM⟩ := c.exists_rep2 hπ hconj
  obtain ⟨M', hM'⟩ := c.exists_rep2 hπ hconj'
  have h := c.rep2_mul hM hM'
  rw [mul_inv_cancel p] at h
  have hid : ∀ w, dg (g * g') (bm (M * M') w) = w := fun w => c.inj ((h w).trans rfl)
  have hdet := det_ne_zero_of_dg_bm _ _ hid
  rw [Matrix.det_mul] at hdet
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (left_ne_zero_of_mul hdet), by simpa using hM⟩

theorem Coord.trivial_of_rep_det_one (c : Coord K π) (hπ : Function.Surjective π)
    {x : MulAut V} (hxK : x ∈ K) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1)
    (hrep : ∃ a b d e : F, c.Rep x a b d e ∧ a * e - b * d = 1) :
    ∀ u ∈ commV K, x u = u := by
  intro u hu
  obtain ⟨a, b, d, e, hr, hdet⟩ := hrep
  obtain ⟨γ, hγ⟩ := hπ ⟨x, hxK⟩
  have hγx : ∀ w, c.T (dg (γ : GL (Fin 3) F) w) = x (c.T w) := fun w => by
    rw [c.equiv, hγ]
  have key : ∀ w, blockSmul a b d e w = dg (γ : GL (Fin 3) F) w := fun w =>
    c.inj ((hr w).trans (hγx w).symm)
  have h1 := key (fun _ => 1, 0)
  have h2 := key (0, fun _ => 1)
  simp only [blockSmul, dg, smul_zero, add_zero, zero_add, Matrix.mulVec_zero, Prod.mk.injEq]
    at h1 h2
  have hd : d = 0 := by simpa using congrFun h1.2 0
  have hb : b = 0 := by simpa using congrFun h2.1 0
  have hae : a = e := by
    have p1 := congrFun h1.1 0
    have p2 := congrFun h2.2 0
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at p1 p2
    exact p1.trans p2.symm
  subst hd hb hae
  have haa : a * a = 1 := by simpa using hdet
  have hpow : ∀ k : ℕ, c.Rep (x ^ k) (a ^ k) 0 0 (a ^ k) := by
    intro k
    induction k with
    | zero => simpa using c.rep_one
    | succ k ih => simpa [pow_succ] using c.rep_mul ih hr
  have hm' : a ^ m = 1 := by
    have h := hpow m
    rw [hxm] at h
    exact (c.rep_unique c.rep_one h).1.symm
  obtain ⟨k, rfl⟩ := hm
  have ha : a = 1 := by
    rw [pow_succ, pow_mul, sq, haa, one_pow, one_mul] at hm'
    exact hm'
  subst ha
  obtain ⟨w, rfl⟩ := c.surj u hu
  rw [← hr w]
  congr 1
  simp [blockSmul]

end Normalizing

section Main

variable {V : Type} [CommGroup V]

theorem commutator_trivial_of_case1ii_diag {K P : Subgroup (MulAut V)} {F : Type} [Field F]
    {I : Fin 2 → Subgroup V} (π : ↥(StatedSL 3 F) →* ↥K) (hind : iSupIndep I)
    (hsup : (⨆ i, I i) = commV K)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia K (I i) ⊥ π)
    (A : MulAut V → GL (Fin 3) F)
    (hA : ∀ p ∈ P, ∀ γ γ' : ↥(StatedSL 3 F),
      (γ' : GL (Fin 3) F) = A p * (γ : GL (Fin 3) F) * (A p)⁻¹ →
        p * (π γ : MulAut V) * p⁻¹ = (π γ' : MulAut V))
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, A p * A q = A q * A p) :
    ∀ x ∈ ⁅P, P⁆, x ∈ K → ∀ m : ℕ, Odd m → x ^ m = 1 → ∀ u ∈ commV K, x u = u := by
  obtain ⟨c⟩ := exists_coord_of_two_natural hind hsup hreal
  have hπ := (hreal 0).1
  have hrep : ∀ p ∈ P, ∃ M : GL (Fin 2) F, c.Rep2 p (A p) (M : Matrix (Fin 2) (Fin 2) F) :=
    fun p hp => c.exists_rep2_unit hπ (hA p hp) (hA p⁻¹ (P.inv_mem hp))
  let S : Subgroup (MulAut V) :=
    { carrier := {x | ∃ M : GL (Fin 2) F, Matrix.GeneralLinearGroup.det M = 1 ∧
        c.Rep2 x 1 (M : Matrix (Fin 2) (Fin 2) F)}
      one_mem' := ⟨1, map_one _, by simpa using c.rep2_one⟩
      mul_mem' := by
        rintro x y ⟨M, hM, hx⟩ ⟨N, hN, hy⟩
        refine ⟨M * N, by rw [map_mul, hM, hN, mul_one], ?_⟩
        simpa using c.rep2_mul hx hy
      inv_mem' := by
        rintro x ⟨M, hM, hx⟩
        refine ⟨M⁻¹, by rw [map_inv, hM, inv_one], ?_⟩
        simpa using c.rep2_inv hx }
  have hle : ⁅P, P⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    obtain ⟨M, hM⟩ := hrep p hp
    obtain ⟨N, hN⟩ := hrep q hq
    have h := c.rep2_mul (c.rep2_mul (c.rep2_mul hM hN) (c.rep2_inv hM)) (c.rep2_inv hN)
    have hg : A p * A q * (A p)⁻¹ * (A q)⁻¹ = 1 := by
      rw [hcomm p hp q hq]; group
    rw [hg] at h
    refine ⟨M * N * M⁻¹ * N⁻¹, ?_, by simpa [commutatorElement_def] using h⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  intro x hx hxK m hm hxm
  obtain ⟨M, hdet, hr⟩ := hle hx
  refine c.trivial_of_rep_det_one hπ hxK hm hxm
    ⟨(M : Matrix (Fin 2) (Fin 2) F) 0 0, (M : Matrix (Fin 2) (Fin 2) F) 0 1,
      (M : Matrix (Fin 2) (Fin 2) F) 1 0, (M : Matrix (Fin 2) (Fin 2) F) 1 1, ?_, ?_⟩
  · intro w
    have := hr w
    rwa [dg_one] at this
  · have := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
    simpa using this

end Main

end CFSG.HardMathSupport.Curtis.Coordinator
