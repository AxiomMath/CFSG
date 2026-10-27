module

public import CFSG.ClassicalInvolution.Phan.PhanP1Model
public import CFSG.ClassicalInvolution.Phan.PhanD7Block

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem sq_eq_one_sl2 (h2 : (2 : F) ≠ 0) {M : SL(2, F)} (h : M * M = 1) : M = 1 ∨ M = -1 := by
  have hm : (M : Matrix (Fin 2) (Fin 2) F) * M = 1 := by
    simpa using congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F)) h
  have hd : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (M : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hM] at hm hd
  rw [Matrix.det_fin_two_of] at hd
  rw [Matrix.mul_fin_two, Matrix.one_fin_two] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  by_cases hs : a + d = 0
  · exfalso
    have hd' : d = -a := by linear_combination hs
    rw [hd'] at hd
    apply h2
    linear_combination -e00 - hd
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb, hc] at hd e00 e11
    have ha : a * a = 1 := by linear_combination e00
    have had : a * d = 1 := by linear_combination hd
    have hadd : a = d := by
      have : a * (a - d) = 0 := by linear_combination ha - had
      rcases mul_eq_zero.1 this with h0 | h0
      · exfalso
        rw [h0] at ha
        simp at ha
      · exact sub_eq_zero.1 h0
    have ha1 : a = 1 ∨ a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by linear_combination ha
      rcases mul_eq_zero.1 this with h0 | h0
      · exact Or.inl (sub_eq_zero.1 h0)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h0)
    rcases ha1 with h1 | h1
    · left
      refine Subtype.ext ?_
      rw [hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, h1, ← hadd]
    · right
      refine Subtype.ext ?_
      rw [hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, h1, ← hadd]

end SL2

section Inv

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] (S : PhanFamilyD4 K p f G)

@[expose] noncomputable def sInv (k : Fin 4) : G :=
  tor S k (negOne (unitaryInvolution K p f))

theorem sInv_eq (k : Fin 4) :
    sInv S k = S.ι k (torusTwo (unitaryInvolution K p f) (negOne (unitaryInvolution K p f))) :=
  rfl

theorem conjDiag_torusTwo (hK : Nat.card K = (p ^ f) ^ 2)
    (e : Fin 2 → normOne (unitaryInvolution K p f))
    (u : normOne (unitaryInvolution K p f)) :
    conjDiag hK e (torusTwo (unitaryInvolution K p f) u) =
      torusTwo (unitaryInvolution K p f) u := by
  refine Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  rw [coe_conjDiag_apply, coe_torusTwo]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq]
    rw [mul_right_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  · simp [Matrix.diagonal_apply_ne _ hxy]

theorem tor_commute_sInv (hK : Nat.card K = (p ^ f) ^ 2) (j k : Fin 4)
    (x : normOne (unitaryInvolution K p f)) : tor S j x * sInv S k = sInv S k * tor S j x := by
  have h := tor_conj_ι hK S j k x
    (torusTwo (unitaryInvolution K p f) (negOne (unitaryInvolution K p f)))
  rw [conjDiag_torusTwo hK] at h
  rw [sInv_eq]
  exact mul_inv_eq_iff_eq_mul.1 h

theorem torusSub_commute_sInv (hK : Nat.card K = (p ^ f) ^ 2) (k : Fin 4) {t : G}
    (ht : t ∈ torusSub S) : t * sInv S k = sInv S k * t := by
  obtain ⟨s, rfl⟩ := ht
  have c : ∀ j (x : normOne (unitaryInvolution K p f)),
      tor S j x * sInv S k = sInv S k * tor S j x := fun j x => tor_commute_sInv S hK j k x
  rw [mTor_apply]
  refine (Commute.mul_left (Commute.mul_left (Commute.mul_left (c 0 _) (c 1 _)) (c 2 _))
    (c 3 _))

end Inv

section Model

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem spinAction_sInv (hg : GoodFamily S) (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0)
    (h2K : (2 : K) ≠ 0) (k : Fin 4) :
    spinAction (quadPlus 4 F) (sInv S k) = (stdFrames ε hε h4 k).La (-1) := by
  set a := torusTwo (unitaryInvolution K p f) (negOne (unitaryInvolution K p f)) with ha
  have hrange : spinAction (quadPlus 4 F) (S.ι k a) ∈ (stdFrames ε hε h4 k).La.range := by
    rw [← hS.map_range k]
    exact ⟨S.ι k a, ⟨a, rfl⟩, rfl⟩
  obtain ⟨M, hM⟩ := hrange
  have hsq : M * M = 1 := by
    apply (stdFrames ε hε h4 k).La_injective
    rw [map_mul, hM, ← map_mul, ← map_mul, ha, ← map_mul, negOne_mul_self, map_one, map_one,
      map_one, map_one]
  have hne : M ≠ 1 := by
    intro h1
    rw [h1, map_one] at hM
    have h3 : S.ι k a = 1 := hS.inj k (S.ι k a) ⟨a, rfl⟩ hM.symm
    have h4' : a = 1 := hg.inj k (by rw [h3, map_one])
    exact negOne_ne_one (unitaryInvolution K p f) h2K
      (torusTwo_injective _ (by rw [← ha, h4', map_one]))
  rcases sq_eq_one_sl2 h2 hsq with h | h
  · exact absurd h hne
  · rw [sInv_eq, ← ha, ← hM, h]

end Model

section Eig

variable {F : Type} [Field F]

theorem coords_eq_zero_of_La_neg_one {V : Type} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (h2 : (2 : F) ≠ 0) (fr : Frame Q) {x : V} (hx : fr.La (-1) x = x) :
    fr.coords x = 0 := by
  rw [Frame.La_neg_one_apply] at hx
  have h1 : (2 : F) • fr.incl (fr.coords x) = 0 := by
    have := sub_eq_self.1 hx
    exact this
  have h3 : fr.incl (fr.coords x) = 0 := by
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h h2
    · exact h
  have := Frame.coords_incl fr (fr.coords x)
  rw [h3, map_zero] at this
  exact this.symm

theorem eq_incl_coords_of_La_neg_one {V : Type} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (h2 : (2 : F) ≠ 0) (fr : Frame Q) {x : V} (hx : fr.La (-1) x = -x) :
    x = fr.incl (fr.coords x) := by
  rw [Frame.La_neg_one_apply] at hx
  rw [sub_eq_iff_eq_add] at hx
  have h1 : (2 : F) • x = (2 : F) • fr.incl (fr.coords x) := by
    rw [two_smul]
    calc x + x = (-x + (2 : F) • fr.incl (fr.coords x)) + x := by rw [← hx]
      _ = (2 : F) • fr.incl (fr.coords x) := by abel
  exact smul_right_injective _ h2 h1

end Eig

section Stab

variable {F V G : Type} [Field F] [AddCommGroup V] [Module F V] [Group G]

@[expose] def stabOf (ρ : G →* (V ≃ₗ[F] V)) (A : Submodule F V) : Subgroup G where
  carrier := {g | ∀ x, ρ g x ∈ A ↔ x ∈ A}
  one_mem' := fun x => by simp
  mul_mem' {a b} ha hb x := by
    rw [map_mul, LinearEquiv.mul_apply, ha, hb]
  inv_mem' {a} ha x := by
    have := ha (ρ a⁻¹ x)
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
    simp only [LinearEquiv.coe_one, id_eq] at this
    exact this.symm

theorem mem_stabOf_of_pointwise {ρ : G →* (V ≃ₗ[F] V)} {A : Submodule F V} {g : G}
    (h : ∀ x ∈ A, ρ g x = x) : g ∈ stabOf ρ A := by
  intro x
  constructor
  · intro hx
    have h1 := h (ρ g x) hx
    have h2 : ρ g x = x := (ρ g).injective h1
    rw [← h2]
    exact hx
  · intro hx
    rw [h x hx]
    exact hx

end Stab

section Plane

variable {F : Type} [Field F]

@[expose] def eigSpace (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (a b c : F) :
    Submodule F (Fin 4 ⊕ Fin 4 → F) where
  carrier := {x | (stdFrames ε hε h4 0).La (-1) x = a • x ∧
    (stdFrames ε hε h4 1).La (-1) x = b • x ∧ (stdFrames ε hε h4 2).La (-1) x = c • x}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx0, hx1, hx2⟩ ⟨hy0, hy1, hy2⟩
    simp only [Set.mem_ofPred_eq, map_add, hx0, hx1, hx2, hy0, hy1, hy2, smul_add, and_self]
  smul_mem' := by
    rintro r x ⟨hx0, hx1, hx2⟩
    simp only [Set.mem_ofPred_eq, map_smul, hx0, hx1, hx2, smul_comm r, and_self]

@[expose] def planeA (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) : Submodule F (Fin 4 ⊕ Fin 4 → F) :=
  eigSpace ε hε h4 (-1) 1 1

theorem map_mem_eigSpace_of_commute {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} {a b c : F}
    {g : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)}
    (h0 : g * (stdFrames ε hε h4 0).La (-1) = (stdFrames ε hε h4 0).La (-1) * g)
    (h1 : g * (stdFrames ε hε h4 1).La (-1) = (stdFrames ε hε h4 1).La (-1) * g)
    (h2 : g * (stdFrames ε hε h4 2).La (-1) = (stdFrames ε hε h4 2).La (-1) * g)
    {x : Fin 4 ⊕ Fin 4 → F} (hx : x ∈ eigSpace ε hε h4 a b c) :
    g x ∈ eigSpace ε hε h4 a b c := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  have key : ∀ (s : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) (c : F), g * s = s * g →
      s x = c • x → s (g x) = c • g x := by
    intro s c hs hxs
    have := LinearEquiv.congr_fun hs x
    simp only [LinearEquiv.mul_apply] at this
    rw [← this, hxs, map_smul]
  exact ⟨key _ _ h0 hx0, key _ _ h1 hx1, key _ _ h2 hx2⟩

end Plane

section PlaneModel

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem torusSub_le_stabOf_eigSpace (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0) (a b c : F) :
    torusSub S ≤ stabOf (spinAction (quadPlus 4 F)) (eigSpace ε hε h4 a b c) := by
  have fwd : ∀ t ∈ torusSub S, ∀ x ∈ eigSpace ε hε h4 a b c,
      spinAction (quadPlus 4 F) t x ∈ eigSpace ε hε h4 a b c := by
    intro t ht x hx
    have hc : ∀ k : Fin 4, spinAction (quadPlus 4 F) t * (stdFrames ε hε h4 k).La (-1) =
        (stdFrames ε hε h4 k).La (-1) * spinAction (quadPlus 4 F) t := by
      intro k
      rw [← spinAction_sInv hg hS h2 h2K k, ← map_mul, ← map_mul, torusSub_commute_sInv S hK k ht]
    exact map_mem_eigSpace_of_commute (hc 0) (hc 1) (hc 2) hx
  intro t ht x
  refine ⟨fun hx => ?_, fun hx => fwd t ht x hx⟩
  have := fwd t⁻¹ (inv_mem ht) _ hx
  simpa [← LinearEquiv.mul_apply, ← map_mul] using this

theorem spinAction_fix_planeA (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0) {k : Fin 4}
    (hk : k ≠ 0) {r : spinGroup (quadPlus 4 F)} (hr : r ∈ (S.ι k).range) :
    ∀ x ∈ planeA ε hε h4, spinAction (quadPlus 4 F) r x = x := by
  intro x hx
  have hmem : spinAction (quadPlus 4 F) r ∈ (stdFrames ε hε h4 k).La.range := by
    rw [← hS.map_range k]
    exact ⟨r, hr, rfl⟩
  obtain ⟨M, hM⟩ := hmem
  rw [← hM]
  have hx1 : (stdFrames ε hε h4 1).La (-1) x = x := by simpa using hx.2.1
  have hx2 : (stdFrames ε hε h4 2).La (-1) x = x := by simpa using hx.2.2
  have c1 := coords_eq_zero_of_La_neg_one h2 _ hx1
  have c2 := coords_eq_zero_of_La_neg_one h2 _ hx2
  fin_cases k
  · exact absurd rfl hk
  · exact Frame.La_apply_of_coords_eq_zero _ M c1
  · exact Frame.La_apply_of_coords_eq_zero _ M c2
  · refine Frame.La_apply_of_coords_eq_zero _ M ?_
    have : (stdFrames ε hε h4 3).coords x = sigmaLin ((stdFrames ε hε h4 2).coords x) :=
      Frame.coords_swap _ x
    show (stdFrames ε hε h4 3).coords x = 0
    rw [this, c2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

theorem parab_le_stabOf_planeA (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0) :
    parab S {1, 2, 3} ≤ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4) := by
  refine sup_le (torusSub_le_stabOf_eigSpace hK hg hS h2 h2K _ _ _) (iSup₂_le fun j hj => ?_)
  rintro _ ⟨A, rfl⟩
  refine mem_stabOf_of_pointwise fun x hx => spinAction_fix_planeA hS h2 ?_ ⟨A, rfl⟩ x hx
  rintro rfl
  simp at hj

end PlaneModel

end CFSG.ClassicalInvolution.PhanP
