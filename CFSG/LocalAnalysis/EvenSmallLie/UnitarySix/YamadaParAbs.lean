module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParR3

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

section Char2

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_W (x : W) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]

end Char2

section Mat

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def matOf (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (f : W →ₗ[ZMod 2] W) : Mat16 :=
  LinearMap.toMatrix' (e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap)

theorem matOf_mulVec (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (f : W →ₗ[ZMod 2] W) (x : W) :
    matOf e f *ᵥ e x = e (f x) := by
  rw [matOf, LinearMap.toMatrix'_mulVec]
  simp

theorem matOf_comp (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (f g : W →ₗ[ZMod 2] W) :
    matOf e (f ∘ₗ g) = matOf e f * matOf e g := by
  rw [matOf, matOf, matOf, ← LinearMap.toMatrix'_comp]
  congr 1
  ext x
  simp

theorem matOf_id (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) : matOf e LinearMap.id = 1 := by
  rw [matOf, ← LinearMap.toMatrix'_id]
  congr 1
  ext x
  simp

theorem matOf_mul (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (f g : W →ₗ[ZMod 2] W) :
    matOf e (f * g) = matOf e f * matOf e g :=
  matOf_comp e f g

theorem matOf_one (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) : matOf e 1 = 1 :=
  matOf_id e

theorem matOf_eq_of_single (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (f : W →ₗ[ZMod 2] W) (M : Mat16)
    (h : ∀ c : Fin 16, e (f (e.symm (Pi.single c 1))) = M *ᵥ Pi.single c 1) : matOf e f = M := by
  ext i j
  rw [matOf, LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h j, mulVec_single_one]
  rfl

theorem matOf_eq_iff (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (f : W →ₗ[ZMod 2] W) (M : Mat16) :
    matOf e f = M ↔ ∀ x, e (f x) = M *ᵥ e x := by
  constructor
  · rintro rfl x; exact (matOf_mulVec e f x).symm
  · intro h
    exact matOf_eq_of_single e f M fun c => by rw [h, LinearEquiv.apply_symm_apply]

end Mat

section Adapted

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def adaptedLin (ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W) (w : Fin 8 → W) :
    (Fin 16 → ZMod 2) →ₗ[ZMod 2] W :=
  ι ∘ₗ LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd 8) +
    Fintype.linearCombination (ZMod 2) w ∘ₗ LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd 8)

theorem adaptedLin_apply (ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W) (w : Fin 8 → W)
    (x : Fin 16 → ZMod 2) :
    adaptedLin ι w x = ι (fun j => x (Fin.castAdd 8 j)) + ∑ j, x (Fin.natAdd 8 j) • w j := by
  simp [adaptedLin, Fintype.linearCombination_apply, LinearMap.funLeft_apply]
  rfl

theorem adaptedLin_append (ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W) (w : Fin 8 → W)
    (u v : Fin 8 → ZMod 2) :
    adaptedLin ι w (Fin.append u v) = ι u + ∑ j, v j • w j := by
  rw [adaptedLin_apply]
  simp only [Fin.append_left, Fin.append_right]

variable {τ : W →ₗ[ZMod 2] W} {ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W} {w : Fin 8 → W}

theorem tau_add_adaptedLin (hτι : ∀ u, τ (ι u) = ι u) (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1))
    (u v : Fin 8 → ZMod 2) :
    τ (adaptedLin ι w (Fin.append u v)) + adaptedLin ι w (Fin.append u v) = ι v := by
  rw [adaptedLin_append, map_add, hτι, map_sum]
  simp only [map_smul]
  rw [show ∀ a b c : W, a + b + (a + c) = (a + a) + (b + c) by intro a b c; abel, add_self_W,
    zero_add, ← Finset.sum_add_distrib]
  simp only [← smul_add, hw]
  have hv : v = ∑ x, v x • (Pi.single x 1 : Fin 8 → ZMod 2) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv, map_sum]
  simp only [map_smul]

theorem adaptedLin_eq_zero (hτι : ∀ u, τ (ι u) = ι u)
    (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1)) (hι : Function.Injective ι)
    (x : Fin 16 → ZMod 2) (hx : adaptedLin ι w x = 0) : x = 0 := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : Fin 8 → ZMod 2, x = Fin.append u v :=
    ⟨fun i => x (Fin.castAdd 8 i), fun i => x (Fin.natAdd 8 i),
      (Fin.append_castAdd_natAdd (m := 8) (n := 8) (f := x)).symm⟩
  have hv : v = 0 := by
    apply hι
    rw [← tau_add_adaptedLin hτι hw u v, hx, map_zero, add_zero, map_zero]
  subst hv
  have hu : u = 0 := by
    apply hι
    rw [map_zero, ← hx, adaptedLin_append]
    simp
  subst hu
  ext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

theorem adaptedLin_injective (hτι : ∀ u, τ (ι u) = ι u)
    (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1)) (hι : Function.Injective ι) :
    Function.Injective (adaptedLin ι w) := by
  have key : ∀ x, adaptedLin ι w x = 0 → x = 0 := by
    intro x hx
    exact adaptedLin_eq_zero hτι hw hι x hx
  intro x y hxy
  have h0 := key (x + y) (by rw [map_add, hxy, add_self_W])
  ext i
  have := congrFun h0 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  exact zmod2_eq_of_add_eq_zero this

theorem card_fin16 : Nat.card (Fin 16 → ZMod 2) = 2 ^ 16 := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

@[expose] noncomputable def adaptedEquiv [Finite W] (hτι : ∀ u, τ (ι u) = ι u)
    (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1)) (hι : Function.Injective ι)
    (hW : Nat.card W = 2 ^ 16) : (Fin 16 → ZMod 2) ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofBijective (adaptedLin ι w)
    ((adaptedLin_injective hτι hw hι).bijective_of_nat_card_le (by rw [hW, card_fin16]))

variable [Finite W] (hτι : ∀ u, τ (ι u) = ι u) (hw : ∀ j, τ (w j) + w j = ι (Pi.single j 1))
  (hι : Function.Injective ι) (hW : Nat.card W = 2 ^ 16)

theorem adaptedEquiv_append (u v : Fin 8 → ZMod 2) :
    adaptedEquiv hτι hw hι hW (Fin.append u v) = ι u + ∑ j, v j • w j :=
  adaptedLin_append ι w u v

theorem adaptedEquiv_symm_iota (u : Fin 8 → ZMod 2) :
    (adaptedEquiv hτι hw hι hW).symm (ι u) = Fin.append u (0 : Fin 8 → ZMod 2) := by
  rw [LinearEquiv.symm_apply_eq, adaptedEquiv_append]
  simp

theorem adaptedEquiv_symm_w (j : Fin 8) :
    (adaptedEquiv hτι hw hι hW).symm (w j) =
      Fin.append (0 : Fin 8 → ZMod 2) (Pi.single j (1 : ZMod 2)) := by
  rw [LinearEquiv.symm_apply_eq, adaptedEquiv_append]
  simp [Pi.single_apply]

theorem append_add_append (a b c d : Fin 8 → ZMod 2) :
    (Fin.append a b : Fin 16 → ZMod 2) + Fin.append c d = Fin.append (a + c) (b + d) := by
  ext r
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r <;>
    simp only [Pi.add_apply, Fin.append_left, Fin.append_right]

theorem adaptedEquiv_append_zero (u : Fin 8 → ZMod 2) :
    adaptedEquiv hτι hw hι hW (Fin.append u (0 : Fin 8 → ZMod 2)) = ι u := by
  rw [adaptedEquiv_append]
  simp

theorem adaptedEquiv_zero_append_single (j : Fin 8) :
    adaptedEquiv hτι hw hι hW (Fin.append (0 : Fin 8 → ZMod 2) (Pi.single j (1 : ZMod 2))) =
      w j := by
  rw [adaptedEquiv_append, map_zero, zero_add]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

theorem matOf_tau : matOf (adaptedEquiv hτι hw hι hW).symm τ = tM16 := by
  apply matOf_eq_of_single
  intro c
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) c
  · rw [append_single_castAdd, LinearEquiv.symm_symm, adaptedEquiv_append_zero, hτι,
      adaptedEquiv_symm_iota, tM16, blk16_mulVec_append, one_mulVec, one_mulVec, add_zero]
  · rw [append_single_natAdd, LinearEquiv.symm_symm, adaptedEquiv_zero_append_single]
    have h2 : τ (w j) = ι (Pi.single j 1) + w j := by
      rw [← hw j, add_assoc, add_self_W, add_zero]
    rw [h2, map_add, adaptedEquiv_symm_iota, adaptedEquiv_symm_w, tM16, blk16_mulVec_append,
      one_mulVec, one_mulVec, append_add_append, add_zero, zero_add]

@[expose] def urBlock (M : Mat16) : Mat8 := Matrix.of fun i j => M (Fin.castAdd 8 i) (Fin.natAdd 8 j)

theorem blk16_urBlock (A C : Mat8) : urBlock (blk16 A C) = C := by
  ext i j; exact blk16_castAdd_natAdd A C i j

theorem natAdd_part {f : W →ₗ[ZMod 2] W} {A : Mat8} (hfι : ∀ u, f (ι u) = ι (A *ᵥ u))
    (hfτ : ∀ x, τ (f x) = f (τ x)) (j : Fin 8) :
    (fun i : Fin 8 => (adaptedEquiv hτι hw hι hW).symm (f (w j)) (Fin.natAdd 8 i)) =
      A *ᵥ Pi.single j 1 := by
  apply hι
  have hy : (Fin.append (fun i : Fin 8 => (adaptedEquiv hτι hw hι hW).symm (f (w j)) (Fin.castAdd 8 i))
      (fun i : Fin 8 => (adaptedEquiv hτι hw hι hW).symm (f (w j)) (Fin.natAdd 8 i)) :
      Fin 16 → ZMod 2) = (adaptedEquiv hτι hw hι hW).symm (f (w j)) :=
    Fin.append_castAdd_natAdd (m := 8) (n := 8)
  have key := tau_add_adaptedLin hτι hw
    (fun i : Fin 8 => (adaptedEquiv hτι hw hι hW).symm (f (w j)) (Fin.castAdd 8 i))
    (fun i : Fin 8 => (adaptedEquiv hτι hw hι hW).symm (f (w j)) (Fin.natAdd 8 i))
  rw [← key]
  change τ (adaptedEquiv hτι hw hι hW _) + adaptedEquiv hτι hw hι hW _ = _
  rw [hy, LinearEquiv.apply_symm_apply, hfτ, ← map_add, hw, hfι]

theorem matOf_eq_blk16 {f : W →ₗ[ZMod 2] W} {A : Mat8} (hfι : ∀ u, f (ι u) = ι (A *ᵥ u))
    (hfτ : ∀ x, τ (f x) = f (τ x)) :
    matOf (adaptedEquiv hτι hw hι hW).symm f =
      blk16 A (urBlock (matOf (adaptedEquiv hτι hw hι hW).symm f)) := by
  set e := (adaptedEquiv hτι hw hι hW).symm with he
  set M := matOf e f with hM
  have h1 : ∀ u, M *ᵥ Fin.append u (0 : Fin 8 → ZMod 2) =
      Fin.append (A *ᵥ u) (0 : Fin 8 → ZMod 2) := fun u => by
    rw [← adaptedEquiv_symm_iota hτι hw hι hW, ← he, matOf_mulVec, hfι, he,
      adaptedEquiv_symm_iota]
  have h2 : ∀ j : Fin 8, ∀ i : Fin 8,
      (M *ᵥ Fin.append (0 : Fin 8 → ZMod 2) (Pi.single j 1)) (Fin.natAdd 8 i) = A i j := by
    intro j i
    rw [hM, ← adaptedEquiv_symm_w hτι hw hι hW, he, matOf_mulVec]
    have h3 := congrFun (natAdd_part hτι hw hι hW hfι hfτ j) i
    refine h3.trans ?_
    rw [mulVec_single_one]
    rfl
  ext r c
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) c
  · rw [blk16_castAdd_castAdd]
    have := congrFun (h1 (Pi.single j 1)) (Fin.castAdd 8 i)
    rw [← append_single_castAdd, mulVec_single_one, Fin.append_left, mulVec_single_one] at this
    exact this
  · rw [blk16_castAdd_natAdd]; rfl
  · rw [blk16_natAdd_castAdd]
    have := congrFun (h1 (Pi.single j 1)) (Fin.natAdd 8 i)
    rw [← append_single_castAdd, mulVec_single_one, Fin.append_right] at this
    exact this
  · rw [blk16_natAdd_natAdd]
    have := h2 j i
    rw [← append_single_natAdd, mulVec_single_one] at this
    exact this

end Adapted

section Step1

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def matHom (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) : (W →ₗ[ZMod 2] W) →* Mat16 where
  toFun := matOf e
  map_one' := matOf_one e
  map_mul' := matOf_mul e

theorem blk16_one_mul_self (X : Mat8) : blk16 1 X * blk16 1 X = 1 := by
  rw [blk16_mul]
  simp only [one_mul, mul_one]
  rw [mat8_add_self, blk16_one]

@[expose] noncomputable def shearEquiv (X : Mat8) :
    (Fin 16 → ZMod 2) ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) where
  toFun v := blk16 1 X *ᵥ v
  invFun v := blk16 1 X *ᵥ v
  map_add' v v' := mulVec_add _ v v'
  map_smul' c v := mulVec_smul _ c v
  left_inv v := by simp only [mulVec_mulVec, blk16_one_mul_self, one_mulVec]
  right_inv v := by simp only [mulVec_mulVec, blk16_one_mul_self, one_mulVec]

theorem shearEquiv_apply (X : Mat8) (v : Fin 16 → ZMod 2) : shearEquiv X v = blk16 1 X *ᵥ v :=
  rfl

theorem matOf_shear (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (X : Mat8) (f : W →ₗ[ZMod 2] W) :
    matOf (e.trans (shearEquiv X)) f = blk16 1 X * matOf e f * blk16 1 X := by
  rw [matOf_eq_iff]
  intro x
  simp only [LinearEquiv.trans_apply, shearEquiv_apply]
  rw [← matOf_mulVec, mulVec_mulVec, mulVec_mulVec,
    mul_assoc (blk16 1 X * matOf e f), blk16_one_mul_self, mul_one]

theorem urBlock_one : urBlock 1 = 0 := by
  ext i j
  simp only [urBlock, Matrix.of_apply, one_apply, Matrix.zero_apply]
  rw [ite_eq_right]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem list_prod_blk16 (C : Fin 3 → Mat8) (w : List (Fin 3)) :
    (w.map fun s => blk16 (genMat s) (C s)).prod = blk16 (urMat C w).1 (urMat C w).2 := by
  induction w with
  | nil => exact blk16_one.symm
  | cons s w ih => rw [List.map_cons, List.prod_cons, ih, blk16_mul]; rfl

theorem shear_conj (A C X : Mat8) (h : C = A * X + X * A) :
    blk16 1 X * blk16 A C * blk16 1 X = rhoM A := by
  rw [blk16_mul, blk16_mul, h, rhoM]
  congr 1
  · simp
  · simp only [one_mul, mul_one]
    rw [show A * X + (A * X + X * A + X * A) = (A * X + A * X) + (X * A + X * A) by abel,
      mat8_add_self, mat8_add_self, add_zero]

@[expose] noncomputable def genSU (s : Fin 3) : SU42b := ⟨genGL s, genGL_mem s⟩

theorem prod_genSU_eq_one {w : List (Fin 3)} (hw : w ∈ h1Rels) :
    (w.map genSU).prod = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  exact wordGL_eq_one_of_mem hw

theorem prod_symm_genSU_eq_one {K : Type*} [Group K] (θ : K ≃* SU42b) {w : List (Fin 3)}
    (hw : w ∈ h1Rels) : (w.map fun s => θ.symm (genSU s)).prod = 1 := by
  have h := map_list_prod θ.symm (w.map genSU)
  rw [prod_genSU_eq_one hw, map_one, List.map_map] at h
  exact h.symm

theorem SU42b_eq_closure : (⊤ : Subgroup SU42b) = Subgroup.closure {genSU 0, genSU 1} := by
  symm
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  refine Subgroup.closure_induction (p := fun g _ => ∀ hg : g ∈ SU42b,
      (⟨g, hg⟩ : SU42b) ∈ Subgroup.closure {genSU 0, genSU 1}) ?_ ?_ ?_ ?_ hg hg
  · rintro x (rfl | rfl) hx
    · exact Subgroup.subset_closure (by simp [genSU])
    · exact Subgroup.subset_closure (by simp [genSU])
  · intro _; exact one_mem _
  · intro x y hx hy ihx ihy hxy
    exact mul_mem (ihx hx) (ihy hy)
  · intro x hx ihx hxi
    exact inv_mem (ihx hx)

variable [Finite W] {Γ : Type*} [Group Γ]

theorem exists_good_coords (π : Γ →* (W →ₗ[ZMod 2] W)) (K : Subgroup Γ) (θ : K ≃* SU42b)
    (τ : W →ₗ[ZMod 2] W) (ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W) (hι : Function.Injective ι)
    (hτι : ∀ u, τ (ι u) = ι u) (hrange : ∀ u, ∃ x, τ x + x = ι u)
    (hW : Nat.card W = 2 ^ 16) (hπτ : ∀ k : K, ∀ x, τ (π k x) = π k (τ x))
    (hπι : ∀ k : K, ∀ u, π k (ι u) = ι (((θ k : GL (Fin 8) (ZMod 2)) : Mat8) *ᵥ u)) :
    ∃ e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2), matOf e τ = tM16 ∧
      ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8) := by
  choose w hw using fun j : Fin 8 => hrange (Pi.single j 1)
  set e₀ := (adaptedEquiv hτι hw hι hW).symm with he₀
  have hblk : ∀ k : K, matOf e₀ (π k) =
      blk16 ((θ k : GL (Fin 8) (ZMod 2)) : Mat8) (urBlock (matOf e₀ (π k))) := fun k =>
    matOf_eq_blk16 hτι hw hι hW (hπι k) (hπτ k)
  set ks : Fin 3 → K := fun s => θ.symm (genSU s) with hks
  have hθks : ∀ s, ((θ (ks s) : GL (Fin 8) (ZMod 2)) : Mat8) = genMat s := fun s => by
    rw [hks]; simp only [MulEquiv.apply_symm_apply, genSU, coe_genGL]
  set C : Fin 3 → Mat8 := fun s => urBlock (matOf e₀ (π (ks s))) with hC
  have hgen : ∀ s, matOf e₀ (π (ks s)) = blk16 (genMat s) (C s) := fun s => by
    rw [hblk, hθks]
  have hrel : ∀ w ∈ h1Rels, (urMat C w).2 = 0 := by
    intro w hw'
    have h1 : (w.map fun s => ((ks s : K) : Γ)).prod = 1 := by
      have h0 : (w.map ks).prod = 1 := prod_symm_genSU_eq_one θ hw'
      have := congrArg (fun g : K => (g : Γ)) h0
      simp only [SubmonoidClass.coe_list_prod, List.map_map, OneMemClass.coe_one] at this
      exact this
    have h2 := congrArg (fun g => matHom e₀ (π g)) h1
    simp only [map_list_prod, map_one, List.map_map] at h2
    have h3 : (w.map fun s => blk16 (genMat s) (C s)).prod = 1 := by
      rw [← h2]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      exact (hgen s).symm
    rw [list_prod_blk16] at h3
    have := congrArg urBlock h3
    rw [blk16_urBlock] at this
    rw [this, urBlock_one]
  obtain ⟨X, hX⟩ := exists_coboundary C hrel
  refine ⟨e₀.trans (shearEquiv X), ?_, ?_⟩
  · rw [matOf_shear, he₀, matOf_tau, tM16, blk16_mul, blk16_mul]
    simp only [one_mul, mul_one]
    congr 1
    rw [show X + (1 + X) = (X + X) + 1 by abel, mat8_add_self, zero_add]
  · set e := e₀.trans (shearEquiv X) with he
    have hgens : ∀ s : Fin 3, matOf e (π (θ.symm (genSU s))) =
        rhoM ((genSU s : GL (Fin 8) (ZMod 2)) : Mat8) := by
      intro s
      rw [he, matOf_shear]
      have hks' : (θ.symm (genSU s) : Γ) = (ks s : Γ) := rfl
      rw [hks', hgen s, shear_conj _ _ _ (hX s)]
      exact congrArg rhoM (coe_genGL s).symm
    have key : ∀ g : SU42b, matOf e (π (θ.symm g)) = rhoM ((g : GL (Fin 8) (ZMod 2)) : Mat8) := by
      intro g
      have hg : g ∈ Subgroup.closure {genSU 0, genSU 1} := by
        rw [← SU42b_eq_closure]; exact Subgroup.mem_top g
      refine Subgroup.closure_induction (p := fun g _ =>
        matOf e (π (θ.symm g)) = rhoM ((g : GL (Fin 8) (ZMod 2)) : Mat8)) ?_ ?_ ?_ ?_ hg
      · rintro x (rfl | rfl)
        · exact hgens 0
        · exact hgens 1
      · rw [map_one, Subgroup.coe_one, map_one, matOf_one]
        rw [Subgroup.coe_one, Units.val_one, rhoM_one]
      · intro x y _ _ hx hy
        rw [map_mul, Subgroup.coe_mul, map_mul, matOf_mul, hx, hy, Subgroup.coe_mul, Units.val_mul,
          rhoM_mul]
      · intro x _ hx
        have h1 : matOf e (π (θ.symm x⁻¹)) * matOf e (π (θ.symm x)) = 1 := by
          rw [← matOf_mul, ← map_mul, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
            Subgroup.coe_one, map_one, matOf_one]
        have h2 : rhoM ((x⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) *
            rhoM ((x : GL (Fin 8) (ZMod 2)) : Mat8) = 1 := by
          rw [← rhoM_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
            Units.val_one, rhoM_one]
        rw [hx] at h1
        have h3 := (mul_eq_one_comm_of_card_eq (Fin 16) (Fin 16) (ZMod 2) rfl).mp h2
        calc matOf e (π (θ.symm x⁻¹))
            = matOf e (π (θ.symm x⁻¹)) * (rhoM ((x : GL (Fin 8) (ZMod 2)) : Mat8) *
                rhoM ((x⁻¹ : SU42b) : GL (Fin 8) (ZMod 2))) := by rw [h3, mul_one]
          _ = rhoM ((x⁻¹ : SU42b) : GL (Fin 8) (ZMod 2)) := by rw [← mul_assoc, h1, one_mul]
    intro k
    have := key (θ k)
    rwa [MulEquiv.symm_apply_apply] at this

end Step1

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
