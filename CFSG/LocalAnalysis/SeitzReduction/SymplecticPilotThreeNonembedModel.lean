module

public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply polar_quadMinus
  polar_quadMinus_single_inl)
open CFSG.RankThree.Classical2 (orthDerived)

section Levi

variable {K : Type} [Field K] {m : ℕ}

@[expose] def nmLeviFun (A B : Matrix (Fin m) (Fin m) K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    Fin m ⊕ Fin m ⊕ Fin 2 → K :=
  Sum.elim (A *ᵥ fun i => v (.inl i)) (Sum.elim ((fun i => v (.inr (.inl i))) ᵥ* B)
    fun k => v (.inr (.inr k)))

@[simp] theorem nmLeviFun_inl (A B : Matrix (Fin m) (Fin m) K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (i : Fin m) : nmLeviFun A B v (.inl i) = (A *ᵥ fun i => v (.inl i)) i := rfl

@[simp] theorem nmLeviFun_inr_inl (A B : Matrix (Fin m) (Fin m) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) (i : Fin m) :
    nmLeviFun A B v (.inr (.inl i)) = ((fun i => v (.inr (.inl i))) ᵥ* B) i := rfl

@[simp] theorem nmLeviFun_inr_inr (A B : Matrix (Fin m) (Fin m) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) (k : Fin 2) :
    nmLeviFun A B v (.inr (.inr k)) = v (.inr (.inr k)) := rfl

theorem nmLeviFun_comp (A B A' B' : Matrix (Fin m) (Fin m) K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    nmLeviFun A B (nmLeviFun A' B' v) = nmLeviFun (A * A') (B' * B) v := by
  funext j
  rcases j with i | i | k
  · simp [Matrix.mulVec_mulVec]
  · simp [Matrix.vecMul_vecMul]
  · simp

theorem nmLeviFun_one (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) : nmLeviFun 1 1 v = v := by
  funext j
  rcases j with i | i | k <;> simp

@[expose] def nmLeviLin (A B : Matrix (Fin m) (Fin m) K) :
    (Fin m ⊕ Fin m ⊕ Fin 2 → K) →ₗ[K] (Fin m ⊕ Fin m ⊕ Fin 2 → K) where
  toFun := nmLeviFun A B
  map_add' v w := by
    funext j
    rcases j with i | i | k
    · simp only [nmLeviFun_inl, Pi.add_apply]
      rw [show (fun i => v (.inl i) + w (.inl i)) = (fun i => v (.inl i)) + fun i => w (.inl i)
        from rfl, Matrix.mulVec_add, Pi.add_apply]
    · simp only [nmLeviFun_inr_inl, Pi.add_apply]
      rw [show (fun i => v (.inr (.inl i)) + w (.inr (.inl i))) =
        (fun i => v (.inr (.inl i))) + fun i => w (.inr (.inl i)) from rfl, Matrix.add_vecMul,
        Pi.add_apply]
    · simp
  map_smul' c v := by
    funext j
    rcases j with i | i | k
    · simp only [nmLeviFun_inl, Pi.smul_apply, RingHom.id_apply]
      rw [show (fun i => c • v (.inl i)) = c • fun i => v (.inl i) from rfl, Matrix.mulVec_smul,
        Pi.smul_apply]
    · simp only [nmLeviFun_inr_inl, Pi.smul_apply, RingHom.id_apply]
      rw [show (fun i => c • v (.inr (.inl i))) = c • fun i => v (.inr (.inl i)) from rfl,
        Matrix.smul_vecMul, Pi.smul_apply]
    · simp

theorem nmLeviFun_zero (A B : Matrix (Fin m) (Fin m) K) : nmLeviFun A B 0 = 0 :=
  (nmLeviLin A B).map_zero

@[expose] noncomputable def nmLevi : GL (Fin m) K →* ((Fin m ⊕ Fin m ⊕ Fin 2 → K) ≃ₗ[K]
    (Fin m ⊕ Fin m ⊕ Fin 2 → K)) where
  toFun A := LinearEquiv.ofLinearMap
    (nmLeviLin (A : Matrix _ _ K) ((A⁻¹ : GL (Fin m) K) : Matrix _ _ K))
    (nmLeviLin ((A⁻¹ : GL (Fin m) K) : Matrix _ _ K) (A : Matrix _ _ K))
    (LinearMap.ext fun v => by
      change nmLeviFun _ _ (nmLeviFun _ _ v) = v
      rw [nmLeviFun_comp, Units.mul_inv, nmLeviFun_one])
    (LinearMap.ext fun v => by
      change nmLeviFun _ _ (nmLeviFun _ _ v) = v
      rw [nmLeviFun_comp, Units.inv_mul, nmLeviFun_one])
  map_one' := LinearEquiv.ext fun v => by
    change nmLeviFun _ _ v = v
    rw [inv_one, Units.val_one, nmLeviFun_one]
  map_mul' A B := LinearEquiv.ext fun v => by
    change nmLeviFun _ _ v = nmLeviFun _ _ (nmLeviFun _ _ v)
    rw [nmLeviFun_comp, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]

theorem nmLevi_apply (A : GL (Fin m) K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    nmLevi A v = nmLeviFun (A : Matrix _ _ K) ((A⁻¹ : GL (Fin m) K) : Matrix _ _ K) v := rfl

theorem nmLevi_injective : Function.Injective (nmLevi (K := K) (m := m)) := by
  intro A B h
  ext i j
  have := congrArg (fun g : (Fin m ⊕ Fin m ⊕ Fin 2 → K) ≃ₗ[K] (Fin m ⊕ Fin m ⊕ Fin 2 → K) =>
    g (Pi.single (.inl j) 1) (.inl i)) h
  simp only [nmLevi_apply, nmLeviFun_inl] at this
  have e : (fun i' : Fin m =>
      (Pi.single (Sum.inl j) (1 : K) : Fin m ⊕ Fin m ⊕ Fin 2 → K) (.inl i')) = Pi.single j 1 := by
    funext i'
    by_cases h : i' = j
    · subst h
      simp
    · simp [h]
  rw [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  exact this

theorem dotProduct_mulVec_vecMul_inv (A : GL (Fin m) K) (p q : Fin m → K) :
    ((A : Matrix (Fin m) (Fin m) K) *ᵥ p) ⬝ᵥ
      (q ᵥ* ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) = p ⬝ᵥ q := by
  rw [dotProduct_comm, dotProduct_mulVec, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one,
    dotProduct_comm]

end Levi

section Form

variable {K : Type} [Field K] {n : ℕ} {b c : K}

theorem nmLevi_mem_orthogonalGroup (A : GL (Fin (n - 1)) K) :
    nmLevi A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [quadMinus_apply, quadMinus_apply]
  simp only [nmLevi_apply, nmLeviFun_inl, nmLeviFun_inr_inl, nmLeviFun_inr_inr]
  have h := dotProduct_mulVec_vecMul_inv A (fun i => v (.inl i)) (fun i => v (.inr (.inl i)))
  simp only [dotProduct] at h
  rw [h]

theorem polar_quadMinus_tail (v t : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (ht₁ : ∀ i, t (.inl i) = 0) (ht₂ : ∀ i, t (.inr (.inl i)) = 0) :
    polar (quadMinus n K b c) v t = 2 * (v (.inr (.inr 0)) * t (.inr (.inr 0))) +
      b * (v (.inr (.inr 0)) * t (.inr (.inr 1)) + t (.inr (.inr 0)) * v (.inr (.inr 1))) +
      2 * c * (v (.inr (.inr 1)) * t (.inr (.inr 1))) := by
  rw [polar_quadMinus]
  simp [ht₁, ht₂]

theorem polar_single_inl_tail (i : Fin (n - 1)) {t : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (ht₂ : ∀ i, t (.inr (.inl i)) = 0) :
    polar (quadMinus n K b c) (Pi.single (.inl i) 1) t = 0 := by
  rw [polar_comm, polar_quadMinus_single_inl, ht₂]

end Form

section Flag

variable {K : Type} [Field K]

theorem mem_flagKernel_of_sub_mem {V : Type*} [AddCommGroup V] [Module K V]
    {F : ℕ → Submodule K V} (hF : Monotone F) (h0 : F 0 = ⊥) {g : V ≃ₗ[K] V}
    (h₁ : ∀ k, ∀ v ∈ F (k + 1), g v - v ∈ F k) (h₂ : ∀ k, ∀ v ∈ F (k + 1), g⁻¹ v - v ∈ F k) :
    g ∈ flagKernel LinearEquiv.automorphismGroup.toLinearMapMonoidHom F := by
  have hstay : ∀ h : V ≃ₗ[K] V, (∀ k, ∀ v ∈ F (k + 1), h v - v ∈ F k) →
      ∀ k, ∀ v ∈ F k, h v ∈ F k := by
    intro h hh k v hv
    cases k with
    | zero =>
      rw [h0, Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ k =>
      have := add_mem (hF (Nat.le_succ k) (hh k v hv)) hv
      rwa [sub_add_cancel] at this
  exact ⟨fun k v hv => ⟨hstay g h₁ k v hv, hstay g⁻¹ h₂ k v hv⟩, h₁⟩

theorem toLinearMapMonoidHom_injective {V : Type*} [AddCommGroup V] [Module K V] :
    Function.Injective (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) :=
  fun _ _ h => LinearEquiv.toLinearMap_injective h

variable {m : ℕ}

@[expose] def nmT : Submodule K (Fin m ⊕ Fin m ⊕ Fin 2 → K) where
  carrier := {v | ∀ j, v (.inr j) = 0}
  add_mem' {v w} hv hw j := by simp [hv j, hw j]
  zero_mem' _ := rfl
  smul_mem' c v hv j := by simp [hv j]

@[expose] def nmS : Submodule K (Fin m ⊕ Fin m ⊕ Fin 2 → K) where
  carrier := {v | ∀ i, v (.inr (.inl i)) = 0}
  add_mem' {v w} hv hw i := by simp [hv i, hw i]
  zero_mem' _ := rfl
  smul_mem' c v hv i := by simp [hv i]

theorem nmT_le_nmS : (nmT : Submodule K (Fin m ⊕ Fin m ⊕ Fin 2 → K)) ≤ nmS :=
  fun _ hv i => hv (.inl i)

@[expose] def nmFlag : ℕ → Submodule K (Fin m ⊕ Fin m ⊕ Fin 2 → K)
  | 0 => ⊥
  | 1 => nmT
  | 2 => nmS
  | _ + 3 => ⊤

theorem nmFlag_zero : nmFlag (K := K) (m := m) 0 = ⊥ := rfl

theorem nmFlag_three : nmFlag (K := K) (m := m) 3 = ⊤ := rfl

theorem nmFlag_mono : Monotone (nmFlag (K := K) (m := m)) := by
  refine monotone_nat_of_le_succ fun k => ?_
  match k with
  | 0 => exact bot_le
  | 1 => exact nmT_le_nmS
  | 2 => exact le_top
  | k + 3 => exact le_top

theorem nmLeviFun_mem_nmFlag (A B : Matrix (Fin m) (Fin m) K) :
    ∀ k, ∀ v ∈ nmFlag (K := K) (m := m) k, nmLeviFun A B v ∈ nmFlag (K := K) (m := m) k := by
  intro k v hv
  match k with
  | 0 =>
    change v ∈ (⊥ : Submodule K _) at hv
    change nmLeviFun A B v ∈ (⊥ : Submodule K _)
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, nmLeviFun_zero]
  | 1 =>
    have hv' : ∀ j, v (.inr j) = 0 := hv
    have hf : (fun i => v (.inr (.inl i))) = 0 := funext fun i => hv' (.inl i)
    change ∀ j, nmLeviFun A B v (.inr j) = 0
    rintro (i | k)
    · rw [nmLeviFun_inr_inl, hf, Matrix.zero_vecMul, Pi.zero_apply]
    · rw [nmLeviFun_inr_inr, hv' (.inr k)]
  | 2 =>
    have hv' : ∀ i, v (.inr (.inl i)) = 0 := hv
    have hf : (fun i => v (.inr (.inl i))) = 0 := funext hv'
    change ∀ i, nmLeviFun A B v (.inr (.inl i)) = 0
    intro i
    rw [nmLeviFun_inr_inl, hf, Matrix.zero_vecMul, Pi.zero_apply]
  | k + 3 => exact Submodule.mem_top

theorem nmLevi_mem_flagStab (A : GL (Fin m) K) :
    nmLevi A ∈ flagStab LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (nmFlag (K := K) (m := m)) := by
  intro k v hv
  refine ⟨nmLeviFun_mem_nmFlag _ _ k v hv, ?_⟩
  rw [← map_inv]
  exact nmLeviFun_mem_nmFlag _ _ k v hv

end Flag

section Radical

variable {K : Type} [Field K] {n : ℕ} {b c : K}

theorem eichler_sub_mem_nmFlag (i : Fin (n - 1)) {t : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (ht₁ : ∀ i, t (.inl i) = 0) (ht₂ : ∀ i, t (.inr (.inl i)) = 0) :
    ∀ k, ∀ v ∈ nmFlag (K := K) (m := n - 1) (k + 1),
      eichler (quadMinus n K b c) (Pi.single (.inl i) 1) t v - v ∈
        nmFlag (K := K) (m := n - 1) k := by
  intro k v hv
  have hE : eichler (quadMinus n K b c) (Pi.single (.inl i) 1) t v - v =
      v (.inr (.inl i)) • t - (polar (quadMinus n K b c) v t +
        quadMinus n K b c t * v (.inr (.inl i))) • Pi.single (.inl i) 1 := by
    rw [eichler_apply (quadMinus_single_inl i) (polar_single_inl_tail i ht₂),
      polar_quadMinus_single_inl]
    abel
  have heT : (Pi.single (.inl i) 1 : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ∈ nmT := by
    intro j
    simp
  have htS : t ∈ nmS := ht₂
  rw [hE]
  match k with
  | 0 =>
    have hv' : ∀ j, v (.inr j) = 0 := hv
    have hp : polar (quadMinus n K b c) v t = 0 := by
      rw [polar_quadMinus_tail v t ht₁ ht₂, hv' (.inr 0), hv' (.inr 1)]
      ring
    change _ ∈ (⊥ : Submodule K _)
    rw [hp, hv' (.inl i), Submodule.mem_bot]
    simp
  | 1 =>
    have hv' : ∀ i, v (.inr (.inl i)) = 0 := hv
    change _ ∈ nmT
    rw [hv' i, zero_smul, zero_sub, mul_zero, add_zero]
    exact neg_mem (Submodule.smul_mem _ _ heT)
  | 2 =>
    change _ ∈ nmS
    exact sub_mem (Submodule.smul_mem _ _ htS) (Submodule.smul_mem _ _ (nmT_le_nmS heT))
  | k + 3 => exact Submodule.mem_top

theorem eichler_mem_nmFlagKernel (i : Fin (n - 1)) {t : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (ht₁ : ∀ i, t (.inl i) = 0) (ht₂ : ∀ i, t (.inr (.inl i)) = 0) :
    eichler (quadMinus n K b c) (Pi.single (.inl i) 1) t ∈
      flagKernel LinearEquiv.automorphismGroup.toLinearMapMonoidHom
        (nmFlag (K := K) (m := n - 1)) := by
  refine mem_flagKernel_of_sub_mem nmFlag_mono rfl (eichler_sub_mem_nmFlag i ht₁ ht₂) ?_
  rw [eichler_inv (polar_single_inl_tail i ht₂)]
  exact eichler_sub_mem_nmFlag i (t := -t) (fun j => by simp [ht₁ j]) (fun j => by simp [ht₂ j])

theorem eichler_mul_ne (hn : 3 ≤ n) (hb : b ≠ 0) :
    eichler (quadMinus n K b c) (Pi.single (.inl ⟨0, by omega⟩) 1) (Pi.single (.inr (.inr 0)) 1) *
      eichler (quadMinus n K b c) (Pi.single (.inl ⟨1, by omega⟩) 1)
        (Pi.single (.inr (.inr 1)) 1) ≠
    eichler (quadMinus n K b c) (Pi.single (.inl ⟨1, by omega⟩) 1) (Pi.single (.inr (.inr 1)) 1) *
      eichler (quadMinus n K b c) (Pi.single (.inl ⟨0, by omega⟩) 1)
        (Pi.single (.inr (.inr 0)) 1) := by
  set i₀ : Fin (n - 1) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (n - 1) := ⟨1, by omega⟩ with hi₁
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  set e₀ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K := Pi.single (.inl i₀) 1 with he₀
  set e₁ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K := Pi.single (.inl i₁) 1 with he₁
  set f₀ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K := Pi.single (.inr (.inl i₀)) 1 with hf₀
  set tu : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K := Pi.single (.inr (.inr 0)) 1 with htu
  set tw : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K := Pi.single (.inr (.inr 1)) 1 with htw
  have htu₁ : ∀ i, tu (.inl i) = 0 := fun i => by simp [htu]
  have htu₂ : ∀ i, tu (.inr (.inl i)) = 0 := fun i => by simp [htu]
  have htw₁ : ∀ i, tw (.inl i) = 0 := fun i => by simp [htw]
  have htw₂ : ∀ i, tw (.inr (.inl i)) = 0 := fun i => by simp [htw]
  have hQtu : quadMinus n K b c tu = 1 := by
    rw [quadMinus_apply]
    simp [htu]
  have hpf₀e₀ : polar (quadMinus n K b c) f₀ e₀ = 1 := by
    rw [he₀, polar_quadMinus_single_inl]
    simp [hf₀]
  have hpf₀e₁ : polar (quadMinus n K b c) f₀ e₁ = 0 := by
    rw [he₁, polar_quadMinus_single_inl]
    simp [hf₀, h01]
  have hpf₀tu : polar (quadMinus n K b c) f₀ tu = 0 := by
    rw [polar_quadMinus_tail f₀ tu htu₁ htu₂]
    simp [hf₀]
  have hpf₀tw : polar (quadMinus n K b c) f₀ tw = 0 := by
    rw [polar_quadMinus_tail f₀ tw htw₁ htw₂]
    simp [hf₀]
  have hpe₀e₁ : polar (quadMinus n K b c) e₀ e₁ = 0 := by
    rw [he₁, polar_quadMinus_single_inl]
    simp [he₀]
  have hpe₀tw : polar (quadMinus n K b c) e₀ tw = 0 := polar_single_inl_tail i₀ htw₂
  have hptue₁ : polar (quadMinus n K b c) tu e₁ = 0 := by
    rw [he₁, polar_quadMinus_single_inl, htu₂]
  have hptutw : polar (quadMinus n K b c) tu tw = b := by
    rw [polar_quadMinus_tail tu tw htw₁ htw₂]
    simp [htu, htw]
  have ha : eichler (quadMinus n K b c) e₀ tu f₀ = f₀ + tu - e₀ := by
    rw [eichler_apply (quadMinus_single_inl i₀) (polar_single_inl_tail i₀ htu₂), hpf₀e₀, hpf₀tu,
      hQtu]
    simp [he₀]
  have ha'f : eichler (quadMinus n K b c) e₁ tw f₀ = f₀ :=
    eichler_apply_of_polar_eq_zero hpf₀e₁ hpf₀tw
  have ha'e : eichler (quadMinus n K b c) e₁ tw e₀ = e₀ :=
    eichler_apply_of_polar_eq_zero hpe₀e₁ hpe₀tw
  have ha'u : eichler (quadMinus n K b c) e₁ tw tu = tu - b • e₁ := by
    rw [eichler_apply (quadMinus_single_inl i₁) (polar_single_inl_tail i₁ htw₂), hptue₁, hptutw]
    simp [he₁]
  intro h
  have hv := congrArg (fun g : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
    (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) => g f₀ (.inl i₁)) h
  simp only [LinearEquiv.mul_apply] at hv
  rw [ha'f, ha, map_sub, map_add, ha'f, ha'u, ha'e] at hv
  simp [hf₀, htu, he₀, he₁, h01] at hv
  exact hb hv

end Radical

section Data

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nm_mem_orthDerived_of_pow_eq_one {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hodd : Odd p)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1) :
    g ∈ orthDerived Q := by
  refine CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hg, ?_⟩)
  have h2 : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
  have hz : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨g, hg⟩ = 1 := by
    have hzp : (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨g, hg⟩) ^ p = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ^ p = 1 := Subtype.ext hgp
      rw [this, map_one]
    obtain ⟨k, hk⟩ := hodd
    have : (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨g, hg⟩) ^ (2 * k + 1) =
        CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ ⟨g, hg⟩ := by
      rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    rw [← this, ← hk]
    exact hzp
  rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply, ← ofAdd_zero,
    Multiplicative.ofAdd.injective.eq_iff, ZMod.natCast_eq_zero_iff_even] at hz
  exact hz

theorem ne_zero_of_irreducible_charTwo {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  apply hirr r
  rw [hr, zero_mul, add_zero, _root_.sq, CharTwo.add_self_eq_zero]

theorem exists_nonabelian_radical_quadMinus {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ℓ : ℕ} (hℓ : Odd ℓ) {A : GL (Fin (n - 1)) K}
    (hA : A ^ ℓ = 1) (hA1 : A ≠ 1) :
    ∃ (R : Subgroup (orthDerived (quadMinus n K b c))) (x : orthDerived (quadMinus n K b c)),
      IsPGroup 2 R ∧ x ∈ normalizer (R : Set (orthDerived (quadMinus n K b c))) ∧ x ^ ℓ = 1 ∧
        x ≠ 1 ∧ ∃ a ∈ R, ∃ a' ∈ R, a * a' ≠ a' * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hnd, hT⟩ := regular_quadMinus (K := K) (b := b) (c := c) hn hirr
  have hΩE := (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hnd hT).1
  set R₀ := flagKernel LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    (nmFlag (K := K) (m := n - 1)) with hR₀
  have hR₀p : IsPGroup 2 R₀ :=
    isPGroup_flagKernel LinearEquiv.automorphismGroup.toLinearMapMonoidHom 2
      toLinearMapMonoidHom_injective nmFlag_zero nmFlag_three
  have hxO := nmLevi_mem_orthogonalGroup (b := b) (c := c) A
  have hxp : nmLevi A ^ ℓ = 1 := by rw [← map_pow, hA, map_one]
  have hxΩ : nmLevi A ∈ orthDerived (quadMinus n K b c) :=
    nm_mem_orthDerived_of_pow_eq_one hnd hT hℓ hxO hxp
  have hxN₀ : nmLevi A ∈ normalizer (R₀ : Set _) :=
    flagStab_le_normalizer_flagKernel _ _ (nmLevi_mem_flagStab A)
  have hEΩ : ∀ u w, eichler (quadMinus n K b c) u w ∈ orthDerived (quadMinus n K b c) :=
    fun u w => hΩE ▸ eichler_mem_elementaryGroup _ u w
  set a₀ := eichler (quadMinus n K b c) (Pi.single (.inl ⟨0, by omega⟩) 1)
    (Pi.single (.inr (.inr 0)) 1) with ha₀
  set a₁ := eichler (quadMinus n K b c) (Pi.single (.inl ⟨1, by omega⟩) 1)
    (Pi.single (.inr (.inr 1)) 1) with ha₁
  have ha₀R : a₀ ∈ R₀ := eichler_mem_nmFlagKernel _ (fun i => by simp) (fun i => by simp)
  have ha₁R : a₁ ∈ R₀ := eichler_mem_nmFlagKernel _ (fun i => by simp) (fun i => by simp)
  refine ⟨R₀.comap (orthDerived (quadMinus n K b c)).subtype, ⟨nmLevi A, hxΩ⟩,
    hR₀p.comap_of_injective _ (orthDerived (quadMinus n K b c)).subtype_injective, ?_,
    Subtype.ext (by simpa using hxp), fun h => hA1 (nmLevi_injective ?_),
    ⟨a₀, hEΩ _ _⟩, ha₀R, ⟨a₁, hEΩ _ _⟩, ha₁R,
    fun h => eichler_mul_ne (by omega) (ne_zero_of_irreducible_charTwo hirr)
      (congrArg Subtype.val h)⟩
  · rw [mem_normalizer_iff]
    intro g
    exact mem_normalizer_iff.1 hxN₀ g
  · rw [map_one]
    exact congrArg Subtype.val h

end Data

end CFSG.SeitzReduction.SymplecticPilot
