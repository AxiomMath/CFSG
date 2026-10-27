module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {b c : K}

@[expose] def permLE (K : Type) [Field K] (σ : Equiv.Perm (Fin 3)) :
    ModelSpace K ≃ₗ[K] ModelSpace K :=
  (LinearEquiv.funCongrLeft K (K × K) σ).prodCongr (LinearEquiv.refl K (K × K))

theorem permLE_apply (σ : Equiv.Perm (Fin 3)) (x : ModelSpace K) :
    permLE K σ x = (fun i => x.1 (σ i), x.2) :=
  rfl

theorem permLE_mem_modelO (b c : K) (σ : Equiv.Perm (Fin 3)) : permLE K σ ∈ modelO b c := by
  rw [modelO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [modelForm_apply, modelForm_apply]
  have hsum : (∑ i, rotForm K ((permLE K σ x).1 i)) = ∑ i, rotForm K (x.1 i) := by
    simp only [permLE_apply]
    exact Equiv.sum_comp σ (fun i => rotForm K (x.1 i))
  rw [hsum]
  rfl

theorem permLE_mul_cmEquiv_mul_inv (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → ZMod 3) :
    permLE K σ * cmEquiv K v * (permLE K σ)⁻¹ = cmEquiv K (fun i => v (σ i)) := by
  have key : permLE K σ * cmEquiv K v = cmEquiv K (fun i => v (σ i)) * permLE K σ := by
    refine LinearEquiv.ext fun x => ?_
    simp only [LinearEquiv.mul_apply]
    refine Prod.ext (funext fun i => ?_) ?_
    · simp [permLE_apply, cmEquiv_apply]
    · simp [permLE_apply, cmEquiv_apply]
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def flipPlane (K : Type) [Field K] : (K × K) ≃ₗ[K] (K × K) :=
  LinearEquiv.prodComm K K K

theorem flipPlane_apply (p : K × K) : flipPlane K p = (p.2, p.1) :=
  rfl

theorem flipPlane_mem_orthogonalGroup :
    flipPlane K ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro p
  rw [rotForm_apply, rotForm_apply, flipPlane_apply]
  dsimp only
  ring

theorem flipPlane_mul_rotLE :
    flipPlane K * rotLE K = (rotLE K)⁻¹ * flipPlane K := by
  refine LinearEquiv.ext fun p => ?_
  refine Prod.ext ?_ ?_ <;> simp [flipPlane_apply, rotLE] <;> ring

private theorem flipPlane_mul_rotLE_pow (n : ℕ) :
    flipPlane K * rotLE K ^ n = (rotLE K)⁻¹ ^ n * flipPlane K := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc flipPlane K * rotLE K ^ (n + 1)
          = (flipPlane K * rotLE K ^ n) * rotLE K := by rw [pow_succ, ← mul_assoc]
        _ = ((rotLE K)⁻¹ ^ n * flipPlane K) * rotLE K := by rw [ih]
        _ = (rotLE K)⁻¹ ^ n * (flipPlane K * rotLE K) := by rw [mul_assoc]
        _ = (rotLE K)⁻¹ ^ n * ((rotLE K)⁻¹ * flipPlane K) := by rw [flipPlane_mul_rotLE]
        _ = ((rotLE K)⁻¹ ^ n * (rotLE K)⁻¹) * flipPlane K := by rw [← mul_assoc]
        _ = (rotLE K)⁻¹ ^ (n + 1) * flipPlane K := by rw [← pow_succ]

theorem flipPlane_mul_rotPow (k : ZMod 3) :
    flipPlane K * rotPow K k = rotPow K (-k) * flipPlane K := by
  have hneg : rotPow K (-k) = (rotPow K k)⁻¹ := by
    have h : rotPow K k * rotPow K (-k) = 1 := by
      rw [← rotPow_add]
      exact (congrArg (rotPow K) (add_neg_cancel k)).trans rotPow_zero
    exact eq_inv_of_mul_eq_one_right h
  rw [hneg]
  unfold rotPow
  rw [flipPlane_mul_rotLE_pow, inv_pow]

private theorem zmod_eq_two_of_ne_zero_ne_one {a : ZMod 3} (h0 : a ≠ 0) (h1 : a ≠ 1) :
    a = 2 := by
  revert a
  decide

private theorem zmod_two_mul_eq_neg (a : ZMod 3) : (2 : ZMod 3) * a = -a := by
  revert a
  decide

@[expose] def signLE (K : Type) [Field K] (ε : Fin 3 → ZMod 3) : ModelSpace K ≃ₗ[K] ModelSpace K :=
  (LinearEquiv.piCongrRight fun i =>
    if ε i = 1 then LinearEquiv.refl K (K × K) else flipPlane K).prodCongr
      (LinearEquiv.refl K (K × K))

theorem signLE_apply (ε : Fin 3 → ZMod 3) (x : ModelSpace K) :
    signLE K ε x = (fun i => (if ε i = 1 then LinearEquiv.refl K (K × K) else flipPlane K) (x.1 i),
      x.2) :=
  rfl

theorem signLE_mem_modelO (b c : K) (ε : Fin 3 → ZMod 3) : signLE K ε ∈ modelO b c := by
  rw [modelO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [modelForm_apply, modelForm_apply]
  have hsum : (∑ i, rotForm K ((signLE K ε x).1 i)) = ∑ i, rotForm K (x.1 i) := by
    simp only [signLE_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ε i = 1
    · simp [h]
    · simp only [if_neg h]
      exact CFSG.ClassicalGroups.Orthogonal.map_of_mem flipPlane_mem_orthogonalGroup (x.1 i)
  rw [hsum]
  rfl

theorem signLE_mul_cmEquiv_mul_inv (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0)
    (v : Fin 3 → ZMod 3) :
    signLE K ε * cmEquiv K v * (signLE K ε)⁻¹ = cmEquiv K (fun i => ε i * v i) := by
  have key : signLE K ε * cmEquiv K v = cmEquiv K (fun i => ε i * v i) * signLE K ε := by
    refine LinearEquiv.ext fun x => ?_
    refine Prod.ext (funext fun i => ?_) ?_
    · simp only [LinearEquiv.mul_apply, signLE_apply, cmEquiv_apply]
      by_cases h : ε i = 1
      · simp [h]
      · have hε2 : ε i = 2 := zmod_eq_two_of_ne_zero_ne_one (hε i) h
        have hmul : ε i * v i = -(v i) := by rw [hε2]; exact zmod_two_mul_eq_neg (v i)
        simp only [if_neg h]
        rw [← LinearEquiv.mul_apply, flipPlane_mul_rotPow, LinearEquiv.mul_apply, hmul]
    · simp [LinearEquiv.mul_apply, signLE_apply, cmEquiv_apply]
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

@[expose] noncomputable def wReflections (b c : K) :
    Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K) :=
  Subgroup.closure (Set.range fun p : K × K => reflect (modelForm b c) (wVec p))

theorem modelForm_wVec (b c : K) (p : K × K) : modelForm b c (wVec p) = wForm b c p := by
  rw [modelForm_apply]
  simp [wVec]

theorem wReflections_le_modelO (b c : K) : wReflections b c ≤ modelO b c := by
  rw [wReflections]
  refine (Subgroup.closure_le (modelO b c)).2 ?_
  rintro _ ⟨p, rfl⟩
  exact reflect_mem_orthogonalGroup (modelForm b c) (wVec p)

theorem commute_cmEquiv_of_mem_wReflections {h : ModelSpace K ≃ₗ[K] ModelSpace K}
    (hh : h ∈ wReflections b c) (v : Fin 3 → ZMod 3) : Commute h (cmEquiv K v) := by
  rw [wReflections] at hh
  refine Subgroup.closure_induction (p := fun h _ => Commute h (cmEquiv K v)) ?_ ?_ ?_ ?_ hh
  · rintro x ⟨p, rfl⟩
    refine (commute_iff_eq _ _).2 ?_
    have hconj : cmEquiv K v * reflect (modelForm b c) (wVec p) * (cmEquiv K v)⁻¹ =
        reflect (modelForm b c) (wVec p) := by
      have h1 : cmEquiv K v * reflect (modelForm b c) (wVec p) * (cmEquiv K v)⁻¹ =
          reflect (modelForm b c) (cmEquiv K v (wVec p)) :=
        reflect_conj (cm_mem_modelO b c (Multiplicative.ofAdd v)) (wVec p)
      rw [cmEquiv_apply_wVec] at h1
      exact h1
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  · exact Commute.one_left _
  · intro x y hx hy hx' hy'
    exact hx'.mul_left hy'
  · intro x hx hx'
    exact hx'.inv_left

theorem reflect_mem_modelOmega_mul_wReflections [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (v : ModelSpace K) :
    ∃ n ∈ modelOmega b c, ∃ h ∈ wReflections b c, reflect (modelForm b c) v = n * h := by
  obtain ⟨p, hp⟩ := exists_wForm_eq hbc (modelForm b c v)
  have hp' : modelForm b c (wVec p) = modelForm b c v := by
    rw [modelForm_wVec]
    exact hp
  refine ⟨reflect (modelForm b c) v * reflect (modelForm b c) (wVec p),
    reflect_mul_reflect_mem_modelOmega h3 hbc hp', reflect (modelForm b c) (wVec p),
    Subgroup.subset_closure ⟨p, rfl⟩, ?_⟩
  rw [mul_assoc, reflect_mul_self, mul_one]

theorem exists_mem_modelOmega_mul_wReflections [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : ModelSpace K ≃ₗ[K] ModelSpace K}
    (hg : g ∈ modelO b c) : ∃ n ∈ modelOmega b c, ∃ h ∈ wReflections b c, g = n * h := by
  have hg' := modelO_le_closure_reflect h3 hbc hg
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ n ∈ modelOmega b c, ∃ h ∈ wReflections b c, g = n * h) ?_ ?_ ?_ ?_ hg'
  · rintro a (⟨v, rfl⟩ | ha)
    · exact reflect_mem_modelOmega_mul_wReflections h3 hbc v
    · exact ⟨a, ha, 1, Subgroup.one_mem _, (mul_one a).symm⟩
  · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, (one_mul 1).symm⟩
  · rintro a b ha hb ⟨n₁, hn₁, h₁, hh₁, rfl⟩ ⟨n₂, hn₂, h₂, hh₂, rfl⟩
    refine ⟨n₁ * (h₁ * n₂ * h₁⁻¹),
      mul_mem hn₁ (conj_mem_modelOmega (wReflections_le_modelO b c hh₁) hn₂),
      h₁ * h₂, mul_mem hh₁ hh₂, ?_⟩
    group
  · rintro a ha ⟨n, hn, h, hh, rfl⟩
    refine ⟨h⁻¹ * n⁻¹ * (h⁻¹)⁻¹,
      conj_mem_modelOmega (wReflections_le_modelO b c (inv_mem hh)) (inv_mem hn),
      h⁻¹, inv_mem hh, ?_⟩
    group

theorem exists_mem_modelOmega_conj_eq [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : ModelSpace K ≃ₗ[K] ModelSpace K}
    (hg : g ∈ modelO b c) (f : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hf : ∀ v, g * cmEquiv K v * g⁻¹ = cmEquiv K (f v)) :
    ∃ n ∈ modelOmega b c, ∀ v, n * cmEquiv K v * n⁻¹ = cmEquiv K (f v) := by
  obtain ⟨n, hn, h, hh, hgh⟩ := exists_mem_modelOmega_mul_wReflections h3 hbc hg
  refine ⟨n, hn, fun v => ?_⟩
  have hn_eq : n = g * h⁻¹ := by rw [hgh, mul_assoc, mul_inv_cancel, mul_one]
  have hc : Commute h (cmEquiv K v) := commute_cmEquiv_of_mem_wReflections hh v
  rw [hn_eq]
  have hkey : (g * h⁻¹) * cmEquiv K v * (g * h⁻¹)⁻¹ = g * cmEquiv K v * g⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    have hc' : Commute h⁻¹ (cmEquiv K v) := hc.inv_left
    calc (g * h⁻¹) * cmEquiv K v * (h * g⁻¹)
        = g * (h⁻¹ * cmEquiv K v * h) * g⁻¹ := by group
      _ = g * cmEquiv K v * g⁻¹ := by
            have hmid : h⁻¹ * cmEquiv K v * h = cmEquiv K v := by
              rw [hc'.eq, mul_assoc, inv_mul_cancel, mul_one]
            rw [hmid]
  rw [hkey]
  exact hf v

theorem exists_mem_modelOmega_conj_cmEquiv_signedPerm [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ∃ n ∈ modelOmega b c, ∀ v : Fin 3 → ZMod 3,
      n * cmEquiv K v * n⁻¹ = cmEquiv K (fun i => ε i * v (σ i)) := by
  have hgO : signLE K ε * permLE K σ ∈ modelO b c :=
    mul_mem (signLE_mem_modelO b c ε) (permLE_mem_modelO b c σ)
  have hf : ∀ v, (signLE K ε * permLE K σ) * cmEquiv K v * (signLE K ε * permLE K σ)⁻¹ =
      cmEquiv K (fun i => ε i * v (σ i)) := by
    intro v
    calc (signLE K ε * permLE K σ) * cmEquiv K v * (signLE K ε * permLE K σ)⁻¹
        = signLE K ε * (permLE K σ * cmEquiv K v * (permLE K σ)⁻¹) * (signLE K ε)⁻¹ := by
          group
      _ = signLE K ε * cmEquiv K (fun i => v (σ i)) * (signLE K ε)⁻¹ := by
          rw [permLE_mul_cmEquiv_mul_inv]
      _ = cmEquiv K (fun i => ε i * v (σ i)) := by
          rw [signLE_mul_cmEquiv_mul_inv ε hε]
  exact exists_mem_modelOmega_conj_eq h3 hbc hgO (fun v i => ε i * v (σ i)) hf

theorem exists_conj_c₀_signedPerm [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ∃ n : ↥(omegaMinus8 K b c), ∀ v : Multiplicative (Fin 3 → ZMod 3),
      n * c₀ h3 hbc v * n⁻¹ = c₀ h3 hbc
        (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
  obtain ⟨n, hn, hnv⟩ := exists_mem_modelOmega_conj_cmEquiv_signedPerm h3 hbc σ ε hε
  exact exists_conj_c₀_of_cmEquiv h3 hbc (fun v i => ε i * v (σ i)) hn hnv

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
