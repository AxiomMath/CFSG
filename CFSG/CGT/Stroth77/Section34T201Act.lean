module

public import CFSG.CGT.Stroth77.Section34T201Mats
public import CFSG.CGT.Stroth77.Section34T201R1

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T201Levels

open Matrix

section Mat

variable {k : Fin 3 → ℕ}

@[expose] noncomputable def matOf (φ : Torus k →+ Torus k) : IntMat :=
  Matrix.of fun i j => ((φ (gen k j) i).val : ℤ)

theorem matOf_apply (φ : Torus k →+ Torus k) (i j : Fin 3) :
    matOf φ i j = ((φ (gen k j) i).val : ℤ) := rfl

theorem two_pow_nsmul_gen (j : Fin 3) : (2 ^ k j : ℕ) • gen k j = 0 := by
  funext l
  by_cases h : l = j
  · subst h; simp [gen]
  · simp [gen, Pi.single_eq_of_ne h]

theorem compat_matOf (φ : Torus k →+ Torus k) : Compat k (matOf φ) := by
  intro i j
  have h1 := congrArg (fun x => x i) (congrArg φ (two_pow_nsmul_gen (k := k) j))
  simp only [map_nsmul, map_zero, Pi.smul_apply, Pi.zero_apply] at h1
  have h2 : (((2 ^ k j * ((φ (gen k j) i).val : ℤ)) : ℤ) : ZMod (2 ^ k i)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    simpa [nsmul_eq_mul] using h1
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  rw [matOf_apply]
  exact_mod_cast this

theorem matAct_matOf (φ : Torus k →+ Torus k) : matAct k (matOf φ) (compat_matOf φ) = φ := by
  refine torus_hom_ext _ _ fun j z => ?_
  funext i
  rw [matAct_single]
  have hs : (Pi.single j (z : ZMod (2 ^ k j)) : Torus k) = z • gen k j := by
    funext l
    by_cases h : l = j
    · subst h; simp [gen]
    · simp [gen, Pi.single_eq_of_ne h]
  rw [hs, map_zsmul, Pi.smul_apply, matOf_apply]
  push_cast
  rw [ZMod.natCast_zmod_val, zsmul_eq_mul]

theorem MatEq.symm' {A B : IntMat} (h : MatEq k A B) : MatEq k B A := fun i j => (h i j).symm

theorem MatEq.trans {A B C : IntMat} (h₁ : MatEq k A B) (h₂ : MatEq k B C) : MatEq k A C :=
  fun i j => (h₁ i j).trans (h₂ i j)

theorem MatEq.mono {k' : Fin 3 → ℕ} (hk : ∀ i, k' i ≤ k i) {A B : IntMat} (h : MatEq k A B) :
    MatEq k' A B := fun i j =>
  Int.ModEq.of_dvd (pow_dvd_pow 2 (hk i)) (h i j)

theorem MatEq.mul_right {A A' : IntMat} (h : MatEq k A A') (B : IntMat) :
    MatEq k (A * B) (A' * B) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Int.ModEq.sum fun l _ => (h i l).mul_right _

theorem MatEq.mul_left {B : IntMat} (hB : Compat k B) {A A' : IntMat} (h : MatEq k A A') :
    MatEq k (B * A) (B * A') := fun i j => by
  simp only [Matrix.mul_apply]
  refine Int.ModEq.sum fun l _ => ?_
  rw [Int.modEq_iff_dvd]
  obtain ⟨c, hc⟩ := hB i l
  obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp (h l j)
  refine ⟨c * d, ?_⟩
  calc B i l * A' l j - B i l * A l j = B i l * (A' l j - A l j) := by ring
    _ = B i l * (2 ^ k l * d) := by rw [hd]
    _ = 2 ^ k l * B i l * d := by ring
    _ = 2 ^ k i * (c * d) := by rw [hc]; ring

theorem matEq_of_matAct_eq {A B : IntMat} (hA : Compat k A) (hB : Compat k B)
    (h : ∀ v, matAct k A hA v = matAct k B hB v) : MatEq k A B :=
  (matAct_eq_iff hA hB).mp (AddMonoidHom.ext h)

theorem matAct_mul_apply {A B : IntMat} (hA : Compat k A) (hB : Compat k B) (v : Torus k) :
    matAct k (A * B) (hA.mul hB) v = matAct k A hA (matAct k B hB v) := by
  rw [matAct_mul]; rfl

theorem Compat.shift {s : ℕ} (hk : ∀ i, s ≤ k i) {M : IntMat} (h : Compat k M) :
    Compat (fun i => k i - s) M := fun i j => by
  obtain ⟨c, hc⟩ := h i j
  refine ⟨c, ?_⟩
  have e₁ : (2 : ℤ) ^ k j = 2 ^ (k j - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel (hk j)]
  have e₂ : (2 : ℤ) ^ k i = 2 ^ (k i - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel (hk i)]
  rw [e₁, e₂] at hc
  have h2 : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero s two_ne_zero
  exact mul_left_cancel₀ h2 (by linear_combination hc)

theorem IsAut1.shift {s : ℕ} (hk : ∀ i, s + 1 ≤ k i) {M : IntMat} (h : IsAut1 k M) :
    IsAut1 (fun i => k i - s) M := fun i j => by
  have hij := Int.modEq_iff_dvd.mp (h i j)
  rw [Int.modEq_iff_dvd]
  simp only [omegaMat, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hij ⊢
  obtain ⟨c, hc⟩ := hij
  refine ⟨c, ?_⟩
  have e₁ : (2 : ℤ) ^ (k j - 1) = 2 ^ (k j - s - 1) * 2 ^ s := by
    rw [← pow_add]; congr 1; have := hk j; omega
  have e₂ : (2 : ℤ) ^ k i = 2 ^ (k i - s) * 2 ^ s := by
    rw [← pow_add, Nat.sub_add_cancel (by have := hk i; omega)]
  have h2 : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero s two_ne_zero
  split_ifs at hc ⊢ with hij'
  · subst hij'
    rw [e₁, e₂] at hc
    exact mul_left_cancel₀ h2 (by linear_combination hc)
  · rw [e₁, e₂] at hc
    exact mul_left_cancel₀ h2 (by linear_combination hc)

theorem type200_k_eq {m p : ℕ} (hp : p ≤ m) :
    Type200.k p = fun i => Type201.k m i - (m - p) := by
  funext i
  fin_cases i <;> simp [Type200.k, Type201.k] <;> omega

end Mat

end Stroth34T201Levels

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

@[expose] def Twist {x f : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hf : f ∈ Subgroup.normalizer (D : Set G)) (s : ℤ) : Prop :=
  ∀ v, dD.thetaT hf (dD.thetaT hx v) = s • dD.thetaT hx (dD.thetaT hf v)

variable {dD}

theorem Twist.congr {x f : G} {hx : x ∈ Subgroup.normalizer (D : Set G)}
    {hf : f ∈ Subgroup.normalizer (D : Set G)} {s s' : ℤ} (h : dD.Twist hx hf s)
    (hs : ∀ v : Torus τ.k, s • v = s' • v) : dD.Twist hx hf s' := fun v => by
  rw [h v, hs]

theorem Twist.mul {x f g : G} {hx : x ∈ Subgroup.normalizer (D : Set G)}
    {hf : f ∈ Subgroup.normalizer (D : Set G)} {hg : g ∈ Subgroup.normalizer (D : Set G)}
    {s s' : ℤ} (h₁ : dD.Twist hx hf s) (h₂ : dD.Twist hx hg s') :
    dD.Twist hx (mul_mem hf hg) (s * s') := fun v => by
  rw [dD.thetaT_mul hf hg, h₁, map_zsmul, h₂, smul_smul, mul_comm, dD.thetaT_mul hf hg]

theorem Twist.inv {x f : G} {hx : x ∈ Subgroup.normalizer (D : Set G)}
    {hf : f ∈ Subgroup.normalizer (D : Set G)} {s : ℤ} (h : dD.Twist hx hf s)
    (hs : ∀ v : Torus τ.k, (s * s) • v = v) : dD.Twist hx (inv_mem hf) s := fun v => by
  have key := h (dD.thetaT (inv_mem hf) v)
  rw [dD.thetaT_thetaT_inv] at key
  have := congrArg (dD.thetaT (inv_mem hf)) key
  rw [dD.thetaT_inv_thetaT, map_zsmul] at this
  rw [this, smul_smul, hs]

theorem twist_of_comm {x f : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hf : f ∈ Subgroup.normalizer (D : Set G))
    (hc : f⁻¹ * x * f * x⁻¹ ∈ Subgroup.normalizer (D : Set G)) {s : ℤ}
    (hs : ∀ v, dD.thetaT hc v = s • v) : dD.Twist hx hf s := fun w => by
  have h1 : ∀ v, dD.thetaT hf (dD.thetaT hx (dD.thetaT (inv_mem hf) v)) =
      dD.thetaT hx (s • v) := fun v => by
    rw [← dD.thetaT_conj hx hf, dD.thetaT_congr _ (mul_mem hc hx) (by group),
      dD.thetaT_mul hc hx, hs]
  have := h1 (dD.thetaT hf w)
  rw [dD.thetaT_inv_thetaT, map_zsmul] at this
  exact this

end StrothWeakTypeData

namespace StrothFrame.IsD

open Stroth34T201

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)}

theorem sigma_sq_zsmul (v : Torus (StrothTypeIndex.t201 m).k) :
    ((1 + 2 ^ (m + 1) : ℤ) * (1 + 2 ^ (m + 1))) • v = v := by
  rw [zsmul_congr (y' := 1) ⟨1 + 2 ^ m, by ring⟩, one_smul]

theorem thetaT_proj (hS : Local.Setting (F.S : Subgroup G) D) {g r : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ hS.R)
    (x : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT (hS.R_le_normalizer (hS.proj_mem hg hr)) x =
      dD.thetaT hg (dD.thetaT (hS.R_le_normalizer hr) (dD.thetaT (inv_mem hg) x)) := by
  rw [← dD.thetaT_conj (hS.R_le_normalizer hr) hg, dD.thetaT_apply, dD.thetaT_apply,
    hS.proj_conj_D hg hr (dD.ofT_mem x)]

theorem thetaT_rel {x y z w : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hy : y ∈ Subgroup.normalizer (D : Set G)) (hz : z ∈ Subgroup.normalizer (D : Set G))
    (hw : w ∈ Subgroup.normalizer (D : Set G)) (h : x * y = z * w)
    (v : Torus (StrothTypeIndex.t201 m).k) :
    dD.thetaT hy (dD.thetaT hx v) = dD.thetaT hw (dD.thetaT hz v) := by
  rw [← dD.thetaT_mul hx hy, ← dD.thetaT_mul hz hw]
  exact dD.thetaT_congr _ _ h v

theorem twist_proj_rho (hS : Local.Setting (F.S : Subgroup G) D) {f : G} (hf : f ∈ hS.R)
    {s₁ s₂ : ℤ} (h₁ : dD.Twist dD.uv_mem (hS.R_le_normalizer hf) s₁)
    (h₂ : dD.Twist dD.t_mem (hS.R_le_normalizer hf) s₂) :
    dD.Twist dD.uv_mem (hS.R_le_normalizer (hS.proj_mem dD.ρ_mem hf)) (s₁ * s₂) ∧
      dD.Twist dD.t_mem (hS.R_le_normalizer (hS.proj_mem dD.ρ_mem hf)) s₁ := by
  have hρ := dD.ρ_mem
  have hρi := inv_mem dD.ρ_mem
  have huv := dD.uv_mem
  have ht := dD.t_mem
  have r₁ : ∀ v, dD.thetaT hρi (dD.thetaT huv v) =
      dD.thetaT ht (dD.thetaT huv (dD.thetaT hρi v)) := fun v => by
    rw [thetaT_rel huv hρi hρi (mul_mem huv ht) (by
      have := dD.rho_mul_uv_mul_rho_inv
      calc dD.uv * dD.ρ⁻¹ = dD.ρ⁻¹ * (dD.ρ * dD.uv * dD.ρ⁻¹) := by group
        _ = dD.ρ⁻¹ * (dD.uv * dD.t) := by rw [this]) v, dD.thetaT_mul huv ht]
  have r₂ : ∀ v, dD.thetaT huv (dD.thetaT hρ v) =
      dD.thetaT hρ (dD.thetaT ht (dD.thetaT huv v)) := fun v => by
    rw [thetaT_rel hρ huv (mul_mem huv ht) hρ (by
      have := dD.rho_mul_uv_mul_rho_inv
      calc dD.ρ * dD.uv = (dD.ρ * dD.uv * dD.ρ⁻¹) * dD.ρ := by group
        _ = dD.uv * dD.t * dD.ρ := by rw [this]) v, dD.thetaT_mul huv ht]
  have r₃ : ∀ v, dD.thetaT hρi (dD.thetaT ht v) = dD.thetaT huv (dD.thetaT hρi v) :=
    fun v => thetaT_rel ht hρi hρi huv (by
      have := dD.rho_mul_t_mul_rho_inv
      calc dD.t * dD.ρ⁻¹ = dD.ρ⁻¹ * (dD.ρ * dD.t * dD.ρ⁻¹) := by group
        _ = dD.ρ⁻¹ * dD.uv := by rw [this]) v
  have r₄ : ∀ v, dD.thetaT ht (dD.thetaT hρ v) = dD.thetaT hρ (dD.thetaT huv v) :=
    fun v => thetaT_rel hρ ht huv hρ (by
      have := dD.rho_mul_t_mul_rho_inv
      calc dD.ρ * dD.t = (dD.ρ * dD.t * dD.ρ⁻¹) * dD.ρ := by group
        _ = dD.uv * dD.ρ := by rw [this]) v
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [thetaT_proj hS hρ hf, thetaT_proj hS hρ hf, r₁, h₂, h₁]
    simp only [map_zsmul, smul_smul]
    rw [← r₂, mul_comm s₂]
  · rw [thetaT_proj hS hρ hf, thetaT_proj hS hρ hf, r₃, h₁, map_zsmul, ← r₄]

theorem twist_conj_u (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {f : G}
    (hf : f ∈ hS.R) {s₁ s₂ : ℤ} (h₁ : dD.Twist dD.uv_mem (hS.R_le_normalizer hf) s₁)
    (h₂ : dD.Twist dD.t_mem (hS.R_le_normalizer hf) s₂) :
    dD.Twist dD.uv_mem (hS.R_le_normalizer (h.conj_u_mem_R hS hf)) s₁ ∧
      dD.Twist dD.t_mem (hS.R_le_normalizer (h.conj_u_mem_R hS hf)) (s₁ * s₂) := by
  have hu := dD.u_mem
  have hui := inv_mem dD.u_mem
  have huv := dD.uv_mem
  have ht := dD.t_mem
  have hfN := hS.R_le_normalizer hf
  have hu2 : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
  have huv2 : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq
  have hconj : ∀ v, dD.thetaT (hS.R_le_normalizer (h.conj_u_mem_R hS hf)) v =
      dD.thetaT hu (dD.thetaT hfN (dD.thetaT hui v)) := fun v => by
    rw [← dD.thetaT_conj hfN hu]
  have r₁ : ∀ v, dD.thetaT hui (dD.thetaT huv v) = dD.thetaT huv (dD.thetaT hui v) :=
    fun v => thetaT_rel huv hui hui huv (by
      rw [hu2]; exact dD.uv_comm_u) v
  have r₂ : ∀ v, dD.thetaT hu (dD.thetaT huv v) = dD.thetaT huv (dD.thetaT hu v) :=
    fun v => thetaT_rel huv hu hu huv dD.uv_comm_u v
  have r₃ : ∀ v, dD.thetaT hui (dD.thetaT ht v) =
      dD.thetaT ht (dD.thetaT huv (dD.thetaT hui v)) := fun v => by
    rw [thetaT_rel ht hui hui (mul_mem huv ht) (by rw [hu2, ← mul_assoc]; exact dD.t_u) v,
      dD.thetaT_mul huv ht]
  have r₄ : ∀ v, dD.thetaT hu (dD.thetaT ht (dD.thetaT huv v)) =
      dD.thetaT ht (dD.thetaT hu v) := fun v => by
    rw [← dD.thetaT_mul huv ht, thetaT_rel (mul_mem huv ht) hu hu ht (by
      calc dD.uv * dD.t * dD.u = dD.uv * (dD.t * dD.u) := by group
        _ = dD.uv * (dD.u * dD.uv * dD.t) := by rw [dD.t_u]
        _ = dD.uv * dD.u * dD.uv * dD.t := by group
        _ = dD.u * dD.uv * dD.uv * dD.t := by rw [dD.uv_comm_u]
        _ = dD.u * dD.t := by rw [mul_assoc dD.u, dD.uv_sq, mul_one]) v]
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [hconj, hconj, r₁, h₁, map_zsmul, r₂]
  · rw [hconj, hconj, r₃, h₂, h₁]
    simp only [map_zsmul, smul_smul]
    rw [r₄, mul_comm s₂]

theorem mem_or_mul_inv_mem_of_mem_sup {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G))
    (he2 : e * e ∈ D) {x : G} (hx : x ∈ D ⊔ Subgroup.zpowers e) : x ∈ D ∨ x * e⁻¹ ∈ D := by
  have hconj : ∀ {d : G}, d ∈ D → e * d * e⁻¹ ∈ D := fun {d} hd => by
    have := (Subgroup.mem_normalizer_iff''.mp (inv_mem heN) d).mp hd
    simpa using this
  let T : Subgroup G :=
    { carrier := {x | x ∈ D ∨ x * e⁻¹ ∈ D}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr (by simpa [mul_assoc] using mul_mem ha hb)
        · right
          have : a * b * e⁻¹ = (a * e⁻¹) * (e * b * e⁻¹) := by group
          rw [this]; exact mul_mem ha (hconj hb)
        · left
          have : a * b = (a * e⁻¹) * (e * (b * e⁻¹) * e⁻¹) * (e * e) := by group
          rw [this]; exact mul_mem (mul_mem ha (hconj hb)) he2
      one_mem' := Or.inl (one_mem D)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · right
          have : a⁻¹ * e⁻¹ = (e⁻¹ * (a * e⁻¹)⁻¹ * e) * (e * e)⁻¹ := by group
          rw [this]
          refine mul_mem ?_ (inv_mem he2)
          have := (Subgroup.mem_normalizer_iff''.mp heN _).mp (inv_mem ha)
          simpa using this }
  have hle : D ⊔ Subgroup.zpowers e ≤ T :=
    sup_le (fun d hd => Or.inl hd) ((Subgroup.zpowers_le).mpr (Or.inr (by simp)))
  exact hle hx

theorem thetaT_eq_of_twist_one (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    {e : G} (heR : e ∈ hS.R) (he : Rel34i dD e (2 ^ (m + 1)))
    (hR1 : hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e) {r : G} (hr : r ∈ hS.R)
    (h₁ : dD.Twist dD.uv_mem (hS.R_le_normalizer hr) 1)
    (h₂ : dD.Twist dD.t_mem (hS.R_le_normalizer hr) 1) :
    (∀ v, dD.thetaT (hS.R_le_normalizer hr) v = v) ∨
      ∀ v, dD.thetaT (hS.R_le_normalizer hr) v = (1 + 2 ^ (m + 1) : ℤ) • v := by
  have hrN := hS.R_le_normalizer hr
  have heN := hS.R_le_normalizer heR
  have hrR1 : r ∈ hS.R1 dD.uv dD.t := by
    refine ⟨hr, ?_, ?_⟩
    · exact dD.conj_mem_of_thetaT_comm hS (hS.R_le_S hr) h.uv_mem_S hrN dD.uv_mem
        (fun v => by rw [h₁ v, one_smul])
    · exact dD.conj_mem_of_thetaT_comm hS (hS.R_le_S hr) h.t_mem_S hrN dD.t_mem
        (fun v => by rw [h₂ v, one_smul])
  rw [hR1] at hrR1
  have he2 : e * e ∈ D := by rw [he.e_sq]; exact inv_mem dD.c.2
  rcases mem_or_mul_inv_mem_of_mem_sup heN he2 hrR1 with hD | hD
  · exact Or.inl fun v => dD.thetaT_of_mem hrN hD v
  · right
    intro v
    have hdN : r * e⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hD
    rw [dD.thetaT_congr hrN (mul_mem hdN heN) (by group), dD.thetaT_mul hdN heN,
      dD.thetaT_of_mem hdN hD, t201_thetaT_of_rel34i he heN]

theorem twist_cases (hS : Local.Setting (F.S : Subgroup G) D) {e : G} (heR : e ∈ hS.R)
    (he : Rel34i dD e (2 ^ (m + 1))) (hR1 : hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e)
    {x f : G} (hx : x ∈ Subgroup.normalizer (D : Set G)) (hf : f ∈ hS.R)
    (hc : f⁻¹ * x * f * x⁻¹ ∈ hS.R1 dD.uv dD.t) :
    dD.Twist hx (hS.R_le_normalizer hf) 1 ∨
      dD.Twist hx (hS.R_le_normalizer hf) (1 + 2 ^ (m + 1)) := by
  have heN := hS.R_le_normalizer heR
  have he2 : e * e ∈ D := by rw [he.e_sq]; exact inv_mem dD.c.2
  have hcN : f⁻¹ * x * f * x⁻¹ ∈ Subgroup.normalizer (D : Set G) := hS.R_le_normalizer hc.1
  rw [hR1] at hc
  rcases mem_or_mul_inv_mem_of_mem_sup heN he2 hc with hD | hD
  · exact Or.inl (dD.twist_of_comm hx (hS.R_le_normalizer hf) hcN
      (fun v => by rw [dD.thetaT_of_mem hcN hD, one_smul]))
  · refine Or.inr (dD.twist_of_comm hx (hS.R_le_normalizer hf) hcN fun v => ?_)
    have hdN : f⁻¹ * x * f * x⁻¹ * e⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      Subgroup.le_normalizer hD
    rw [dD.thetaT_congr hcN (mul_mem hdN heN) (by group), dD.thetaT_mul hdN heN,
      dD.thetaT_of_mem hdN hD, t201_thetaT_of_rel34i he heN]

end StrothFrame.IsD

end CFSG.CGT.Stroth77
