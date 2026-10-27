module

public import CFSG.GH74.Generic.S3.ReflUni

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg Subgroup
open scoped MatrixGroups

section Uni
variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def dU : GL (Fin 2) K := diagGL ![-1, 1]

theorem coe_dU : ((dU : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dU, coe_diagGL]

theorem coe_dU_inv : (((dU : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![-1, 0; 0, 1] := by
  rw [dU, coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem dU_mat_mul_self : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![-1, 0; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem conjTr_dU : conjTr σ (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) = !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr]

theorem dU_conj_mem (A : SUid σ 2) : dU * (A : GL (Fin 2) K) * dU⁻¹ ∈ SUid σ 2 := by
  obtain ⟨hdet, hiso⟩ := A.2
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, coe_dU, coe_dU_inv, Matrix.det_mul, Matrix.det_mul, hdet]
    simp [Matrix.det_fin_two_of]
  · rw [Units.val_mul, Units.val_mul, coe_dU, coe_dU_inv, conjTr_mul, conjTr_mul, conjTr_dU]
    calc _ = (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * (conjTr σ ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![-1, 0; 0, 1]) * ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
            !![-1, 0; 0, 1] := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [dU_mat_mul_self, Matrix.mul_one, hiso, Matrix.mul_one, dU_mat_mul_self]

@[expose] noncomputable def cdU (A : SUid σ 2) : SUid σ 2 := ⟨dU * (A : GL (Fin 2) K) * dU⁻¹, dU_conj_mem σ A⟩

theorem coe_cdU (A : SUid σ 2) : (((cdU σ A : SUid σ 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![-1, 0; 0, 1] * ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * !![-1, 0; 0, 1] := by
  show ((dU * (A : GL (Fin 2) K) * dU⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [Units.val_mul, Units.val_mul, coe_dU, coe_dU_inv]

theorem coe_cdU' (A : SUid σ 2) : (((cdU σ A : SUid σ 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0, -((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1;
      -((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0, ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1] := by
  rw [coe_cdU]
  conv_lhs => rw [Matrix.eta_fin_two ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)]
  simp

theorem blkU_conj_d (A : SUid σ 2) :
    embSUid σ 2 (cU σ) * embSUid σ 0 A * (embSUid σ 2 (cU σ))⁻¹ = embSUid σ 0 (cdU σ A) := by
  rw [inv_eq_of_mul_eq_one_right (blkU_sq σ)]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, cU, coe_diagGL, coe_cdU']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three]

theorem diagU_norm_mem {a : Kˣ} (ha : σ (a : K) * a = 1) :
    (diagGL ![a, a⁻¹] : GL (Fin 2) K) ∈ SUid σ 2 := by
  refine diagGL_mem_SUid σ a a⁻¹ (by simp) ha ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, ha, inv_one]

@[expose] noncomputable def jU : SUid σ 2 :=
  ⟨⟨!![0, -1; 1, 0], !![0, 1; -1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
      by ext i j; fin_cases i <;> fin_cases j <;> simp⟩,
    by simp [Matrix.det_fin_two_of],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_jU : (((jU σ : SUid σ 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := rfl

end Uni

open CFSG.ClassicalInvolution.Phan CFSG.GH74.L5U5 in
theorem exists_refl_action_uni {G : Type} [Group G] {F₂ F : Type} [Field F₂] [Finite F₂] [Field F]
    [Finite F] {z u : G} {Y : Fin 3 → Subgroup G} (p f : ℕ) [Fact p.Prime] [CharP F₂ p]
    (h : GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F z u Y)
    (hp2 : p ≠ 2) (hF₂ : Nat.card F₂ = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) :
    ∃ ι : SUid (unitaryInvolution F₂ p f) 2 →* G, Function.Injective ι ∧ ι.range = Y 2 ∧
      ∀ A, u * ι A * u⁻¹ = ι (cdU (unitaryInvolution F₂ p f) A) := by
  have hq2 : p ^ f ≠ 2 := by omega
  have hoddq : Odd (p ^ f) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hodd2 : Odd (Nat.card F₂) := by rw [hF₂]; exact hoddq.pow
  have h2 : (2 : F₂) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd2
  have hoddF : Odd (Nat.card F) := by rw [hF]; exact hoddq
  have hchar : ringChar F ≠ 2 := by
    intro hc
    have h2F : (2 : F) ≠ 0 :=
      CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hoddF
    apply h2F
    have := ringChar.of_eq hc
    simpa using CharP.cast_eq_zero F 2
  obtain ⟨hcomm, hpair⟩ := h.comm_pairs hF₂ hF hp2 hq
  obtain ⟨hiso, hz0, hz2, hu1, -⟩ := h
  set N : Subgroup G := ⨆ i, Y i with hN
  have hYN : ∀ i, Y i ≤ N := fun i => le_iSup Y i
  have hgen : ⨆ i, (Y i).subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hYN _)]
    exact hN.symm
  have hstd : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair F₂ p f W ((Y i).subgroupOf N) ((Y j).subgroupOf N) :=
    fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf N, unitaryBlockStandardPair_subgroupOf hF₂ hq2 hW N (hYN i) (hYN j)⟩
  have hW : WeakPhanA F₂ p f 3 (fun i => (Y i).subgroupOf N)
      (fun i j => (Y i).subgroupOf N ⊔ (Y j).subgroupOf N) := by
    refine ⟨?_, fun _ _ _ => rfl, ?_, ?_, hgen⟩
    · intro i
      by_cases h : (i : ℕ) + 1 < 3
      · obtain ⟨W, hW⟩ := hstd i ⟨i + 1, h⟩ rfl
        exact (nonempty_mulEquiv_of_standardPair hF₂ hW).1
      · have hi : 0 < (i : ℕ) := by have := i.2; omega
        obtain ⟨W, hW⟩ := hstd ⟨(i : ℕ) - 1, by omega⟩ i (by simp only; omega)
        exact (nonempty_mulEquiv_of_standardPair hF₂ hW).2
    · intro i j hij x hx y hy
      exact Subtype.ext (hcomm i j hij x hx y hy)
    · intro i j hj
      obtain ⟨W, hW⟩ := hstd i j hj
      rwa [unitaryBlockStandardPair_eq_sup hF₂ hq2 hW] at hW
  obtain ⟨Fam, hFι, hFinj, -⟩ := coherent_family hF₂ (by norm_num : 2 ≤ 3) hW
  have hrange : ∀ i, (N.subtype.comp (Fam.ι i)).range = Y i := by
    intro i
    rw [MonoidHom.range_comp, hFι i, Subgroup.subgroupOf_map_subtype, inf_of_le_left (hYN i)]
  have hinj : ∀ i, Function.Injective (N.subtype.comp (Fam.ι i)) := fun i =>
    N.subtype_injective.comp (hFinj i)
  obtain ⟨e1⟩ := hiso 1
  have hu : u = N.subtype (Fam.ι 1 (cU (unitaryInvolution F₂ p f))) :=
    (img_eq_of_central (unitaryInvolution F₂ p f) hchar e1 hu1 (N.subtype.comp (Fam.ι 1))
      (hrange 1) (hinj 1) _ (cU_central _) (cU_ne_one _ h2)).symm
  have hθ1 := Fam.left 1 (by norm_num)
  have hθ2 := Fam.right 1 (by norm_num)
  have hθ1' : ∀ c, Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 2 c) = Fam.ι 1 c := fun c =>
    DFunLike.congr_fun hθ1 c
  have hθ2' : ∀ A, Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 0 A) = Fam.ι 2 A := fun A =>
    DFunLike.congr_fun hθ2 A
  refine ⟨N.subtype.comp (Fam.ι 2), hinj 2, hrange 2, fun A => ?_⟩
  change u * N.subtype (Fam.ι 2 A) * u⁻¹ = N.subtype (Fam.ι 2 (cdU (unitaryInvolution F₂ p f) A))
  calc u * N.subtype (Fam.ι 2 A) * u⁻¹
      = N.subtype (Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 2 (cU (unitaryInvolution F₂ p f)) *
          embSUid (unitaryInvolution F₂ p f) 0 A *
          (embSUid (unitaryInvolution F₂ p f) 2 (cU (unitaryInvolution F₂ p f)))⁻¹)) := by
        rw [hu, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hθ1', hθ2']
    _ = N.subtype (Fam.θ 1 (embSUid (unitaryInvolution F₂ p f) 0
          (cdU (unitaryInvolution F₂ p f) A))) := by
        rw [blkU_conj_d _ A]
    _ = N.subtype (Fam.ι 2 (cdU (unitaryInvolution F₂ p f) A)) := by rw [hθ2']

open CFSG.ClassicalInvolution.Phan CFSG.GH74.L5U5 in
theorem not_inner_uni {G : Type} [Group G] {F₂ F : Type} [Field F₂] [Finite F₂] [Field F] [Finite F]
    {z u : G} {Y : Fin 3 → Subgroup G} (p f : ℕ) [Fact p.Prime] [CharP F₂ p]
    (h : GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F z u Y)
    (hp2 : p ≠ 2) (hF₂ : Nat.card F₂ = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) :
    ¬ ∃ x₀ ∈ Y 2, ∀ g ∈ Y 2, u * g * u⁻¹ = x₀ * g * x₀⁻¹ := by
  have hoddq : Odd (p ^ f) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hodd2 : Odd (Nat.card F₂) := by rw [hF₂]; exact hoddq.pow
  have h2 : (2 : F₂) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd2
  obtain ⟨ι, hinj, hrange, hact⟩ := exists_refl_action_uni p f h hp2 hF₂ hF hq
  rintro ⟨x₀, hx₀, hall⟩
  rw [← hrange] at hx₀
  obtain ⟨A₀, rfl⟩ := hx₀
  have hkey : ∀ A : SUid (unitaryInvolution F₂ p f) 2,
      cdU (unitaryInvolution F₂ p f) A * A₀ = A₀ * A := by
    intro A
    have h1 := hact A
    have h2' := hall (ι A) (by rw [← hrange]; exact ⟨A, rfl⟩)
    have h3 : ι (cdU (unitaryInvolution F₂ p f) A) = ι (A₀ * A * A₀⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← h1, h2']
    have h4 := hinj h3
    rw [h4]
    group
  have hkeyM : ∀ A : SUid (unitaryInvolution F₂ p f) 2,
      (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F₂) * ((A : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) *
        !![-1, 0; 0, 1] * ((A₀ : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) =
      ((A₀ : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) * ((A : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) := by
    intro A
    have := congrArg (fun g : SUid (unitaryInvolution F₂ p f) 2 =>
      ((g : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂)) (hkey A)
    simpa [Subgroup.coe_mul, Units.val_mul, coe_cdU] using this
  have hd : (p ^ f + 1) ∣ Nat.card F₂ - 1 := by
    rw [hF₂]
    obtain ⟨m, hm⟩ : ∃ m, p ^ f = m + 1 := ⟨p ^ f - 1, by omega⟩
    refine ⟨m, ?_⟩
    rw [hm]
    apply Nat.sub_eq_of_eq_add
    ring
  obtain ⟨a, ha⟩ := exists_units_orderOf (F := F₂) (d := p ^ f + 1) hd
  have ha1 : a ^ (p ^ f + 1) = 1 := ha ▸ pow_orderOf_eq_one a
  have hσa : unitaryInvolution F₂ p f (a : F₂) * a = 1 := by
    rw [unitaryInvolution_apply, ← pow_succ]
    have := congrArg Units.val ha1
    simpa using this
  have hane : (a : F₂) ≠ ((a⁻¹ : F₂ˣ) : F₂) := by
    intro hae
    have hae' : a = a⁻¹ := Units.ext hae
    have hsq : a ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 hae'
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [ha] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  let Dg : SUid (unitaryInvolution F₂ p f) 2 :=
    ⟨diagGL ![a, a⁻¹], diagU_norm_mem _ hσa⟩
  obtain ⟨x, y, z', t, hA0⟩ : ∃ x y z' t : F₂,
      ((A₀ : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) = !![x, y; z', t] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : x * t - y * z' = 1 := by
    have := A₀.2.1
    rw [hA0, Matrix.det_fin_two_of] at this
    exact this
  have hiso := A₀.2.2
  rw [hA0] at hiso
  have hiso00 := congrFun (congrFun hiso 0) 0
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at hiso00
  have hDg : ((Dg : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) =
      !![(a : F₂), 0; 0, ((a⁻¹ : F₂ˣ) : F₂)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dg, CFSG.LieType.Steinberg.coe_diagGL]
  have e1 := hkeyM Dg
  rw [hDg, hA0] at e1
  have e01 := congrFun (congrFun e1 0) 1
  have e10 := congrFun (congrFun e1 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have eJ := congrFun (congrFun (hkeyM (jU (unitaryInvolution F₂ p f))) 0) 1
  rw [coe_jU, hA0] at eJ
  simp [Matrix.mul_apply, Fin.sum_univ_two] at eJ
  have hane' : (a : F₂) ≠ (a : F₂)⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    exact hane
  have hy : y = 0 := by
    have : ((a : F₂) - (a : F₂)⁻¹) * y = 0 := by linear_combination e01
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (sub_eq_zero.1 h') hane'
    · exact h'
  have hz' : z' = 0 := by
    have : ((a : F₂)⁻¹ - (a : F₂)) * z' = 0 := by linear_combination e10
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (sub_eq_zero.1 h').symm hane'
    · exact h'
  have hxx : x * x = -1 := by
    rw [eJ, hy, hz'] at hdet
    linear_combination (-1 : F₂) * hdet
  rw [hz', iterateFrobenius_def] at hiso00
  have hxp : x ^ p ^ f * x = 1 := by
    have hpf0 : p ^ f ≠ 0 := pow_ne_zero f (Fact.out : p.Prime).ne_zero
    simpa [hpf0] using hiso00
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
  have hx2 : x ^ 2 = -1 := by linear_combination hxx
  have hpow : x ^ p ^ f * x = (-1) ^ (2 * k + 1) := by
    rw [hk, ← pow_succ, show 4 * k + 1 + 1 = 2 * (2 * k + 1) by ring, pow_mul, hx2]
  rw [(odd_two_mul_add_one k).neg_one_pow, hxp] at hpow
  apply h2
  linear_combination hpow

end CFSG.GH74.Generic.S3
