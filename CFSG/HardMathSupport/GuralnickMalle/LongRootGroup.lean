module

public import CFSG.HardMathSupport.GuralnickMalle.SiegelTransformation

public section

open LinearMap Module

namespace CFSG.HardMathSupport.GuralnickMalle

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

theorem polarBilin_self_of_eq_zero (Qf : QuadraticForm K E) (a : E) (ha : Qf a = 0) :
    QuadraticMap.polarBilin Qf a a = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, ha]
  simp

theorem siegelLin_apply_self_left (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hab : QuadraticMap.polarBilin Qf a b = 0) (c : K) :
    siegelLin Qf a b c a = a := by
  rw [siegelLin_apply, hab, polarBilin_self_of_eq_zero Qf a ha]
  simp

theorem siegelLin_apply_self_right (Qf : QuadraticForm K E) (a b : E)
    (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0) (c : K) :
    siegelLin Qf a b c b = b := by
  have hba : QuadraticMap.polarBilin Qf b a = 0 := by
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using hab
  rw [siegelLin_apply, hba, polarBilin_self_of_eq_zero Qf b hb]
  simp

theorem siegelLin_mul (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0)
    (c c' : K) :
    siegelLin Qf a b c * siegelLin Qf a b c' = siegelLin Qf a b (c + c') := by
  have hca : siegelLin Qf a b c a = a := siegelLin_apply_self_left Qf a b ha hab c
  have hcb : siegelLin Qf a b c b = b := siegelLin_apply_self_right Qf a b hb hab c
  ext x
  rw [Module.End.mul_apply, siegelLin_apply Qf a b c' x]
  rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, hca, hcb]
  rw [siegelLin_apply Qf a b c x, siegelLin_apply Qf a b (c + c') x]
  simp only [smul_smul, add_mul, add_smul]
  abel

theorem siegelLin_mul_self (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0) (c : K) :
    siegelLin Qf a b c * siegelLin Qf a b c = 1 := by
  rw [siegelLin_mul Qf a b ha hb hab c c, CharTwo.add_self_eq_zero, siegelLin_zero,
    Module.End.one_eq_id]

theorem siegelLin_isometry (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0)
    (c : K) (x : E) : Qf (siegelLin Qf a b c x) = Qf x := by
  set u : K := QuadraticMap.polarBilin Qf x b with hu
  set v : K := QuadraticMap.polarBilin Qf x a with hv
  have hQz : Qf ((c * u) • a + (c * v) • b) = 0 := by
    simp only [QuadraticMap.map_add Qf, ← QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.map_smul, map_smul, LinearMap.smul_apply, ha, hb, hab, smul_zero, mul_zero,
      zero_mul, add_zero, zero_add]
  have hBz : QuadraticMap.polarBilin Qf x ((c * u) • a + (c * v) • b) = 0 := by
    simp only [map_add, map_smul, LinearMap.smul_apply, ← hu, ← hv, smul_eq_mul]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    calc (c * u) * v + (c * v) * u = 2 * (c * u * v) := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hx : siegelLin Qf a b c x = x + ((c * u) • a + (c * v) • b) := by
    rw [siegelLin_apply, ← hu, ← hv]
    simp only [smul_smul]
    abel
  rw [hx, QuadraticMap.map_add Qf, ← QuadraticMap.polarBilin_apply_apply, hQz, hBz, add_zero,
    add_zero]

@[expose] noncomputable def siegelEquiv (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0)
    (c : K) : E ≃ₗ[K] E :=
  LinearEquiv.ofInvolutive (siegelLin Qf a b c) fun x => by
    have h := congrArg (fun f : E →ₗ[K] E => f x)
      (siegelLin_mul_self Qf a b ha hb hab c)
    rw [Module.End.mul_apply] at h
    simpa only [Module.End.one_apply] using h

@[simp] theorem siegelEquiv_apply (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0)
    (c : K) (x : E) : siegelEquiv Qf a b ha hb hab c x = siegelLin Qf a b c x :=
  rfl

theorem siegelEquiv_mul (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0)
    (c c' : K) :
    siegelEquiv Qf a b ha hb hab c * siegelEquiv Qf a b ha hb hab c'
      = siegelEquiv Qf a b ha hb hab (c + c') := by
  ext x
  simp only [LinearEquiv.mul_apply, siegelEquiv_apply]
  rw [← Module.End.mul_apply, siegelLin_mul Qf a b ha hb hab c c']

theorem siegelEquiv_zero (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0) :
    siegelEquiv Qf a b ha hb hab 0 = 1 := by
  ext x
  simp only [siegelEquiv_apply, siegelLin_zero, LinearMap.id_apply, LinearEquiv.coe_one, id_eq]

@[simp] theorem siegelEquiv_symm_apply (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0)
    (c : K) (x : E) : (siegelEquiv Qf a b ha hb hab c).symm x = siegelLin Qf a b c x :=
  rfl

theorem siegelEquiv_mul_self (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0) (c : K) :
    siegelEquiv Qf a b ha hb hab c * siegelEquiv Qf a b ha hb hab c = 1 := by
  rw [siegelEquiv_mul, CharTwo.add_self_eq_zero, siegelEquiv_zero]

theorem siegelEquiv_inv (Qf : QuadraticForm K E) (a b : E)
    (ha : Qf a = 0) (hb : Qf b = 0) (hab : QuadraticMap.polarBilin Qf a b = 0) (c : K) :
    (siegelEquiv Qf a b ha hb hab c)⁻¹ = siegelEquiv Qf a b ha hb hab c :=
  inv_eq_of_mul_eq_one_right (siegelEquiv_mul_self Qf a b ha hb hab c)

theorem exists_polarBilin_pair (Qf : QuadraticForm K E) (a b : E)
    (hnd : ∀ x, (∀ y, QuadraticMap.polarBilin Qf x y = 0) → x = 0)
    (hli : LinearIndependent K ![a, b]) (α β : K) :
    ∃ x : E, QuadraticMap.polarBilin Qf x a = α ∧
      QuadraticMap.polarBilin Qf x b = β := by
  let f : E →ₗ[K] K := (QuadraticMap.polarBilin Qf).flip a
  let g : E →ₗ[K] K := (QuadraticMap.polarBilin Qf).flip b
  let Φ : E →ₗ[K] K × K := LinearMap.prod f g
  have hΦx : ∀ x, Φ x = (QuadraticMap.polarBilin Qf x a,
      QuadraticMap.polarBilin Qf x b) := by
    intro x
    simp [Φ, f, g, BilinForm.flip_apply]
  have hsurj : Function.Surjective Φ := by
    by_contra hnot
    have hlt : LinearMap.range Φ < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact hnot fun y => by
        have hy : y ∈ LinearMap.range Φ := by rw [htop]; exact Submodule.mem_top
        exact LinearMap.mem_range.mp hy
    obtain ⟨lam, hlamne, hlamker⟩ :=
      Submodule.exists_le_ker_of_lt_top (LinearMap.range Φ) hlt
    let l1 : K := lam (1, 0)
    let l2 : K := lam (0, 1)
    have hlam_eq : ∀ p q : K, lam (p, q) = p * l1 + q * l2 := by
      intro p q
      have h : (p, q) = p • ((1 : K), (0 : K)) + q • ((0 : K), (1 : K)) := by
        ext <;> simp
      rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hzero : ∀ y : E, QuadraticMap.polarBilin Qf (l1 • a + l2 • b) y = 0 := by
      intro y
      have hx : lam (Φ y) = 0 := by
        simpa only [LinearMap.mem_ker] using hlamker (LinearMap.mem_range_self Φ y)
      have hx' : QuadraticMap.polarBilin Qf y a * l1 +
          QuadraticMap.polarBilin Qf y b * l2 = 0 := by
        rw [hΦx y, hlam_eq] at hx
        exact hx
      have hsymm : ∀ x y : E, QuadraticMap.polarBilin Qf x y =
          QuadraticMap.polarBilin Qf y x := by
        intro x y
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
          ← QuadraticMap.polarBilin_apply_apply]
      calc QuadraticMap.polarBilin Qf (l1 • a + l2 • b) y
          = l1 * QuadraticMap.polarBilin Qf a y +
              l2 * QuadraticMap.polarBilin Qf b y := by
            rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
              map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
        _ = l1 * QuadraticMap.polarBilin Qf y a +
              l2 * QuadraticMap.polarBilin Qf y b := by rw [hsymm a y, hsymm b y]
        _ = QuadraticMap.polarBilin Qf y a * l1 +
              QuadraticMap.polarBilin Qf y b * l2 := by ring
        _ = 0 := hx'
    have hind : l1 • a + l2 • b = 0 := hnd _ hzero
    have hpair := (LinearIndependent.pair_iff.mp hli) l1 l2 hind
    have hlam0 : lam = 0 := by
      apply LinearMap.ext
      rintro ⟨p, q⟩
      rw [hlam_eq p q, hpair.1, hpair.2]
      simp
    exact hlamne hlam0
  obtain ⟨x, hx⟩ := hsurj (α, β)
  exact ⟨x, by simpa [hΦx x] using congrArg Prod.fst hx,
    by simpa [hΦx x] using congrArg Prod.snd hx⟩

theorem siegelLin_sub_one_apply (Qf : QuadraticForm K E) (a b : E) (c : K) (x : E) :
    (siegelLin Qf a b c - 1) x =
      c • (QuadraticMap.polarBilin Qf x b • a) +
        c • (QuadraticMap.polarBilin Qf x a • b) := by
  rw [LinearMap.sub_apply, Module.End.one_eq_id, LinearMap.id_apply, siegelLin_apply]
  abel

theorem siegelLin_sub_one_range (Qf : QuadraticForm K E) (a b : E)
    (hnd : ∀ x, (∀ y, QuadraticMap.polarBilin Qf x y = 0) → x = 0)
    (hli : LinearIndependent K ![a, b]) (c : K) (hc : c ≠ 0) :
    LinearMap.range (siegelLin Qf a b c - 1) = Submodule.span K {a, b} := by
  have hpair := exists_polarBilin_pair Qf a b hnd hli
  have hsubset : LinearMap.range (siegelLin Qf a b c - 1) ≤
      Submodule.span K {a, b} := by
    rintro y ⟨x, rfl⟩
    rw [siegelLin_sub_one_apply]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span (by simp)))
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span (by simp)))
  have ha_mem : a ∈ LinearMap.range (siegelLin Qf a b c - 1) := by
    obtain ⟨x, hxa, hxb⟩ := hpair 0 c⁻¹
    refine ⟨x, ?_⟩
    rw [siegelLin_sub_one_apply, hxa, hxb]
    simp only [zero_smul, smul_zero, add_zero, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hb_mem : b ∈ LinearMap.range (siegelLin Qf a b c - 1) := by
    obtain ⟨x, hxa, hxb⟩ := hpair c⁻¹ 0
    refine ⟨x, ?_⟩
    rw [siegelLin_sub_one_apply, hxa, hxb]
    simp only [zero_smul, smul_zero, add_zero, zero_add, smul_smul, mul_inv_cancel₀ hc,
      one_smul]
  refine le_antisymm hsubset (Submodule.span_le.mpr ?_)
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact ha_mem
  · exact hb_mem

section MovedSpaceSingular

variable {Qf : QuadraticForm K E} {a b : E}

theorem Qf_eq_zero_on_span_singular_pair (ha : Qf a = 0) (hb : Qf b = 0)
    (hab : QuadraticMap.polarBilin Qf a b = 0) {y : E}
    (hy : y ∈ Submodule.span K ({a, b} : Set E)) : Qf y = 0 := by
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨α, β, rfl⟩ := hy
  have h1 : Qf (α • a) = 0 := by
    rw [QuadraticMap.map_smul, ha, smul_zero]
  have h2 : Qf (β • b) = 0 := by
    rw [QuadraticMap.map_smul, hb, smul_zero]
  have h3 : QuadraticMap.polar Qf (α • a) (β • b) = 0 := by
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      ← QuadraticMap.polarBilin_apply_apply, hab, smul_zero, smul_zero]
  rw [QuadraticMap.map_add Qf, h1, h2, h3, add_zero, add_zero]

end MovedSpaceSingular

end CFSG.HardMathSupport.GuralnickMalle

end
