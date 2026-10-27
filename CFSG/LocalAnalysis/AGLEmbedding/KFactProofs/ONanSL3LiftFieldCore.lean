module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldSemi
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

open CFSG CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.ComponentClassification.CatalogueBHigherLinearField

theorem actionAut_trans {X S S' : Type} [Group X] [Group S] [Group S'] (K : Subgroup X)
    [K.Normal] (ψ : S ≃* K) (e : S' ≃* S) (x : X) (s : S') :
    actionAut K (e.trans ψ) x s = e.symm (actionAut K ψ x (e s)) := by
  apply e.injective
  apply ψ.injective
  apply Subtype.ext
  have h1 := coe_psi_actionAut K (e.trans ψ) x s
  have h2 := coe_psi_actionAut K ψ x (e s)
  rw [MulEquiv.apply_symm_apply, h2]
  exact h1

theorem actionAut_eq_one_of_mem_centralizer {X S : Type} [Group X] [Group S] (K : Subgroup X)
    [K.Normal] (ψ : S ≃* K) {x : X} (hx : x ∈ Subgroup.centralizer (K : Set X)) :
    actionAut K ψ x = 1 := by
  ext1 s
  apply ψ.injective
  apply Subtype.ext
  rw [coe_psi_actionAut]
  have := Subgroup.mem_centralizer_iff.mp hx (ψ s : X) (ψ s).2
  simp only [MulAut.one_apply]
  rw [← this]
  group

theorem actionAut_fix_of_pow_three {X S : Type} [Group X] [Group S] (K : Subgroup X) [K.Normal]
    (ψ : S ≃* K) {z : X} (hzc : z ∈ Subgroup.center X)
    (hCz : ∀ c ∈ Subgroup.centralizer (K : Set X), c ^ 3 = 1 → c ∈ Subgroup.zpowers z)
    {f₁ f₂ : X} (h12 : f₁ * f₂ = f₂ * f₁) (hf₁ : f₁ ^ 3 = 1) {s : S} (hs : s ^ 3 = 1)
    (hact : ∀ t, actionAut K ψ f₁ t = s * t * s⁻¹) : actionAut K ψ f₂ s = s := by
  obtain ⟨κ, hκ⟩ : ∃ κ : X, κ = (ψ s : X) := ⟨_, rfl⟩
  have hκK : κ ∈ K := hκ ▸ (ψ s).2
  obtain ⟨c, hc⟩ : ∃ c : X, c = κ⁻¹ * f₁ := ⟨_, rfl⟩
  have hf : f₁ = κ * c := by rw [hc]; group
  have hcC : c ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro κ' hκ'
    obtain ⟨t, ht⟩ := ψ.surjective ⟨κ', hκ'⟩
    have h2 : (ψ t : X) = κ' := congrArg Subtype.val ht
    have h1 := coe_psi_actionAut K ψ f₁ t
    rw [hact t, map_mul, map_mul, map_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2, ← hκ] at h1
    have h3 : f₁ * κ' = κ * κ' * κ⁻¹ * f₁ := by
      rw [h1]
      group
    calc κ' * c = κ' * (κ⁻¹ * f₁) := by rw [hc]
      _ = κ⁻¹ * (κ * κ' * κ⁻¹ * f₁) := by group
      _ = κ⁻¹ * (f₁ * κ') := by rw [h3]
      _ = c * κ' := by rw [hc]; group
  have hκ3 : κ ^ 3 = 1 := by
    have h2 : (ψ s) ^ 3 = 1 := by rw [← map_pow, hs, map_one]
    rw [hκ]
    exact congrArg Subtype.val h2
  have hκc : Commute κ c := Subgroup.mem_centralizer_iff.mp hcC κ hκK
  have hc3 : c ^ 3 = 1 := by
    have h1 := hf₁
    rw [hf, hκc.mul_pow, hκ3, one_mul] at h1
    exact h1
  have hcz : c ∈ Subgroup.zpowers z := hCz c hcC hc3
  have hf₂c : f₂ * c * f₂⁻¹ = c := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcz
    have hzf : Commute f₂ z := Subgroup.mem_center_iff.1 hzc f₂
    rw [mul_inv_eq_iff_eq_mul]
    exact (hzf.zpow_right n).eq
  have h2 : f₂ * f₁ * f₂⁻¹ = f₁ := by rw [← h12]; group
  have hκ' : κ = f₁ * c⁻¹ := by rw [hf]; group
  have hκfix : f₂ * κ * f₂⁻¹ = κ := by
    calc f₂ * κ * f₂⁻¹ = (f₂ * f₁ * f₂⁻¹) * (f₂ * c * f₂⁻¹)⁻¹ := by rw [hκ']; group
      _ = κ := by rw [h2, hf₂c, hκ']
  apply ψ.injective
  apply Subtype.ext
  rw [coe_psi_actionAut, ← hκ]
  exact hκfix

theorem slFieldAut_ne_one {k : Type} [Field k] {τ : k ≃+* k} (hτ : τ ≠ 1) :
    slFieldAut (Fin 3) k τ ≠ 1 := by
  intro h
  apply hτ
  ext x
  have h1 := congrArg (fun σ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k) =>
    ((σ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) x) :
      Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 1) h
  change τ ((1 + Matrix.single (0 : Fin 3) 1 x : Matrix (Fin 3) (Fin 3) k) 0 1) =
    (1 + Matrix.single (0 : Fin 3) 1 x : Matrix (Fin 3) (Fin 3) k) 0 1 at h1
  simpa using h1

theorem closure_fixed_eq_top_of_field
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (z : X)
    {k : Type} [Field k] [Finite k] (h3 : 3 ∣ Nat.card k - 1) (F : FrobData k)
    (hτ : orderOf F.τ = 3) (ψ : Matrix.SpecialLinearGroup (Fin 3) k ≃* K)
    (hzc : z ∈ Subgroup.center X)
    (hCz : ∀ c ∈ Subgroup.centralizer (K : Set X), c ^ 3 = 1 → c ∈ Subgroup.zpowers z)
    {A : Subgroup X} (hAe : Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27) (hzA : z ∈ A)
    {f₂ : X} (hf₂A : f₂ ∈ A) (hf₂ : actionAut K ψ f₂ = slFieldAut (Fin 3) k F.τ) :
    Subgroup.closure {x : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
      f * (x : X) * f⁻¹ = x} = ⊤ := by
  classical
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    isMulCommutative_iff_of_setLike.1 hAe.1 a ha b hb
  obtain ⟨a, haA, ha⟩ := exists_mem_not_mem_sup_zpowers hAe hAcard hzA hf₂A
  have hβ3 : actionAut K ψ a ^ 3 = 1 := by rw [← map_pow, hAe.2 a haA, map_one]
  obtain ⟨m, g, hg⟩ := exists_isConjBy_mul_pow hτ (actionAut K ψ a) hβ3
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : X, f₁ = a * f₂ ^ m := ⟨_, rfl⟩
  have hf₁A : f₁ ∈ A := hf₁ ▸ mul_mem haA (pow_mem hf₂A m)
  have hf₁3 : f₁ ^ 3 = 1 := hAe.2 f₁ hf₁A
  have h12 : f₁ * f₂ = f₂ * f₁ := hcomm f₁ hf₁A f₂ hf₂A
  have hφ₁ : actionAut K ψ f₁ = actionAut K ψ a * slFieldAut (Fin 3) k F.τ ^ m := by
    rw [hf₁, map_mul, map_pow, hf₂]
  have hg₁ : IsConjBy (actionAut K ψ f₁) g := by rwa [hφ₁]
  have hf₁C : f₁ ∉ Subgroup.centralizer (K : Set X) := by
    intro hmem
    apply ha
    have h1 : a = f₁ * (f₂ ^ m)⁻¹ := by rw [hf₁]; group
    rw [h1]
    exact mul_mem (Subgroup.mem_sup_left (hCz f₁ hmem hf₁3))
      (inv_mem (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers f₂) m)))
  have hf₂C : f₂ ∉ Subgroup.centralizer (K : Set X) := by
    intro hmem
    refine slFieldAut_ne_one ?_ (hf₂ ▸ actionAut_eq_one_of_mem_centralizer K ψ hmem)
    rintro h
    rw [h, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hφcomm : actionAut K ψ f₁ * slFieldAut (Fin 3) k F.τ =
      slFieldAut (Fin 3) k F.τ * actionAut K ψ f₁ := by
    rw [← hf₂, ← map_mul, ← map_mul, h12]
  obtain ⟨y, hy, hyfix⟩ := exists_fixed_conj F hg₁ hφcomm
  obtain ⟨c, s, hcdet, hs, hsact⟩ := exists_det_one_conj F h3 hy hyfix
  obtain ⟨c', hc'⟩ : ∃ c' : k, (y : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      c' • (1 : Matrix (Fin 3) (Fin 3) k) := by
    obtain ⟨c', hc'⟩ := eq_scalar_of_forall_commute (y ^ 3) (fun t => by
      have h3' := (hy.pow 3) t
      have h4 : (actionAut K ψ f₁ ^ 3) t = t := by rw [← map_pow, hf₁3, map_one]; rfl
      rw [h4] at h3'
      exact comm_of_conj_eq h3')
    exact ⟨c', by rw [← Units.val_pow_eq_pow_val]; exact hc'⟩
  have hlift : (y : Matrix (Fin 3) (Fin 3) k) ^ 3 = (c : k) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) k) →
      F.τ (c : k) = c := by
    intro hy3
    have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hs, smul_pow, hy3, smul_smul, ← mul_pow,
        inv_mul_cancel₀ c.ne_zero, one_pow, one_smul]
      rfl
    have hfix := actionAut_fix_of_pow_three K ψ hzc hCz h12 hf₁3 hs3 hsact
    rw [hf₂] at hfix
    obtain ⟨i, j, hij⟩ : ∃ i j, (y : Matrix (Fin 3) (Fin 3) k) i j ≠ 0 := by
      by_contra hcon
      exact GL_ne_zero y (by ext i j; by_contra hij; exact hcon ⟨i, j, hij⟩)
    have h1 : F.τ ((s : Matrix (Fin 3) (Fin 3) k) i j) = (s : Matrix (Fin 3) (Fin 3) k) i j :=
      congrFun (congrFun (congrArg Subtype.val hfix) i) j
    rw [hs] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hyfix i j] at h1
    have h2 : F.τ ((c : k)⁻¹) = (c : k)⁻¹ := mul_right_cancel₀ hij h1
    rw [map_inv₀] at h2
    exact inv_injective h2
  obtain ⟨P, u, hP, hPu⟩ := F.exists_fixed_frame h3 y hyfix hcdet hc' hlift
  have hPGL : Matrix.GeneralLinearGroup.map (F.τ : k →+* k) P = P :=
    Units.ext (by ext i j; exact hP i j)
  have hgen := closure_fixed_eq_top_semi F hy hPGL hPu
  have hsub : ∀ x ∈ {x : Matrix.SpecialLinearGroup (Fin 3) k |
      slFieldAut (Fin 3) k F.τ x = x ∨ actionAut K ψ f₁ x = x},
      (ψ x : K) ∈ {y : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (y : X) * f⁻¹ = y} := by
    rintro x (hx | hx)
    · refine ⟨f₂, hf₂A, hf₂C, ?_⟩
      have h1 := coe_psi_actionAut K ψ f₂ x
      rw [hf₂, hx] at h1
      exact h1.symm
    · refine ⟨f₁, hf₁A, hf₁C, ?_⟩
      have h1 := coe_psi_actionAut K ψ f₁ x
      rw [hx] at h1
      exact h1.symm
  rw [eq_top_iff]
  have hmap : Subgroup.map (ψ : Matrix.SpecialLinearGroup (Fin 3) k →* K) (Subgroup.closure
      {x : Matrix.SpecialLinearGroup (Fin 3) k |
        slFieldAut (Fin 3) k F.τ x = x ∨ actionAut K ψ f₁ x = x}) = ⊤ := by
    rw [hgen, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr ψ.surjective
  rw [MonoidHom.map_closure] at hmap
  rw [← hmap]
  exact Subgroup.closure_mono (Set.image_subset_iff.mpr (fun x hx => hsub x hx))

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
