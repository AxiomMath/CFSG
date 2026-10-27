module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderFlip

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open TensorProduct Module

universe u v

section Transport

variable {F : Type u} [Field F] {U : Type u} [AddCommGroup U] [Module F U]
variable {ι κ : Type*}

@[expose] noncomputable def opT (ν : Equiv.Perm ι) (g : ι → (U ≃ₗ[F] U)) :
    (⨂[F] _ : ι, U) ≃ₗ[F] ⨂[F] _ : ι, U :=
  (PiTensorProduct.reindex F (fun _ : ι => U) ν).trans (PiTensorProduct.congr g)

theorem opT_tprod (ν : Equiv.Perm ι) (g : ι → (U ≃ₗ[F] U)) (m : ι → U) :
    opT ν g (PiTensorProduct.tprod F m) =
      PiTensorProduct.tprod F (fun i => g i (m (ν.symm i))) := by
  simp [opT, PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]

@[expose] noncomputable def phiEquiv (E : ι ≃ κ ⊕ κ) :
    (⨂[F] _ : ι, U) ≃ₗ[F] (⨂[F] _ : κ, U) ⊗[F] (⨂[F] _ : κ, U) :=
  (PiTensorProduct.reindex F (fun _ : ι => U) E).trans (PiTensorProduct.tmulEquiv F U).symm

theorem phiEquiv_symm_tmul (E : ι ≃ κ ⊕ κ) (mp mq : κ → U) :
    (phiEquiv (F := F) (U := U) E).symm
      (PiTensorProduct.tprod F mp ⊗ₜ[F] PiTensorProduct.tprod F mq) =
      PiTensorProduct.tprod F (fun i => Sum.elim mp mq (E i)) := by
  rw [phiEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    PiTensorProduct.tmulEquiv_apply, PiTensorProduct.reindex_symm, PiTensorProduct.reindex_tprod]
  simp


theorem tmulEquiv_symm_tprod (h : κ ⊕ κ → U) :
    (PiTensorProduct.tmulEquiv F U).symm (PiTensorProduct.tprod F h) =
      PiTensorProduct.tprod F (fun l => h (Sum.inl l)) ⊗ₜ[F]
        PiTensorProduct.tprod F (fun l => h (Sum.inr l)) := by
  rw [LinearEquiv.symm_apply_eq]
  have := PiTensorProduct.tmulEquiv_apply F U (fun l => h (Sum.inl l)) (fun l => h (Sum.inr l))
  rw [this]
  congr 1
  funext i
  cases i <;> rfl

theorem phi_conj_tprod (E : ι ≃ κ ⊕ κ) (π : Equiv.Perm ι) (g : ι → (U ≃ₗ[F] U))
    (mp mq : κ → U) :
    phiEquiv E (opT π g ((phiEquiv E).symm
        (PiTensorProduct.tprod F mp ⊗ₜ[F] PiTensorProduct.tprod F mq))) =
      PiTensorProduct.tprod F (fun l => g (E.symm (Sum.inl l))
          (Sum.elim mp mq (E (π.symm (E.symm (Sum.inl l)))))) ⊗ₜ[F]
        PiTensorProduct.tprod F (fun l => g (E.symm (Sum.inr l))
          (Sum.elim mp mq (E (π.symm (E.symm (Sum.inr l)))))) := by
  rw [phiEquiv_symm_tmul, opT_tprod, phiEquiv, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_tprod, tmulEquiv_symm_tprod]

theorem tmul_ext_tprod {Z : Type*} [AddCommGroup Z] [Module F Z]
    (f f' : (⨂[F] _ : κ, U) ⊗[F] (⨂[F] _ : κ, U) →ₗ[F] Z)
    (h : ∀ mp mq : κ → U, f (PiTensorProduct.tprod F mp ⊗ₜ[F] PiTensorProduct.tprod F mq) =
      f' (PiTensorProduct.tprod F mp ⊗ₜ[F] PiTensorProduct.tprod F mq)) : f = f' := by
  refine TensorProduct.ext' fun p q => ?_
  induction p using PiTensorProduct.induction_on with
  | smul_tprod r mp =>
    induction q using PiTensorProduct.induction_on with
    | smul_tprod r' mq =>
      rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul,
        map_smul, h]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]


theorem phi_conj_block (E : ι ≃ κ ⊕ κ) (π : Equiv.Perm ι) (g : ι → (U ≃ₗ[F] U))
    (ν₁ ν₂ : Equiv.Perm κ)
    (h1 : ∀ l, E (π.symm (E.symm (Sum.inl l))) = Sum.inl (ν₁.symm l))
    (h2 : ∀ l, E (π.symm (E.symm (Sum.inr l))) = Sum.inr (ν₂.symm l))
    (z : (⨂[F] _ : κ, U) ⊗[F] (⨂[F] _ : κ, U)) :
    phiEquiv E (opT π g ((phiEquiv E).symm z)) =
      TensorProduct.congr (opT ν₁ (fun l => g (E.symm (Sum.inl l))))
        (opT ν₂ (fun l => g (E.symm (Sum.inr l)))) z := by
  have key := tmul_ext_tprod
    ((phiEquiv E).toLinearMap ∘ₗ (opT π g).toLinearMap ∘ₗ (phiEquiv E).symm.toLinearMap)
    (TensorProduct.congr (opT ν₁ (fun l => g (E.symm (Sum.inl l))))
      (opT ν₂ (fun l => g (E.symm (Sum.inr l))))).toLinearMap (fun mp mq => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [phi_conj_tprod, TensorProduct.congr_tmul, opT_tprod, opT_tprod]
      simp [h1, h2])
  exact LinearMap.congr_fun key z

theorem phi_conj_swap (E : ι ≃ κ ⊕ κ) (π : Equiv.Perm ι) (g : ι → (U ≃ₗ[F] U))
    (h1 : ∀ l, E (π.symm (E.symm (Sum.inl l))) = Sum.inr l)
    (h2 : ∀ l, E (π.symm (E.symm (Sum.inr l))) = Sum.inl l)
    (z : (⨂[F] _ : κ, U) ⊗[F] (⨂[F] _ : κ, U)) :
    phiEquiv E (opT π g ((phiEquiv E).symm z)) =
      TensorProduct.congr (PiTensorProduct.congr (fun l => g (E.symm (Sum.inl l))))
        (PiTensorProduct.congr (fun l => g (E.symm (Sum.inr l))))
        (TensorProduct.comm F _ _ z) := by
  have key := tmul_ext_tprod
    ((phiEquiv E).toLinearMap ∘ₗ (opT π g).toLinearMap ∘ₗ (phiEquiv E).symm.toLinearMap)
    ((TensorProduct.congr (PiTensorProduct.congr (fun l => g (E.symm (Sum.inl l))))
      (PiTensorProduct.congr (fun l => g (E.symm (Sum.inr l))))).toLinearMap ∘ₗ
      (TensorProduct.comm F (⨂[F] _ : κ, U) (⨂[F] _ : κ, U)).toLinearMap) (fun mp mq => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [phi_conj_tprod, TensorProduct.comm_tmul, TensorProduct.congr_tmul,
        PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod]
      simp [h1, h2])
  exact LinearMap.congr_fun key z

end Transport






theorem counting_arith (q D f nA nB : ℕ) (hq : 2 ≤ q) (hD : 2 ≤ D)
    (hoff : q ^ (D * D) ≤ nA * q ^ f) (hf : f ≤ D * D - D * (D - 1) / 2)
    (hA : nA = 2 * nB) (h3 : 3 ≤ D → nB = 1)
    (h2 : D = 2 → nB ≤ q ∧ (nB = 1 ∨ f ≤ 2)) : D = 2 ∧ q = 2 := by
  have hqpos : 0 < q := by omega
  by_cases hD3 : 3 ≤ D
  · exfalso
    have hnB := h3 hD3
    subst hA
    rw [hnB] at hoff
    have hR : 3 ≤ D * (D - 1) / 2 := by
      have : 6 ≤ D * (D - 1) := by
        calc 6 = 3 * 2 := by norm_num
          _ ≤ D * (D - 1) := Nat.mul_le_mul hD3 (by omega)
      omega
    have hRle : D * (D - 1) / 2 ≤ D * D := by
      calc D * (D - 1) / 2 ≤ D * (D - 1) := Nat.div_le_self _ _
        _ ≤ D * D := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    set R := D * (D - 1) / 2 with hRdef
    have h1 : q ^ (D * D) = q ^ (D * D - R) * q ^ R := by
      rw [← pow_add, Nat.sub_add_cancel hRle]
    have h2' : q ^ f ≤ q ^ (D * D - R) := Nat.pow_le_pow_right hqpos hf
    have h3' : q ^ (D * D - R) * q ^ R ≤ q ^ (D * D - R) * 2 := by
      rw [← h1]
      calc q ^ (D * D) ≤ 2 * 1 * q ^ f := hoff
        _ ≤ 2 * q ^ (D * D - R) := by
          rw [mul_one]; exact Nat.mul_le_mul_left _ h2'
        _ = q ^ (D * D - R) * 2 := mul_comm _ _
    have h4 : q ^ R ≤ 2 := Nat.le_of_mul_le_mul_left h3' (pow_pos hqpos _)
    have h5 : 2 ^ 3 ≤ q ^ R := calc 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
      _ ≤ q ^ R := Nat.pow_le_pow_right hqpos hR
    omega
  · have hD2 : D = 2 := by omega
    subst hD2
    refine ⟨rfl, ?_⟩
    obtain ⟨hnB, hcases⟩ := h2 rfl
    have key : q ^ 4 ≤ 2 * q ^ 3 := by
      rcases hcases with h1 | h1
      · subst hA
        rw [h1] at hoff
        have : f ≤ 3 := by simpa using hf
        calc q ^ 4 = q ^ (2 * 2) := by norm_num
          _ ≤ 2 * 1 * q ^ f := hoff
          _ ≤ 2 * q ^ 3 := by
            rw [mul_one]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hqpos this)
      · subst hA
        calc q ^ 4 = q ^ (2 * 2) := by norm_num
          _ ≤ 2 * nB * q ^ f := hoff
          _ ≤ 2 * q * q ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hnB) (Nat.pow_le_pow_right hqpos h1)
          _ = 2 * q ^ 3 := by ring
    have : q * q ^ 3 ≤ 2 * q ^ 3 := by
      calc q * q ^ 3 = q ^ 4 := by ring
        _ ≤ 2 * q ^ 3 := key
    have := Nat.le_of_mul_le_mul_right this (pow_pos hqpos 3)
    omega

section TFC

variable {F : Type u} [Field F] {P : Type u} [AddCommGroup P] [Module F P]
  {W : Type u} [AddCommGroup W] [Module F W]

@[expose] def conjHom {X : Type*} [AddCommGroup X] [Module F X] (Θ : W ≃ₗ[F] X) :
    (W ≃ₗ[F] W) →* (X ≃ₗ[F] X) where
  toFun a := Θ.symm.trans (a.trans Θ)
  map_one' := LinearEquiv.ext fun z => by simp
  map_mul' a b := LinearEquiv.ext fun z => by simp

theorem conjHom_apply {X : Type*} [AddCommGroup X] [Module F X] (Θ : W ≃ₗ[F] X)
    (a : W ≃ₗ[F] W) (z : X) : conjHom Θ a z = Θ (a (Θ.symm z)) := rfl

theorem conjHom_injective {X : Type*} [AddCommGroup X] [Module F X] (Θ : W ≃ₗ[F] X) :
    Function.Injective (conjHom Θ) := by
  intro a b h
  refine LinearEquiv.ext fun w => ?_
  have := congrArg (fun f : X ≃ₗ[F] X => Θ.symm (f (Θ w))) h
  simpa [conjHom_apply] using this

theorem transitive_two_factor_core [Finite F] [CharP F 2] [Module.Finite F P]
    (hD : 2 ≤ Module.finrank F P) (Φ : W ≃ₗ[F] P ⊗[F] P)
    (A A₁ : Subgroup (W ≃ₗ[F] W)) (hA₁ : A₁ ≤ A) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a * a = 1) (a₀ : W ≃ₗ[F] W) (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ∉ A₁)
    (hidx : ∀ a ∈ A, a ∈ A₁ ∨ a * a₀ ∈ A₁)
    (hblock : ∀ b ∈ A₁, ∃ x y : P ≃ₗ[F] P, ∀ p q,
      Φ (b (Φ.symm (p ⊗ₜ[F] q))) = x p ⊗ₜ[F] y q)
    (hswap : ∃ α β : P ≃ₗ[F] P, ∀ p q, Φ (a₀ (Φ.symm (p ⊗ₜ[F] q))) = α q ⊗ₜ[F] β p)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card (fixGL A)) :
    Module.finrank F P = 2 ∧ Nat.card F = 2 := by
  classical
  have hnt : Nontrivial P := Module.nontrivial_of_finrank_pos (R := F) (M := P) (by omega)
  obtain ⟨α, β, hαβ⟩ := hswap
  let Ψ : (P ⊗[F] P) ≃ₗ[F] (P ⊗[F] P) := TensorProduct.congr (LinearEquiv.refl F P) α
  let Θ : W ≃ₗ[F] P ⊗[F] P := Φ.trans Ψ
  let cj : (W ≃ₗ[F] W) →* ((P ⊗[F] P) ≃ₗ[F] (P ⊗[F] P)) := conjHom Θ
  have hΘsymm : ∀ p q : P, Θ.symm (p ⊗ₜ[F] q) = Φ.symm (p ⊗ₜ[F] α.symm q) := by
    intro p q
    simp [Θ, Ψ]
  have hcj_a₀ : ∀ p q : P, cj a₀ (p ⊗ₜ[F] q) = q ⊗ₜ[F] α (β p) := by
    intro p q
    show Θ (a₀ (Θ.symm (p ⊗ₜ[F] q))) = _
    rw [hΘsymm]
    show Ψ (Φ (a₀ (Φ.symm (p ⊗ₜ[F] α.symm q)))) = _
    rw [hαβ]
    simp [Ψ]
  have hw1 : β.trans α = 1 := by
    apply eq_of_tensor_square_eq
    intro u v
    have h2 := congrArg (fun f : W ≃ₗ[F] W => cj f (u ⊗ₜ[F] v)) (hA2 a₀ ha₀)
    simp only [map_mul, map_one, LinearEquiv.mul_apply, hcj_a₀] at h2
    exact h2
  have hcj_flip : ∀ z, cj a₀ z = TensorProduct.comm F P P z := by
    intro z
    refine LinearMap.congr_fun (f := (cj a₀).toLinearMap)
      (g := (TensorProduct.comm F P P).toLinearMap) (TensorProduct.ext' fun p q => ?_) z
    simp only [LinearEquiv.coe_coe, hcj_a₀, TensorProduct.comm_tmul]
    rw [show α (β p) = p from LinearEquiv.congr_fun hw1 p]
  have hcj_b : ∀ b ∈ A₁, ∃ x y : P ≃ₗ[F] P, ∀ p q, cj b (p ⊗ₜ[F] q) = x p ⊗ₜ[F] y q := by
    intro b hb
    obtain ⟨x, y, hxy⟩ := hblock b hb
    refine ⟨x, α.symm.trans (y.trans α), fun p q => ?_⟩
    show Θ (b (Θ.symm (p ⊗ₜ[F] q))) = _
    rw [hΘsymm]
    show Ψ (Φ (b (Φ.symm (p ⊗ₜ[F] α.symm q)))) = _
    rw [hxy]
    simp [Ψ]
  let B'' : Subgroup ((P ⊗[F] P) ≃ₗ[F] (P ⊗[F] P)) := A₁.map cj
  have hform : ∀ b ∈ B'', ∃ x y : P ≃ₗ[F] P, ∀ u v, b (u ⊗ₜ[F] v) = x u ⊗ₜ[F] y v := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    exact hcj_b b₀ hb₀
  have hcomm : ∀ b ∈ B'', ∀ w, b (TensorProduct.comm F P P w) =
      TensorProduct.comm F P P (b w) := by
    intro b hb w
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← hcj_flip, ← LinearEquiv.mul_apply, ← map_mul, hAab b₀ (hA₁ hb₀) a₀ ha₀, map_mul,
      LinearEquiv.mul_apply]
    exact hcj_flip _
  have hfix : ∀ b ∈ B'', ∀ w, b (TensorProduct.comm F P P w - w) =
      TensorProduct.comm F P P w - w := by
    intro b hb w
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    have h1 : cj a₀ w - w = Θ (a₀ (Θ.symm w) - Θ.symm w) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; rfl
    rw [← hcj_flip, h1]
    show Θ (b₀ (Θ.symm (Θ (a₀ (Θ.symm w) - Θ.symm w)))) = _
    rw [LinearEquiv.symm_apply_apply, hquad a₀ ha₀ b₀ (hA₁ hb₀)]
  have hP2 : IsPGroup 2 B'' := fun g => ⟨1, by
    obtain ⟨g, hg⟩ := g
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hg
    apply Subtype.ext
    show (cj b₀) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two, ← map_mul, hA2 b₀ (hA₁ hb₀), map_one]⟩
  obtain ⟨γ, hγ1, hγ2, hγ3, hγ4, hγ5, hγ6, hγ7⟩ :=
    quadratic_tensor_flip_factor_kernel hD B'' hform hcomm hfix
  have hWfin : Module.Finite F W := Module.Finite.equiv Θ.symm
  have hq2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hAcard : Nat.card A = 2 * Nat.card A₁ := by
    have hidx2 : (A₁.subgroupOf A).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨a₀, ha₀⟩, fun b => ?_⟩
      have hb := hidx b.1 b.2
      have hnot : ¬ ((b : W ≃ₗ[F] W) ∈ A₁ ∧ (b : W ≃ₗ[F] W) * a₀ ∈ A₁) := by
        rintro ⟨h1, h2⟩
        apply ha₀1
        have := A₁.mul_mem (A₁.inv_mem h1) h2
        simpa using this
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      unfold Xor
      tauto
    have := Subgroup.card_mul_index (A₁.subgroupOf A)
    rw [hidx2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁).toEquiv] at this
    omega
  have hB''card : Nat.card B'' = Nat.card A₁ :=
    Subgroup.card_map_of_injective (conjHom_injective Θ)
  have hWcard : Nat.card W = Nat.card F ^ (Module.finrank F P * Module.finrank F P) := by
    rw [Nat.card_congr Θ.toEquiv, Module.natCard_eq_pow_finrank (K := F),
      Module.finrank_tensorProduct]
  have hfA : Nat.card (fixGL A) = Nat.card F ^ Module.finrank F (fixGL A) :=
    Module.natCard_eq_pow_finrank (K := F)
  let T : Module.End F (P ⊗[F] P) :=
    (TensorProduct.comm F P P : (P ⊗[F] P) →ₗ[F] (P ⊗[F] P)) - LinearMap.id
  let Y : Submodule F (P ⊗[F] P) := (fixGL A).map Θ.toLinearMap
  have hY : Module.finrank F Y = Module.finrank F (fixGL A) := LinearEquiv.finrank_map_eq Θ _
  have hYker : Y ≤ LinearMap.ker T := by
    rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker]
    show TensorProduct.comm F P P (Θ w) - Θ w = 0
    rw [← hcj_flip, sub_eq_zero]
    show Θ (a₀ (Θ.symm (Θ w))) = Θ w
    rw [LinearEquiv.symm_apply_apply, mem_fixGL.1 hw a₀ ha₀]
  have hYfix : Y ≤ fixGL B'' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_fixGL]
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    show Θ (b₀ (Θ.symm (Θ w))) = Θ w
    rw [LinearEquiv.symm_apply_apply, mem_fixGL.1 hw b₀ (hA₁ hb₀)]
  have hf1 : Module.finrank F (fixGL A) ≤
      Module.finrank F P * Module.finrank F P - Module.finrank F P * (Module.finrank F P - 1) / 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker T
    rw [Module.finrank_tensorProduct, hγ7] at h1
    have h2 : Module.finrank F Y ≤ Module.finrank F (LinearMap.ker T) :=
      Submodule.finrank_mono hYker
    omega
  rw [hWcard, hfA] at hoff
  refine counting_arith (Nat.card F) (Module.finrank F P) (Module.finrank F (fixGL A))
    (Nat.card A) (Nat.card A₁) hq2 hD hoff hf1 hAcard (fun h3 => ?_) (fun h2 => ?_)
  · have := hγ4 h3
    rw [← hB''card, this, Subgroup.card_bot]
  · obtain ⟨hle, himp⟩ := hγ6 h2 hP2
    refine ⟨hB''card ▸ hle, ?_⟩
    by_cases hbot : B'' = ⊥
    · left; rw [← hB''card, hbot, Subgroup.card_bot]
    · right
      calc Module.finrank F (fixGL A) = Module.finrank F Y := hY.symm
        _ ≤ Module.finrank F (fixGL B'') := Submodule.finrank_mono hYfix
        _ ≤ 2 := himp hbot

end TFC

end CFSG.QuasithinUnique.Setup.Offender
