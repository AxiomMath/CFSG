module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TensorModel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModule

open Module Subgroup
open scoped Matrix
open CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3)
open CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

section Fixed

variable (ρ : Representation (ZMod 2) K W)

theorem rep_mul_apply (k k' : K) (w : W) : ρ (k * k') w = ρ k (ρ k' w) := by
  rw [map_mul]
  rfl

@[expose] def fixFst : Submodule (ZMod 2) W where
  carrier := {w | ∀ g : S, ρ (g, 1) w = w}
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  zero_mem' _ := map_zero _
  smul_mem' c w hw g := by rw [map_smul, hw g]

@[expose] def fixSnd : Submodule (ZMod 2) W where
  carrier := {w | ∀ h : S, ρ (1, h) w = w}
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  zero_mem' _ := map_zero _
  smul_mem' c w hw g := by rw [map_smul, hw g]

theorem rep_mem_fixFst (k : K) {w : W} (hw : w ∈ fixFst ρ) : ρ k w ∈ fixFst ρ := fun g => by
  rw [← rep_mul_apply, show ((g, 1) : K) * k = k * (k.1⁻¹ * g * k.1, 1) from
    Prod.ext (by simp only [Prod.fst_mul]; group) (by simp), rep_mul_apply, hw]

theorem rep_mem_fixSnd (k : K) {w : W} (hw : w ∈ fixSnd ρ) : ρ k w ∈ fixSnd ρ := fun h => by
  rw [← rep_mul_apply, show ((1, h) : K) * k = k * (1, k.2⁻¹ * h * k.2) from
    Prod.ext (by simp) (by simp only [Prod.snd_mul]; group), rep_mul_apply, hw]

end Fixed

section NoFactorFixed

variable (ρ : Representation (ZMod 2) K W)
  (σ : W →ₗ[ZMod 2] W) (hσσ : ∀ w, σ (σ w) = w) (hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w))
  (hfix : ∀ w, (∀ g, ρ (g, g) w = w) → w = 0)

include hσρ in
theorem σ_mem_fixFst {w : W} (hw : w ∈ fixSnd ρ) : σ w ∈ fixFst ρ := fun g => by
  rw [← (show ((1, g) : K).swap = (g, 1) from rfl), ← hσρ, hw]

include hσρ in
theorem σ_mem_fixSnd {w : W} (hw : w ∈ fixFst ρ) : σ w ∈ fixSnd ρ := fun g => by
  rw [← (show ((g, 1) : K).swap = (1, g) from rfl), ← hσρ, hw]

include hfix in
theorem fixFst_inf_fixSnd : fixFst ρ ⊓ fixSnd ρ = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  refine hfix w fun g => ?_
  rw [show ((g, g) : K) = (g, 1) * (1, g) from Prod.ext (mul_one g).symm (one_mul g).symm,
    rep_mul_apply, hw.2 g, hw.1 g]

include hσσ hσρ in
theorem finrank_fixFst_eq [FiniteDimensional (ZMod 2) W] :
    finrank (ZMod 2) (fixFst ρ) = finrank (ZMod 2) (fixSnd ρ) := by
  have h₁ : ∀ w ∈ fixSnd ρ, σ w ∈ fixFst ρ := fun w hw => σ_mem_fixFst ρ σ hσρ hw
  have h₂ : ∀ w ∈ fixFst ρ, σ w ∈ fixSnd ρ := fun w hw => σ_mem_fixSnd ρ σ hσρ hw
  have hinj : Function.Injective σ := fun x y hxy => by rw [← hσσ x, hxy, hσσ]
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (f := σ.restrict h₂)
      fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))
  · exact LinearMap.finrank_le_finrank_of_injective (f := σ.restrict h₁)
      fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))

theorem commutator_S : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
  have : IsSimpleGroup S :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
  have : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).Normal := Subgroup.commutator_normal _ _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆
    with h | h
  · exfalso
    apply not_commute_U3
    rw [← commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_bot).1 (h ▸ Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
  · exact h

theorem eq_one_of_commute {M : Type*} [Monoid M] (ψ : S →* M) (hψ : ∀ g h, ψ g * ψ h = ψ h * ψ g)
    (g : S) : ψ g = 1 := by
  have hle : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul,
      mul_assoc (ψ x), hψ y x⁻¹, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul,
      ← map_mul, mul_inv_cancel, map_one]
  rw [commutator_S, top_le_iff] at hle
  exact (MonoidHom.mem_ker).1 (hle ▸ mem_top g)

end NoFactorFixed

section Quotient

variable [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) K W)
  (σ : W →ₗ[ZMod 2] W) (hσσ : ∀ w, σ (σ w) = w) (hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w))
  (hfix : ∀ w, (∀ g, ρ (g, g) w = w) → w = 0)
  (hdims : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ (g, g) u ∈ U) →
      finrank (ZMod 2) U = 0 ∨ finrank (ZMod 2) U = 3 ∨ finrank (ZMod 2) U = 6 ∨
        finrank (ZMod 2) U = 9)
  (hW : finrank (ZMod 2) W = 9)
  (hker : finrank (ZMod 2) (LinearMap.ker (σ - LinearMap.id)) = 6)
  (hnt : ∃ g w, σ w = w ∧ ρ (g, g) w - w ∉ LinearMap.range (σ - LinearMap.id))

omit [FiniteDimensional (ZMod 2) W] in
theorem sub_id_apply (w : W) : (σ - LinearMap.id : W →ₗ[ZMod 2] W) w = σ w + w := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_add_neg, ZModModule.neg_eq_self]

include hσσ hσρ hfix hdims hW hker hnt in
theorem fixSnd_eq_bot : fixSnd ρ = ⊥ := by
  set Z₁ := fixFst ρ with hZ₁
  set Z₂ := fixSnd ρ with hZ₂
  set P := Z₁ ⊔ Z₂ with hP
  have hinf : Z₁ ⊓ Z₂ = ⊥ := fixFst_inf_fixSnd ρ hfix
  have heq : finrank (ZMod 2) Z₁ = finrank (ZMod 2) Z₂ := finrank_fixFst_eq ρ σ hσσ hσρ
  have hPinv : ∀ k, ∀ w ∈ P, ρ k w ∈ P := fun k w hw => by
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup (rep_mem_fixFst ρ k hz₁) (rep_mem_fixSnd ρ k hz₂)
  have hPσ : ∀ w ∈ P, σ w ∈ P := fun w hw => by
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add, add_comm]
    exact Submodule.add_mem_sup (σ_mem_fixFst ρ σ hσρ hz₂) (σ_mem_fixSnd ρ σ hσρ hz₁)
  have hPdim : finrank (ZMod 2) P = 2 * finrank (ZMod 2) Z₂ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Z₁ Z₂
    rw [hinf, finrank_bot, add_zero, heq, ← hP] at h
    omega
  have hd : finrank (ZMod 2) Z₂ = 0 ∨ finrank (ZMod 2) Z₂ = 3 := by
    rcases hdims P (fun g u hu => hPinv _ u hu) with h | h | h | h <;> omega
  rcases hd with hd | hd
  · exact Submodule.finrank_eq_zero.1 hd
  exfalso
  set A := LinearMap.ker (σ - LinearMap.id) with hA
  set I := LinearMap.range (σ - LinearMap.id) with hI
  have hIdim : finrank (ZMod 2) I = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker (σ - LinearMap.id)
    rw [← hI, ← hA, hker, hW] at this
    omega
  have hmemA : ∀ w, w ∈ A ↔ σ w = w := fun w => by
    rw [hA, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hPAI : P ⊓ A ≤ I := by
    intro p hp
    obtain ⟨z₁, hz₁, z₂, hz₂, hp'⟩ := Submodule.mem_sup.1 hp.1
    have hσp := (hmemA p).1 hp.2
    rw [← hp', map_add] at hσp
    have h1 : σ z₁ + z₂ ∈ Z₁ ⊓ Z₂ := by
      have h2 : σ z₁ + z₂ = z₁ + σ z₂ := by
        have h3 : σ z₁ + σ z₂ + (z₂ + σ z₂) = z₁ + z₂ + (z₂ + σ z₂) := by rw [hσp]
        rw [show σ z₁ + σ z₂ + (z₂ + σ z₂) = σ z₁ + z₂ + (σ z₂ + σ z₂) by abel,
          ZModModule.add_self, add_zero,
          show z₁ + z₂ + (z₂ + σ z₂) = z₁ + σ z₂ + (z₂ + z₂) by abel, ZModModule.add_self,
          add_zero] at h3
        exact h3
      refine ⟨?_, Z₂.add_mem (σ_mem_fixSnd ρ σ hσρ hz₁) hz₂⟩
      rw [h2]
      exact Z₁.add_mem hz₁ (σ_mem_fixFst ρ σ hσρ hz₂)
    rw [hinf, Submodule.mem_bot] at h1
    have h4 : z₂ = σ z₁ := by
      have := congrArg (· + σ z₁) h1
      simp only [zero_add] at this
      rw [add_comm, ← add_assoc, ZModModule.add_self, zero_add] at this
      exact this
    refine ⟨z₁, ?_⟩
    rw [sub_id_apply, ← hp', h4, add_comm]
  have hinj : Function.Injective ((σ - LinearMap.id).domRestrict Z₁) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, sub_id_apply] at hz
    have hσz : σ z = z := by
      have := congrArg (· + (z : W)) hz
      simp only [zero_add] at this
      rwa [add_assoc, ZModModule.add_self, add_zero] at this
    have hz2 : (z : W) ∈ Z₁ ⊓ Z₂ := ⟨z.2, hσz ▸ σ_mem_fixSnd ρ σ hσρ z.2⟩
    rw [hinf, Submodule.mem_bot] at hz2
    exact (Submodule.mem_bot _).2 (Subtype.ext hz2)
  have hZ₁le : Z₁.map (σ - LinearMap.id) ≤ P ⊓ A := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨?_, (hmemA _).2 ?_⟩
    · rw [sub_id_apply, add_comm]
      exact Submodule.add_mem_sup hz (σ_mem_fixSnd ρ σ hσρ hz)
    · rw [sub_id_apply, map_add, hσσ, add_comm]
  have hPA : P ⊓ A = I := by
    refine Submodule.eq_of_le_of_finrank_le hPAI ?_
    have h1 := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict] at h1
    rw [hIdim, ← hd, ← heq, ← h1]
    exact Submodule.finrank_mono hZ₁le
  have hAP : A ⊔ P = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq A P
    rw [inf_comm, hPA, hIdim, hker, hPdim, hd] at h
    omega
  have hσw : ∀ w, σ w + w ∈ P := fun w => by
    obtain ⟨a, ha, p, hp, rfl⟩ := Submodule.mem_sup.1 (hAP ▸ Submodule.mem_top : w ∈ A ⊔ P)
    rw [map_add, (hmemA a).1 ha, show a + σ p + (a + p) = σ p + p + (a + a) by abel,
      ZModModule.add_self, add_zero]
    exact P.add_mem (hPσ p hp) hp
  have hswap : ∀ (h : S) (x : W), ρ (1, h) x + ρ (h, 1) x ∈ P := fun h x => by
    have h1 : ρ (1, h) x = σ (ρ (h, 1) (σ x)) := by rw [hσρ, hσσ]; rfl
    rw [h1, show σ (ρ (h, 1) (σ x)) + ρ (h, 1) x =
      (σ (ρ (h, 1) (σ x)) + ρ (h, 1) (σ x)) + ρ (h, 1) (σ x + x) by
        rw [map_add, show ∀ a b c : W, a + b + (b + c) = a + c + (b + b) from fun a b c => by abel,
          ZModModule.add_self, add_zero]]
    exact P.add_mem (hσw _) (hPinv _ _ (hσw x))
  let ψ : S →* Module.End (ZMod 2) (W ⧸ P) :=
    { toFun := fun g => P.mapQ P (ρ (g, 1)) fun w hw => hPinv _ w hw
      map_one' := by
        ext w
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
          Submodule.mapQ_apply, Module.End.one_apply]
        rw [show ((1, 1) : K) = 1 from rfl, map_one]
        rfl
      map_mul' := fun g h => by
        ext w
        simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
          Submodule.mapQ_apply, Module.End.mul_apply]
        rw [show ((g * h, 1) : K) = (g, 1) * (h, 1) from Prod.ext rfl (mul_one 1).symm,
          rep_mul_apply] }
  have hψ : ∀ g h, ψ g * ψ h = ψ h * ψ g := fun g h => by
    ext w
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Module.End.mul_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, sub_eq_add_neg, ZModModule.neg_eq_self]
    have e1 : ρ (g, 1) (ρ (1, h) w) = ρ (1, h) (ρ (g, 1) w) := by
      rw [← rep_mul_apply, ← rep_mul_apply,
        show ((g, 1) : K) * (1, h) = (1, h) * (g, 1) from Prod.ext (by simp) (by simp)]
    rw [show ρ (g, 1) (ρ (h, 1) w) + ρ (h, 1) (ρ (g, 1) w) =
      ρ (g, 1) (ρ (h, 1) w + ρ (1, h) w) + (ρ (1, h) (ρ (g, 1) w) + ρ (h, 1) (ρ (g, 1) w)) by
        rw [map_add, e1, show ∀ a b c : W, a + c = a + b + (b + c) from fun a b c => by
          rw [show a + b + (b + c) = a + c + (b + b) by abel, ZModModule.add_self, add_zero]]]
    exact P.add_mem (hPinv _ _ (by rw [add_comm]; exact hswap h w)) (hswap h _)
  have hfirst : ∀ (g : S) (w : W), ρ (g, 1) w + w ∈ P := fun g w => by
    have h1 := LinearMap.congr_fun (eq_one_of_commute ψ hψ g) (Submodule.Quotient.mk w)
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply,
      Module.End.one_apply] at h1
    rw [Submodule.Quotient.eq, sub_eq_add_neg, ZModModule.neg_eq_self] at h1
    exact h1
  obtain ⟨g, w, hσw', hnot⟩ := hnt
  apply hnot
  have hdiagP : ρ (g, g) w - w ∈ P := by
    rw [sub_eq_add_neg, ZModModule.neg_eq_self,
      show ((g, g) : K) = (g, 1) * (1, g) from Prod.ext (mul_one g).symm (one_mul g).symm,
      rep_mul_apply,
      show ρ (g, 1) (ρ (1, g) w) + w = (ρ (g, 1) (ρ (1, g) w) + ρ (1, g) w) +
        (ρ (1, g) w + ρ (g, 1) w) + (ρ (g, 1) w + w) by
          rw [show ∀ a b c d : W, a + b + (b + c) + (c + d) = a + d + (b + b) + (c + c) from
            fun a b c d => by abel, ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]]
    exact P.add_mem (P.add_mem (hfirst _ _) (hswap _ _)) (hfirst _ _)
  have hdiagA : ρ (g, g) w - w ∈ A := by
    rw [hmemA, map_sub, hσρ, hσw']
    rfl
  rw [← hPA]
  exact ⟨hdiagP, hdiagA⟩

end Quotient

theorem toLinearEquiv_map_apply {G W₁ W₂ : Type*} [Group G] [AddCommGroup W₁]
    [Module (ZMod 2) W₁] [AddCommGroup W₂] [Module (ZMod 2) W₂]
    {ρ₁ : Representation (ZMod 2) G W₁} {ρ₂ : Representation (ZMod 2) G W₂} (e : ρ₁.Equiv ρ₂)
    (g : G) (x : W₁) : e.toLinearEquiv (ρ₁ g x) = ρ₂ g (e.toLinearEquiv x) :=
  Equiv.map_apply e g x

theorem rho_of_mem_labelSub_zero (g : S) {x : V} (hx : x ∈ labelSub 0) : rho g x = x := by
  obtain ⟨c, rfl⟩ := (show x ∈ LinearMap.range inc0 from hx)
  exact Prod.ext rfl (Prod.ext (map_zero (repN g)) (Prod.ext (map_zero (repNd g))
    (map_zero (repA g))))

theorem repK_left_of_mem_block (j : Fin 4) (g : S) {m : T} (hm : m ∈ block 0 j) :
    repK (g, 1) m = m := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, y, -, rfl⟩ := hm
    rw [repK_tmul, rho_of_mem_labelSub_zero g hx, map_one]
    rfl
  | zero => exact map_zero _
  | add m m' _ _ h h' => rw [map_add, h, h']
  | smul c m _ h => rw [map_smul, h]

theorem repK_right_of_mem_block (i : Fin 4) (h : S) {m : T} (hm : m ∈ block i 0) :
    repK (1, h) m = m := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, -, y, hy, rfl⟩ := hm
    rw [repK_tmul, rho_of_mem_labelSub_zero h hy, map_one]
    rfl
  | zero => exact map_zero _
  | add m m' _ _ h h' => rw [map_add, h, h']
  | smul c m _ h => rw [map_smul, h]

theorem finrank_block (ij : Fin 4 × Fin 4) :
    finrank (ZMod 2) (block ij.1 ij.2) = labelDim ij.1 * labelDim ij.2 := by
  rw [← (blockEquiv ij).toLinearEquiv.finrank_eq, Module.finrank_tensorProduct,
    finrank_labelSub, finrank_labelSub]

theorem congr_outer {G H W₁ W₁' W₂ W₂' : Type*} [Group G] [Group H] [AddCommGroup W₁]
    [Module (ZMod 2) W₁] [AddCommGroup W₁'] [Module (ZMod 2) W₁'] [AddCommGroup W₂]
    [Module (ZMod 2) W₂] [AddCommGroup W₂'] [Module (ZMod 2) W₂']
    {ρ₁ : Representation (ZMod 2) G W₁} {ρ₁' : Representation (ZMod 2) G W₁'}
    {ρ₂ : Representation (ZMod 2) H W₂} {ρ₂' : Representation (ZMod 2) H W₂'}
    (e₁ : ρ₁.Equiv ρ₁') (e₂ : ρ₂.Equiv ρ₂') (p : G × H) (x : TensorProduct (ZMod 2) W₁ W₂) :
    TensorProduct.congr e₁.toLinearEquiv e₂.toLinearEquiv (outer ρ₁ ρ₂ p x) =
      outer ρ₁' ρ₂' p (TensorProduct.congr e₁.toLinearEquiv e₂.toLinearEquiv x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    rw [outer_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul, outer_tmul]
    exact congrArg₂ _ (Equiv.map_apply e₁ p.1 x) (Equiv.map_apply e₂ p.2 y)
  | add x y hx hy =>
    simp only [map_add, hx, hy]

theorem nine_le_labelDim_mul (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
    9 ≤ labelDim i * labelDim j := by
  revert hi hj
  fin_cases i <;> fin_cases j <;> decide

theorem labelDim_mul_eq_nine (i j : Fin 4) (h : labelDim i * labelDim j = 9) :
    (i = 1 ∨ i = 2) ∧ (j = 1 ∨ j = 2) := by
  revert h
  fin_cases i <;> fin_cases j <;> decide

section Identification

variable [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) K W)
  (σ : W →ₗ[ZMod 2] W) (hσσ : ∀ w, σ (σ w) = w) (hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w))
  (hfix : ∀ w, (∀ g, ρ (g, g) w = w) → w = 0)
  (hdims : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ (g, g) u ∈ U) →
      finrank (ZMod 2) U = 0 ∨ finrank (ZMod 2) U = 3 ∨ finrank (ZMod 2) U = 6 ∨
        finrank (ZMod 2) U = 9)
  (hW : finrank (ZMod 2) W = 9)
  (hker : finrank (ZMod 2) (LinearMap.ker (σ - LinearMap.id)) = 6)
  (hnt : ∃ g w, σ w = w ∧ ρ (g, g) w - w ∉ LinearMap.range (σ - LinearMap.id))

include hσσ hσρ hfix hdims hW hker hnt in
theorem isIrreducible_of_hyps : ρ.IsIrreducible := by
  rw [isIrreducible_iff]
  refine ⟨Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hW]; norm_num), fun U hU => ?_⟩
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  obtain ⟨W₀, hW₀U, hW₀, hW₀0, hmin⟩ := exists_minimal ρ hU hU0
  have hirr := isIrreducible_subrepOf hW₀ hW₀0 hmin
  obtain ⟨⟨i, j⟩, ⟨e⟩⟩ := exists_equiv_blockRepK _ hirr
  have hZ₂ := fixSnd_eq_bot ρ σ hσσ hσρ hfix hdims hW hker hnt
  have hi : i ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₀0
    have htriv : ∀ g : S, ρ (g, 1) w = w := fun g => by
      have h1 := Equiv.map_apply e (g, 1) ⟨w, hw⟩
      rw [show blockRepK (0, j) (g, 1) (e ⟨w, hw⟩) = e ⟨w, hw⟩ from
        Subtype.ext (repK_left_of_mem_block j g (e ⟨w, hw⟩).2)] at h1
      exact congrArg Subtype.val (e.toLinearEquiv.injective h1)
    have hσw : σ w ∈ fixSnd ρ := σ_mem_fixSnd ρ σ hσρ htriv
    rw [hZ₂, Submodule.mem_bot] at hσw
    apply hw0
    rw [← hσσ w, hσw, map_zero]
  have hj : j ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₀0
    have htriv : w ∈ fixSnd ρ := fun h => by
      have h1 := Equiv.map_apply e (1, h) ⟨w, hw⟩
      rw [show blockRepK (i, 0) (1, h) (e ⟨w, hw⟩) = e ⟨w, hw⟩ from
        Subtype.ext (repK_right_of_mem_block i h (e ⟨w, hw⟩).2)] at h1
      exact congrArg Subtype.val (e.toLinearEquiv.injective h1)
    rw [hZ₂, Submodule.mem_bot] at htriv
    exact hw0 htriv
  have hdim : finrank (ZMod 2) W₀ = labelDim i * labelDim j :=
    e.toLinearEquiv.finrank_eq.trans (finrank_block (i, j))
  have h9 : 9 ≤ finrank (ZMod 2) W₀ := hdim ▸ nine_le_labelDim_mul i j hi hj
  have hW₀top : W₀ = ⊤ := Submodule.eq_top_of_finrank_eq
    (le_antisymm (Submodule.finrank_le _) (hW ▸ h9))
  exact eq_top_iff.2 (hW₀top ▸ hW₀U)

include hσσ hσρ hfix hdims hW hker hnt in
theorem exists_tensor_model :
    ∃ (Φ : W ≃ₗ[ZMod 2] Mat3) (α : S ≃* S),
      (∀ k w, Φ (ρ k w) = repM (α k.1, α k.2) (Φ w)) ∧ ∀ w, Φ (σ w) = (Φ w)ᵀ := by
  have hirr := isIrreducible_of_hyps ρ σ hσσ hσρ hfix hdims hW hker hnt
  obtain ⟨⟨i, j⟩, ⟨e⟩⟩ := exists_equiv_blockRepK ρ hirr
  have hdim : labelDim i * labelDim j = 9 := by
    rw [← finrank_block (i, j), ← e.toLinearEquiv.finrank_eq, hW]
  obtain ⟨hi, hj⟩ := labelDim_mul_eq_nine i j hdim
  have key : ∃ (Φ₀ : W ≃ₗ[ZMod 2] Mat3) (α β : S ≃* S),
      (∀ k w, Φ₀ (ρ k w) = repM (α k.1, β k.2) (Φ₀ w)) ∧
        (α = β ∨ ∀ g, repM (α g, β g) 1 = 1) := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · refine ⟨e.toLinearEquiv ≪≫ₗ (blockEquiv (1, 1)).symm.toLinearEquiv ≪≫ₗ
        TensorProduct.congr labelEquiv1.toLinearEquiv labelEquiv1.toLinearEquiv ≪≫ₗ tensorMat,
        tau, tau, fun k w => ?_, Or.inl rfl⟩
      simp only [LinearEquiv.trans_apply]
      rw [toLinearEquiv_map_apply e, toLinearEquiv_map_apply (blockEquiv (1, 1)).symm,
        congr_outer]
      exact tensorMat_outer_NN k _
    · refine ⟨e.toLinearEquiv ≪≫ₗ (blockEquiv (1, 2)).symm.toLinearEquiv ≪≫ₗ
        TensorProduct.congr labelEquiv1.toLinearEquiv labelEquiv2.toLinearEquiv ≪≫ₗ tensorMat,
        tau, MulEquiv.refl S, fun k w => ?_, Or.inr repM_tau_left_one⟩
      simp only [LinearEquiv.trans_apply]
      rw [toLinearEquiv_map_apply e, toLinearEquiv_map_apply (blockEquiv (1, 2)).symm,
        congr_outer]
      exact tensorMat_outer_NNd k _
    · refine ⟨e.toLinearEquiv ≪≫ₗ (blockEquiv (2, 1)).symm.toLinearEquiv ≪≫ₗ
        TensorProduct.congr labelEquiv2.toLinearEquiv labelEquiv1.toLinearEquiv ≪≫ₗ tensorMat,
        MulEquiv.refl S, tau, fun k w => ?_, Or.inr repM_tau_right_one⟩
      simp only [LinearEquiv.trans_apply]
      rw [toLinearEquiv_map_apply e, toLinearEquiv_map_apply (blockEquiv (2, 1)).symm,
        congr_outer]
      exact tensorMat_outer_NdN k _
    · refine ⟨e.toLinearEquiv ≪≫ₗ (blockEquiv (2, 2)).symm.toLinearEquiv ≪≫ₗ
        TensorProduct.congr labelEquiv2.toLinearEquiv labelEquiv2.toLinearEquiv ≪≫ₗ tensorMat,
        MulEquiv.refl S, MulEquiv.refl S, fun k w => ?_, Or.inl rfl⟩
      simp only [LinearEquiv.trans_apply]
      rw [toLinearEquiv_map_apply e, toLinearEquiv_map_apply (blockEquiv (2, 2)).symm,
        congr_outer]
      exact tensorMat_outer_NdNd k _
  obtain ⟨Φ₀, α, β, hΦ₀, hαβ⟩ := key
  have hαβ' : α = β := by
    rcases hαβ with h | h
    · exact h
    exfalso
    have h1 : Φ₀.symm 1 = 0 := hfix _ fun g => by
      apply Φ₀.injective
      rw [hΦ₀, LinearEquiv.apply_symm_apply, h g]
    have h2 := congrArg Φ₀ h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact one_ne_zero h2
  subst hαβ'
  refine ⟨Φ₀, α, hΦ₀, ?_⟩
  have hsymm : ∀ (k : K) (X : Mat3), Φ₀.symm (repM k X) =
      ρ (α.symm k.1, α.symm k.2) (Φ₀.symm X) := fun k X => by
    apply Φ₀.injective
    rw [LinearEquiv.apply_symm_apply, hΦ₀, LinearEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  obtain ⟨F, hF⟩ : ∃ F : Module.End (ZMod 2) Mat3,
      F = transM ∘ₗ Φ₀.toLinearMap ∘ₗ σ ∘ₗ Φ₀.symm.toLinearMap := ⟨_, rfl⟩
  have hFapply : ∀ X, F X = (Φ₀ (σ (Φ₀.symm X)))ᵀ := fun X => by
    rw [hF]
    rfl
  have hFcomm : ∀ k, F * repM k = repM k * F := fun k => by
    ext1 X
    rw [Module.End.mul_apply, Module.End.mul_apply, hFapply, hFapply, hsymm, hσρ, hΦ₀]
    change (repM (α (α.symm k.2), α (α.symm k.1)) _)ᵀ = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← transM_apply, transM_repM,
      transM_apply]
    rfl
  rcases repM_end_cases F hFcomm with hF0 | hF1
  ·
    exfalso
    have hnt' : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2)
      (by rw [hW]; norm_num)
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    have h1 : F (Φ₀ w) = 0 := by rw [hF0, LinearMap.zero_apply]
    rw [hFapply, LinearEquiv.symm_apply_apply] at h1
    have h2 : Φ₀ (σ w) = 0 := by
      have := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_transpose, Matrix.transpose_zero] at this
    rw [← hσσ w, Φ₀.map_eq_zero_iff.1 h2, map_zero]
  · intro w
    have h1 : F (Φ₀ w) = Φ₀ w := by rw [hF1, Module.End.one_apply]
    rw [hFapply, LinearEquiv.symm_apply_apply] at h1
    rw [← h1, Matrix.transpose_transpose]

end Identification

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModule
