module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Model
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamASylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup

@[expose] def conjEquiv {W U : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U]
    [Module (ZMod 2) U] (e : W ≃ₗ[ZMod 2] U) : (W ≃ₗ[ZMod 2] W) ≃* (U ≃ₗ[ZMod 2] U) where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' f g := by ext x; simp

theorem conjEquiv_apply {W U : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U]
    [Module (ZMod 2) U] (e : W ≃ₗ[ZMod 2] U) (f : W ≃ₗ[ZMod 2] W) (u : U) :
    conjEquiv e f u = e (f (e.symm u)) := rfl

theorem orderOf_two_zmod_five : orderOf ((2 : ℕ) : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem factorization_card_aut {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] {n : ℕ} (hn : Module.finrank (ZMod 2) W = n) :
    (Nat.card (W ≃ₗ[ZMod 2] W)).factorization 5 = (n / 4) + padicValNat 5 (n / 4).factorial := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let b : Module.Basis (Fin n) (ZMod 2) W := Module.finBasisOfFinrankEq (ZMod 2) W hn
  let e : GL (Fin n) (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  rw [← Nat.card_congr e.toEquiv]
  have h := CFSG.GroupTheory.WeirSylow.factorization_card_GL (p := 5) (by decide) (ZMod 2)
    (by rw [ZMod.card]; decide) n
  rw [h, ZMod.card, orderOf_two_zmod_five]
  have h15 : padicValNat 5 (2 ^ 4 - 1) = 1 := by
    have : (2 : ℕ) ^ 4 - 1 = 5 * 3 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [h15, one_mul]

theorem factorization_card_aut_twenty {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (hn : Module.finrank (ZMod 2) W = 20) :
    (Nat.card (W ≃ₗ[ZMod 2] W)).factorization 5 = 6 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [factorization_card_aut hn]
  have h120 : padicValNat 5 (20 / 4).factorial = 1 := by
    have : (20 / 4).factorial = 5 * 24 := by decide
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [h120]

theorem commutative_of_finrank_lt {P W : Type} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (hP : IsPGroup 5 P) (σ : P →* (W ≃ₗ[ZMod 2] W))
    (hσ : Function.Injective σ) (hn : Module.finrank (ZMod 2) W < 20) (a b : P) :
    a * b = b * a := by
  classical
  set n := Module.finrank (ZMod 2) W with hn'
  let bas : Module.Basis (Fin n) (ZMod 2) W := Module.finBasisOfFinrankEq (ZMod 2) W rfl
  let e : GL (Fin n) (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
    (Matrix.GeneralLinearGroup.toLin' bas).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  let σ' : P →* GL (Fin n) (ZMod 2) := e.symm.toMonoidHom.comp σ
  have hσ' : Function.Injective σ' := e.symm.injective.comp hσ
  have hQ : IsPGroup 5 σ'.range := hP.of_surjective σ'.rangeRestrict
    (MonoidHom.rangeRestrict_surjective σ')
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have h5 : (5 : ℕ).Prime := Nat.prime_five
  have hlt : n / orderOf (Nat.card (ZMod 2) : ZMod 5) < 5 := by
    rw [Nat.card_zmod, orderOf_two_zmod_five]
    omega
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.heisFamA_sylow_GL (K := ZMod 2)
    (n := n) h5 (by norm_num) (by rw [Nat.card_zmod]; decide) hlt S
  have hcomm : ∀ x y : S, x * y = y * x := fun x y => φ.injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)
  apply hσ'
  rw [map_mul, map_mul]
  have := hcomm ⟨σ' a, hS ⟨a, rfl⟩⟩ ⟨σ' b, hS ⟨b, rfl⟩⟩
  exact congrArg Subtype.val this

instance : Finite (UU ≃ₗ[ZMod 2] UU) :=
  Finite.of_injective (fun f : UU ≃ₗ[ZMod 2] UU => (f : UU → UU)) DFunLike.coe_injective

theorem card_range_Trep : Nat.card (Trep.range) = 5 ^ 6 := by
  rw [Nat.card_congr (MonoidHom.ofInjective Trep_injective).toEquiv.symm, card_Wr]

theorem eq_of_le_sylow {S : Sylow 5 (UU ≃ₗ[ZMod 2] UU)} (hS : Trep.range ≤ (S : Subgroup _)) :
    Trep.range = (S : Subgroup (UU ≃ₗ[ZMod 2] UU)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine Subgroup.eq_of_le_of_card_ge hS ?_
  rw [Sylow.card_eq_multiplicity, factorization_card_aut_twenty finrank_UU, card_range_Trep]

theorem exists_model_embedding {P W : Type} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (hP : IsPGroup 5 P) (σ : P →* (W ≃ₗ[ZMod 2] W))
    (hσ : Function.Injective σ) (hn : Module.finrank (ZMod 2) W = 20) :
    ∃ (τ : W ≃ₗ[ZMod 2] UU) (ψ : P →* Wr), Function.Injective ψ ∧
      ∀ (p : P) (v : W), τ (σ p v) = T (ψ p) (τ v) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let e₀ : W ≃ₗ[ZMod 2] UU := LinearEquiv.ofFinrankEq W UU (by rw [hn, finrank_UU])
  let σ' : P →* (UU ≃ₗ[ZMod 2] UU) := (conjEquiv e₀).toMonoidHom.comp σ
  have hσ' : Function.Injective σ' := (conjEquiv e₀).injective.comp hσ
  have hQ : IsPGroup 5 σ'.range := hP.of_surjective σ'.rangeRestrict
    (MonoidHom.rangeRestrict_surjective σ')
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have hRp : IsPGroup 5 Trep.range := IsPGroup.of_card card_range_Trep
  obtain ⟨S₀, hS₀⟩ := hRp.exists_le_sylow
  have hRS₀ : Trep.range = (S₀ : Subgroup (UU ≃ₗ[ZMod 2] UU)) := eq_of_le_sylow hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (UU ≃ₗ[ZMod 2] UU) S₀ S
  have hconj : ∀ f ∈ σ'.range, g⁻¹ * f * g ∈ Trep.range := by
    intro f hf
    have hfS : f ∈ (S : Subgroup (UU ≃ₗ[ZMod 2] UU)) := hS hf
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hfS
    rw [hRS₀]
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hfS
  let σ'' : P →* (UU ≃ₗ[ZMod 2] UU) := (MulAut.conj g⁻¹).toMonoidHom.comp σ'
  have hσ'' : ∀ p, σ'' p = g⁻¹ * σ' p * g := by
    intro p
    simp [σ'', MulAut.conj_apply]
  have hmem : ∀ p, σ'' p ∈ Trep.range := fun p => by
    rw [hσ'']
    exact hconj _ ⟨p, rfl⟩
  let ψ : P →* Wr := (MonoidHom.ofInjective Trep_injective).symm.toMonoidHom.comp
    (σ''.codRestrict Trep.range hmem)
  have hψ : ∀ p, Trep (ψ p) = σ'' p := by
    intro p
    have := (MonoidHom.ofInjective Trep_injective).apply_symm_apply
      (σ''.codRestrict Trep.range hmem p)
    exact congrArg Subtype.val this
  refine ⟨e₀.trans g.symm, ψ, ?_, ?_⟩
  · intro p q hpq
    have h1 : Trep (ψ p) = Trep (ψ q) := congrArg Trep hpq
    rw [hψ, hψ, hσ'', hσ''] at h1
    have h2 : σ' p = σ' q := by simpa using h1
    exact hσ' h2
  · intro p v
    have h1 := LinearEquiv.congr_fun (hψ p) (g.symm (e₀ v))
    have h2 : T (ψ p) (g.symm (e₀ v)) = σ'' p (g.symm (e₀ v)) := h1
    change g.symm (e₀ (σ p v)) = T (ψ p) (g.symm (e₀ v))
    rw [h2, hσ'']
    change _ = (g⁻¹ * σ' p * g) (g.symm (e₀ v))
    simp [LinearEquiv.mul_apply, σ', conjEquiv_apply]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
