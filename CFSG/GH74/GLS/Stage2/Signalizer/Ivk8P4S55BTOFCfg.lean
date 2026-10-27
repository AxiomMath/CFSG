module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenB
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

@[expose] def BTConfig (k : Kind) (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ (W I Q : Subgroup Y) (U : Subgroup (MulAut Y)), W ≠ ⊥ ∧ IsPGroup p ↥W ∧ ⁅I, I⁆ = I ∧
    I ≤ normalizer (W : Set Y) ∧ Q ≤ I ∧ IVK.IsFourSubgroup Q ∧ IVK.IsFourSubgroup U ∧
    (∀ u ∈ U, ∀ w ∈ W, u w ∈ W) ∧ (∀ u ∈ U, ∀ x ∈ I, u x = x) ∧
    ∀ u ∈ U, u ≠ 1 → AdmAut k u

namespace OFC

variable {A B : Type} [Group A] [Group B]

theorem congr_apply' (e : A ≃* B) (α : MulAut A) (x : B) :
    MulAut.congr e α x = e (α (e.symm x)) := by
  simp [MulAut.congr_apply]

@[expose] noncomputable def fixSubEquiv (e : A ≃* B) (α : MulAut A) :
    ↥(fixSub α) ≃* ↥(fixSub (MulAut.congr e α)) where
  toFun x := ⟨e x.1, by
    show MulAut.congr e α (e x.1) = e x.1
    rw [congr_apply', MulEquiv.symm_apply_apply, show α x.1 = x.1 from x.2]⟩
  invFun y := ⟨e.symm y.1, by
    have hy : MulAut.congr e α y.1 = y.1 := y.2
    rw [congr_apply'] at hy
    show α (e.symm y.1) = e.symm y.1
    apply e.injective
    rw [hy, MulEquiv.apply_symm_apply]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

theorem admAut_congr {k : Kind} (e : A ≃* B) {α : MulAut A} (h : AdmAut k α) :
    AdmAut k (MulAut.congr e α) := fun Z _ _ hns hsec =>
  h Z hns (IsSection.of_equiv (fixSubEquiv e α) hsec)

theorem isFourSubgroup_map {X : Subgroup A} (hX : IVK.IsFourSubgroup X) (f : A →* B)
    (hf : Function.Injective f) : IVK.IsFourSubgroup (X.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.1
  exact ⟨IsElementaryAbelian.map f, by rw [Subgroup.card_map_of_injective hf, hX.2]⟩

theorem perfect_map {X : Subgroup A} (hX : ⁅X, X⁆ = X) (f : A →* B) :
    ⁅X.map f, X.map f⁆ = X.map f := by
  rw [← Subgroup.map_commutator, hX]

theorem perfect_subgroupOf {X Y : Subgroup A} (hXY : X ≤ Y) (hX : ⁅X, X⁆ = X) :
    ⁅X.subgroupOf Y, X.subgroupOf Y⁆ = X.subgroupOf Y := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXY, hX]

theorem mul_conj_inv (φ : MulAut A) (w : A) :
    φ * MulAut.conj w * φ⁻¹ = MulAut.conj (φ w) := by
  ext v
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

end OFC

theorem BTConfig.of_mulEquiv {k : Kind} {p : ℕ} {Y Y' : Type} [Group Y] [Group Y']
    (e : Y ≃* Y') (h : BTConfig k p Y) : BTConfig k p Y' := by
  obtain ⟨W, I, Q, U, hW, hWp, hI, hIW, hQI, hQ, hU, hUW, hUI, hadm⟩ := h
  refine ⟨W.map e.toMonoidHom, I.map e.toMonoidHom, Q.map e.toMonoidHom,
    U.map (MulAut.congr e).toMonoidHom, ?_, hWp.map _, OFC.perfect_map hI _, ?_,
    Subgroup.map_mono hQI, OFC.isFourSubgroup_map hQ _ e.injective,
    OFC.isFourSubgroup_map hU _ (MulAut.congr e).injective, ?_, ?_, ?_⟩
  · intro h0
    exact hW ((Subgroup.map_eq_bot_iff_of_injective W e.injective).mp h0)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨x, hIW hx, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩
    refine ⟨u w, hUW u hu w hw, ?_⟩
    simp
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨x, hx, rfl⟩
    simp [hUI u hu x hx]
  · rintro _ ⟨u, hu, rfl⟩ hu1
    have hu1' : u ≠ 1 := fun h1 => hu1 (by rw [h1, map_one])
    exact OFC.admAut_congr e (hadm u hu hu1')

theorem false_of_innerPart_eq_bot {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} [K.Normal] {a : Γ} {P : Subgroup Γ}
    (hM : Mod55 p ρ K a P) (hOF : OuterFalseNS p (↥K ⧸ center ↥K))
    (hU : innerPart (K := K) P = ⊥) : False := by
  have hnotinn : actYHom (K := K) a ∉
      (MulAut.conj : (K ⧸ center ↥K) →* MulAut (K ⧸ center ↥K)).range := by
    rintro ⟨y, hy⟩
    have hyU : y ∈ innerPart (K := K) P := mem_innerPart.mpr ⟨a, hM.a_mem, hy.symm⟩
    rw [hU, Subgroup.mem_bot] at hyU
    apply hM.actYHom_ne_one
    rw [← hy, hyU, map_one]
  exact hOF _ hnotinn hM.actYHom_pow fun r hr hr2 hrp Q hQ hinv x hx =>
    hM.actYHom_eq_of_invariant hr hr2 hrp hQ hinv hx

theorem card_dvd_of_sl2_five {K : Type} [Group K] (h5 : HasSL2Model K (fun q => q = 5)) :
    Nat.card (K ⧸ center K) ∣ 120 := by
  obtain ⟨F, _, _, hF5, ⟨e⟩⟩ := h5
  have hK : Nat.card K = 120 := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF5]
    decide
  rw [← hK]
  exact Subgroup.card_quotient_dvd_card _

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
