module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

@[expose] def innAut (K : Type) [Group K] : Subgroup (MulAut K) :=
  (MulAut.conj : K →* MulAut K).range

theorem innAut_normal (K : Type) [Group K] : (innAut K).Normal := by
  constructor
  rintro _ ⟨k, rfl⟩ g
  refine ⟨g k, ?_⟩
  ext y
  simp [MulAut.conj_apply]

@[expose] def KInEightT (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin 5)) ∨ Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (K ≃* alternatingGroup (Fin 7)) ∨ Nonempty (K ≃* alternatingGroup (Fin 8)) ∨
  Nonempty (K ≃* PSL(2, ZMod 7)) ∨ StatedClassicalModel K .PSL 2 17 1 ∨
  StatedClassicalModel K .PSL 3 3 1 ∨
  Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)

structure K32Datum (K : Type) [Group K] [Finite K] (X P R A V : Subgroup (MulAut K)) : Prop where
  inn_le : innAut K ≤ X
  sylow : IsSylowTwoOf P X
  a4 : IsA4Block A V
  A_le : A ≤ X
  V_le : V ≤ R
  R_le : R ≤ P
  R_norm : R ≤ Subgroup.normalizer (A : Set (MulAut K))
  R_normV : R ≤ Subgroup.normalizer (V : Set (MulAut K))
  idx : R.relIndex P ≤ 2
  moves : ¬ R ≤ Subgroup.centralizer (V : Set (MulAut K))

inductive K32ListedType (K : Type) [Group K] : Prop
  | bender : fusionIsBenderGroup K → K32ListedType K
  | psl3 (n : ℕ) : 1 ≤ n → StatedClassicalModel K .PSL 3 2 n → K32ListedType K
  | psp4 (n : ℕ) : 2 ≤ n → StatedClassicalModel K .PSp 2 2 n → K32ListedType K
  | alt6 : Nonempty (K ≃* alternatingGroup (Fin 6)) → K32ListedType K
  | psl3four : StatedClassicalModel (K ⧸ CFSG.pCore 2 K) .PSL 3 2 2 → K32ListedType K
  | alt7 : Nonempty (K ≃* alternatingGroup (Fin 7)) → K32ListedType K
  | psl33 : StatedClassicalModel K .PSL 3 3 1 → K32ListedType K
  | m11 : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) → K32ListedType K
  | psl2p (p : ℕ) : Ch1.IsFermatOrMersennePrime p → StatedClassicalModel K .PSL 2 p 1 →
      K32ListedType K
  | m22 : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) → K32ListedType K
  | m22cover :
      Nonempty ((K ⧸ CFSG.pCore 2 K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) →
        K32ListedType K
  | m23 : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) → K32ListedType K
  | psl42 : StatedClassicalModel K .PSL 4 2 1 → K32ListedType K

@[expose] def K32AutExcl : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → K32ListedType K → ¬ KInEightT K →
    ∀ X P R A V : Subgroup (MulAut K), K32Datum K X P R A V → False

@[expose] def K32AltOut : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7))) →
    ∀ A V : Subgroup (MulAut K), IsA4Block A V → V ⊓ innAut K ≠ ⊥

section Counting

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem false_of_centralizer_index_le_two {J A V P W : Subgroup Γ} (hA : IsA4Block A V)
    (hVJ : V ≤ J) (hP : IsSylowTwoOf P J) (hWP : W ≤ P)
    (hWC : W ≤ Subgroup.centralizer (A : Set Γ)) (hidx : W.relIndex P ≤ 2) : False := by
  obtain ⟨c, hcA, hc3, hcN, hcfp, hAc⟩ := hA.exists_c
  have hW2 : IsPGroup 2 W := hP.2.1.to_le hWP
  have hvw : ∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ = w := by
    intro v hv w hw
    have h1 : v * w = w * v := Subgroup.mem_centralizer_iff.mp (hWC hw) v (hA.le hv)
    calc v * w * v⁻¹ = w * v * v⁻¹ := by rw [h1]
      _ = w := by group
  have hVW : V ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    by_contra hv1
    have hcv : c * v = v * c := (Subgroup.mem_centralizer_iff.mp (hWC hv.2) c hcA)
    exact hcfp v hv.1 hv1 (by
      calc c * v * c⁻¹ = v * c * c⁻¹ := by rw [hcv]
        _ = v := by group)
  have hVN : V ≤ Subgroup.normalizer (W : Set Γ) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [hvw v hv w hw]
      exact hw
    · intro hw
      have h1 := hvw v⁻¹ (inv_mem hv) _ hw
      have e : v⁻¹ * (v * w * v⁻¹) * v⁻¹⁻¹ = w := by group
      rw [e] at h1
      exact h1.symm ▸ hw
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hVN
  rw [hVW, Subgroup.card_bot, hA.card_U] at hmul
  have hVWle : V ⊔ W ≤ J := sup_le hVJ (hWP.trans hP.1)
  obtain ⟨k, hk⟩ := hW2.exists_card_eq
  have hVW2 : IsPGroup 2 ↥(V ⊔ W) := by
    refine IsPGroup.of_card (n := k + 2) ?_
    rw [pow_add, ← hk]
    omega
  have hle := card_le_twoPart hVWle hVW2
  rw [← hP.card_eq] at hle
  have hPcard := C5.card_eq_card_mul_relIndex hWP
  have hpos : 0 < Nat.card W := Nat.card_pos
  have h2 : Nat.card ↥P ≤ Nat.card W * 2 := by
    rw [hPcard]; exact Nat.mul_le_mul_left _ hidx
  omega

end Counting

end CFSG.QuasithinUnique.DoubleA3
