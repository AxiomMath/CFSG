module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAut

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

@[expose] def K32NoDatum (K : Type) [Group K] [Finite K] : Prop :=
  ∀ X P R A V : Subgroup (MulAut K), K32Datum K X P R A V → False

@[expose] def K32ExclBender : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → fusionIsBenderGroup K →
    ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclPSL3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → ∀ n : ℕ, 1 ≤ n →
    StatedClassicalModel K .PSL 3 2 n → ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclPSp4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → ∀ n : ℕ, 2 ≤ n →
    StatedClassicalModel K .PSp 2 2 n → ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclPSL3Cover : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    StatedClassicalModel (K ⧸ CFSG.pCore 2 K) .PSL 3 2 2 → ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclPSL2p : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → ∀ p : ℕ,
    Ch1.IsFermatOrMersennePrime p → p ≠ 17 → StatedClassicalModel K .PSL 2 p 1 →
      ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclM22 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) → ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclM22Cover : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    Nonempty ((K ⧸ CFSG.pCore 2 K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) →
      ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclM23 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) → ¬ KInEightT K → K32NoDatum K

@[expose] def K32ExclPSL42 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    StatedClassicalModel K .PSL 4 2 1 → ¬ KInEightT K → K32NoDatum K

theorem k32AutExcl_of_families (h1 : K32ExclBender) (h2 : K32ExclPSL3) (h3 : K32ExclPSp4)
    (h4 : K32ExclPSL3Cover) (h5 : K32ExclPSL2p) (h6 : K32ExclM22) (h7 : K32ExclM22Cover)
    (h8 : K32ExclM23) (h9 : K32ExclPSL42) : K32AutExcl := by
  intro K _ _ hq hty hK X P R A V hd
  cases hty with
  | bender h => exact h1 K hq h hK X P R A V hd
  | psl3 n hn h => exact h2 K hq n hn h hK X P R A V hd
  | psp4 n hn h => exact h3 K hq n hn h hK X P R A V hd
  | alt6 h => exact hK (Or.inr (Or.inl h))
  | psl3four h => exact h4 K hq h hK X P R A V hd
  | alt7 h => exact hK (Or.inr (Or.inr (Or.inl h)))
  | psl33 h => exact hK (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  | m11 h => exact hK (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  | psl2p p hp h =>
    by_cases hp17 : p = 17
    · subst hp17
      exact hK (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact h5 K hq p hp hp17 h hK X P R A V hd
  | m22 h => exact h6 K hq h hK X P R A V hd
  | m22cover h => exact h7 K hq h hK X P R A V hd
  | m23 h => exact h8 K hq h hK X P R A V hd
  | psl42 h => exact h9 K hq h hK X P R A V hd

end CFSG.QuasithinUnique.DoubleA3
