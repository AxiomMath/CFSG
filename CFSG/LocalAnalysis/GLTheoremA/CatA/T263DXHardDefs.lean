module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Quot
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

@[expose] def ModelSelH (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  ∀ r : T, r ^ p = 1 → r ≠ 1 → ∀ A Q : Subgroup T, r ∈ A → (∀ a ∈ A, a ^ p = 1) →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Q ≤ Subgroup.centralizer ({r} : Set T) →
    IsPGroup 2 ↥Q → A ≤ Subgroup.normalizer (Q : Set T) → (⁅A, Q⁆ : Subgroup T) ≠ ⊥ →
    ∃ J : Subgroup T, IsComponentOf J (Subgroup.centralizer ({r} : Set T)) ∧
      p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅(⁅A, Q⁆ : Subgroup T), J⁆ ≠ ⊥ ∧
      (⁅A, Q⁆ : Subgroup T) ≤
        J ⊔ (Subgroup.centralizer ({r} : Set T) ⊓ Subgroup.centralizer (J : Set T))

@[expose] def ModelSelQ (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  ∀ r : T, r ^ p = 1 → r ≠ 1 → ∀ P : Subgroup T, P ≤ Subgroup.centralizer ({r} : Set T) →
    IsPGroup 2 ↥P → P ≠ ⊥ →
    ∃ J : Subgroup T, IsComponentOf J (Subgroup.centralizer ({r} : Set T)) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (Subgroup.centralizer ({r} : Set T) ⊓ Subgroup.centralizer (J : Set T))

@[expose] def CompTriv (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  ∀ r : T, r ^ p = 1 → r ≠ 1 → ∀ w ∈ Subgroup.centralizer ({r} : Set T), w ^ p = 1 →
    ∀ J : Subgroup T, IsComponentOf J (Subgroup.centralizer ({r} : Set T)) →
      ¬ p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) → w ∈ Subgroup.centralizer (J : Set T)

variable {p : ℕ}

section Transport

variable {X Y : Type} [Group X] [Group Y]

private theorem selH_nonempty_centerQuot_equiv (e : X ≃* Y) :
    Nonempty (X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

end Transport

theorem dvd_of_component_of_triv {T : Type} [Group T] [Finite T] (hT : CompTriv p T) {r : T}
    (hrp : r ^ p = 1) (hr1 : r ≠ 1) {A Q J : Subgroup T} (hrA : r ∈ A)
    (hAp : ∀ a ∈ A, a ^ p = 1) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hQC : Q ≤ Subgroup.centralizer ({r} : Set T))
    (hJc : IsComponentOf J (Subgroup.centralizer ({r} : Set T)))
    (hJa : ⁅(⁅A, Q⁆ : Subgroup T), J⁆ ≠ ⊥) : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  by_contra hndvd
  refine hJa ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
  intro a ha t ht
  have haC : a ∈ Subgroup.centralizer ({r} : Set T) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hAab a ha r hrA)
  have haJ : a ∈ Subgroup.centralizer (J : Set T) := hT r hrp hr1 a haC (hAp a ha) J hJc hndvd
  have htN : t⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer ({r} : Set T) : Set T) :=
    Subgroup.le_normalizer ((Subgroup.centralizer ({r} : Set T)).inv_mem (hQC ht))
  have hJ'c := isComponentOf_map_conj_of_mem_normalizer hJc htN
  have hndvd' : ¬ p ∣ Nat.card (↥(J.map (MulAut.conj t⁻¹).toMonoidHom) ⧸
      Subgroup.center ↥(J.map (MulAut.conj t⁻¹).toMonoidHom)) := by
    obtain ⟨ε⟩ := selH_nonempty_centerQuot_equiv
      (Subgroup.equivMapOfInjective J (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective)
    rw [← Nat.card_congr ε.toEquiv]
    exact hndvd
  have haJ' := hT r hrp hr1 a haC (hAp a ha) _ hJ'c hndvd'
  have htat : t * a * t⁻¹ ∈ Subgroup.centralizer (J : Set T) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hj' : t⁻¹ * j * t ∈ J.map (MulAut.conj t⁻¹).toMonoidHom :=
      ⟨j, hj, by simp [MulAut.conj_apply]⟩
    have h1 := Subgroup.mem_centralizer_iff.1 haJ' _ hj'
    calc j * (t * a * t⁻¹) = t * ((t⁻¹ * j * t) * a) * t⁻¹ := by group
      _ = t * (a * (t⁻¹ * j * t)) * t⁻¹ := by rw [h1]
      _ = (t * a * t⁻¹) * j := by group
  rw [commutatorElement_def, show a * t * a⁻¹ * t⁻¹ = a * (t * a * t⁻¹)⁻¹ by group]
  exact Subgroup.mul_mem _ haJ (Subgroup.inv_mem _ htat)

theorem modelSelH_of_triv {T : Type} [Group T] [Finite T] (hQ : ModelSelQ p T)
    (hT : CompTriv p T) : ModelSelH p T := by
  intro r hrp hr1 A Q hrA hAp hAab hQC hQ2 hAN hne
  have hPQ : (⁅A, Q⁆ : Subgroup T) ≤ Q := Subgroup.le_normalizer_iff_commutator_le_right.1 hAN
  obtain ⟨J, hJc, hJa, hJP⟩ := hQ r hrp hr1 _ (hPQ.trans hQC) (hQ2.to_le hPQ) hne
  exact ⟨J, hJc, dvd_of_component_of_triv hT hrp hr1 hrA hAp hAab hQC hJc hJa, hJa, hJP⟩

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
