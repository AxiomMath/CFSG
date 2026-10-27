module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TNineCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.SectionRank.OddCover Matrix

section Std

variable {F : Type} [Field F]

@[expose] def NineFix (S : Subgroup (GL (Fin 3) F)) (Ψ : GL (Fin 3) F →* GL (Fin 3) F) : Prop :=
  ∃ T P Q : Subgroup (GL (Fin 3) F), T ≤ S ∧ Q ≤ S ∧ P ≤ Q ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
    P ≤ Subgroup.normalizer (T : Set (GL (Fin 3) F)) ∧
    Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
    Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) ∧
    T.map Ψ = T ∧ ∃ k : ℕ, ∀ x ∈ Q, Ψ x = x ^ k

theorem map_tMat (σ : F →+* F) : GeneralLinearGroup.map σ (tMat F) = tMat F := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_tMat]

theorem map_diagHom (σ : F →+* F) (v : Fin 3 → Fˣ) :
    GeneralLinearGroup.map σ (diagHom 3 v) = diagHom 3 (fun i => Units.map σ.toMonoidHom (v i)) := by
  apply Units.ext
  ext i j
  simp only [coe_diagHom, GeneralLinearGroup.map_apply, Matrix.diagonal_apply]
  by_cases hij : i = j <;> simp [hij]

theorem exists_map_eq_pow {ω : Fˣ} [Finite F] (hω : orderOf ω = 9) (σ : F ≃+* F) :
    ∃ k : ℕ, Units.map (σ : F →+* F).toMonoidHom ω = ω ^ k := by
  have hord : orderOf (Units.map (σ : F →+* F).toMonoidHom ω) = 9 := by
    rw [← hω]
    exact orderOf_injective (Units.map (σ : F →+* F).toMonoidHom)
      (fun a b h => Units.ext (σ.injective (congrArg (fun u : Fˣ => (u : F)) h))) ω
  have hcard : ∀ x : Fˣ, orderOf x = 9 → Nat.card (Subgroup.zpowers x) = 9 := fun x hx => by
    rw [Nat.card_zpowers, hx]
  have hEq : Subgroup.zpowers (Units.map (σ : F →+* F).toMonoidHom ω) = Subgroup.zpowers ω := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, hcard _ hord, hcard _ hω]
  have hmem : Units.map (σ : F →+* F).toMonoidHom ω ∈ Subgroup.zpowers ω := by
    rw [← hEq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := (IsOfFinOrder.mem_powers_iff_mem_zpowers (isOfFinOrder_of_finite ω)).2 hmem
  exact ⟨k, hk.symm⟩

theorem nineFix_of_mem [Finite F] {S : Subgroup (GL (Fin 3) F)} {ω : Fˣ} (hω : orderOf ω = 9)
    (hθ : ∀ a b : Fˣ, a ∈ Subgroup.zpowers ω → b ∈ Subgroup.zpowers ω →
      diagHom 3 ![a, b, (a * b)⁻¹] ∈ S) (ht : tMat F ∈ S) (σ : F ≃+* F) :
    NineFix S (GeneralLinearGroup.map (σ : F →+* F)) := by
  set C := Subgroup.zpowers ω with hC
  have hCcard : Nat.card C = 9 := by rw [hC, Nat.card_zpowers, hω]
  haveI : IsCyclic C := inferInstance
  have hcardZ : Nat.card (Multiplicative (ZMod 9)) = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let eC : C ≃* Multiplicative (ZMod 9) := mulEquivOfCyclicCardEq (hCcard.trans hcardZ.symm)
  let δ : ↥C →* ↥C × ↥C := (MonoidHom.id ↥C).prod (MonoidHom.id ↥C)
  have hδinj : Function.Injective δ := fun x y h => congrArg Prod.fst h
  have ht2 : tMat F ^ 2 = 1 := by rw [pow_two]; exact tMat_mul_self
  have hord : orderOf (tMat F) = 2 := orderOf_eq_prime ht2 tMat_ne_one
  obtain ⟨k, hk⟩ := exists_map_eq_pow hω σ
  refine ⟨Subgroup.zpowers (tMat F), ((theta (K := F) C).comp δ).range, (theta (K := F) C).range,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.zpowers_le).2 ht
  · rintro _ ⟨x, rfl⟩
    exact hθ _ _ x.1.2 x.2.2
  · rintro _ ⟨a, rfl⟩
    exact ⟨δ a, rfl⟩
  · intro h0
    apply tMat_ne_one (K := F)
    have : tMat F ∈ Subgroup.zpowers (tMat F) := Subgroup.mem_zpowers _
    rw [h0] at this
    exact Subgroup.mem_bot.1 this
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  · rintro _ ⟨a, rfl⟩
    refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers (tMat F) : Subgroup (GL (Fin 3) F)) :
      Set (GL (Fin 3) F)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hc : ((theta (K := F) C).comp δ) a * tMat F = tMat F * ((theta (K := F) C).comp δ) a := by
      change theta (K := F) C (δ a) * tMat F = tMat F * theta (K := F) C (δ a)
      rw [show δ a = (a, a) from rfl, theta_apply]
      have := diag_mul_tMat (K := F) a.1 (a.1 * a.1)⁻¹
      convert this using 3
    exact (Commute.zpow_left (show Commute (tMat F) (((theta (K := F) C).comp δ) a) from hc.symm) j).eq
  · exact ⟨((MonoidHom.ofInjective (f := (theta (K := F) C).comp δ)
      (fun x y h => hδinj ((theta_injective C) h))).symm.trans eC)⟩
  · exact ⟨((MonoidHom.ofInjective (theta_injective (K := F) C)).symm.trans
      ((eC.prodCongr eC).trans (MulEquiv.prodMultiplicative (G := ZMod 9) (H := ZMod 9)).symm))⟩
  · rw [MonoidHom.map_zpowers, map_tMat]
  · refine ⟨k, ?_⟩
    have hσa : ∀ a ∈ C, Units.map (σ : F →+* F).toMonoidHom a = a ^ k := by
      intro a ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [map_zpow, hk, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [theta_apply, map_diagHom, ← map_pow]
    congr 1
    funext i
    fin_cases i
    · exact hσa _ a.2
    · exact hσa _ b.2
    · change Units.map (σ : F →+* F).toMonoidHom (a.1 * b.1)⁻¹ = ((a.1 * b.1)⁻¹) ^ k
      rw [map_inv, map_mul, hσa _ a.2, hσa _ b.2, inv_pow, mul_pow]

end Std

end CFSG.HardMathSupport.Solomon.Coordinator
