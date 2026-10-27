module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.SectionRank.OddCover Matrix

@[expose] def NineData (G : Type*) [Group G] : Prop :=
  ∃ T P Q : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ P ≤ Subgroup.normalizer (T : Set G) ∧
    Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
    Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) ∧ P ≤ Q

theorem NineData.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : NineData G') : NineData G := by
  obtain ⟨T, P, Q, hT, hT2, hPT, ⟨eP⟩, ⟨eQ⟩, hPQ⟩ := h
  refine ⟨T.map e.symm.toMonoidHom, P.map e.symm.toMonoidHom, Q.map e.symm.toMonoidHom, ?_, ?_, ?_,
    ⟨(P.equivMapOfInjective _ e.symm.injective).symm.trans eP⟩,
    ⟨(Q.equivMapOfInjective _ e.symm.injective).symm.trans eQ⟩, Subgroup.map_mono hPQ⟩
  · intro h0
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T (f := e.symm.toMonoidHom) e.symm.injective).1 h0)
  · exact hT2.of_equiv (T.equivMapOfInjective _ e.symm.injective)
  · rintro _ ⟨x0, hx0, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.coe_toMonoidHom, map_mul,
      map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.1 (hPT hx0) _

section Linear

variable {K : Type} [Field K]

@[expose] def tMat (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_tMat : ((tMat K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, 1, 0; 1, 0, 0; 0, 0, -1] := rfl

theorem tMat_mul_self : tMat K * tMat K = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_tMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem tMat_ne_one : tMat K ≠ 1 := by
  intro h
  have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp [coe_tMat] at this

theorem diag_mul_tMat (a c : Kˣ) :
    diagHom 3 ![a, a, c] * tMat K = tMat K * diagHom 3 ![a, a, c] := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_tMat, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

@[expose] def thetaPi (C : Subgroup Kˣ) : ↥C × ↥C →* (Fin 3 → Kˣ) where
  toFun x := ![x.1.1, x.2.1, (x.1.1 * x.2.1)⁻¹]
  map_one' := by
    funext i; fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change ((x.1.1 * y.1.1) * (x.2.1 * y.2.1))⁻¹ = (x.1.1 * x.2.1)⁻¹ * (y.1.1 * y.2.1)⁻¹
      rw [mul_mul_mul_comm, mul_inv]

theorem thetaPi_injective (C : Subgroup Kˣ) : Function.Injective (thetaPi C) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [thetaPi, MonoidHom.coe_mk, OneHom.coe_mk] at h0 h1
  exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)

@[expose] noncomputable def theta (C : Subgroup Kˣ) : ↥C × ↥C →* GL (Fin 3) K :=
  (diagHom 3).comp (thetaPi C)

theorem theta_injective (C : Subgroup Kˣ) : Function.Injective (theta (K := K) C) :=
  (diagHom_injective 3).comp (thetaPi_injective C)

theorem theta_apply (C : Subgroup Kˣ) (a b : ↥C) :
    theta (K := K) C (a, b) = diagHom 3 ![a.1, b.1, (a.1 * b.1)⁻¹] := rfl

theorem nineData_of_mem {S : Subgroup (GL (Fin 3) K)} {ω : Kˣ} (hω : orderOf ω = 9)
    (hθ : ∀ a b : Kˣ, a ∈ Subgroup.zpowers ω → b ∈ Subgroup.zpowers ω →
      diagHom 3 ![a, b, (a * b)⁻¹] ∈ S) (ht : tMat K ∈ S) : NineData ↥S := by
  set C := Subgroup.zpowers ω with hC
  have hCcard : Nat.card C = 9 := by rw [hC, Nat.card_zpowers, hω]
  haveI : IsCyclic C := inferInstance
  have hcardZ : Nat.card (Multiplicative (ZMod 9)) = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let eC : C ≃* Multiplicative (ZMod 9) := mulEquivOfCyclicCardEq (hCcard.trans hcardZ.symm)
  have hmem : ∀ x : ↥C × ↥C, theta (K := K) C x ∈ S := fun x => hθ _ _ x.1.2 x.2.2
  let θ' : ↥C × ↥C →* ↥S := (theta (K := K) C).codRestrict S hmem
  have hθ'inj : Function.Injective θ' := fun x y h =>
    theta_injective C (congrArg Subtype.val h)
  let δ : ↥C →* ↥C × ↥C := (MonoidHom.id ↥C).prod (MonoidHom.id ↥C)
  have hδinj : Function.Injective δ := fun x y h => congrArg Prod.fst h
  let t' : ↥S := ⟨tMat K, ht⟩
  have ht'2 : t' ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact tMat_mul_self)
  have ht'1 : t' ≠ 1 := fun h => tMat_ne_one (congrArg Subtype.val h)
  have hord : orderOf t' = 2 := orderOf_eq_prime ht'2 ht'1
  refine ⟨Subgroup.zpowers t', (θ'.comp δ).range, θ'.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply ht'1
    have : t' ∈ Subgroup.zpowers t' := Subgroup.mem_zpowers t'
    rw [h0] at this
    exact Subgroup.mem_bot.1 this
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  · rintro _ ⟨a, rfl⟩
    refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers t' : Subgroup ↥S) : Set ↥S) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hc : (θ'.comp δ) a * t' = t' * (θ'.comp δ) a := by
      apply Subtype.ext
      change theta (K := K) C (δ a) * tMat K = tMat K * theta (K := K) C (δ a)
      rw [show δ a = (a, a) from rfl, theta_apply]
      have := diag_mul_tMat (K := K) a.1 (a.1 * a.1)⁻¹
      convert this using 3
    exact (Commute.zpow_left (show Commute t' ((θ'.comp δ) a) from hc.symm) k).eq
  · exact ⟨((MonoidHom.ofInjective (f := θ'.comp δ) (fun x y h => hδinj (hθ'inj h))).symm.trans eC)⟩
  · exact ⟨((MonoidHom.ofInjective hθ'inj).symm.trans
      ((eC.prodCongr eC).trans (MulEquiv.prodMultiplicative (G := ZMod 9) (H := ZMod 9)).symm))⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨δ a, rfl⟩

end Linear

end CFSG.HardMathSupport.Solomon.Coordinator
