module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CentralExt
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

section Core

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] {τ : Tag} {K : Type} [Group K]

theorem excAut_core (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (x : (Fin τ.rank → ℤ) → F → K) (π : K →* ↥(adjointGroup τ F))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center K)
    (hC : ¬ p ∣ Nat.card π.ker)
    (hlift : ∀ ψ : K →* ↥(adjointGroup τ F), ∃! α : K →* K, π.comp α = ψ)
    (hgen : Subgroup.closure {y : K | ∃ n : ℕ, orderOf y = p ^ n} = ⊤)
    (hxp : ∀ i c, (∃ n : ℕ, orderOf (x (Pi.single i 1) c) = p ^ n) ∧
      ∃ n : ℕ, orderOf (x (-Pi.single i 1) c) = p ^ n)
    (hπx : ∀ i c, π (x (Pi.single i 1) c) = adjX τ F i c)
    (hπy : ∀ i c, π (x (-Pi.single i 1) c) = adjY τ F i c)
    {X : Type} [Group X] (θ : K →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X) :
    ∃ (α : K ≃* K) (g : K) (a : Fin τ.rank → Fˣ) (φ : F ≃+* F) (ε : Fin (exactE τ)),
      (∀ y, θ (α y) = σ (θ y)) ∧ ∀ i c,
        α (x (Pi.single i 1) c) = g * x (Pi.single (exactPerm τ ε i) 1)
          ((a (exactPerm τ ε i) : F) * φ c) * g⁻¹ ∧
        α (x (-Pi.single i 1) c) = g * x (-Pi.single (exactPerm τ ε i) 1)
          ((((a (exactPerm τ ε i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹ := by
  have hZC : Subgroup.center (adjointGroup τ F) = ⊥ := center_adjointGroup_eq_bot
  have hkerπ : θ.ker ≤ π.ker := hker.trans (center_le_ker_of_surjective hπ hZC)
  obtain ⟨α, σ', hαθ, hαπ⟩ := exists_mulEquiv_lift_of_centralQuotient θ hθ π hπ hcen hC hlift hZC
    hkerπ hgen σ
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form τ hτ F
  obtain ⟨g₀, a, φ, ε, hform⟩ := hnf σ'
  have hσ' : σ' = MulAut.conj g₀ * exactNormalAut τ F a φ ε := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hform h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  obtain ⟨g, rfl⟩ := hπ g₀
  refine ⟨α, g, a, φ, ε, hαθ, fun i c => ⟨?_, ?_⟩⟩
  · refine eq_of_pElement (π := π) hcen hC ?_ ?_ ?_
    · rw [hαπ, hπx, hσ', MulAut.mul_apply, MulAut.conj_apply, exactNormalAut_adjX,
        map_mul, map_mul, hπx, map_inv]
    · exact exists_orderOf_map_eq_pow α.toMonoidHom (hxp i c).1
    · have := exists_orderOf_map_eq_pow (MulAut.conj g).toMonoidHom
        (hxp (exactPerm τ ε i) ((a (exactPerm τ ε i) : F) * φ c)).1
      simpa using this
  · refine eq_of_pElement (π := π) hcen hC ?_ ?_ ?_
    · rw [hαπ, hπy, hσ', MulAut.mul_apply, MulAut.conj_apply, exactNormalAut_adjY,
        map_mul, map_mul, hπy, map_inv]
    · exact exists_orderOf_map_eq_pow α.toMonoidHom (hxp i c).2
    · have := exists_orderOf_map_eq_pow (MulAut.conj g).toMonoidHom
        (hxp (exactPerm τ ε i) ((((a (exactPerm τ ε i))⁻¹ : Fˣ) : F) * φ c)).2
      simpa using this

end Core

section Groups

variable {F : Type} [Field F] [Finite F]

theorem excAut_E6 {p : ℕ} [Fact p.Prime] [CharP F p] {X : Type} [Group X]
    (θ : ↥(e6Data_valid.minGroup F) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F)) (σ : X ≃* X) :
    ∃ (α : ↥(e6Data_valid.minGroup F) ≃* ↥(e6Data_valid.minGroup F))
      (g : ↥(e6Data_valid.minGroup F)) (a : Fin Tag.E6.rank → Fˣ) (φ : F ≃+* F)
      (ε : Fin (exactE Tag.E6)),
      (∀ y, θ (α y) = σ (θ y)) ∧ ∀ i c,
        α (e6Data_valid.xm F (Pi.single i 1) c) = g * e6Data_valid.xm F
          (Pi.single (exactPerm Tag.E6 ε i) 1) ((a (exactPerm Tag.E6 ε i) : F) * φ c) * g⁻¹ ∧
        α (e6Data_valid.xm F (-Pi.single i 1) c) = g * e6Data_valid.xm F
          (-Pi.single (exactPerm Tag.E6 ε i) 1)
          ((((a (exactPerm Tag.E6 ε i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹ := by
  have := finite_minGroup e6Data_valid F
  have hpar := e6Datum_isParametrization F
    (RootSystem.ofCartan (e6Datum F).isFiniteType (e6Datum F).divisible)
    (roots_eq isFiniteType_cartan_E6)
  refine excAut_core (p := p) (Or.inl rfl) (e6Data_valid.xm F) (e6Isogeny F)
    (e6Isogeny_surjective F) (e6Isogeny_ker_le_center F) (e6Isogeny_not_dvd_card_ker F)
    (fun ψ => (e6_hasCentralPSplit (p := p) F).existsUnique_lift (e6Isogeny_surjective F)
      (e6Isogeny_ker_le_center F) (e6Isogeny_not_dvd_card_ker F) ψ)
    (closure_of_isParametrization hpar (e6Datum_isCTGroupDatum F).iSup_eq_top)
    (fun i c => simple_orderOf_of_isParametrization hpar i c)
    (fun i c => ?_) (fun i c => ?_) θ hθ hker σ
  · rw [e6Isogeny_xm_single, eltElement_simpleRoot]
    rfl
  · rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
    rfl

theorem excAut_E7 {p : ℕ} [Fact p.Prime] [CharP F p] {X : Type} [Group X]
    (θ : ↥(e7Data_valid.minGroup F) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup F)) (σ : X ≃* X) :
    ∃ (α : ↥(e7Data_valid.minGroup F) ≃* ↥(e7Data_valid.minGroup F))
      (g : ↥(e7Data_valid.minGroup F)) (a : Fin Tag.E7.rank → Fˣ) (φ : F ≃+* F)
      (ε : Fin (exactE Tag.E7)),
      (∀ y, θ (α y) = σ (θ y)) ∧ ∀ i c,
        α (e7Data_valid.xm F (Pi.single i 1) c) = g * e7Data_valid.xm F
          (Pi.single (exactPerm Tag.E7 ε i) 1) ((a (exactPerm Tag.E7 ε i) : F) * φ c) * g⁻¹ ∧
        α (e7Data_valid.xm F (-Pi.single i 1) c) = g * e7Data_valid.xm F
          (-Pi.single (exactPerm Tag.E7 ε i) 1)
          ((((a (exactPerm Tag.E7 ε i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹ := by
  have := finite_minGroup e7Data_valid F
  have hpar := e7Datum_isParametrization F
    (RootSystem.ofCartan (e7Datum F).isFiniteType (e7Datum F).divisible)
    (roots_eq isFiniteType_cartan_E7)
  refine excAut_core (p := p) (Or.inr (Or.inl rfl)) (e7Data_valid.xm F) (e7Isogeny F)
    (e7Isogeny_surjective F) (e7Isogeny_ker_le_center F) (e7Isogeny_not_dvd_card_ker F)
    (fun ψ => (e7_hasCentralPSplit (p := p) F).existsUnique_lift (e7Isogeny_surjective F)
      (e7Isogeny_ker_le_center F) (e7Isogeny_not_dvd_card_ker F) ψ)
    (closure_of_isParametrization hpar (e7Datum_isCTGroupDatum F).iSup_eq_top)
    (fun i c => simple_orderOf_of_isParametrization hpar i c)
    (fun i c => ?_) (fun i c => ?_) θ hθ hker σ
  · rw [e7Isogeny_xm_single, eltElement_simpleRoot]
    rfl
  · rw [e7Isogeny_xm_neg_single]
    exact Subtype.ext ((rootOperatorFamily .E7).eltUnit_neg_simple i c)

theorem excAut_E8 {p : ℕ} [Fact p.Prime] [CharP F p] {X : Type} [Group X]
    (θ : ↥(adjointGroup Tag.E8 F) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center ↥(adjointGroup Tag.E8 F)) (σ : X ≃* X) :
    ∃ (α : ↥(adjointGroup Tag.E8 F) ≃* ↥(adjointGroup Tag.E8 F))
      (g : ↥(adjointGroup Tag.E8 F)) (a : Fin Tag.E8.rank → Fˣ) (φ : F ≃+* F)
      (ε : Fin (exactE Tag.E8)),
      (∀ y, θ (α y) = σ (θ y)) ∧ ∀ i c,
        α (Adjoint.e8Par F (Pi.single i 1) c) = g * Adjoint.e8Par F
          (Pi.single (exactPerm Tag.E8 ε i) 1) ((a (exactPerm Tag.E8 ε i) : F) * φ c) * g⁻¹ ∧
        α (Adjoint.e8Par F (-Pi.single i 1) c) = g * Adjoint.e8Par F
          (-Pi.single (exactPerm Tag.E8 ε i) 1)
          ((((a (exactPerm Tag.E8 ε i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹ := by
  have hpar := Adjoint.e8_isParametrization F
  refine excAut_core (p := p) (Or.inr (Or.inr rfl)) (Adjoint.e8Par F) (MonoidHom.id _)
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le)
    (by rw [MonoidHom.ker_id, Subgroup.card_bot]; exact (Fact.out : p.Prime).not_dvd_one)
    (fun ψ => ⟨ψ, by simp, fun α' h => by simpa using h⟩)
    (closure_of_isParametrization hpar (Adjoint.e8_isCTGroupDatum F).iSup_eq_top)
    (fun i c => simple_orderOf_of_isParametrization hpar i c)
    (fun i c => ?_) (fun i c => ?_) θ hθ hker σ
  · exact (Adjoint.xPar_simple (F := rootOperatorFamily .E8) i c).trans
      (eltElement_simpleRoot i c)
  · exact (Adjoint.xPar_neg_simple (F := rootOperatorFamily .E8) i c).trans
      (Subtype.ext ((rootOperatorFamily .E8).eltUnit_neg_simple i c))

theorem excAut_F4 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {X : Type} [Group X]
    (θ : ↥(adjointGroup Tag.F4 F) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center ↥(adjointGroup Tag.F4 F)) (σ : X ≃* X) :
    ∃ (α : ↥(adjointGroup Tag.F4 F) ≃* ↥(adjointGroup Tag.F4 F))
      (g : ↥(adjointGroup Tag.F4 F)) (φ : F ≃+* F),
      (∀ y, θ (α y) = σ (θ y)) ∧ ∀ i c,
        α (Adjoint.f4Par F (Pi.single i 1) c) = g * Adjoint.f4Par F (Pi.single i 1) (φ c) * g⁻¹ ∧
        α (Adjoint.f4Par F (-Pi.single i 1) c) =
          g * Adjoint.f4Par F (-Pi.single i 1) (φ c) * g⁻¹ := by
  have hpar := Adjoint.f4_isParametrization F
  have hZC : Subgroup.center (adjointGroup Tag.F4 F) = ⊥ := center_adjointGroup_eq_bot
  have hkerπ : θ.ker ≤ (MonoidHom.id ↥(adjointGroup Tag.F4 F)).ker := by
    rw [MonoidHom.ker_id]
    exact hker.trans hZC.le
  obtain ⟨α, σ', hαθ, hαπ⟩ := exists_mulEquiv_lift_of_centralQuotient (p := p) θ hθ
    (MonoidHom.id _) Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le)
    (by rw [MonoidHom.ker_id, Subgroup.card_bot]; exact (Fact.out : p.Prime).not_dvd_one)
    (fun ψ => ⟨ψ, by simp, fun α' h => by simpa using h⟩) hZC hkerπ
    (closure_of_isParametrization hpar (Adjoint.f4_isCTGroupDatum F).iSup_eq_top) σ
  have := Fintype.ofFinite F
  obtain ⟨n, -, hcard⟩ := FiniteField.card F p
  have hF : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨⟨g, φ⟩, hform, -⟩ := (odd_F4_and_nonexceptional_G2_automorphism_normal_form
    (Fact.out : p.Prime) hp2 n.pos F hF Tag.F4 (Or.inl rfl)).1 σ'
  have hX : ∀ (i : Fin Tag.F4.rank) (c : F),
      Adjoint.f4Par F (Pi.single i 1) c = adjX Tag.F4 F i c := fun i c =>
    (Adjoint.xPar_simple (F := rootOperatorFamily .F4) i c).trans (eltElement_simpleRoot i c)
  have hY : ∀ (i : Fin Tag.F4.rank) (c : F),
      Adjoint.f4Par F (-Pi.single i 1) c = adjY Tag.F4 F i c := fun i c =>
    (Adjoint.xPar_neg_simple (F := rootOperatorFamily .F4) i c).trans
      (Subtype.ext ((rootOperatorFamily .F4).eltUnit_neg_simple i c))
  have hα : ∀ y, α y = σ' y := fun y => hαπ y
  refine ⟨α, g, φ, hαθ, fun i c => ⟨?_, ?_⟩⟩
  · rw [hα, hX, hX]
    refine Subtype.ext ?_
    rw [hform, Subgroup.coe_mul, Subgroup.coe_mul]
    exact congrArg (fun u => (g : ModGL Tag.F4 F) * u * (g : ModGL Tag.F4 F)⁻¹)
      (units_map_entrywiseHom_xUnit φ.toRingHom i c)
  · rw [hα, hY, hY]
    refine Subtype.ext ?_
    rw [hform, Subgroup.coe_mul, Subgroup.coe_mul]
    exact congrArg (fun u => (g : ModGL Tag.F4 F) * u * (g : ModGL Tag.F4 F)⁻¹)
      (units_map_entrywiseHom_yUnit φ.toRingHom i c)

end Groups

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
