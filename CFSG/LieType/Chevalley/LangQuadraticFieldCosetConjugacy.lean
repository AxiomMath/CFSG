module

public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
open CFSG.GroupTheory CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exceptional_Lang_quadratic_field_coset_conjugacy
    {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (K : Type) [Field K] (hK : Nat.card K = (p ^ e) ^ 2) (δ : K →+* K)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) :
    (∀ τ : Tag, ∃ β : MulAut (adjointGroup τ K),
      (∀ u, (β u : ModGL τ K) = Units.map (entrywiseHom δ) (u : ModGL τ K)) ∧
      ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        (∃ α : MulAut (adjointGroup τ K), ∀ u, (α u : ModGL τ K) =
          (g : ModGL τ K) * rootDiagUnit τ a * Units.map (entrywiseHom δ) (u : ModGL τ K) *
            (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) ∧
        ∀ α : MulAut (adjointGroup τ K), (∀ u, (α u : ModGL τ K) =
          (g : ModGL τ K) * rootDiagUnit τ a * Units.map (entrywiseHom δ) (u : ModGL τ K) *
            (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) →
          α * α = 1 → ∃ ψ : MulAut (adjointGroup τ K),
            (∀ u, ((ψ * α * ψ⁻¹) u : ModGL τ K) = Units.map (entrywiseHom δ) (u : ModGL τ K)) ∧
            (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
              β.toMonoidHom.eqLocus (MonoidHom.id _) ∧
            (∃ e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))) ≃*
                ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))),
              ∀ u, (e u : adjointGroup τ K) = ψ u) ∧
            (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
              Subgroup.centralizer {β} ∧
            ∃ e : ↥(Subgroup.centralizer {α}) ≃* ↥(Subgroup.centralizer {β}),
              ∀ γ, (e γ : MulAut (adjointGroup τ K)) = ψ * γ * ψ⁻¹) ∧
    (∃ β : MulAut (adjointGroup TwistTag.E6.tag K),
      (∀ u, (β u : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹) ∧
      ∀ (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ),
        (∃ α : MulAut (adjointGroup TwistTag.E6.tag K), ∀ u, (α u : ModGL TwistTag.E6.tag K) =
          (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
            diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹) ∧
        ∀ α : MulAut (adjointGroup TwistTag.E6.tag K), (∀ u, (α u : ModGL TwistTag.E6.tag K) =
          (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
            diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹) →
          α * α = 1 → ∃ ψ : MulAut (adjointGroup TwistTag.E6.tag K),
            (∀ u, ((ψ * α * ψ⁻¹) u : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
              Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
                (diagramMap TwistTag.E6 K)⁻¹) ∧
            (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
              β.toMonoidHom.eqLocus (MonoidHom.id _) ∧
            (∃ e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K))) ≃*
                ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K))),
              ∀ u, (e u : adjointGroup TwistTag.E6.tag K) = ψ u) ∧
            (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
              Subgroup.centralizer {β} ∧
            ∃ e : ↥(Subgroup.centralizer {α}) ≃* ↥(Subgroup.centralizer {β}),
              ∀ γ, (e γ : MulAut (adjointGroup TwistTag.E6.tag K)) = ψ * γ * ψ⁻¹) := by
  classical
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos e) 2).ne')
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK'
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    have h2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    nlinarith
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  set Fe := iterateFrobenius (AlgebraicClosure K) p e with hFedef
  have hFe : ∀ c, Fe c = c ^ p ^ e := fun c => by rw [hFedef, iterateFrobenius_def]
  have hFr : ∀ c, (Fe.comp Fe) c = c ^ Nat.card K := fun c => by
    rw [RingHom.comp_apply, hFe, hFe, ← pow_mul, hK, sq]
  have hFeι : Fe.comp (algebraMap K (AlgebraicClosure K)) =
      (algebraMap K (AlgebraicClosure K)).comp δ := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, hFe, hδ, map_pow]
  have hFeGL : ∀ {τ : Tag} (u : ModGL τ K), Units.map (entrywiseHom Fe)
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) u) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (Units.map (entrywiseHom δ) u) := by
    intro τ u
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFeι]
  have hFeFe : ∀ {τ : Tag} (g : ModGL τ (AlgebraicClosure K)), Units.map (entrywiseHom Fe)
      (Units.map (entrywiseHom Fe) g) = Units.map (entrywiseHom (Fe.comp Fe)) g := by
    intro τ g
    refine Units.ext ?_
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact entrywise_entrywise (R := AlgebraicClosure K) _ _ _
  let δ' : K ≃+* K := RingEquiv.ofBijective δ
    ⟨δ.injective, Finite.surjective_of_injective δ.injective⟩
  have hδ' : δ'.toRingHom = δ := RingHom.ext fun _ => rfl
  refine ⟨fun τ => ?_, ?_⟩
  ·
    obtain ⟨S, hS, hLang⟩ :=
      (exceptional_all_characteristic_field_Lang_surjectivity p (AlgebraicClosure K) e he).1 τ
    set β := entrywiseAdjointAut τ δ' with hβdef
    have hβu : ∀ u, (β u : ModGL τ K) = Units.map (entrywiseHom δ) (u : ModGL τ K) := fun u => by
      rw [hβdef, coe_entrywiseAdjointAut, hδ']
    have hS2 : ∀ g, ((S (S g) : adjointGroup τ (AlgebraicClosure K)) :
        ModGL τ (AlgebraicClosure K)) = Units.map (entrywiseHom (Fe.comp Fe)) g := fun g => by
      rw [hS, hS, hFeFe]
    have hβS : ∀ u, S (adjointBaseChangeHom τ (algebraMap K (AlgebraicClosure K)) u) =
        adjointBaseChangeHom τ (algebraMap K (AlgebraicClosure K)) (β u) := fun u => by
      apply Subtype.ext
      rw [hS, coe_adjointBaseChangeHom, coe_adjointBaseChangeHom, hFeGL, hβu]
    refine ⟨β, hβu, fun g a => ?_⟩
    obtain ⟨hex, hdesc⟩ := quadratic_involution_descent_of_lang τ K hK4 (AlgebraicClosure K)
      (Fe.comp Fe) hFr S hS2 hLang β hβS g a
    refine ⟨?_, fun α hα hα2 => ?_⟩
    · obtain ⟨α, hα⟩ := hex
      exact ⟨α, fun u => by rw [hα, hβu]⟩
    · obtain ⟨ψ, hψ, hrest⟩ := hdesc α (fun u => by rw [hα, hβu]) hα2
      exact ⟨ψ, fun u => by rw [hψ, hβu], hrest⟩
  ·
    obtain ⟨S, hS, hLang⟩ :=
      (exceptional_all_characteristic_field_Lang_surjectivity p (AlgebraicClosure K) e he).2
        TwistTag.E6 1
    simp only [zpow_one] at hS
    set β := diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag δ' with hβdef
    have hβu : ∀ u, (β u : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ :=
      fun u => by
      rw [hβdef, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut, hδ']
    have hP2 : diagramMap TwistTag.E6 (AlgebraicClosure K) *
        diagramMap TwistTag.E6 (AlgebraicClosure K) = 1 := by
      have h := diagramMap_pow_order TwistTag.E6 (AlgebraicClosure K)
      rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
    have hFeP : Units.map (entrywiseHom Fe) (diagramMap TwistTag.E6 (AlgebraicClosure K)) =
        diagramMap TwistTag.E6 (AlgebraicClosure K) :=
      Units.ext (entrywise_diagramMap Fe)
    have hS2 : ∀ g, ((S (S g) : adjointGroup TwistTag.E6.tag (AlgebraicClosure K)) :
        ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
          Units.map (entrywiseHom (Fe.comp Fe)) g := fun g => by
      rw [hS, hS, map_mul, map_mul, map_inv, hFeP, hFeFe]
      calc diagramMap TwistTag.E6 (AlgebraicClosure K) *
            (diagramMap TwistTag.E6 (AlgebraicClosure K) *
              Units.map (entrywiseHom (Fe.comp Fe)) (g : ModGL TwistTag.E6.tag _) *
              (diagramMap TwistTag.E6 (AlgebraicClosure K))⁻¹) *
            (diagramMap TwistTag.E6 (AlgebraicClosure K))⁻¹ =
          (diagramMap TwistTag.E6 (AlgebraicClosure K) *
              diagramMap TwistTag.E6 (AlgebraicClosure K)) *
            Units.map (entrywiseHom (Fe.comp Fe)) (g : ModGL TwistTag.E6.tag _) *
            (diagramMap TwistTag.E6 (AlgebraicClosure K) *
              diagramMap TwistTag.E6 (AlgebraicClosure K))⁻¹ := by group
        _ = _ := by rw [hP2, one_mul, inv_one, mul_one]
    have hβS : ∀ u, S (adjointBaseChangeHom TwistTag.E6.tag (algebraMap K (AlgebraicClosure K)) u)
        = adjointBaseChangeHom TwistTag.E6.tag (algebraMap K (AlgebraicClosure K)) (β u) :=
      fun u => by
        apply Subtype.ext
        rw [hS, coe_adjointBaseChangeHom, coe_adjointBaseChangeHom, hFeGL, hβu, map_mul,
          map_mul, map_inv, baseChangeGL_diagramMap]
    refine ⟨β, hβu, fun g a => ?_⟩
    obtain ⟨hex, hdesc⟩ := quadratic_involution_descent_of_lang TwistTag.E6.tag K hK4
      (AlgebraicClosure K) (Fe.comp Fe) hFr S hS2 hLang β hβS g a
    have hform : ∀ u, (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
        (β u : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹ =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹ := fun u => by
      rw [hβu]
      group
    refine ⟨?_, fun α hα hα2 => ?_⟩
    · obtain ⟨α, hα⟩ := hex
      exact ⟨α, fun u => by rw [hα, hform]⟩
    · obtain ⟨ψ, hψ, hrest⟩ := hdesc α (fun u => by rw [hα, hform]) hα2
      exact ⟨ψ, fun u => by rw [hψ, hβu], hrest⟩

end CFSG.LieType.Chevalley
