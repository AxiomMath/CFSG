module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Split

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

theorem nonempty_SL_mulEquiv_of_card {F F' : Type*} [Field F] [Field F'] [Finite F] [Finite F']
    (h : Nat.card F = Nat.card F') : Nonempty (SL(2, F) ≃* SL(2, F')) := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite F'
  let e : F ≃+* F' := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h])
  refine ⟨{ toFun := Matrix.SpecialLinearGroup.map e.toRingHom
            invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
            left_inv := fun A => ?_
            right_inv := fun A => ?_
            map_mul' := fun A B => map_mul _ A B }⟩
  · ext i j
    simp
  · ext i j
    simp

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem classOrbit_eq_of_mem_simpleRootsJ
    (D : OrthogonalSemilinearFixedRootDatum τ p k) {J' J'' : Set.range D.classOrbit}
    {β : Fin τ.rank → ℤ} (h' : β ∈ (D.withOrbit J').simpleRootsJ)
    (h'' : β ∈ (D.withOrbit J'').simpleRootsJ) : J' = J'' := by
  obtain ⟨-, hβ, hJ'⟩ := h'
  obtain ⟨-, hβ', hJ''⟩ := h''
  obtain ⟨i₀, hi₀⟩ := J'.2
  obtain ⟨i₁, hi₁⟩ := J''.2
  have hc₀ : (⟦⟨β, hβ⟩⟧ : KernelComponent D.χ) ∈ D.classOrbit i₀ := by
    rw [hi₀]
    exact hJ'
  have hc₁ : (⟦⟨β, hβ⟩⟧ : KernelComponent D.χ) ∈ D.classOrbit i₁ := by
    rw [hi₁]
    exact hJ''
  apply Subtype.ext
  rw [← hi₀, ← hi₁, ← D.classOrbit_eq_of_mem hc₀, ← D.classOrbit_eq_of_mem hc₁]

theorem card_SL_dvd_orbitGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ D.simpleRootsJ) (hθβ : D.θ (toReal β) = toReal β) :
    Nat.card SL(2, frobeniusFixedField k p D.e) ∣ Nat.card D.orbitGroup := by
  have hOβ : ({β} : Set (Fin τ.rank → ℤ)) ∈ D.orbits :=
    ⟨β, hβ, (thetaOrbit_eq_singleton D.θ hθβ).symm⟩
  have h1 : orbitCard ({β} : Set (Fin τ.rank → ℤ)) = 1 := Set.ncard_singleton β
  have hr : orbitRoot ({β} : Set (Fin τ.rank → ℤ)) = β :=
    lexLeast_mem (Set.finite_singleton β) (Set.singleton_nonempty β)
  have hfield : ∀ c : k, c ∈ D.orbitField {β} ↔ c ∈ frobeniusFixedField k p D.e := by
    intro c
    change c ∈ frobeniusFixedField k p (D.e * orbitCard {β}) ↔ _
    rw [h1, mul_one]
  let φ : SL2 (frobeniusFixedField k p D.e) →* ModGL τ k :=
    (baseChangeGL (frobeniusFixedField k p D.e).subtype).comp
      (rootSL2 τ (frobeniusFixedField k p D.e) β)
  have hφ : Function.Injective φ :=
    (baseChangeGL_injective _).comp (rootSL2_injective_of_field β)
  have hle : φ.range ≤ D.orbitGroup := by
    refine range_le_of_uSL_vSL φ (fun c => ?_) (fun c => ?_)
    · have hc : (c : k) ∈ D.orbitField {β} := (hfield c).2 c.2
      have hX := D.orbitX_of_orbitCard_eq_one h1 ⟨c, hc⟩
      rw [hr] at hX
      change baseChangeGL _ (rootSL2 τ _ β (uSL c)) ∈ _
      rw [baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_uSL]
      exact hX ▸ Subgroup.subset_closure ⟨{β}, hOβ, ⟨c, hc⟩, Or.inl rfl⟩
    · have hc : (c : k) ∈ D.orbitField {β} := (hfield c).2 c.2
      have hY := D.orbitY_of_orbitCard_eq_one h1 ⟨c, hc⟩
      rw [hr] at hY
      change baseChangeGL _ (rootSL2 τ _ β (vSL c)) ∈ _
      rw [baseChangeGL_rootSL2_of_field, LieType.Chevalley.map_vSL]
      exact hY ▸ Subgroup.subset_closure ⟨{β}, hOβ, ⟨c, hc⟩, Or.inr rfl⟩
  calc Nat.card SL(2, frobeniusFixedField k p D.e) = Nat.card φ.range :=
        Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    _ ∣ Nat.card D.orbitGroup := Subgroup.card_dvd_of_le hle

theorem orbitGroup_mulEquiv_SL_of_singleton
    (D : OrthogonalSemilinearFixedRootDatum τ p k) {β : Fin τ.rank → ℤ}
    (hJ : D.simpleRootsJ = {β}) (hθβ : D.θ (toReal β) = toReal β) :
    Nonempty (D.orbitGroup ≃* SL(2, frobeniusFixedField k p D.e)) := by
  have hβJ : β ∈ D.simpleRootsJ := by
    rw [hJ]
    exact Set.mem_singleton β
  have hroot : IsRoot τ β := (D.mem_kernelRoots_of_mem_simpleRootsJ hβJ).1
  have horb := orbitGroup_eq_map_pairSpan D fun γ hγ => by
    rw [hJ, Set.mem_singleton_iff] at hγ
    rw [hγ]
    exact hθβ
  rw [hJ, pairSpan_singleton] at horb
  have hKq : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : CharP (frobeniusFixedField k p D.e) p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (Fact.out : p.Prime) D.one_le_e hKq
  have hK2 : ringChar (frobeniusFixedField k p D.e) ≠ 2 := by
    rw [ringChar.eq (frobeniusFixedField k p D.e) p]
    exact D.odd
  obtain ⟨-, ⟨eQ⟩, -⟩ :=
    odd_arbitrary_root_pair_SL2_p_components τ (frobeniusFixedField k p D.e) hK2 hroot
  exact ⟨(MulEquiv.subgroupCongr horb).trans
    ((Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).symm.trans eQ.symm)⟩

theorem slComponentForm_of_datum_classes
    (D : OrthogonalSemilinearFixedRootDatum τ p k) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ D.e) {G : Type} [Group G]
    (hJ : ∀ L : Subgroup G, IsComponent L → ∃ J' : Set.range D.classOrbit,
      IsQuasisimple (D.withOrbit J').orbitGroup ∧ Nonempty (L ≃* (D.withOrbit J').orbitGroup))
    {S : Set (Fin τ.rank → ℤ)} {β₁ : Fin τ.rank → ℤ} (hβ₁ : β₁ ∈ S)
    (hβ₁θ : D.θ (toReal β₁) = toReal β₁)
    (hΔ : ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      (D.withOrbit J').simpleRootsJ = S ∨
        ∃ β₀, (D.withOrbit J').simpleRootsJ = {β₀} ∧ D.θ (toReal β₀) = toReal β₀) :
    SLComponentForm K G := by
  have hKq : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : Finite (frobeniusFixedField k p D.e) :=
    Nat.finite_of_card_ne_zero (by rw [hKq]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨eF⟩ := nonempty_SL_mulEquiv_of_card (F := frobeniusFixedField k p D.e) (F' := K)
    (hKq.trans hK.symm)
  have hSL : ∀ J' : Set.range D.classOrbit, (∃ β₀, (D.withOrbit J').simpleRootsJ = {β₀} ∧
      D.θ (toReal β₀) = toReal β₀) → Nonempty ((D.withOrbit J').orbitGroup ≃* SL(2, K)) := by
    rintro J' ⟨β₀, h, hθ₀⟩
    obtain ⟨e₀⟩ := orbitGroup_mulEquiv_SL_of_singleton (D.withOrbit J') h hθ₀
    exact ⟨e₀.trans eF⟩
  have hmem : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').simpleRootsJ = S →
      β₁ ∈ (D.withOrbit J').simpleRootsJ := fun J' h => by
    rw [h]
    exact hβ₁
  intro L hL
  obtain ⟨J', hq, ⟨eL⟩⟩ := hJ L hL
  rcases hΔ J' hq with hS | hsing
  · refine Or.inr ⟨?_, fun L' hL' hL'SL => ?_⟩
    · have h1 := card_SL_dvd_orbitGroup (D.withOrbit J') (hmem J' hS) hβ₁θ
      calc Nat.card SL(2, K) = Nat.card SL(2, frobeniusFixedField k p D.e) :=
            (Nat.card_congr eF.toEquiv).symm
        _ ∣ Nat.card (D.withOrbit J').orbitGroup := h1
        _ = Nat.card L := (Nat.card_congr eL.toEquiv).symm
    · obtain ⟨J'', hq'', ⟨eL'⟩⟩ := hJ L' hL'
      rcases hΔ J'' hq'' with hS'' | hsing''
      · have hJJ : J' = J'' := classOrbit_eq_of_mem_simpleRootsJ D (hmem J' hS) (hmem J'' hS'')
        subst hJJ
        exact ⟨eL.trans eL'.symm⟩
      · obtain ⟨f⟩ := hSL J'' hsing''
        exact absurd ⟨eL'.trans f⟩ hL'SL
  · obtain ⟨f⟩ := hSL J' hsing
    exact Or.inl ⟨eL.trans f⟩

end CFSG.ComponentClassification.CatLeafProof
