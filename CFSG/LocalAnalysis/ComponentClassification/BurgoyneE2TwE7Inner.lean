module

public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Four

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.Chevalley (conjGL)


theorem rootSL2_single {τ : Tag} {M : Type} [Field M] (i : Fin τ.rank) (A : SL2 M) :
    rootSL2 τ M (Pi.single i 1) A = simpleRootSL2 τ M i A := by
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]

theorem conjGL_one_apply {M : Type*} [Field M] (A : SL2 M) : conjGL (1 : GL (Fin 2) M) A = A :=
  Subtype.ext (by simp [conjGL])

theorem mem_inner_of_odd_fix_orbitGroup {p f : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) {L : Type} [Field L] [Algebra K L] [IsAlgClosed L]
    [CharP L p] (D : OrthogonalSemilinearFixedRootDatum .E7 p L) (hDe : D.e = f)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (hΔ : Pi.single (e7Node 4) 1 ∈ D.simpleRootsJ) {u g₁ : ModGL .E7 L}
    (hH : ∀ w ∈ D.orbitGroup, g₁⁻¹ * (u * w * u⁻¹) * g₁ ∈
      (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)))
    {β : MulAut (adjointGroup .E7 K)} (hβ : Odd (orderOf β))
    (hfix : ∀ t : adjointGroup .E7 K, (∃ w ∈ D.orbitGroup, baseChangeGL (algebraMap K L)
      (t : ModGL .E7 K) = g₁⁻¹ * (u * w * u⁻¹) * g₁) → β t = t) :
    β ∈ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hO, hcard1, hmap⟩ := orbitMap_four D hθ hΔ
  have hKO : ∀ c : K, algebraMap K L c ∈ D.orbitField {Pi.single (e7Node 4) 1} := by
    intro c
    rw [OrthogonalSemilinearFixedRootDatum.orbitField, hcard1, mul_one,
      mem_frobeniusFixedField, hDe, ← hK, ← map_pow, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  set ι' : K →+* D.orbitField {Pi.single (e7Node 4) 1} :=
    (algebraMap K L).codRestrict _ hKO with hι'
  have hρ : ∀ B : SL2 K, rootSL2 .E7 L (Pi.single (e7Node 4) 1)
      (Matrix.SpecialLinearGroup.map (algebraMap K L) B) ∈ D.orbitGroup := by
    intro B
    have h := D.orbitMap_mem_orbitGroup hO (Matrix.SpecialLinearGroup.map ι' B)
    have e : Matrix.SpecialLinearGroup.map (D.orbitField {Pi.single (e7Node 4) 1}).subtype
        (Matrix.SpecialLinearGroup.map ι' B) =
          Matrix.SpecialLinearGroup.map (algebraMap K L) B := by
      ext i j
      rfl
    rw [hmap, e] at h
    exact h
  set h := g₁⁻¹ * u with hh
  have hU : ∀ B : SL2 K, h * simpleRootSL2 .E7 L (e7Node 4) (conjGL 1
      (Matrix.SpecialLinearGroup.map (algebraMap K L) B)) * h⁻¹ ∈
        (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) := by
    intro B
    have h1 := hH _ (hρ B)
    rw [conjGL_one_apply, ← rootSL2_single]
    have e : h * rootSL2 .E7 L (Pi.single (e7Node 4) 1)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) B) * h⁻¹ =
        g₁⁻¹ * (u * rootSL2 .E7 L (Pi.single (e7Node 4) 1)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) B) * u⁻¹) * g₁ := by
      rw [hh]; group
    rw [e]
    exact h1
  have hZ : ∀ η ∈ Subgroup.zpowers β, ∀ (t : adjointGroup .E7 K) (B : SL2 K),
      baseChangeGL (algebraMap K L) (t : ModGL .E7 K) = h * simpleRootSL2 .E7 L (e7Node 4)
        (conjGL 1 (Matrix.SpecialLinearGroup.map (algebraMap K L) B)) * h⁻¹ → η t = t := by
    intro η hη t B ht
    have htQ : β t = t := hfix t ⟨_, hρ B, by
      rw [ht, conjGL_one_apply, ← rootSL2_single, hh]
      group⟩
    have hβt : β ∈ MulAction.stabilizer (MulAut (adjointGroup .E7 K)) t := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact htQ
    have h2 := (Subgroup.zpowers_le.2 hβt) hη
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
  obtain ⟨-, -, hE7, -⟩ :=
    RankThree.PartOne.KE.ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E7
      (Or.inr (Or.inl rfl)) K L (e7Node 4) 1 h hU (Subgroup.zpowers β) hZ
  have hcard := hE7 rfl
  rw [MonoidHom.map_zpowers, Nat.card_zpowers] at hcard
  have hodd : Odd (orderOf (QuotientGroup.mk' (inner (adjointGroup .E7 K)) β)) :=
    Odd.of_dvd_nat hβ (orderOf_map_dvd _ β)
  have h1 : orderOf (QuotientGroup.mk' (inner (adjointGroup .E7 K)) β) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hcard with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
