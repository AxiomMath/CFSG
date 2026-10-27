module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedConfig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.Lattice.SteinbergBIGenOrbitMaps

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KD4T

namespace Up34Chev2

section Gen

theorem range_le_of_gen {K : Type} [Field K] {G : Type*} [Group G] (ψ : SL2 K →* G)
    (C : Subgroup G) (hu : ∀ c, ψ (CFSG.LieType.Chevalley.uSL c) ∈ C)
    (hv : ∀ c, ψ (CFSG.LieType.Chevalley.vSL c) ∈ C) : ψ.range ≤ C := by
  rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower (K := K), MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact hu c
  · exact hv c

end Gen

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀]
  [IsAlgClosed k] {M : Type} [CommGroup M] (D : GenFixedRootDatum τ p₀ k M)

theorem orbitX_card_one {O : Set (Fin τ.rank → ℤ)} (h1 : GenFixedRootDatum.orbitCard O = 1)
    (c : D.orbitField O) :
    D.orbitX O c = rootSL2 τ k (GenFixedRootDatum.orbitRoot O)
      (CFSG.LieType.Chevalley.uSL (c : k)) := by
  rw [GenFixedRootDatum.orbitX, D.orbitMap_eq_prod, h1]
  simp [D.orbitFactor_uSL, GenFixedRootDatum.orbitVec_zero]

theorem orbitY_card_one {O : Set (Fin τ.rank → ℤ)} (h1 : GenFixedRootDatum.orbitCard O = 1)
    (c : D.orbitField O) :
    D.orbitY O c = rootSL2 τ k (GenFixedRootDatum.orbitRoot O)
      (CFSG.LieType.Chevalley.vSL (c : k)) := by
  rw [GenFixedRootDatum.orbitY, D.orbitMap_eq_prod, h1]
  simp [D.orbitFactor_vSL, GenFixedRootDatum.orbitVec_zero]

theorem orbitX_card_two {O : Set (Fin τ.rank → ℤ)} (h2 : GenFixedRootDatum.orbitCard O = 2)
    (c : D.orbitField O) :
    D.orbitX O c = rootSL2 τ k (D.orbitVec O 0) (CFSG.LieType.Chevalley.uSL (c : k)) *
      rootSL2 τ k (D.orbitVec O 1) (CFSG.LieType.Chevalley.uSL ((c : k) ^ D.q)) := by
  rw [GenFixedRootDatum.orbitX, D.orbitMap_eq_prod, h2]
  simp [List.range_succ, D.orbitFactor_uSL]

theorem orbitY_card_two {O : Set (Fin τ.rank → ℤ)} (h2 : GenFixedRootDatum.orbitCard O = 2)
    (c : D.orbitField O) :
    D.orbitY O c = rootSL2 τ k (D.orbitVec O 0) (CFSG.LieType.Chevalley.vSL (c : k)) *
      rootSL2 τ k (D.orbitVec O 1) (CFSG.LieType.Chevalley.vSL ((c : k) ^ D.q)) := by
  rw [GenFixedRootDatum.orbitY, D.orbitMap_eq_prod, h2]
  simp [List.range_succ, D.orbitFactor_vSL]

theorem orbitX_mem_orbitGroup' {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (c : D.orbitField O) : D.orbitX O c ∈ D.orbitGroup :=
  Subgroup.subset_closure ⟨O, hO, c, Or.inl rfl⟩

theorem orbitY_mem_orbitGroup' {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (c : D.orbitField O) : D.orbitY O c ∈ D.orbitGroup :=
  Subgroup.subset_closure ⟨O, hO, c, Or.inr rfl⟩

theorem slHom_range_le_orbitGroup_one {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h1 : GenFixedRootDatum.orbitCard O = 1) {β : Fin τ.rank → ℤ}
    (hβ : GenFixedRootDatum.orbitRoot O = β) :
    (slHom β (RingHom.id k) (frobeniusFixedField k p₀ D.e)).range ≤ D.orbitGroup := by
  have hmem : ∀ c : frobeniusFixedField k p₀ D.e, (c : k) ∈ D.orbitField O := fun c =>
    D.mem_orbitField.2 (by rw [h1, pow_one]; exact mem_frobeniusFixedField.1 c.2)
  refine range_le_of_gen _ _ (fun c => ?_) (fun c => ?_)
  · have h := orbitX_mem_orbitGroup' D hO ⟨(c : k), hmem c⟩
    rw [orbitX_card_one D h1, hβ] at h
    rw [slHom_apply, CFSG.LieType.Chevalley.map_uSL]
    exact h
  · have h := orbitY_mem_orbitGroup' D hO ⟨(c : k), hmem c⟩
    rw [orbitY_card_one D h1, hβ] at h
    rw [slHom_apply, CFSG.LieType.Chevalley.map_vSL]
    exact h

end Datum

section DatumTwo

variable {τ : Tag} {k : Type} [Field k] [CharP k 2] [IsAlgClosed k] {M : Type}
  [CommGroup M] (D : GenFixedRootDatum τ 2 k M)

theorem psiAB_range_le_orbitGroup_two (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (h2 : GenFixedRootDatum.orbitCard O = 2)
    {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a) (hb : IsRoot τ b) (h0 : iform a b = 0)
    (hOa : D.orbitVec O 0 = a) (hOb : D.orbitVec O 1 = b) :
    (psiAB hτ ha hb h0 D.e (2 * D.e)).range ≤ D.orbitGroup := by
  have hq : (2 ^ D.e) ^ 2 = 2 ^ (2 * D.e) := by rw [← pow_mul, mul_comm]
  have hmem : ∀ c : frobeniusFixedField k 2 (2 * D.e), (c : k) ∈ D.orbitField O := fun c =>
    D.mem_orbitField.2 (by
      rw [h2]
      change (c : k) ^ (2 ^ D.e) ^ 2 = c
      rw [hq]
      exact mem_frobeniusFixedField.1 c.2)
  refine range_le_of_gen _ _ (fun c => ?_) (fun c => ?_)
  · have h := orbitX_mem_orbitGroup' D hO ⟨(c : k), hmem c⟩
    rw [orbitX_card_two D h2, hOa, hOb] at h
    rw [psiAB_apply hτ ha hb h0, slHom_apply, slHom_apply, CFSG.LieType.Chevalley.map_uSL,
      CFSG.LieType.Chevalley.map_uSL]
    exact h
  · have h := orbitY_mem_orbitGroup' D hO ⟨(c : k), hmem c⟩
    rw [orbitY_card_two D h2, hOa, hOb] at h
    rw [psiAB_apply hτ ha hb h0, slHom_apply, slHom_apply, CFSG.LieType.Chevalley.map_vSL,
      CFSG.LieType.Chevalley.map_vSL]
    exact h

end DatumTwo

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
