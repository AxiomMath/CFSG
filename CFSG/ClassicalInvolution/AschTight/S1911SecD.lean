module

public import CFSG.ClassicalInvolution.AschTight.S1911SecC

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

omit [IsSimpleGroup G] in
theorem coe_eq_of_isUniqueInvolution (hd : Sec19Data p f K z S W) {a : G}
    (c : ↥(Subgroup.centralizer ({a} : Set G))) {u : ↥(Subgroup.centralizer ({a} : Set G))}
    (hu : IsUniqueInvolution (conjSub c (perfectCoreIn K a)) u) :
    (u : G) = (c : G) * z * (c : G)⁻¹ := by
  have hI := (isUniqueInvolution_of_tight hd.tight.toTightBranch).conj (c : G)
  have hsq : (u : G) * u = 1 := congrArg Subtype.val hu.sq
  have hne : (u : G) ≠ 1 := fun h => hu.ne_one (Subtype.ext h)
  exact (hI.unique _ (le_conjSub_of_mem c hu.mem) hsq).resolve_left hne

theorem omega5_conjFamily (hd : Sec19Data p f K z S W) (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a),
    ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
    ∀ u : ↥(Subgroup.centralizer ({a} : Set G)), IsUniqueInvolution M₁ u → ∀ v ∈ M₂,
      (¬ ∀ w ∈ M₂, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * u = u * v →
        v ∈ Subgroup.normalizer (M₁ : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hJne := conjSub_ne_of_ne hne
  have hu' := coe_eq_of_isUniqueInvolution hd c₁ hu
  have hvJ := le_conjSub_of_mem c₂ hv
  have hnc' : ¬ ∀ w ∈ conjSub (c₂ : G) K, (v : G) * w = w * v := by
    intro h
    apply hnc
    intro w hw
    exact Subtype.ext (h _ (le_conjSub_of_mem c₂ hw))
  have h2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    have := h2.map (Subgroup.centralizer ({a} : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this
  have hvz : (v : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) = ((c₁ : G) * z * (c₁ : G)⁻¹) * v := by
    rw [← hu']
    exact congrArg Subtype.val hvu
  have hN := hΩ.omega5 _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hJne _ (hI.conj (c₁ : G)) _ hvJ hnc' h2' hvz
  exact mem_normalizer_conjSub_of c₁ v hN

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
