module

public import CFSG.GH74.GLS.LU.Local.Setup
public import CFSG.GH74.GLS.LU.Local.FiveModel

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

@[expose] def LUSetupLeaf' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (Gs : Type) [Group Gs],
    IsTwoCentralClassicalTypeCompat G Gs → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) →
      ∃ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
        LUComps G (p ^ f) z K₁ K₂ ∧ LUSyl G z S K₁ K₂ t u ∧ LUEps G (p ^ f) 1 z K₁ u ∧
          (p ^ f = 5 → FiveExtra G z S)) ∧
    ((p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f) →
      ∃ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
        LUComps G (p ^ f) z K₁ K₂ ∧ LUSyl G z S K₁ K₂ t u ∧ LUEps G (p ^ f) (-1) z K₁ u)

theorem prime_pow_eq_five {p f : ℕ} (hp : p.Prime) (h : p ^ f = 5) : p = 5 ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h
  have hdvd : p ∣ 5 := by
    rw [← h]
    exact dvd_pow_self p hf
  have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd
  subst hp5
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num))
    (show 5 ^ f = 5 ^ 1 by simpa using h)⟩

theorem fiveExtra_of_compat {G : Type} [Group G] {Gs : Type} [Group Gs] (hF : FiveModelFusion)
    {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs} (I : CompatIso G z S z' S')
    (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z)
    (hz' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    (hz2 : orderOf z = 2) (hz'2 : orderOf z' = 2) (hL : LieModel Gs .PSL 4 5 1) :
    FiveExtra G z S := by
  refine ⟨?_, Gs, inferInstance, S', z', hL, hz', hz'2, ⟨I⟩⟩
  intro x hxS hx2
  have hzS : z ∈ (S : Subgroup G) := (mem_of_center_eq hz).1
  have hxX : x ∈ layerTimesSylow z (S : Subgroup G) := S_le_X z _ hxS
  have hzX : z ∈ layerTimesSylow z (S : Subgroup G) := z_mem_X hz
  have hψz := I.psi_z hz hz' hz'2
  have hψx2 : orderOf ((I.ψ ⟨x, hxX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hx2
  refine (I.fusion ⟨z, hzX⟩ ⟨x, hxX⟩ hzS hxS hz2 hx2).mpr ?_
  rw [hψz]
  exact hF Gs hL z' _ hz'2 hψx2

theorem luSetupLeaf'_of_model
    (hM : LUModelLeaf) : LUSetupLeaf' := by
  intro G _ _ hG Gs _ hcompat p f hp hp2 hq
  obtain ⟨-, S, z, S', z', hz, hz', ⟨ψ, hψS, hψfus⟩, -, hAcyc⟩ := hcompat
  let I : CompatIso G z S z' S' := ⟨ψ, hψS, hψfus⟩
  constructor
  · rintro ⟨h8, hL⟩
    have : Finite Gs := (CFSG.LieType.Catalog.lieModel_finite_simple Gs _ 4 p f hL).1
    obtain ⟨E₁, E₂, t', u', d⟩ := (hM Gs p f hp hp2 hq S' z' hz').1 ⟨h8, hL⟩
    obtain ⟨K₁, K₂, t, u, hc, hs, he⟩ :=
      setup_of_model I hz hz' (hAcyc ⟨p, f, hp, hp2, Or.inl hL⟩) d
    refine ⟨z, S, K₁, K₂, t, u, hc, hs, he, fun hpf => ?_⟩
    obtain ⟨rfl, rfl⟩ := prime_pow_eq_five hp hpf
    exact fiveExtra_of_compat fiveModelFusion I hz hz' hs.z_inv d.syl.z_inv hL
  · rintro ⟨h8, hU⟩
    have : Finite Gs := (CFSG.LieType.Catalog.lieModel_finite_simple Gs _ 4 p f hU).1
    obtain ⟨E₁, E₂, t', u', d⟩ := (hM Gs p f hp hp2 hq S' z' hz').2 ⟨h8, hU⟩
    obtain ⟨K₁, K₂, t, u, hc, hs, he⟩ :=
      setup_of_model I hz hz' (hAcyc ⟨p, f, hp, hp2, Or.inr hU⟩) d
    exact ⟨z, S, K₁, K₂, t, u, hc, hs, he⟩

end CFSG.GH74.GLS.LU.Local
