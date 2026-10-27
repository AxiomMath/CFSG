module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup

theorem normalizer_map_subtype_mem {A : Type} [Group A] {K : Subgroup A} (Q : Subgroup K)
    {x : K} (hx : x ∈ normalizer (Q : Set K)) :
    (x : A) ∈ normalizer ((Q.map K.subtype : Subgroup A) : Set A) := by
  have hQ := Subgroup.mem_normalizer_iff.mp hx
  have e1 : ∀ y : K, (y : A) ∈ Q.map K.subtype ↔ y ∈ Q := fun y =>
    Subgroup.mem_map_iff_mem K.subtype_injective
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hh : h ∈ K
  · obtain ⟨h', rfl⟩ : ∃ h' : K, (h' : A) = h := ⟨⟨h, hh⟩, rfl⟩
    have key : (x : A) * (h' : A) * (x : A)⁻¹ = ((x * h' * x⁻¹ : K) : A) := by simp
    rw [key]
    exact (e1 h').trans ((hQ h').trans (e1 _).symm)
  · have h1 : h ∉ Q.map K.subtype := fun hm => hh (Subgroup.map_subtype_le Q hm)
    have h2 : (x : A) * h * (x : A)⁻¹ ∉ Q.map K.subtype := by
      intro hm
      apply hh
      have hm' : (x : A) * h * (x : A)⁻¹ ∈ K := Subgroup.map_subtype_le Q hm
      have heq : h = (x : A)⁻¹ * ((x : A) * h * (x : A)⁻¹) * (x : A) := by group
      rw [heq]
      exact K.mul_mem (K.mul_mem (K.inv_mem x.2) hm') x.2
    exact iff_of_false h1 h2

theorem exists_mulEquiv_map_eq {A : Type} [Group A] [Finite A] {K : Subgroup A} {G : Type}
    [Group G] (e : ↥K ≃* G) (U₀ : Sylow 2 G) (Q : Sylow 2 ↥K) :
    ∃ ρ : G ≃* ↥K, (U₀ : Subgroup G).map ρ.toMonoidHom = (Q : Subgroup ↥K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : (U₀ : Subgroup G) ≤ e.toMonoidHom.range :=
    fun g _ => MonoidHom.mem_range.mpr ⟨e.symm g, e.apply_symm_apply g⟩
  obtain ⟨V, hVcoe⟩ : ∃ V : Sylow 2 ↥K,
      (V : Subgroup ↥K) = (U₀ : Subgroup G).comap e.toMonoidHom :=
    ⟨U₀.comapOfInjective e.toMonoidHom e.injective hrange, rfl⟩
  haveI : Finite (Sylow 2 ↥K) := Finite.of_injective (fun P : Sylow 2 ↥K => (P : Set ↥K))
    SetLike.coe_injective
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K V Q
  obtain ⟨ρ, hρ⟩ : ∃ ρ : G ≃* ↥K, ∀ g, ρ g = k * e.symm g * k⁻¹ :=
    ⟨e.symm.trans (MulAut.conj k), fun g => rfl⟩
  have hQmem : ∀ t : ↥K, t ∈ (Q : Subgroup ↥K) ↔ k⁻¹ * t * k ∈ (V : Subgroup ↥K) := by
    intro t
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  have hρsymm : ∀ t : ↥K, ρ.symm t = e (k⁻¹ * t * k) := by
    intro t
    rw [MulEquiv.symm_apply_eq, hρ, MulEquiv.symm_apply_apply]
    group
  refine ⟨ρ, ?_⟩
  ext t
  rw [Subgroup.mem_map_equiv, hρsymm t, hQmem t, hVcoe]
  rfl

theorem parabolic_transport {A : Type} [Group A] [Finite A] {K K₀ : Subgroup A} {G : Type}
    [Group G] [Finite G] (e : ↥K ≃* G)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K K₀) (U₀ : Sylow 2 G) :
    ∃ (φ : G →* A) (P : Subgroup G), Function.Injective φ ∧ φ.range = K ∧ P.map φ = K₀ ∧
      normalizer (U₀ : Set G) ≤ P := by
  obtain ⟨hK₀K, U, ⟨Q, hQU⟩, hN⟩ := hpar
  subst hQU
  obtain ⟨ρ, hρU⟩ := exists_mulEquiv_map_eq e U₀ Q
  refine ⟨K.subtype.comp ρ.toMonoidHom, K₀.comap (K.subtype.comp ρ.toMonoidHom), ?_, ?_, ?_, ?_⟩
  · exact K.subtype_injective.comp ρ.injective
  · ext a
    constructor
    · intro ha
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp ha
      rw [← hg]
      exact (ρ g).2
    · intro ha
      exact MonoidHom.mem_range.mpr ⟨ρ.symm ⟨a, ha⟩, by simp⟩
  · ext a
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro ha
      have haK : a ∈ K := hK₀K ha
      refine ⟨ρ.symm ⟨a, haK⟩, ?_, ?_⟩
      · show (K.subtype.comp ρ.toMonoidHom) (ρ.symm ⟨a, haK⟩) ∈ K₀
        simpa using ha
      · simp
  · intro g hg
    have h1 : ρ g ∈ (normalizer (U₀ : Subgroup G)).map ρ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hg
    rw [Subgroup.map_equiv_normalizer_eq, hρU] at h1
    have h2 : ((ρ g : ↥K) : A) ∈ K₀ :=
      hN (Subgroup.mem_inf.mpr ⟨normalizer_map_subtype_mem (Q : Subgroup ↥K) h1, (ρ g).2⟩)
    rw [Subgroup.mem_comap]
    exact h2

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
