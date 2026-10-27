module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

section Orbit

variable {S : Type*} [Group S] {A : Type*} [Group A]

@[expose] def orbitOf (ρ : A →* MulAut S) (K : Subgroup S) : Set (Subgroup S) :=
  {K' | ∃ a : A, K.map (ρ a).toMonoidHom = K'}

theorem mem_orbitOf_self (ρ : A →* MulAut S) (K : Subgroup S) : K ∈ orbitOf ρ K :=
  ⟨1, by rw [map_one]; ext x; simp⟩

theorem comp_ρ (ρ : A →* MulAut S) (x y : A) :
    (ρ x).toMonoidHom.comp (ρ y).toMonoidHom = (ρ (x * y)).toMonoidHom := by
  rw [map_mul]
  rfl

theorem orbitOf_map_mem (ρ : A →* MulAut S) {K K' : Subgroup S} (h : K' ∈ orbitOf ρ K)
    (a : A) : K'.map (ρ a).toMonoidHom ∈ orbitOf ρ K := by
  obtain ⟨b, rfl⟩ := h
  refine ⟨a * b, ?_⟩
  rw [Subgroup.map_map, comp_ρ]

theorem orbitOf_eq_of_mem (ρ : A →* MulAut S) {K K' : Subgroup S} (h : K' ∈ orbitOf ρ K) :
    orbitOf ρ K' = orbitOf ρ K := by
  obtain ⟨a, rfl⟩ := h
  ext L
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨b * a, ?_⟩
    rw [Subgroup.map_map, comp_ρ]
  · rintro ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [Subgroup.map_map, comp_ρ, show b * a⁻¹ * a = b from by group]

theorem orbitOf_eq_of_common (ρ : A →* MulAut S) {K₁ K₂ K : Subgroup S}
    (h1 : K ∈ orbitOf ρ K₁) (h2 : K ∈ orbitOf ρ K₂) : orbitOf ρ K₁ = orbitOf ρ K₂ := by
  rw [← orbitOf_eq_of_mem ρ h1, orbitOf_eq_of_mem ρ h2]

theorem isComponentOf_orbit {ρ : A →* MulAut S} {X K K' : Subgroup S}
    (hX : ∀ a : A, X.map (ρ a).toMonoidHom = X) (hK : IsComponentOf K X)
    (hK' : K' ∈ orbitOf ρ K) : IsComponentOf K' X := by
  obtain ⟨a, rfl⟩ := hK'
  have hinj : ∀ g : S, (ρ a).toMonoidHom g = 1 → g = 1 := by
    intro g hg
    exact (MulEquiv.map_eq_one_iff (ρ a)).1 hg
  have h := isComponentOf_map (ρ a).toMonoidHom
    (fun g hg => by rw [hinj g hg]; exact Subgroup.one_mem _) hK
  rw [hX a] at h
  exact h

theorem sSup_orbit_map_le (ρ : A →* MulAut S) (O : Set (Subgroup S))
    (hO : ∀ K ∈ O, ∀ a : A, K.map (ρ a).toMonoidHom ∈ O) (a : A) :
    (sSup O).map (ρ a).toMonoidHom ≤ sSup O := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (hO K hK a)

theorem sSup_orbit_map (ρ : A →* MulAut S) (O : Set (Subgroup S))
    (hO : ∀ K ∈ O, ∀ a : A, K.map (ρ a).toMonoidHom ∈ O) (a : A) :
    (sSup O).map (ρ a).toMonoidHom = sSup O := by
  apply le_antisymm (sSup_orbit_map_le ρ O hO a)
  have h := sSup_orbit_map_le ρ O hO a⁻¹
  have h2 := Subgroup.map_mono (f := (ρ a).toMonoidHom) h
  rw [Subgroup.map_map] at h2
  have hid : ∀ L : Subgroup S, L.map ((ρ a).toMonoidHom.comp (ρ a⁻¹).toMonoidHom) = L := by
    intro L
    ext x
    simp
  rw [hid] at h2
  exact h2

theorem commutator_sSup_eq_bot {X : Subgroup S} [Finite S] {O O' : Set (Subgroup S)}
    (hO : ∀ K ∈ O, IsComponentOf K X) (hO' : ∀ K ∈ O', IsComponentOf K X)
    (hdisj : ∀ K ∈ O, ∀ K' ∈ O', K ≠ K') :
    ⁅sSup O, sSup O'⁆ = ⊥ := by
  have hpair : ∀ K ∈ O, ∀ K' ∈ O', ⁅K, K'⁆ = ⊥ := by
    intro K hK K' hK'
    rcases isComponent_commute_or_eq (hO K hK) (hO' K' hK') with h | h
    · exact absurd h (hdisj K hK K' hK')
    · exact h
  have h1 : ∀ K ∈ O, ⁅K, sSup O'⁆ = ⊥ := by
    intro K hK
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine sSup_le fun K' hK' => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by
      rw [Subgroup.commutator_comm]
      exact hpair K hK K' hK')
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact h1 K hK

@[expose] def orbitPerm (ρ : A →* MulAut S) (O : Set (Subgroup S))
    (hO : ∀ K ∈ O, ∀ a : A, K.map (ρ a).toMonoidHom ∈ O) (a : A) : Equiv.Perm ↥O where
  toFun K := ⟨K.1.map (ρ a).toMonoidHom, hO K.1 K.2 a⟩
  invFun K := ⟨K.1.map (ρ a⁻¹).toMonoidHom, hO K.1 K.2 a⁻¹⟩
  left_inv K := by
    apply Subtype.ext
    simp only [Subgroup.map_map]
    ext x
    simp
  right_inv K := by
    apply Subtype.ext
    simp only [Subgroup.map_map]
    ext x
    simp

theorem orbitPerm_mul (ρ : A →* MulAut S) (O : Set (Subgroup S))
    (hO : ∀ K ∈ O, ∀ a : A, K.map (ρ a).toMonoidHom ∈ O) (a b : A) (K : ↥O) :
    orbitPerm ρ O hO (a * b) K = orbitPerm ρ O hO a (orbitPerm ρ O hO b K) := by
  apply Subtype.ext
  show K.1.map (ρ (a * b)).toMonoidHom = (K.1.map (ρ b).toMonoidHom).map (ρ a).toMonoidHom
  rw [Subgroup.map_map, map_mul]
  rfl

@[expose] def orbitAct (ρ : A →* MulAut S) (O : Set (Subgroup S))
    (hO : ∀ K ∈ O, ∀ a : A, K.map (ρ a).toMonoidHom ∈ O) : A →* Equiv.Perm ↥O :=
  MonoidHom.mk' (orbitPerm ρ O hO) (fun a b => Equiv.ext fun K => by
    rw [Equiv.Perm.mul_apply]
    exact orbitPerm_mul ρ O hO a b K)

theorem layer_eq_iSup_orbits {X : Subgroup S} (ρ : A →* MulAut S)
    (hX : ∀ a : A, X.map (ρ a).toMonoidHom = X) {ι : Type*} (O : ι → Set (Subgroup S))
    (hι : ∀ K, IsComponentOf K X → ∃ i, K ∈ O i)
    (hsub : ∀ i, ∀ K ∈ O i, IsComponentOf K X) :
    GLALayer X = ⨆ i, sSup (O i) := by
  apply le_antisymm
  · refine GLALayer_le_of fun K hK => ?_
    obtain ⟨i, hi⟩ := hι K hK
    exact le_iSup_of_le i (le_sSup hi)
  · refine iSup_le fun i => ?_
    refine sSup_le fun K hK => ?_
    exact le_GLALayer (hsub i K hK)

end Orbit

end CFSG.LocalAnalysis.GLTheoremA.I142N
