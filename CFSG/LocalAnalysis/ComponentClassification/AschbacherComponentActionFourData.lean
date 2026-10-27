module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionBasic
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentAction

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def rightComponent (L : Subgroup G) (g : G) : Subgroup G :=
  UniversalOrbitBlock.conjugate L g⁻¹

@[expose] def gammaOne (U : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G | ∃ V : Subgroup G,
    V ≤ U ∧ V ≠ ⊥ ∧ N = Subgroup.normalizer (V : Set G)}

theorem involution_inverse (u : G) (hu : u * u = 1) : u⁻¹ = u := by
  calc
    u⁻¹ = u⁻¹ * (u * u) := by rw [hu, mul_one]
    _ = u := by group

theorem rightComponent_involution (L : Subgroup G) (u : G) (hu : u * u = 1) :
    rightComponent L u = L.map (MulAut.conj u).toMonoidHom := by
  dsimp [rightComponent, UniversalOrbitBlock.conjugate]
  rw [involution_inverse u hu]

theorem rightComponent_mul (L : Subgroup G) (g h : G) :
    rightComponent (rightComponent L g) h = rightComponent L (g * h) := by
  simpa only [rightComponent, mul_inv_rev] using
    UniversalOrbitBlock.conjugate_conjugate L g⁻¹ h⁻¹

theorem rightComponent_eq_iff_normalizer (L : Subgroup G) (g : G) :
    rightComponent L g = L ↔ g ∈ Subgroup.normalizer (L : Set G) := by
  change L.map (MulAut.conj g⁻¹) = L ↔
    g ∈ Subgroup.normalizer (L : Set G)
  rw [← Subgroup.mem_normalizer_iff_map_conj_eq]
  exact (Subgroup.normalizer (L : Set G)).inv_mem_iff

theorem rightComponent_component (L : Subgroup G) (hL : IsComponentOf L ⊤) (g : G) :
    IsComponentOf (rightComponent L g) ⊤ :=
  (LocalComponents.equiv_iff (MulAut.conj g⁻¹) L).mpr hL

theorem involution_conjugation_twice (u x : G) (hu : u * u = 1) :
    MulAut.conj u (MulAut.conj u x) = x := by
  simp only [MulAut.conj_apply, involution_inverse u hu]
  calc
    u * (u * x * u) * u = (u * u) * x * (u * u) := by group
    _ = x := by rw [hu]; group

theorem normalizer_le_gammaOne (U V : Subgroup G) (hVU : V ≤ U) (hne : V ≠ ⊥) :
    Subgroup.normalizer (V : Set G) ≤ gammaOne U :=
  le_sSup ⟨V, hVU, hne, rfl⟩

theorem centralizer_le_gammaOne (U : Subgroup G) (u : G) (hu : u ∈ U) (hne : u ≠ 1) :
    Subgroup.centralizer ({u} : Set G) ≤ gammaOne U := by
  apply le_trans _ (normalizer_le_gammaOne U (Subgroup.zpowers u)
    (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_ne_bot.mpr hne))
  intro c hc
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  have hcu := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hfixed : MulAut.conj c u = u := by
    change c * u * c⁻¹ = u
    rw [hcu]
    group
  change Subgroup.zpowers (MulAut.conj c u) = Subgroup.zpowers u
  rw [hfixed]

theorem cyclic_involution_cases (u : G) (hu : u * u = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u := by
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
  have heq := zpow_eq_zpow_emod' n (show u ^ 2 = 1 by simpa only [pow_two] using hu)
  rw [heq]
  have hcases : n % (2 : ℤ) = 0 ∨ n % (2 : ℤ) = 1 := by omega
  rcases hcases with hzero | hone
  · left
    change u ^ (n % (2 : ℤ)) = 1
    rw [hzero, zpow_zero]
  · right
    change u ^ (n % (2 : ℤ)) = u
    rw [hone, zpow_one]

theorem cyclic_involution_commutator_le (L T : Subgroup G) (u : G)
    (hu : u * u = 1) (hgenerators : ∀ x ∈ L, ⁅x, u⁆ ∈ T) :
    ⁅L, Subgroup.zpowers u⁆ ≤ T := by
  apply Subgroup.commutator_le.mpr
  intro x hx w hw
  rcases cyclic_involution_cases u hu hw with rfl | rfl
  · simpa only [commutatorElement_one_right] using T.one_mem
  · exact hgenerators x hx

theorem cyclic_commutator_trivial_iff (L : Subgroup G) (u : G) :
    ⁅L, Subgroup.zpowers u⁆ = ⊥ ↔ u ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.le_centralizer_iff, Subgroup.zpowers_le]

theorem perfect_le_of_all_squares (L T : Subgroup G) [Group.IsPerfect L]
    (hsquares : ∀ x ∈ L, x ^ 2 ∈ T) : L ≤ T := by
  rw [← Subgroup.commutator_eq_self (H := L)]
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have hmiddle := hsquares (x⁻¹ * y) (L.mul_mem (L.inv_mem hx) hy)
  have hlast := hsquares y⁻¹ (L.inv_mem hy)
  have hidentity : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y⁻¹) ^ 2 := by
    simp only [pow_two]
    group
  rw [hidentity]
  exact T.mul_mem (T.mul_mem (hsquares x hx) hmiddle) hlast

theorem involution_diagonal_mem_centralizer (u x : G) (hu : u * u = 1)
    (hcommute : Commute x (MulAut.conj u x)) :
    x * MulAut.conj u x ∈ Subgroup.centralizer ({u} : Set G) := by
  have hfixed : MulAut.conj u (x * MulAut.conj u x) = x * MulAut.conj u x := by
    rw [map_mul, involution_conjugation_twice u x hu, hcommute.eq]
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc
    (x * MulAut.conj u x) * u =
        (u * (x * MulAut.conj u x) * u⁻¹) * u := by
      change _ = (MulAut.conj u (x * MulAut.conj u x)) * u
      rw [hfixed]
    _ = u * (x * MulAut.conj u x) := by group

variable [Finite G]

theorem moved_component_commutes (L : Subgroup G) (u : G)
    (hL : IsComponentOf L ⊤) (hmoved : rightComponent L u ≠ L) :
    ⁅L, rightComponent L u⁆ = ⊥ :=
  LocalComponents.commute_of_ne L (rightComponent L u) hL
    (rightComponent_component L hL u) hmoved.symm

theorem moved_component_commutator (L : Subgroup G) (u : G)
    (hL : IsComponentOf L ⊤) (hu : u * u = 1)
    (hmoved : rightComponent L u ≠ L) :
    ⁅L, Subgroup.zpowers u⁆ = L ⊔ rightComponent L u := by
  have hnontrivial : ⁅L, Subgroup.zpowers u⁆ ≠ ⊥ := by
    intro htrivial
    have hcentral := (cyclic_commutator_trivial_iff L u).mp htrivial
    exact hmoved ((rightComponent_eq_iff_normalizer L u).mpr
      (Subgroup.centralizer_le_normalizer (L : Set G) hcentral))
  have hcontained := (component_arbitrary_action L (Subgroup.zpowers u) hL).resolve_right hnontrivial
  apply le_antisymm
  · apply cyclic_involution_commutator_le L _ u hu
    intro x hx
    rw [rightComponent_involution L u hu]
    change x * u * x⁻¹ * u⁻¹ ∈ L ⊔ L.map (MulAut.conj u).toMonoidHom
    have himage : u * x⁻¹ * u⁻¹ ∈ L.map (MulAut.conj u).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom (L.inv_mem hx)
    simpa only [mul_assoc] using Subgroup.mul_mem_sup hx himage
  · apply sup_le hcontained
    rw [rightComponent_involution L u hu]
    rintro x ⟨y, hy, rfl⟩
    have hnormalizes : u ∈ Subgroup.normalizer
        ((⁅L, Subgroup.zpowers u⁆ : Subgroup G) : Set G) :=
      (Subgroup.normalizer_commutator_ge_right L (Subgroup.zpowers u))
        (Subgroup.mem_zpowers u)
    exact (Subgroup.mem_normalizer_iff.mp hnormalizes y).mp (hcontained hy)

theorem moved_component_diagonal (L : Subgroup G) (u : G)
    (hL : IsComponentOf L ⊤) (hu : u * u = 1)
    (hmoved : rightComponent L u ≠ L) (x : G) (hx : x ∈ L) :
    x * MulAut.conj u x ∈
      ⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u} : Set G) := by
  have hpartner : MulAut.conj u x ∈ rightComponent L u := by
    rw [rightComponent_involution L u hu]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hx
  have hcommute : Commute x (MulAut.conj u x) :=
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (moved_component_commutes L u hL hmoved) hx) _ hpartner).symm
  refine ⟨?_, involution_diagonal_mem_centralizer u x hu hcommute⟩
  rw [moved_component_commutator L u hL hu hmoved]
  exact Subgroup.mul_mem_sup hx hpartner

end CFSG.ComponentClassification.AschbacherComponentAction
