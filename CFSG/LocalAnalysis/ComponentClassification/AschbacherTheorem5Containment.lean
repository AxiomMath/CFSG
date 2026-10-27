module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Preimages

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

theorem enters_normalizer_of_preimage_le {G : Type*} [Group G]
    (D : Subgroup G) (r : ℕ) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) → g ∈ Subgroup.normalizer (D : Set G))
    (i : Fin r) (g : G)
    (hcontained : aschbacherThm5Preimage D (Abar i) ≤
      (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom) :
    g ∈ Subgroup.normalizer (D : Set G) := by
  apply hii i g _ le_rfl
  intro a ha
  exact ⟨a, hcontained ha, 1, (aschbacherThm5Core D).one_mem, (mul_one a).symm⟩

theorem factor_normalizer_le {G : Type*} [Group G]
    (D : Subgroup G) (r : ℕ) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) → g ∈ Subgroup.normalizer (D : Set G)) (i : Fin r) :
    Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) ≤
      Subgroup.normalizer (D : Set G) := by
  intro g hg
  apply enters_normalizer_of_preimage_le D r Abar hii i g
  have hfixed := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)).inv_mem hg)
  rw [← hfixed]
  apply Subgroup.map_mono
  exact (preimage_le D (Abar i)).trans Subgroup.le_normalizer

theorem factor_centralizer_le {G : Type*} [Group G]
    (D : Subgroup G) (r : ℕ) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) → g ∈ Subgroup.normalizer (D : Set G)) (i : Fin r) :
    Subgroup.centralizer (aschbacherThm5Preimage D (Abar i) : Set G) ≤
      Subgroup.normalizer (D : Set G) :=
  (Subgroup.centralizer_le_normalizer _).trans (factor_normalizer_le D r Abar hii i)

theorem normalizer_adjoin_center {G : Type*} [Group G]
    (D : Subgroup G) (r : ℕ) (hr : 1 ≤ r)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) → g ∈ Subgroup.normalizer (D : Set G)) :
    Subgroup.normalizer ((D ⊔ Subgroup.center G : Subgroup G) : Set G) =
      Subgroup.normalizer (D : Set G) := by
  apply le_antisymm
  · intro g hg
    apply enters_normalizer_of_preimage_le D r Abar hii (⟨0, by omega⟩ : Fin r) g
    have hfixed := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer ((D ⊔ Subgroup.center G : Subgroup G) : Set G)).inv_mem hg)
    have hsup : D ⊔ Subgroup.center G ≤ Subgroup.normalizer (D : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
    have hmapped := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hsup
    have hfixed' : (D ⊔ Subgroup.center G).map (MulAut.conj g⁻¹).toMonoidHom =
        D ⊔ Subgroup.center G := hfixed
    rw [hfixed'] at hmapped
    exact (preimage_le D _).trans (le_sup_left.trans hmapped)
  · exact Subgroup.normalizer_le_normalizer_sup_normal

end CFSG.ComponentClassification.AschbacherTheorem5
