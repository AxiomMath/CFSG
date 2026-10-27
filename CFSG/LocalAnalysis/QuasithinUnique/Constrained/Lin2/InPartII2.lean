module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartII1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Stage2

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.R_le_Bo : thompsonJ S ≤ L ⊓ M := by
  rw [← dat.R_sup_D h]
  exact le_sup_left

theorem Lin2Data.D_le_Bo : D ≤ L ⊓ M := by
  rw [← dat.R_sup_D h]
  exact le_sup_right

theorem Lin2Data.conjR_D_le_K {x₀ g : G} (hx₀ : x₀ ∈ T) (hx₀S : x₀ ∉ S) (hg : g ∈ T) :
    conjR D g ≤ (L ⊓ M) ⊔ conjR D x₀ := by
  by_cases hgS : g ∈ S
  · calc conjR D g ≤ conjR (L ⊓ M) g := conjR_mono (dat.D_le_Bo h) g
      _ = L ⊓ M := conjR_eq_of_mem_normalizer (h.S_le_normalizer_Bo hgS)
      _ ≤ _ := le_sup_left
  · exact dat.conjR_D_le_sup h hg hgS hx₀ hx₀S

theorem Lin2Data.conjR_K_le {x₀ t : G} (hx₀ : x₀ ∈ T) (hx₀S : x₀ ∉ S) (ht : t ∈ T) :
    conjR ((L ⊓ M) ⊔ conjR D x₀) t ≤ (L ⊓ M) ⊔ conjR D x₀ := by
  have hRt := dat.x_normalizer_R h ht
  have h1 : conjR (L ⊓ M) t ≤ (L ⊓ M) ⊔ conjR D x₀ := by
    rw [← dat.R_sup_D h, conjR_sup, conjR_eq_of_mem_normalizer hRt]
    rw [dat.R_sup_D h]
    exact sup_le ((dat.R_le_Bo h).trans le_sup_left) (dat.conjR_D_le_K h hx₀ hx₀S ht)
  have h2 : conjR (conjR D x₀) t ≤ (L ⊓ M) ⊔ conjR D x₀ := by
    rw [conjR_conjR]
    exact dat.conjR_D_le_K h hx₀ hx₀S (T.mul_mem hx₀ ht)
  rw [conjR_sup]
  exact sup_le h1 h2

theorem Lin2Data.T_le_normalizer_K {x₀ : G} (hx₀ : x₀ ∈ T) (hx₀S : x₀ ∉ S) :
    T ≤ Subgroup.normalizer (((L ⊓ M) ⊔ conjR D x₀ : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : t * y * t⁻¹ ∈ conjR ((L ⊓ M) ⊔ conjR D x₀) t⁻¹ := by
      rw [mem_conjR]
      simpa [mul_assoc] using hy
    exact dat.conjR_K_le h hx₀ hx₀S (T.inv_mem ht) this
  · intro hy
    have : y ∈ conjR ((L ⊓ M) ⊔ conjR D x₀) t := mem_conjR.2 hy
    exact dat.conjR_K_le h hx₀ hx₀S ht this

end Stage2

end CFSG.QuasithinUnique.Lin2
