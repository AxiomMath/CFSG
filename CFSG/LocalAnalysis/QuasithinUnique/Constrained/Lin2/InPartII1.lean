module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Borel2

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.R_sup_D : thompsonJ S ⊔ D = L ⊓ M := by
  rw [dat.R_eq_P h]
  exact h.decomp.2.1

theorem Lin2Data.Bo_le_normalizer_R : L ⊓ M ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  rw [← dat.R_sup_D h]
  exact sup_le Subgroup.le_normalizer (dat.D_le_normalizer_R h)

omit dat in
theorem Lin2Cfg.S_le_normalizer_Bo : S ≤ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) := by
  intro s hs
  rw [← conjR_eq_self_iff, conjR_inf, conjR_eq_of_mem_normalizer (h.S_le_normalizer hs),
    conjR_eq_of_mem (S_le_M h.cs hs)]

theorem Lin2Data.conjR_D_le_normalizer_Bo {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    conjR D x ≤ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) := by
  intro y hy
  have hL := dat.conjR_D_le_normalizer_L h hx hxS hy
  obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hy
  have hM : x⁻¹ * d * x ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem (h.T_le_M hx)) (h.D_le_M hd)) (h.T_le_M hx)
  rw [← conjR_eq_self_iff, conjR_inf, conjR_eq_of_mem_normalizer hL, conjR_eq_of_mem hM]

omit [Finite G] h in
theorem Lin2Data.x_mul_inv_mem {x x' : G} (hx : x ∈ T) (hxS : x ∉ S) (hx' : x' ∈ T)
    (hx'S : x' ∉ S) : x * x'⁻¹ ∈ S := by
  have := inv_mul_mem_of_relIndex_two dat.index_two (a := x⁻¹) (b := x'⁻¹) (T.inv_mem hx)
    (T.inv_mem hx') (fun hh => hxS (by simpa using S.inv_mem hh))
    (fun hh => hx'S (by simpa using S.inv_mem hh))
  simpa using this

theorem Lin2Data.conjR_D_le_sup {x x' : G} (hx : x ∈ T) (hxS : x ∉ S) (hx' : x' ∈ T)
    (hx'S : x' ∉ S) : conjR D x ≤ (L ⊓ M) ⊔ conjR D x' := by
  have hs : x * x'⁻¹ ∈ S := dat.x_mul_inv_mem hx hxS hx' hx'S
  have e : x = (x * x'⁻¹) * x' := by group
  have h1 : conjR D (x * x'⁻¹) ≤ L ⊓ M := by
    calc conjR D (x * x'⁻¹) ≤ conjR (L ⊓ M) (x * x'⁻¹) := by
          refine conjR_mono ?_ _
          rw [← dat.R_sup_D h]
          exact le_sup_right
      _ = L ⊓ M := conjR_eq_of_mem_normalizer (h.S_le_normalizer_Bo hs)
  have hxR := dat.x_normalizer_R h hx'
  calc conjR D x = conjR (conjR D (x * x'⁻¹)) x' := by rw [← conjR_mul, ← e]
    _ ≤ conjR (L ⊓ M) x' := conjR_mono h1 x'
    _ = conjR (thompsonJ S ⊔ D) x' := by rw [dat.R_sup_D h]
    _ = thompsonJ S ⊔ conjR D x' := by rw [conjR_sup, conjR_eq_of_mem_normalizer hxR]
    _ ≤ (L ⊓ M) ⊔ conjR D x' :=
        sup_le_sup_right (by rw [← dat.R_sup_D h]; exact le_sup_left) _

theorem Lin2Data.K_eq {x x' : G} (hx : x ∈ T) (hxS : x ∉ S) (hx' : x' ∈ T) (hx'S : x' ∉ S) :
    (L ⊓ M) ⊔ conjR D x = (L ⊓ M) ⊔ conjR D x' :=
  le_antisymm (sup_le le_sup_left (dat.conjR_D_le_sup h hx hxS hx' hx'S))
    (sup_le le_sup_left (dat.conjR_D_le_sup h hx' hx'S hx hxS))

end Borel2

end CFSG.QuasithinUnique.Lin2
