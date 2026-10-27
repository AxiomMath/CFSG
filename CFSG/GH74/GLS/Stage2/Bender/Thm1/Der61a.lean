module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Fpi61

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Fpi_le_Fm (σ : Set ℕ) (N : Subgroup G) : Fpi σ N ≤ Fm N :=
  iSup₂_le fun q _ => Op_le q (Fm N)

theorem le_normalizer_Fpi {σ : Set ℕ} (hσ : ∀ q ∈ σ, q.Prime) (N : Subgroup G) :
    N ≤ normalizer ((Fpi σ N : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_forall fun x hx => ?_
  have hmap : (Fpi σ N).map (MulAut.conj g).toMonoidHom ≤ Fpi σ N := by
    unfold Fpi
    rw [Subgroup.map_iSup]
    refine iSup_le fun q => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hq => ?_
    have hn : g ∈ normalizer ((Op q (Fm N) : Subgroup G) : Set G) := by
      rw [Op_Fm_eq (hσ q hq) N]
      exact le_normalizer_Op q N hg
    have : (Op q (Fm N)).map (MulAut.conj g).toMonoidHom ≤ Op q (Fm N) := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hn y).mp hy
    exact this.trans (le_iSup₂_of_le q hq le_rfl)
  exact hmap ⟨x, hx, rfl⟩

theorem Fm_le_Fpi_sup (P : ℕ → Prop) (N : Subgroup G) :
    Fm N ≤ Fpi {q | q.Prime ∧ P q} N ⊔ Fpi {q | q.Prime ∧ ¬ P q} N := by
  refine Fm_le_of_forall fun q hq => ?_
  rw [← Op_Fm_eq hq N]
  by_cases h : P q
  · exact le_sup_of_le_left (le_iSup₂_of_le q ⟨hq, h⟩ le_rfl)
  · exact le_sup_of_le_right (le_iSup₂_of_le q ⟨hq, h⟩ le_rfl)

theorem inverts_of_fixed_free {z : G} (hz : z * z = 1) {D : Subgroup G}
    (hzD : z ∈ normalizer (D : Set G)) (hfix : ∀ d ∈ D, z * d = d * z → d = 1) : Inverts z D := by
  classical
  have hmem : ∀ d : ↥D, (d : G)⁻¹ * (z * d * z⁻¹) ∈ D := fun d =>
    D.mul_mem (D.inv_mem d.2) ((mem_normalizer_iff.mp hzD d).mp d.2)
  let f : ↥D → ↥D := fun d => ⟨(d : G)⁻¹ * (z * d * z⁻¹), hmem d⟩
  have hinj : Function.Injective f := by
    intro d e hde
    have h1 : (d : G)⁻¹ * (z * d * z⁻¹) = (e : G)⁻¹ * (z * e * z⁻¹) := congrArg Subtype.val hde
    have h4 : z * d * z⁻¹ = (d : G) * ((e : G)⁻¹ * (z * e * z⁻¹)) := by
      calc z * (d : G) * z⁻¹ = (d : G) * ((d : G)⁻¹ * (z * d * z⁻¹)) := by group
        _ = (d : G) * ((e : G)⁻¹ * (z * e * z⁻¹)) := by rw [h1]
    have h2 : z * ((d : G) * (e : G)⁻¹) = ((d : G) * (e : G)⁻¹) * z := by
      calc z * ((d : G) * (e : G)⁻¹) = (z * d * z⁻¹) * (z * e * z⁻¹)⁻¹ * z := by group
        _ = (d : G) * ((e : G)⁻¹ * (z * e * z⁻¹)) * (z * e * z⁻¹)⁻¹ * z := by rw [h4]
        _ = ((d : G) * (e : G)⁻¹) * z := by group
    have h3 := hfix _ (D.mul_mem d.2 (D.inv_mem e.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro a ha
  obtain ⟨d, hd⟩ := hsurj ⟨a, ha⟩
  have hda : (d : G)⁻¹ * (z * d * z⁻¹) = a := congrArg Subtype.val hd
  rw [← hda]
  exact conj_inv_elt hz d

omit [Finite G] in
theorem commutator_centralizes_of_inverts {z u : G} (hz : z * z = 1) {D : Subgroup G}
    (hinv : Inverts z D) (hu : u ∈ normalizer (D : Set G)) :
    ∀ d ∈ D, (u * z * u⁻¹ * z⁻¹) * d = d * (u * z * u⁻¹ * z⁻¹) := by
  intro d hd
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h1 : z⁻¹ * d * z = d⁻¹ := by
    have := hinv d hd
    rw [hzi] at this ⊢
    exact this
  have he : u⁻¹ * d * u ∈ D := by
    have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) d).mp hd
    simpa using this
  have h2 : z * (u⁻¹ * d * u)⁻¹ * z⁻¹ = u⁻¹ * d * u := by
    have := hinv _ (D.inv_mem he)
    rw [inv_inv] at this
    exact this
  have h3 : (u * z * u⁻¹ * z⁻¹) * d * (u * z * u⁻¹ * z⁻¹)⁻¹ = d := by
    calc (u * z * u⁻¹ * z⁻¹) * d * (u * z * u⁻¹ * z⁻¹)⁻¹
        = u * z * (u⁻¹ * (z⁻¹ * d * z) * u) * z⁻¹ * u⁻¹ := by group
      _ = u * z * (u⁻¹ * d⁻¹ * u) * z⁻¹ * u⁻¹ := by rw [h1]
      _ = u * (z * (u⁻¹ * d * u)⁻¹ * z⁻¹) * u⁻¹ := by group
      _ = u * (u⁻¹ * d * u) * u⁻¹ := by rw [h2]
      _ = d := by group
  calc (u * z * u⁻¹ * z⁻¹) * d = (u * z * u⁻¹ * z⁻¹) * d * (u * z * u⁻¹ * z⁻¹)⁻¹ * (u * z * u⁻¹ * z⁻¹) := by group
    _ = d * (u * z * u⁻¹ * z⁻¹) := by rw [h3]

omit [Finite G] in
theorem mem_of_sq_mem {H : Subgroup G} {u : G} {N : ℕ} (hN : Odd N) (hu : u ^ N = 1) (h : u ^ 2 ∈ H) :
    u ∈ H := by
  obtain ⟨j, hj⟩ := hN
  have : (u ^ 2) ^ (j + 1) = u := by
    rw [← pow_mul]
    calc u ^ (2 * (j + 1)) = u ^ (2 * j + 1 + 1) := by rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      _ = u ^ (2 * j + 1) * u := pow_succ _ _
      _ = u := by rw [← hj, hu, one_mul]
  rw [← this]
  exact Subgroup.pow_mem _ h _

end Fpi61

end CFSG.GH74.GLS.Stage2.Bender.Thm1
