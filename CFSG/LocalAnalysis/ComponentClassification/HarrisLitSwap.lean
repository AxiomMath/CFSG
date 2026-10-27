module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLiftField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def swapDiag (K : Subgroup G) (t : G)
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    ↥K →* G where
  toFun k := (k : G) * MulAut.conj t k
  map_one' := by simp
  map_mul' a b := by
    have h1 : MulAut.conj t (a : G) * b = b * MulAut.conj t a :=
      mem_centralizer_iff.mp (hc b.2) _ ⟨a, a.2, rfl⟩
    simp only [Subgroup.coe_mul, map_mul]
    calc (a : G) * b * (MulAut.conj t a * MulAut.conj t b) =
          a * (b * MulAut.conj t a) * MulAut.conj t b := by group
      _ = a * (MulAut.conj t a * b) * MulAut.conj t b := by rw [h1]
      _ = a * MulAut.conj t a * (b * MulAut.conj t b) := by group

theorem swapDiag_apply (K : Subgroup G) (t : G)
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) (k : ↥K) :
    swapDiag K t hc k = (k : G) * MulAut.conj t k := rfl

theorem conj_conj_of_sq_eq_one {t : G} (ht : t ^ 2 = 1) (y : G) :
    MulAut.conj t (MulAut.conj t y) = y := by
  rw [← MulAut.mul_apply, ← map_mul, ← sq, ht, map_one, MulAut.one_apply]

theorem conj_swapDiag (K : Subgroup G) {t : G} (ht : t ^ 2 = 1)
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) (k : ↥K) :
    MulAut.conj t (swapDiag K t hc k) = swapDiag K t hc k := by
  rw [swapDiag_apply, map_mul, conj_conj_of_sq_eq_one ht]
  exact mem_centralizer_iff.mp (hc k.2) _ ⟨k, k.2, rfl⟩

theorem inf_le_centralizer_sup (K : Subgroup G) {t : G}
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    K ⊓ K.map (MulAut.conj t).toMonoidHom ≤
      centralizer ((K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rintro c ⟨hcK, hcKt⟩
  rw [mem_centralizer_iff]
  have hcen : (K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup G) ≤
      centralizer ({c} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hc hx) c hcKt).symm
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hc hcK) x hx)
  intro y hy
  exact mem_centralizer_singleton_iff.mp (hcen hy)

theorem commutatorElement_mul_mul_of_commute {x y c d : G} (hcy : Commute c y)
    (hdx : Commute d x) (hcd : Commute c d) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹ = x * (c * y) * d * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by
        group
    _ = x * (y * c) * d * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by rw [hcy.eq]
    _ = x * y * (c * d) * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by group
    _ = x * y * (d * c) * c⁻¹ * x⁻¹ * d⁻¹ * y⁻¹ := by rw [hcd.eq]
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [hdx.inv_right.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem exists_eq_swapDiag_mul (K : Subgroup G) {t : G} (ht : t ^ 2 = 1)
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    {x : G} (hx : x ∈ (K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set G)) :
    ∃ a : ↥K, ∃ c ∈ K ⊓ K.map (MulAut.conj t).toMonoidHom, x = swapDiag K t hc a * c := by
  have hN : K ≤ normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    fun k hk => centralizer_le_normalizer _ (hc hk)
  have hx1 : x ∈ ((K : Set G) * ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hN]
    exact hx.1
  obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := hx1
  simp only [MulEquiv.coe_toMonoidHom] at hx ⊢
  have hfix : MulAut.conj t (a * MulAut.conj t b) = a * MulAut.conj t b := by
    have h1 := mem_centralizer_singleton_iff.mp hx.2
    rw [MulAut.conj_apply]
    calc t * (a * (MulAut.conj t) b) * t⁻¹ = (a * (MulAut.conj t) b * t) * t⁻¹ := by
          rw [h1]
      _ = a * (MulAut.conj t) b := by group
  rw [map_mul, conj_conj_of_sq_eq_one ht] at hfix
  have hcomm : MulAut.conj t a * b = b * MulAut.conj t a :=
    mem_centralizer_iff.mp (hc hb) _ ⟨a, ha, rfl⟩
  have hc0 : a⁻¹ * b = MulAut.conj t (b * a⁻¹) := by
    rw [map_mul, map_inv]
    calc a⁻¹ * b = a⁻¹ * (b * MulAut.conj t a) * (MulAut.conj t a)⁻¹ := by group
      _ = a⁻¹ * (MulAut.conj t a * b) * (MulAut.conj t a)⁻¹ := by rw [hcomm]
      _ = a⁻¹ * (a * MulAut.conj t b) * (MulAut.conj t a)⁻¹ := by rw [hfix]
      _ = MulAut.conj t b * (MulAut.conj t a)⁻¹ := by group
  refine ⟨⟨a, ha⟩, MulAut.conj t (a⁻¹ * b),
    ⟨?_, ⟨a⁻¹ * b, K.mul_mem (K.inv_mem ha) hb, rfl⟩⟩, ?_⟩
  · rw [hc0, conj_conj_of_sq_eq_one ht]
    exact K.mul_mem hb (K.inv_mem ha)
  · rw [swapDiag_apply, mul_assoc, ← map_mul]
    congr 2
    group

theorem centralizerResidual_sup_eq_range [Finite G] (K : Subgroup G) {t : G} (ht : t ^ 2 = 1)
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hK : Group.IsPerfect ↥K) :
    centralizerResidual (K ⊔ K.map (MulAut.conj t).toMonoidHom) t =
      (swapDiag K t hc).range := by
  set C := (K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set G) with hC
  have hRC : (swapDiag K t hc).range ≤ C := by
    rintro _ ⟨k, rfl⟩
    refine ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · exact mul_mem (mem_sup_left k.2) (mem_sup_right ⟨k, k.2, rfl⟩)
    · have h1 := conj_swapDiag K ht hc k
      rw [MulAut.conj_apply] at h1
      calc swapDiag K t hc k * t = t * swapDiag K t hc k * t⁻¹ * t := by rw [h1]
        _ = t * swapDiag K t hc k := by group
  apply le_antisymm
  ·
    have hcomm : ⁅C, C⁆ ≤ (swapDiag K t hc).range := by
      rw [commutator_le]
      intro x hx y hy
      obtain ⟨a, c, hc', rfl⟩ := exists_eq_swapDiag_mul K ht hc hx
      obtain ⟨b, d, hd', rfl⟩ := exists_eq_swapDiag_mul K ht hc hy
      have hcz := inf_le_centralizer_sup K hc hc'
      have hdz := inf_le_centralizer_sup K hc hd'
      have hφa : swapDiag K t hc a ∈ (K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup G) :=
        (hRC ⟨a, rfl⟩).1
      have hφb : swapDiag K t hc b ∈ (K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup G) :=
        (hRC ⟨b, rfl⟩).1
      have hcb : Commute c (swapDiag K t hc b) := (mem_centralizer_iff.mp hcz _ hφb).symm
      have hda : Commute d (swapDiag K t hc a) := (mem_centralizer_iff.mp hdz _ hφa).symm
      have hcd : Commute c d := mem_centralizer_iff.mp hdz _ (mem_sup_left hc'.1)
      rw [commutatorElement_mul_mul_of_commute hcb hda hcd]
      exact ⟨⁅a, b⁆, map_commutatorElement _ _ _⟩
    obtain ⟨n, hn, hn1⟩ := (perfect_residual_characterization (G := ↥C)).1
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : y ∈ derivedSeries ↥C 1 := by
      rw [hn] at hy
      have := derivedSeries_antitone ↥C (show 1 ≤ n + 1 by omega)
      exact this (hn1 ▸ hy)
    rw [derivedSeries_one, _root_.commutator_def] at hy1
    have hmap : (⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ : Subgroup ↥C).map C.subtype ≤
        ⁅C, C⁆ := by
      rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hcomm (hmap ⟨y, hy1, rfl⟩)
  ·
    have : Group.IsPerfect ↥(swapDiag K t hc).range :=
      Group.IsPerfect.ofSurjective (f := (swapDiag K t hc).rangeRestrict)
        (swapDiag K t hc).rangeRestrict_surjective
    exact le_perfectResidual_map hRC this

end CFSG.ComponentClassification.HarrisLit
