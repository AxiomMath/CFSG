module

public import CFSG.CGT.T75M.SzLemma
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherOne
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem commutatorElement_mul_center_left {L : Type*} [Group L] {c : L} (hc : c ∈ center L)
    (a g : L) : ⁅a * c, g⁆ = ⁅a, g⁆ := by
  have h := mem_center_iff.mp hc g
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * g * (a * c)⁻¹ * g⁻¹ = a * (c * g) * c⁻¹ * a⁻¹ * g⁻¹ := by group
    _ = a * (g * c) * c⁻¹ * a⁻¹ * g⁻¹ := by rw [h]
    _ = a * g * a⁻¹ * g⁻¹ := by group

theorem commutatorElement_mul_center_right {L : Type*} [Group L] {d : L} (hd : d ∈ center L)
    (g b : L) : ⁅g, b * d⁆ = ⁅g, b⁆ := by
  have h := mem_center_iff.mp hd g⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc g * (b * d) * g⁻¹ * (b * d)⁻¹ = g * b * (d * g⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = g * b * (g⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [h]
    _ = g * b * g⁻¹ * b⁻¹ := by group

theorem eq_of_mk_eq_of_perfect {L : Type*} [Group L] (hL : commutator L = ⊤) (ρ : L →* L)
    (hρ : ∀ l : L, (QuotientGroup.mk (ρ l) : L ⧸ center L) = QuotientGroup.mk l) (l : L) :
    ρ l = l := by
  have hmov : ∀ a : L, ∃ c ∈ center L, ρ a = a * c := fun a =>
    ⟨a⁻¹ * ρ a, QuotientGroup.eq.mp (hρ a).symm, by group⟩
  have hfix : ∀ a b : L, ρ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨c, hc, hca⟩ := hmov a
    obtain ⟨d, hd, hdb⟩ := hmov b
    rw [map_commutatorElement, hca, hdb, commutatorElement_mul_center_left hc,
      commutatorElement_mul_center_right hd]
  have hle : commutator L ≤ MonoidHom.eqLocus ρ (MonoidHom.id L) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hfix a b
  exact hle (hL ▸ mem_top l)

variable {X : Type} [Group X]

theorem mem_sup_centralizer_of_odd_outer {L : Subgroup X} [hLn : L.Normal]
    (hperf : commutator L = ⊤) (hodd : Odd (Nat.card (Outer (L ⧸ center L)))) {x : X}
    (hx : x * x = 1) : x ∈ L ⊔ centralizer (L : Set X) := by
  have hN : ∀ y : X, y ∈ normalizer (L : Set X) := fun y => mem_normalizer_iff.mpr fun l =>
    ⟨fun hl => hLn.conj_mem l hl y, fun hl => by simpa [mul_assoc] using hLn.conj_mem _ hl y⁻¹⟩
  set σ := CGT.T75M.conjMulEquiv L x (hN x) with hσdef
  have hZ : (center L).map σ.toMonoidHom = center L :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance σ
  set τ : MulAut (L ⧸ center L) := QuotientGroup.congr (center L) (center L) σ hZ with hτdef
  have hτ : ∀ l : L, τ (QuotientGroup.mk l) = QuotientGroup.mk (σ l) := fun l => rfl
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hττ : τ * τ = 1 := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, hτ, hτ, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only [hσdef, CGT.T75M.conjMulEquiv_apply, hxi]
    calc x * (x * (l : X) * x) * x = (x * x) * l * (x * x) := by simp only [mul_assoc]
      _ = l := by rw [hx, one_mul, mul_one]
  obtain ⟨gbar, hg⟩ := CGT.T75M.exists_conj_of_mul_self_eq_one hodd hττ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gbar
  set y := (g : X)⁻¹ * x with hydef
  set ρ := CGT.T75M.conjMulEquiv L y (hN y) with hρdef
  have hρ : ∀ l : L, (QuotientGroup.mk (ρ l) : L ⧸ center L) = QuotientGroup.mk l := by
    intro l
    have h1 : ρ l = g⁻¹ * σ l * g := Subtype.ext (by
      simp only [hρdef, hσdef, CGT.T75M.conjMulEquiv_apply, hydef, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group)
    have h2 : (QuotientGroup.mk (σ l) : L ⧸ center L) =
        QuotientGroup.mk g * QuotientGroup.mk l * (QuotientGroup.mk g)⁻¹ := by
      rw [← hτ, hg, MulAut.conj_apply]
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h2]
    group
  have hy : y ∈ centralizer (L : Set X) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h := congrArg Subtype.val
      (eq_of_mk_eq_of_perfect hperf ρ.toMonoidHom hρ ⟨l, hl⟩)
    simp only [MulEquiv.coe_toMonoidHom, hρdef, CGT.T75M.conjMulEquiv_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rw [show x = (g : X) * y by rw [hydef, mul_inv_cancel_left]]
  exact mul_mem (mem_sup_left g.2) (mem_sup_right hy)

theorem isCoverOverTwo_of_card_center {L A : Type*} [Group L] [Group A] (hL : commutator L = ⊤)
    (hZ : Nat.card (center L) = 2) (e : L ⧸ center L ≃* A) : FooteLit.IsCoverOverTwo L A := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker = center L := by
    ext l
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      EmbeddingLike.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center L)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, ?_, by rw [hker, hZ]⟩
  rw [hker, hL]
  exact le_top

end CFSG.ComponentClassification.Foote5
