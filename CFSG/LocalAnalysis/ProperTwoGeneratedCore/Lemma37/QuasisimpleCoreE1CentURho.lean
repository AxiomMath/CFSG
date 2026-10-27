module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUBasic
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv
open CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup (eq_one_of_forall_commute_alternating)
open CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover (eq_conj_of_perfect)

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

@[expose] noncomputable def rho5 : QuasiQuotient u →* Perm (Fin 5) :=
  @permAction _ _ L d.oneComponent.normal d.eA

theorem rho5_eq_of {g : QuasiQuotient u} {π : Perm (Fin 5)}
    (h : ∀ w : L ⧸ Subgroup.center L,
      permOf d.eA (@quotientConj _ _ L d.oneComponent.normal g w) = π * permOf d.eA w * π⁻¹) :
    d.rho5 g = π := by
  have := d.oneComponent.normal
  have hc : π⁻¹ * d.rho5 g = 1 := by
    refine eq_one_of_forall_commute_alternating (by simp) fun σ hσ => ?_
    have h1 := permOf_quotientConj d.eA g (d.eA.symm ⟨σ, hσ⟩)
    rw [h] at h1
    have h2 : permOf d.eA (d.eA.symm ⟨σ, hσ⟩) = σ := by simp [permOf]
    rw [h2] at h1
    calc π⁻¹ * d.rho5 g * σ = π⁻¹ * (d.rho5 g * σ * (d.rho5 g)⁻¹) * d.rho5 g := by group
      _ = π⁻¹ * (π * σ * π⁻¹) * d.rho5 g := by rw [rho5, h1]
      _ = σ * (π⁻¹ * d.rho5 g) := by group
  calc d.rho5 g = π * (π⁻¹ * d.rho5 g) := by group
    _ = π := by rw [hc, mul_one]

theorem rho5_of_mem {l : QuasiQuotient u} (hl : l ∈ L) :
    d.rho5 l = permOf d.eA (((⟨l, hl⟩ : L) : L) : L ⧸ Subgroup.center L) := by
  have := d.oneComponent.normal
  refine d.rho5_eq_of fun w => ?_
  induction w using QuotientGroup.induction_on with
  | H k =>
    rw [quotientConj_mk, ← permOf_inv, ← permOf_mul, ← permOf_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2

theorem rho5_of_mem_centralizer {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) : d.rho5 k = 1 := by
  have := d.oneComponent.normal
  refine d.rho5_eq_of fun w => ?_
  induction w using QuotientGroup.induction_on with
  | H l =>
    rw [quotientConj_mk, inv_one, mul_one, one_mul]
    congr 2
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← Subgroup.mem_centralizer_iff.mp hk l l.2, mul_inv_cancel_right]

theorem sign_rho5_of_mem_sup {g : QuasiQuotient u}
    (hg : g ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u))) :
    Perm.sign (d.rho5 g) = 1 := by
  have := d.oneComponent.centralizer_normal
  obtain ⟨l, hl, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  rw [map_mul, d.rho5_of_mem hl, d.rho5_of_mem_centralizer hk, mul_one]
  exact sign_permOf _ _

theorem mem_sup_iff_sign {g : QuasiQuotient u} :
    g ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) ↔ Perm.sign (d.rho5 g) = 1 := by
  have := d.oneComponent.normal
  exact ⟨d.sign_rho5_of_mem_sup,
    fun hg => mem_sup_centralizer_of_sign d.oneComponent.perfect d.eA hg⟩

theorem sign_rho5_yBar : Perm.sign (d.rho5 d.yBar) = -1 :=
  (Int.units_eq_one_or _).resolve_left fun h => d.yBar_not_mem (d.mem_sup_iff_sign.mpr h)

theorem mem_sup_or_mul_inv_mem_sup (g : QuasiQuotient u) :
    g ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) ∨
      g * d.yBar⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  rcases Int.units_eq_one_or (Perm.sign (d.rho5 g)) with h | h
  · exact Or.inl (d.mem_sup_iff_sign.mpr h)
  · right
    rw [d.mem_sup_iff_sign, map_mul, map_inv, Perm.sign_mul, Perm.sign_inv, h, d.sign_rho5_yBar]
    rfl

theorem mem_centralizer_of_rho5_eq_one {g : QuasiQuotient u} (hg : d.rho5 g = 1) :
    g ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  have := d.oneComponent.normal
  have htriv : ∀ k : L, ((MulAut.conjNormal g k : L) : L ⧸ Subgroup.center L) =
      ((1 * k * 1⁻¹ : L) : L ⧸ Subgroup.center L) := fun k => by
    rw [one_mul, inv_one, mul_one, ← quotientConj_mk]
    apply permOf_injective d.eA
    rw [permOf_quotientConj]
    change d.rho5 g * _ * (d.rho5 g)⁻¹ = _
    rw [hg, one_mul, inv_one, mul_one]
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have h := congrArg Subtype.val (eq_conj_of_perfect d.oneComponent.perfect
    (MulAut.conjNormal g).toMonoidHom 1 htriv ⟨l, hl⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, one_mul, inv_one, mul_one] at h
  calc l * g = g * l * g⁻¹ * g := by rw [h]
    _ = g * l := by group

theorem rho5_surjective : Function.Surjective d.rho5 := by
  have heven : ∀ π : Perm (Fin 5), Perm.sign π = 1 → ∃ l ∈ L, d.rho5 l = π := by
    intro π hπ
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (d.eA.symm ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩)
    refine ⟨w, w.2, ?_⟩
    rw [d.rho5_of_mem w.2]
    change ((d.eA ((w : L) : L ⧸ Subgroup.center L) : alternatingGroup (Fin 5)) : Perm (Fin 5)) = π
    rw [hw]
    simp
  intro π
  rcases Int.units_eq_one_or (Perm.sign π) with h | h
  · obtain ⟨l, -, hl⟩ := heven π h
    exact ⟨l, hl⟩
  · obtain ⟨l, -, hl⟩ := heven (π * (d.rho5 d.yBar)⁻¹) (by
      rw [Perm.sign_mul, Perm.sign_inv, h, d.sign_rho5_yBar]
      rfl)
    exact ⟨l * d.yBar, by rw [map_mul, hl, inv_mul_cancel_right]⟩

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
