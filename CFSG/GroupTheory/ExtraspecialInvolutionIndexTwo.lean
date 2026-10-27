module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.GroupTheory.Extraspecial2PG
public import CFSG.GroupTheory.ClassTwoInvolutionIndexTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GroupTheory

open Subgroup CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

variable {Q : Type*} [Group Q]

theorem apply_mul_inv_mem_center_of_index_eq_two [Finite Q] (hQ : IsExtraspecialPGroup 2 Q)
    (σ : MulAut Q) (hσ : ∀ x, σ (σ x) = x) {D : Subgroup Q}
    (hDmem : ∀ x, x ∈ D ↔ σ x = x) (hD : D.index = 2) (x : Q) :
    σ x * x⁻¹ ∈ center Q :=
  apply_mul_inv_mem_center_of_index_eq_two_of_class_two
    (fun v => by rw [← pow_two]; exact sq_mem_center hQ v) (commutatorElement_mem_center hQ) σ hσ
    (fun _ hc => mulAut_apply_eq_of_mem_center hQ.2.2.2 σ hc) hDmem hD x

theorem exists_conj_eq_of_forall_apply_mul_inv_mem_center [Finite Q]
    (hQ : IsExtraspecialPGroup 2 Q) (σ : MulAut Q) (hfix : ∀ x : Q, σ x * x⁻¹ ∈ center Q) :
    ∃ q₀ : Q, ∀ x : Q, σ x = q₀ * x * q₀⁻¹ := by
  classical
  let := extraspecialQuotientModule hQ
  have hind : ∀ x y : Q, ind (σ (x * y) * (x * y)⁻¹) =
      ind (σ x * x⁻¹) + ind (σ y * y⁻¹) := by
    intro x y
    rw [← ind_mul hQ (hfix x) (hfix y), map_mul]
    have hc := mem_center_iff.mp (hfix y)
    congr 1
    calc σ x * σ y * (x * y)⁻¹ = σ x * (σ y * y⁻¹) * x⁻¹ := by group
      _ = σ x * x⁻¹ * (σ y * y⁻¹) := by
        rw [mul_assoc (σ x), ← hc x⁻¹]; group
  let μ : Q →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (ind (σ x * x⁻¹))
      map_one' := by
        rw [map_one, inv_one, mul_one, ind_one]
        rfl
      map_mul' := fun x y => by
        rw [hind, ofAdd_add] }
  let μ' : Additive (Abelianization Q) →+ ZMod 2 :=
    MonoidHom.toAdditive (Abelianization.lift μ)
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  obtain ⟨u, hu⟩ := (LinearMap.BilinForm.toDual (extraspecialQuadForm hQ).polarBilin
    (extraspecialQuadForm_nondegenerate hQ)).surjective (AddMonoidHom.toZModLinearMap 2 μ')
  obtain ⟨q₀, rfl⟩ := exists_ofMul_of u
  refine ⟨q₀, fun x => ?_⟩
  have key : σ x * x⁻¹ = ⁅q₀, x⁆ := by
    have h := LinearMap.congr_fun hu (Additive.ofMul (Abelianization.of x))
    rw [LinearMap.BilinForm.toDual_def, QuadraticMap.polarBilin_apply_apply,
      polar_extraspecialQuadForm_apply] at h
    have h' : ind ⁅q₀, x⁆ = ind (σ x * x⁻¹) := h
    by_contra hne
    have hc1 := commutatorElement_mem_center hQ q₀ x
    by_cases ha : σ x * x⁻¹ = 1
    · rw [ha, ind_one, ind_eq_zero_iff] at h'
      exact hne (ha.trans h'.symm)
    · by_cases hb : ⁅q₀, x⁆ = 1
      · rw [hb, ind_one, eq_comm, ind_eq_zero_iff] at h'
        exact ha h'
      · exact hne (eq_of_mem_center hQ (hfix x) hc1 ha hb)
  calc σ x = σ x * x⁻¹ * x := by group
    _ = ⁅q₀, x⁆ * x := by rw [key]
    _ = q₀ * x * q₀⁻¹ := by rw [commutatorElement_def]; group

section Ambient

variable {G : Type} [Group G]

theorem mem_sup_centralizer_of_relIndex_centralizer_eq_two [Finite G] {J : Subgroup G}
    (hJ : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 J) {x : G}
    (hx : x ∈ normalizer (J : Set G)) (hx2 : x ^ 2 ∈ centralizer (J : Set G))
    (hidx : (centralizer ({x} : Set G)).relIndex J = 2) :
    ∃ j ∈ J, j⁻¹ * x ∈ centralizer (J : Set G) := by
  have hQ : IsExtraspecialPGroup 2 J := CFSG.IsExtraspecial2.toIsExtraspecialPGroup hJ
  set σ : MulAut J := J.normalizerMonoidHom ⟨x, hx⟩ with hσdef
  have hσσ : ∀ q : J, σ (σ q) = q := by
    intro q
    ext
    have h : (q : G) * (x * x) = (x * x) * q := by
      simpa [pow_two] using mem_centralizer_iff.mp hx2 (q : G) q.2
    change x * (x * q * x⁻¹) * x⁻¹ = q
    calc x * (x * q * x⁻¹) * x⁻¹ = ((x * x) * q) * (x * x)⁻¹ := by group
      _ = (q * (x * x)) * (x * x)⁻¹ := by rw [h]
      _ = q := by group
  have hDmem : ∀ q : J, q ∈ (centralizer ({x} : Set G)).subgroupOf J ↔ σ q = q := by
    intro q
    rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      ext
      change x * q * x⁻¹ = q
      rw [← h]; group
    · intro h
      have h' := congrArg Subtype.val h
      change x * q * x⁻¹ = q at h'
      calc (q : G) * x = x * q * x⁻¹ * x := by rw [h']
        _ = x * q := by group
  have hfix : ∀ q : J, σ q * q⁻¹ ∈ center J := fun q =>
    apply_mul_inv_mem_center_of_index_eq_two hQ σ hσσ hDmem hidx q
  obtain ⟨q₀, hq₀⟩ := exists_conj_eq_of_forall_apply_mul_inv_mem_center hQ σ hfix
  have hc : (q₀ : G)⁻¹ * x ∈ centralizer (J : Set G) := by
    rw [mem_centralizer_iff]
    intro q hq
    have h := congrArg Subtype.val (hq₀ ⟨q, hq⟩)
    change x * q * x⁻¹ = q₀ * q * (q₀ : G)⁻¹ at h
    calc q * ((q₀ : G)⁻¹ * x) = (q₀ : G)⁻¹ * (q₀ * q * (q₀ : G)⁻¹) * x := by group
      _ = (q₀ : G)⁻¹ * (x * q * x⁻¹) * x := by rw [h]
      _ = (q₀ : G)⁻¹ * x * q := by group
  exact ⟨q₀, q₀.2, hc⟩

theorem relIndex_centralizer_ne_two_of_sq_mem_centralizer [Finite G] {H J : Subgroup G}
    (hJ : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 J) (hJH : J ≤ H)
    (hN : H ≤ normalizer (J : Set G)) (hC : H ⊓ centralizer (J : Set G) ≤ J) {x : G}
    (hxH : x ∈ H) (hxJ : x ∉ J) (hx2 : x ^ 2 ∈ centralizer (J : Set G)) :
    (centralizer ({x} : Set G)).relIndex J ≠ 2 := by
  intro hidx
  obtain ⟨j, hj, hjx⟩ := mem_sup_centralizer_of_relIndex_centralizer_eq_two hJ (hN hxH) hx2 hidx
  apply hxJ
  have hjx' : j⁻¹ * x ∈ J := hC ⟨H.mul_mem (H.inv_mem (hJH hj)) hxH, hjx⟩
  have : x = j * (j⁻¹ * x) := by group
  rw [this]
  exact J.mul_mem hj hjx'

end Ambient

end CFSG.GroupTheory
