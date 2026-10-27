module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64MiddleSubgroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

include hinf in
theorem degree64_middle_subgroup_full [Finite G] {D₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)} {κ₂ : ZMod 2} (hD₂N : D₂ ≤ 𝒩₂)
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂)
    (hfaith : ∀ m ∈ 𝒩₂, (∀ B : ↥(binarySymMatrices 3),
      m⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) * m =
        radHom φ he hzC hz (Multiplicative.ofAdd (B, 1))) → m ∈ ℛ) :
    ∃ F₂ E₂ : Subgroup G,
      (∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he) ∧
      E₂ ≤ F₂ ∧ IsMulCommutative E₂ ∧ Nat.card E₂ = 512 ∧
      (∀ E' : Subgroup G, E' ≤ F₂ → IsMulCommutative E' → Nat.card E' = 512 → E' = E₂) ∧
      (F₂ : Set G) = (zpowers z : Set G) * (E₂ : Set G) ∧ E₂ ⊓ ℛ = 𝒜₂ ∧
      (∀ f ∈ F₂, f ^ 2 ∈ altSub φ he) ∧
      (∀ Y : Subgroup G, Y ≤ F₂ → IsMulCommutative Y →
        4 ≤ Subgroup.relIndex 𝒜₂ (Y ⊔ 𝒜₂) → Y ≤ E₂) := by
  classical
  have hRn : ((radSub φ z e).subgroupOf D₂).Normal := ⟨fun r hr d => by
    rw [mem_subgroupOf] at hr ⊢
    exact (mem_normalizer_iff.1 (hD₂N d.2) r).1 hr⟩
  set θ := radLabelOf φ he hzC hz hinf hRD₂ with hθ
  have hθv : ∀ x, ((θ.symm x : D₂) : G) = radHom φ he hzC hz x := fun x => rfl
  have hzD : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  have hact : ∀ d : D₂, ∃ C : binarySymMatrices 3, ∀ B : binarySymMatrices 3,
      d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D₂) * d = θ.symm (.ofAdd (symThreeAffine κ₂ C B, 1)) := by
    intro d
    refine ⟨ν₂ d, fun B => Subtype.ext ?_⟩
    have h := hact₂ d d.2 B 1
    rw [symThreeAffine_eq] at h
    exact h
  have hsurj : ∀ C : binarySymMatrices 3, ∃ d : D₂, ∀ B : binarySymMatrices 3,
      d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D₂) * d = θ.symm (.ofAdd (symThreeAffine κ₂ C B, 1)) := by
    intro C
    obtain ⟨d, hd, hdC⟩ := hν₂surj C
    refine ⟨⟨d, hd⟩, fun B => Subtype.ext ?_⟩
    have h := hact₂ d hd B 1
    rw [hdC, symThreeAffine_eq] at h
    exact h
  have hfaith' : ∀ d : D₂, (∀ B : binarySymMatrices 3,
      d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D₂) * d = θ.symm (.ofAdd (B, 1))) →
        d ∈ (radSub φ z e).subgroupOf D₂ := by
    intro d h
    rw [mem_subgroupOf]
    exact hfaith d (hD₂N d.2) fun B => congrArg Subtype.val (h B)
  have hρact : ∀ (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) (ε : ZMod 2),
      leviAct he φ hzC hz hD₂n g (θ.symm (.ofAdd (B, ε)) : D₂) =
        θ.symm (.ofAdd (symThreeCongr g B, ε)) := by
    intro g B ε
    apply Subtype.ext
    rw [coe_leviAct, hθv, hθv, leviHom_conj_radHom]
  have hzθ : (⟨z, hzD⟩ : D₂) = θ.symm (.ofAdd (0, 1)) := Subtype.ext (by rw [hθv, radHom_z])
  have hA : ∀ x : D₂, x ∈ Subgroup.subgroupOf 𝒜₂ D₂ ↔ ∃ B : binarySymMatrices 3,
      x = θ.symm (.ofAdd (B, 0)) := by
    intro x
    rw [mem_subgroupOf, mem_pullSub_iff φ he]
    constructor
    · rintro ⟨B, hB⟩
      exact ⟨Multiplicative.toAdd B, Subtype.ext (by rw [hθv, radHom_tau, ofAdd_toAdd, hB])⟩
    · rintro ⟨B, rfl⟩
      exact ⟨Multiplicative.ofAdd B, by rw [hθv, radHom_tau]⟩
  have hI : ∀ x : D₂, x ∈ (altSub φ he).subgroupOf D₂ ↔ ∃ B : binarySymMatrices 3,
      (B : M₃) ∈ binaryAltMatrices 3 ∧ x = θ.symm (.ofAdd (B, 0)) := by
    intro x
    rw [mem_subgroupOf, mem_altSub]
    have hd : ∀ B : binarySymMatrices 3, symThreeDiag (B : M₃) = 0 ↔
        (B : M₃) ∈ binaryAltMatrices 3 := fun B => by
      rw [mem_binaryAltMatrices]
      exact ⟨fun h => ⟨B.2, fun i => congrFun h i⟩, fun h => funext h.2⟩
    constructor
    · rintro ⟨B, hB, hBx⟩
      exact ⟨B, (hd B).1 hB, Subtype.ext (by rw [hθv, radHom_tau, hBx])⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, (hd B).2 hB, by rw [hθv, radHom_tau]⟩
  obtain ⟨-, -, -, F, hF, -, -, -, hFsq, E, ⟨hEF, hEc, hEcard⟩, huniq, -, -, -, hFzE, hER, hY,
    -⟩ :=
    binary_symmetric_three_full_coset_characteristic_abelian_middle_subgroup
      ((radSub φ z e).subgroupOf D₂) θ κ₂ hact hsurj hfaith' (leviAct he φ hzC hz hD₂n) hρact
      ⟨z, hzD⟩ hzθ (Subgroup.subgroupOf 𝒜₂ D₂) ((altSub φ he).subgroupOf D₂) hA hI
  have hmemF : ∀ {x : G}, x ∈ F.map D₂.subtype ↔ ∃ h : x ∈ D₂, (⟨x, h⟩ : D₂) ∈ F :=
    mem_map_subtype_iff
  have hEc' : IsMulCommutative (E.map D₂.subtype) := by
    have := hEc
    infer_instance
  have hEcard' : Nat.card (E.map D₂.subtype) = 512 := by
    rw [card_map_of_injective D₂.subtype_injective, hEcard]
  have huniq' : ∀ E' : Subgroup G, E' ≤ F.map D₂.subtype → IsMulCommutative E' →
      Nat.card E' = 512 → E' = E.map D₂.subtype := by
    intro E' hE'F hE'c hE'card
    have hE'D : E' ≤ D₂ := hE'F.trans (map_subtype_le _)
    have h1 : E'.subgroupOf D₂ ≤ F := fun x hx => by
      rw [mem_subgroupOf] at hx
      obtain ⟨h, hxF⟩ := hmemF.1 (hE'F hx)
      exact hxF
    have h2 := huniq (E'.subgroupOf D₂) h1 inferInstance
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hE'D).toEquiv, hE'card])
    rw [← h2, subgroupOf_map_subtype, inf_of_le_left hE'D]
  refine ⟨F.map D₂.subtype, E.map D₂.subtype, fun d => ?_, map_mono hEF, hEc', hEcard', huniq',
    ?_, ?_, fun f hf => ?_, fun Y hYF hYc hYi => ?_⟩
  · rw [hmemF]
    constructor
    · rintro ⟨h, hdF⟩
      refine ⟨h, ?_⟩
      have h1 := (hF _).1 hdF
      rw [mem_subgroupOf] at h1
      exact h1
    · rintro ⟨h, hd⟩
      exact ⟨h, (hF _).2 (by rw [mem_subgroupOf]; exact hd)⟩
  · rw [coe_map, hFzE, Set.image_mul, ← coe_map, ← coe_map, MonoidHom.map_zpowers]
    rfl
  · have h1 := congrArg (Subgroup.map D₂.subtype) hER
    rw [Subgroup.map_inf_eq _ _ _ D₂.subtype_injective, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_of_le_left hRD₂] at h1
    rw [h1, inf_of_le_left (le_sup_left.trans hRD₂)]
  · obtain ⟨hfD, hfF⟩ := hmemF.1 hf
    have h1 : (⟨f, hfD⟩ : D₂) ^ 2 ∈ (altSub φ he).subgroupOf D₂ := by
      rw [← hFsq]
      exact subset_closure ⟨_, hfF, rfl⟩
    rw [mem_subgroupOf, Subgroup.coe_pow] at h1
    exact h1
  · have hYD : Y ≤ D₂ := hYF.trans (map_subtype_le _)
    have hAD : 𝒜₂ ≤ D₂ := le_sup_left.trans hRD₂
    have h1 : Y.subgroupOf D₂ ≤ F := fun x hx => by
      rw [mem_subgroupOf] at hx
      obtain ⟨h, hxF⟩ := hmemF.1 (hYF hx)
      exact hxF
    have hYc' : IsMulCommutative (Y.subgroupOf D₂) := ⟨⟨fun x y => by
      have hx : ((x : D₂) : G) ∈ Y := mem_subgroupOf.1 x.2
      have hy : ((y : D₂) : G) ∈ Y := mem_subgroupOf.1 y.2
      have h := hYc.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩
      apply Subtype.ext
      apply Subtype.ext
      change ((x : D₂) : G) * ((y : D₂) : G) = ((y : D₂) : G) * ((x : D₂) : G)
      exact congrArg (fun w : Y => (w : G)) h⟩⟩
    have h2 : 4 ≤ (Subgroup.subgroupOf 𝒜₂ D₂).relIndex (Y.subgroupOf D₂ ⊔
        Subgroup.subgroupOf 𝒜₂ D₂) := by
      rw [← subgroupOf_sup hYD hAD, relIndex_subgroupOf (sup_le hYD hAD)]
      exact hYi
    have h3 := hY (Y.subgroupOf D₂) h1 hYc' h2
    intro y hy
    exact ⟨⟨y, hYD hy⟩, h3 (by rw [mem_subgroupOf]; exact hy), rfl⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
