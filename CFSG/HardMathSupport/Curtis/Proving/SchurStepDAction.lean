module

public import CFSG.HardMathSupport.Curtis.Proving.BlockUZModule

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjU {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ↥(blockU L) →* ↥(blockU L) where
  toFun u := ⟨g * u * g⁻¹, blockU_conj_mem_normalizer hg u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjU_coe {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (u : ↥(blockU L)) : ((conjU hg u : ↥(blockU L)) : G) = g * u * g⁻¹ := rfl

theorem conjU_mem_blockZ {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (u : ↥(blockU L)) (hu : u ∈ (blockZ L).subgroupOf (blockU L)) :
    conjU hg u ∈ (blockZ L).subgroupOf (blockU L) :=
  Subgroup.mem_subgroupOf.2 (blockZ_conj_mem_normalizer hg (Subgroup.mem_subgroupOf.1 hu))

@[expose] def actUZ {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    UZ L →* UZ L :=
  QuotientGroup.map _ _ (conjU hg)
    (fun u hu => Subgroup.mem_comap.2 (conjU_mem_blockZ hg u hu))

@[expose] def rhoLin {L : Subgroup G} [Fact (IsShort2 L)] {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    Module.End (ZMod 2) (Additive (UZ L)) :=
  (MonoidHom.toAdditive (actUZ hg)).toZModLinearMap 2

@[expose] def piU (L : Subgroup G) (u : ↥(blockU L)) : Additive (UZ L) :=
  Additive.ofMul (QuotientGroup.mk u : UZ L)

theorem rhoLin_piU {L : Subgroup G} [Fact (IsShort2 L)] {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (u : ↥(blockU L)) :
    rhoLin hg (piU L u) = piU L (conjU hg u) := rfl

theorem piU_mul {L : Subgroup G} (x y : ↥(blockU L)) :
    piU L (x * y) = piU L x + piU L y := by
  unfold piU
  rw [QuotientGroup.mk_mul, ofMul_mul]

theorem piU_inv {L : Subgroup G} (x : ↥(blockU L)) :
    piU L x⁻¹ = -piU L x := by
  unfold piU
  rw [QuotientGroup.mk_inv, ofMul_inv]

theorem piU_eq_zero_iff {L : Subgroup G} (u : ↥(blockU L)) :
    piU L u = 0 ↔ (u : G) ∈ blockZ L := by
  unfold piU
  rw [← Subgroup.mem_subgroupOf]
  exact (QuotientGroup.eq_one_iff u).trans Iff.rfl

theorem piU_surj {L : Subgroup G} (v : Additive (UZ L)) : ∃ u : ↥(blockU L), piU L u = v := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  exact ⟨u, by unfold piU; rw [hu]; rfl⟩

theorem conjU_comm_of_centralizes {L : Subgroup G} [hL : Fact (IsShort2 L)] {a l : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ Subgroup.normalizer (L : Set G))
    (hc : a * l * a⁻¹ * l⁻¹ ∈ blockQ L) (u : ↥(blockU L)) :
    conjU hl (conjU ha u) = conjU ha (conjU hl u) := by
  apply Subtype.ext
  simp only [conjU_coe]
  have hW : l * (a * (u : G) * a⁻¹) * l⁻¹ ∈ blockU L :=
    blockU_conj_mem_normalizer hl (blockU_conj_mem_normalizer ha u.2)
  have hcW : (a * l * a⁻¹ * l⁻¹) * (l * (a * (u : G) * a⁻¹) * l⁻¹) =
      (l * (a * (u : G) * a⁻¹) * l⁻¹) * (a * l * a⁻¹ * l⁻¹) :=
    Subgroup.mem_centralizer_iff.1 (blockU_mem_centralizer_blockQ hL.out hW) _ hc
  have e : a * ((l : G) * (u : G) * l⁻¹) * a⁻¹ =
      (a * l * a⁻¹ * l⁻¹) * (l * (a * (u : G) * a⁻¹) * l⁻¹) * (a * l * a⁻¹ * l⁻¹)⁻¹ := by
    group
  rw [e, hcW, mul_inv_cancel_right]

theorem rhoLin_comm {L : Subgroup G} [Fact (IsShort2 L)] {a l : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ u : ↥(blockU L), conjU hl (conjU ha u) = conjU ha (conjU hl u)) :
    rhoLin hl * rhoLin ha = rhoLin ha * rhoLin hl := by
  apply LinearMap.ext
  intro v
  obtain ⟨u, rfl⟩ := piU_surj v
  simp only [Module.End.mul_apply, rhoLin_piU, hcomm]

theorem mem_blockZ_of_piU_eq {L : Subgroup G} {x u : G} (hx : x ∈ blockU L) (hu : u ∈ blockU L)
    (h : piU L ⟨x, hx⟩ = piU L ⟨u, hu⟩) : x⁻¹ * u ∈ blockZ L := by
  have hxu : x⁻¹ * u ∈ blockU L := (blockU L).mul_mem ((blockU L).inv_mem hx) hu
  refine (piU_eq_zero_iff ⟨x⁻¹ * u, hxu⟩).1 ?_
  have e : (⟨x⁻¹ * u, hxu⟩ : ↥(blockU L)) = ⟨x, hx⟩⁻¹ * ⟨u, hu⟩ := rfl
  rw [e, piU_mul, piU_inv, h, neg_add_cancel]

end CFSG.HardMathSupport.Curtis.Proving

end
