module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {H : Type} [Group H] {Q : Subgroup H} [Module (ZMod 2) (Additive (Abelianization Q))]

private def piQ (x : Q) : Additive (Abelianization Q) :=
  Additive.ofMul (Abelianization.of x)

private lemma piQ_one : piQ (1 : Q) = 0 := by
  simp [piQ]

private lemma piQ_mul (x y : Q) : piQ (x * y) = piQ x + piQ y := by
  simp [piQ]

private lemma piQ_inv (x : Q) : piQ x⁻¹ = -piQ x := by
  simp [piQ]

private lemma piQ_eq_zero_iff (hE : IsExtraspecialPGroup 2 Q) (x : Q) :
    piQ x = 0 ↔ x ∈ Subgroup.center Q :=
  ofMul_of_eq_zero_iff hE x

private noncomputable def rhoQ [Finite Q] (hE : IsExtraspecialPGroup 2 Q)
    (hQn : Q.Normal) (g : H) :
    Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q) :=
  ((extraspecialConjOrth hE hQn g : TauCeti.QuadraticMap.orthogonalGroup
    (extraspecialQuadForm hE)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
      Additive (Abelianization Q))

private lemma rhoQ_piQ [Finite Q] (hE : IsExtraspecialPGroup 2 Q) (hQn : Q.Normal) (g : H)
    (x : Q) : rhoQ hE hQn g (piQ x) = piQ (conjAut hQn g x) :=
  extraspecialConjOrth_apply hE hQn g x

private def preimageSubgroup (U : Submodule (ZMod 2) (Additive (Abelianization Q))) :
    Subgroup Q where
  carrier := {x : Q | piQ x ∈ U}
  mul_mem' := by
    intro x y hx hy
    show piQ (x * y) ∈ U
    rw [piQ_mul]
    exact U.add_mem hx hy
  one_mem' := by
    show piQ (1 : Q) ∈ U
    rw [piQ_one]
    exact U.zero_mem
  inv_mem' := by
    intro x hx
    show piQ x⁻¹ ∈ U
    rw [piQ_inv]
    exact U.neg_mem hx

theorem forall_invariant_subgroup_iff_of_subgroup [hQn : Q.Normal] [Finite Q]
    (hE : IsExtraspecialPGroup 2 Q) (K : Subgroup H) :
    (∀ W : Subgroup H, centerOf Q ≤ W → W ≤ Q → (∀ g ∈ K, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        W = centerOf Q ∨ W = Q) ↔
      ∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
        (∀ g ∈ K, ∀ u ∈ U, ((extraspecialConjOrth hE hQn g : TauCeti.QuadraticMap.orthogonalGroup
          (extraspecialQuadForm hE)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
            Additive (Abelianization Q)) u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  constructor
  · intro hsub U hU
    let W : Subgroup H := (preimageSubgroup (Q := Q) U).map Q.subtype
    have hcenter : centerOf Q ≤ W := by
      intro x hx
      refine Subgroup.mem_map.2 ⟨⟨x, hx.1⟩, ?_, rfl⟩
      have hxc : (⟨x, hx.1⟩ : Q) ∈ Subgroup.center Q :=
        (mem_centerOf_iff (Q := Q) ⟨x, hx.1⟩).1 (by simpa using hx)
      have hzero : piQ (⟨x, hx.1⟩ : Q) = 0 := (piQ_eq_zero_iff hE _).2 hxc
      show piQ (⟨x, hx.1⟩ : Q) ∈ U
      rw [hzero]
      exact U.zero_mem
    have hWQ : W ≤ Q := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    have hinv : ∀ g ∈ K, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      intro g hg w hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hw
      refine Subgroup.mem_map.2 ⟨conjAut hQn g y, ?_, ?_⟩
      · have hmem : rhoQ hE hQn g (piQ y) ∈ U := hU g hg (piQ y) hy
        rwa [rhoQ_piQ hE hQn g y] at hmem
      · show ((conjAut hQn g y : Q) : H) = g * (y : H) * g⁻¹
        rw [conjAut_apply hQn g y]
    rcases hsub W hcenter hWQ hinv with hW | hW
    · left
      rw [Submodule.eq_bot_iff]
      intro u hu
      obtain ⟨y, rfl⟩ := exists_ofMul_of u
      have hyW : (y : H) ∈ W := Subgroup.mem_map.2 ⟨y, hu, rfl⟩
      have hyc : (y : H) ∈ centerOf Q := hW.le hyW
      exact (piQ_eq_zero_iff hE y).2 ((mem_centerOf_iff (Q := Q) y).1 hyc)
    · right
      rw [Submodule.eq_top_iff']
      intro u
      obtain ⟨y, rfl⟩ := exists_ofMul_of u
      have hyW : (y : H) ∈ W := ge_of_eq hW y.2
      obtain ⟨y', hy', hy'w⟩ := Subgroup.mem_map.1 hyW
      have hyy' : y' = y := Subtype.ext hy'w
      rw [← hyy']
      exact hy'
  · intro hsub W hcenter hWQ hinv
    let W' : Subgroup Q := W.comap Q.subtype
    let U' : AddSubgroup (Additive (Abelianization Q)) :=
      { carrier := {v | ∃ y : Q, y ∈ W' ∧ piQ y = v}
        add_mem' := by
          rintro v₁ v₂ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
          exact ⟨y₁ * y₂, W'.mul_mem hy₁ hy₂, by rw [piQ_mul]⟩
        zero_mem' := ⟨1, W'.one_mem, by rw [piQ_one]⟩
        neg_mem' := by
          rintro v ⟨y, hy, rfl⟩
          exact ⟨y⁻¹, W'.inv_mem hy, by rw [piQ_inv]⟩ }
    let U : Submodule (ZMod 2) (Additive (Abelianization Q)) :=
      AddSubgroup.toZModSubmodule 2 U'
    have hUinv : ∀ g ∈ K, ∀ u ∈ U, rhoQ hE hQn g u ∈ U := by
      intro g hg u hu
      have hu' : u ∈ U' := hu
      obtain ⟨y, hy, rfl⟩ := hu'
      rw [rhoQ_piQ hE hQn g y]
      refine ⟨conjAut hQn g y, ?_, rfl⟩
      show ((conjAut hQn g y : Q) : H) ∈ W
      rw [conjAut_apply hQn g y]
      exact hinv g hg (y : H) hy
    rcases hsub U hUinv with hbot | htop
    · left
      apply le_antisymm _ hcenter
      intro w hw
      have hwQ : w ∈ Q := hWQ hw
      have hmem : piQ (⟨w, hwQ⟩ : Q) ∈ U := ⟨⟨w, hwQ⟩, hw, rfl⟩
      rw [hbot] at hmem
      have hzero : piQ (⟨w, hwQ⟩ : Q) = 0 := by simpa using hmem
      have hc : (⟨w, hwQ⟩ : Q) ∈ Subgroup.center Q := (piQ_eq_zero_iff hE _).1 hzero
      simpa using (mem_centerOf_iff (Q := Q) ⟨w, hwQ⟩).2 hc
    · right
      apply le_antisymm hWQ
      intro y hy
      let yq : Q := ⟨y, hy⟩
      have hmem : piQ yq ∈ U := by rw [htop]; exact Submodule.mem_top
      have hmem' : piQ yq ∈ U' := hmem
      obtain ⟨y', hy', hp⟩ := hmem'
      have hcent : y' * yq⁻¹ ∈ Subgroup.center Q :=
        (piQ_eq_zero_iff hE (y' * yq⁻¹)).1 (by rw [piQ_mul, piQ_inv, hp]; abel)
      have hcentW : ((y' * yq⁻¹ : Q) : H) ∈ W :=
        hcenter ((mem_centerOf_iff (Q := Q) (y' * yq⁻¹)).2 hcent)
      have hy'W : ((y' : Q) : H) ∈ W := hy'
      have hprod : ((y' * yq⁻¹ : Q) : H)⁻¹ * (y' : H) ∈ W :=
        W.mul_mem (W.inv_mem hcentW) hy'W
      have heq : ((y' * yq⁻¹ : Q) : H)⁻¹ * (y' : H) = y := by
        show ((y' * yq⁻¹ : Q) : H)⁻¹ * (y' : H) = (yq : H)
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [heq] at hprod

theorem forall_invariant_subgroup_iff [hQn : Q.Normal] [Finite Q]
    (hE : IsExtraspecialPGroup 2 Q) :
    (∀ W : Subgroup H, centerOf Q ≤ W → W ≤ Q → (∀ g : H, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        W = centerOf Q ∨ W = Q) ↔
      ∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
        (∀ g : H, ∀ u ∈ U, ((extraspecialConjOrth hE hQn g : TauCeti.QuadraticMap.orthogonalGroup
          (extraspecialQuadForm hE)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
            Additive (Abelianization Q)) u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  simpa only [Subgroup.mem_top, true_imp_iff] using
    forall_invariant_subgroup_iff_of_subgroup hE (⊤ : Subgroup H)

end CFSG.EvenSporadicStandard.HNRecog
