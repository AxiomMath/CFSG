module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

private theorem commutatorElement_mul_center {x x' z z' : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) :
    ⁅x * z, x' * z'⁆ = ⁅x, x'⁆ := by
  have hz_comm : ∀ g : G, Commute z g := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have hz'_comm : ∀ g : G, Commute z' g := fun g => (Subgroup.mem_center_iff.mp hz' g).symm
  rw [commutatorElement_mul_left_eq_conj_mul, (hz_comm (x' * z')).commutator_eq,
    commutatorElement_mul_right_eq_mul_conj, (hz'_comm x).symm.commutator_eq]
  group

private theorem nonempty_equiv_ctrQ_map {G' : Type} [Group G'] (K : Subgroup G) (f : G →* G')
    (hf : Function.Injective f) :
    Nonempty (K ⧸ Subgroup.center ↥K ≃* (K.map f) ⧸ Subgroup.center ↥(K.map f)) := by
  refine ⟨QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥(K.map f))
    (Subgroup.equivMapOfInjective K f hf) ?_⟩
  exact Subgroup.map_center_eq _

theorem ctrQ_dvd_of_le [Finite G] {X Y : Subgroup G} (h : X ≤ Y) : ctrQ X ∣ ctrQ Y := by
  let ψ : ↥X →* ↥Y := Subgroup.inclusion h
  let φ : ↥X →* ↥Y ⧸ Subgroup.center ↥Y := (QuotientGroup.mk' (Subgroup.center ↥Y)).comp ψ
  have hψinj : Function.Injective ψ := Subgroup.inclusion_injective h
  have hker : φ.ker = (Subgroup.center ↥Y).comap ψ := by
    change ((QuotientGroup.mk' (Subgroup.center ↥Y)).comp ψ).ker =
      (Subgroup.center ↥Y).comap ψ
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hKle : φ.ker ≤ Subgroup.center ↥X := by
    rw [hker]
    exact Subgroup.comap_center_le_center (f := ψ) hψinj
  have h1 : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ Nat.card (↥X ⧸ φ.ker) := by
    have hq := Subgroup.card_quotient_dvd_card
      ((Subgroup.center ↥X).map (QuotientGroup.mk' φ.ker))
    rw [← Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient φ.ker
      (Subgroup.center ↥X) hKle).toEquiv]
    exact hq
  have h2 : Nat.card (↥X ⧸ φ.ker) ∣ Nat.card (↥Y ⧸ Subgroup.center ↥Y) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card φ.range
  exact h1.trans h2

theorem equiv_ctrQ_of_le_of_ctrQ_eq [Finite G] {X Y : Subgroup G} (h : X ≤ Y)
    (hc : ctrQ X = ctrQ Y) :
    Y = X ⊔ centerIn Y ∧ Nonempty (X ⧸ center X ≃* Y ⧸ center Y) := by
  let ψ : ↥X →* ↥Y := Subgroup.inclusion h
  let φ : ↥X →* ↥Y ⧸ Subgroup.center ↥Y := (QuotientGroup.mk' (Subgroup.center ↥Y)).comp ψ
  have hψinj : Function.Injective ψ := Subgroup.inclusion_injective h
  have hker : φ.ker = (Subgroup.center ↥Y).comap ψ := by
    change ((QuotientGroup.mk' (Subgroup.center ↥Y)).comp ψ).ker =
      (Subgroup.center ↥Y).comap ψ
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hKle : φ.ker ≤ Subgroup.center ↥X := by
    rw [hker]
    exact Subgroup.comap_center_le_center (f := ψ) hψinj
  have hc' : Nat.card (↥X ⧸ Subgroup.center ↥X) =
      Nat.card (↥Y ⧸ Subgroup.center ↥Y) := hc
  have h1 : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ Nat.card (↥X ⧸ φ.ker) := by
    have hq := Subgroup.card_quotient_dvd_card
      ((Subgroup.center ↥X).map (QuotientGroup.mk' φ.ker))
    rw [← Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient φ.ker
      (Subgroup.center ↥X) hKle).toEquiv]
    exact hq
  have h2 : Nat.card (↥X ⧸ φ.ker) ∣ Nat.card (↥Y ⧸ Subgroup.center ↥Y) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hba : Nat.card (↥X ⧸ φ.ker) ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
    rw [hc']
    exact h2
  have hab : Nat.card (↥X ⧸ φ.ker) = Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    (Nat.dvd_antisymm h1 hba).symm
  have hkerindex : φ.ker.index = (Subgroup.center ↥X).index := hab
  have hrel : φ.ker.relIndex (Subgroup.center ↥X) = 1 := by
    have hmul := Subgroup.relIndex_mul_index hKle
    rw [hkerindex] at hmul
    have he : (Subgroup.center ↥X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero he) (by rw [one_mul]; exact hmul)
  have hker_eq : φ.ker = Subgroup.center ↥X :=
    le_antisymm hKle (Subgroup.relIndex_eq_one.mp hrel)
  have hbc : Nat.card (↥X ⧸ φ.ker) = Nat.card (↥Y ⧸ Subgroup.center ↥Y) :=
    Nat.dvd_antisymm h2 (by rw [← hc']; exact h1)
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact hbc
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hrange
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hker_eq).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx⟩ := hsurj (QuotientGroup.mk' (Subgroup.center ↥Y) (⟨y, hy⟩ : ↥Y))
    have hx' : QuotientGroup.mk' (Subgroup.center ↥Y) (Subgroup.inclusion h x) =
        QuotientGroup.mk' (Subgroup.center ↥Y) (⟨y, hy⟩ : ↥Y) := hx
    let c : ↥Y := Subgroup.inclusion h x / (⟨y, hy⟩ : ↥Y)
    have hcZ : c ∈ Subgroup.center ↥Y := QuotientGroup.eq_iff_div_mem.mp hx'
    have hcG : ((c⁻¹ : ↥Y) : G) ∈ centerIn Y :=
      Subgroup.mem_map_of_mem Y.subtype ((Subgroup.center ↥Y).inv_mem hcZ)
    have hy_eq : (⟨y, hy⟩ : ↥Y) = c⁻¹ * Subgroup.inclusion h x := by
      change (⟨y, hy⟩ : ↥Y) =
        (Subgroup.inclusion h x / (⟨y, hy⟩ : ↥Y))⁻¹ * Subgroup.inclusion h x
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    have hyG : (y : G) = ((c⁻¹ : ↥Y) : G) * (x : G) := by
      have := congrArg (Subtype.val : ↥Y → G) hy_eq
      simpa using this
    rw [hyG]
    exact (X ⊔ centerIn Y).mul_mem (Subgroup.mem_sup_right hcG) (Subgroup.mem_sup_left x.2)
  · refine sup_le h ?_
    rintro _ ⟨z, -, rfl⟩
    exact z.2

theorem eq_of_le_of_ctrQ_eq [Finite G] {X Y : Subgroup G} (hY : IsQuasisimple Y) (h : X ≤ Y)
    (hc : ctrQ X = ctrQ Y) : X = Y := by
  obtain ⟨hYeq, -⟩ := equiv_ctrQ_of_le_of_ctrQ_eq h hc
  refine le_antisymm h ?_
  have hZY : centerIn Y ≤ Y := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hZsub : (centerIn Y).subgroupOf Y = Subgroup.center ↥Y := by
    change ((Subgroup.center ↥Y).map Y.subtype).comap Y.subtype = Subgroup.center ↥Y
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have hAZ : (X.subgroupOf Y) ⊔ Subgroup.center ↥Y = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup (A := X) (A' := centerIn Y) (B := Y) h hZY
    rw [hZsub] at hsup
    rw [← hYeq, Subgroup.subgroupOf_self] at hsup
    exact hsup.symm
  have hcomm : ⁅(X.subgroupOf Y) ⊔ Subgroup.center ↥Y,
      (X.subgroupOf Y) ⊔ Subgroup.center ↥Y⁆ ≤ X.subgroupOf Y := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have ha' : a ∈ (↑(X.subgroupOf Y) : Set ↥Y) * (↑(Subgroup.center ↥Y) : Set ↥Y) := by
      rw [← Subgroup.mul_normal (X.subgroupOf Y) (Subgroup.center ↥Y)]
      exact ha
    have hb' : b ∈ (↑(X.subgroupOf Y) : Set ↥Y) * (↑(Subgroup.center ↥Y) : Set ↥Y) := by
      rw [← Subgroup.mul_normal (X.subgroupOf Y) (Subgroup.center ↥Y)]
      exact hb
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := Set.mem_mul.mp ha'
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := Set.mem_mul.mp hb'
    rw [commutatorElement_mul_center hz₁ hz₂]
    exact (X.subgroupOf Y).mul_mem
      ((X.subgroupOf Y).mul_mem
        ((X.subgroupOf Y).mul_mem ha₁ ha₂) ((X.subgroupOf Y).inv_mem ha₁))
      ((X.subgroupOf Y).inv_mem ha₂)
  have hle : commutator ↥Y ≤ X.subgroupOf Y := by
    change ⁅(⊤ : Subgroup ↥Y), ⊤⁆ ≤ X.subgroupOf Y
    rw [← hAZ]
    exact hcomm
  have hperf : commutator ↥Y = ⊤ := Group.isPerfect_def.mp hY.1
  rw [hperf] at hle
  exact Subgroup.subgroupOf_eq_top.mp (top_le_iff.mp hle)

theorem ctrQ_conjugate (K : Subgroup G) (g : G) : ctrQ (CFSG.conjugate K g) = ctrQ K := by
  have hK : CFSG.conjugate K g = K.map (MulAut.conj g⁻¹).toMonoidHom := rfl
  rw [hK]
  obtain ⟨e⟩ := nonempty_equiv_ctrQ_map K (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective
  exact (Nat.card_congr e.toEquiv).symm

theorem nonempty_equiv_ctrQ_conjugate (K : Subgroup G) (g : G) :
    Nonempty (K ⧸ center K ≃* CFSG.conjugate K g ⧸ center (CFSG.conjugate K g)) := by
  have hK : CFSG.conjugate K g = K.map (MulAut.conj g⁻¹).toMonoidHom := rfl
  rw [hK]
  exact nonempty_equiv_ctrQ_map K (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective

end CFSG.OddStandard.SmallF3.Omega
