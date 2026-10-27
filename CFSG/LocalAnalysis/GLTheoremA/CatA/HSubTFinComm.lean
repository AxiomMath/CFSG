module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open
open scoped commutatorElement

theorem isSubnormal_comap_open {G H : Type} [Group G] [Group H] (f : G →* H) {A B : Subgroup H}
    (h : IsSubnormal A B) : IsSubnormal (A.comap f) (B.comap f) := by
  induction h with
  | refl A => exact IsSubnormal.refl _
  | @step H' M' K' hHM hn _ ih =>
    refine IsSubnormal.step (Subgroup.comap_mono hHM) ?_ ih
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    have hfn : f (n : G) ∈ H' := hn'
    have hfM : f (n : G) ∈ M' := n.2
    have hfg : f (g : G) ∈ M' := g.2
    have hA := hn.conj_mem ⟨f (n : G), hfM⟩ (Subgroup.mem_subgroupOf.mpr hfn) ⟨f (g : G), hfg⟩
    rw [Subgroup.mem_subgroupOf] at hA
    simpa [map_mul, map_inv] using hA

theorem commutator_self_le {G : Type} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutator_subgroupOf_normal {G : Type} [Group G] {H M : Subgroup G} (hHM : H ≤ M)
    (hn : (H.subgroupOf M).Normal) : (⁅H, H⁆.subgroupOf M).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  set f : G →* G := (MulAut.conj (g : G)).toMonoidHom with hf
  have hmapH : H.map f ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hn.conj_mem ⟨y, hHM hy⟩ (Subgroup.mem_subgroupOf.mpr hy) g)
  have hmap : ⁅H, H⁆.map f ≤ ⁅H, H⁆ := by
    rw [hf, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmapH hmapH
  exact hmap (Subgroup.mem_map_of_mem f hx)

theorem isSubnormal_commutator_open {G : Type} [Group G] {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal ⁅H, H⁆ K := by
  induction h with
  | refl H =>
    refine IsSubnormal.step (commutator_self_le H) ?_ (IsSubnormal.refl H)
    exact commutator_subgroupOf_normal le_rfl
      ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (H.mul_mem (H.mul_mem g.2
        (Subgroup.mem_subgroupOf.mp hn)) (H.inv_mem g.2))⟩
  | step hHM hn hMK _ =>
    exact IsSubnormal.step ((commutator_self_le _).trans hHM)
      (commutator_subgroupOf_normal hHM hn) hMK

theorem commutatorElement_central_left {G : Type} [Group G] {z p q : G}
    (hz : z ∈ Subgroup.center G) : ⁅z * p, q⁆ = ⁅p, q⁆ := by
  have hX : ∀ X : G, z * X * z⁻¹ = X := fun X => by
    rw [← Subgroup.mem_center_iff.mp hz X]
    simp
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have e : z * p * q * (p⁻¹ * z⁻¹) = z * (p * q * p⁻¹) * z⁻¹ := by group
  rw [e, hX]

theorem commutatorElement_central_right {G : Type} [Group G] {z p q : G}
    (hz : z ∈ Subgroup.center G) : ⁅p, z * q⁆ = ⁅p, q⁆ := by
  have hX : ∀ X : G, z * X * z⁻¹ = X := fun X => by
    rw [← Subgroup.mem_center_iff.mp hz X]
    simp
  have hpz : p * z = z * p := Subgroup.mem_center_iff.mp hz p
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have e : p * (z * q) * p⁻¹ * (q⁻¹ * z⁻¹) = z * (p * q * p⁻¹ * q⁻¹) * z⁻¹ := by
    calc p * (z * q) * p⁻¹ * (q⁻¹ * z⁻¹) = (p * z) * q * p⁻¹ * (q⁻¹ * z⁻¹) := by group
      _ = (z * p) * q * p⁻¹ * (q⁻¹ * z⁻¹) := by rw [hpz]
      _ = z * (p * q * p⁻¹ * q⁻¹) * z⁻¹ := by group
  rw [e, hX]

theorem commutatorElement_central_mul {G : Type} [Group G] {z z' p q : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) :
    ⁅z * p, z' * q⁆ = ⁅p, q⁆ := by
  rw [commutatorElement_central_left hz, commutatorElement_central_right hz']

theorem openQuasisimple_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  refine ⟨?_, ?_⟩
  · have htop : (⊤ : Subgroup A).map e.toMonoidHom = ⊤ := by
      ext x
      simp
    have hA1 : ⁅(⊤ : Subgroup A), ⊤⁆ = ⊤ := hA.1
    have h1 := Subgroup.map_commutator (f := e.toMonoidHom) (H₁ := (⊤ : Subgroup A)) (H₂ := ⊤)
    rw [hA1, htop] at h1
    exact h1.symm
  · haveI := hA.2
    exact MulEquiv.isSimpleGroup (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).symm

theorem isComponentOf_map_of_injective {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {A B : Subgroup G} (h : IsComponentOf A B) :
    IsComponentOf (A.map f) (B.map f) :=
  ⟨Subgroup.map_mono h.1, CFSG.ComponentClassification.Components.chain_map f h.2.1,
    openQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective A f hf) h.2.2⟩

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
