module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Ord
public import CFSG.GH74.Generic.S45.LQData
public import CFSG.GH74.Generic.S45.LOddPSU

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem conj_injective_of_center_eq_bot {K : Type} [Group K] (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center K := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut K => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem exists_conj_component {K : Type} [Group K] (hZ : center K = ⊥) (z : MulAut K)
    {B : Subgroup K} (hBle : B ≤ fixedSubgroup K z)
    (hB : CFSG.IsComponent (B.subgroupOf (fixedSubgroup K z))) :
    ∃ L' : Subgroup (MulAut K),
      CFSG.Assembly.IsComponentOf L' (inner K ⊓ Subgroup.centralizer ({z} : Set (MulAut K))) ∧
        Nonempty (↥B ≃* ↥L') := by
  classical
  have hι := conj_injective_of_center_eq_bot hZ
  let ι : K →* MulAut K := MulAut.conj
  let D : Subgroup (MulAut K) := inner K ⊓ Subgroup.centralizer ({z} : Set (MulAut K))
  have hconj : ∀ s : K, z * MulAut.conj s * z⁻¹ = MulAut.conj (z s) := fun s => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hmemD : ∀ s : K, ι s ∈ D ↔ s ∈ fixedSubgroup K z := by
    intro s
    constructor
    · intro hD
      have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hD).2
      show z s = s
      apply hι
      have h1 := hconj s
      calc MulAut.conj (z s) = z * MulAut.conj s * z⁻¹ := h1.symm
        _ = (MulAut.conj s * z) * z⁻¹ := by rw [← h]
        _ = MulAut.conj s := by group
    · intro h
      have h' : z s = s := h
      refine Subgroup.mem_inf.2 ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hconj s
      rw [h'] at h1
      calc MulAut.conj s * z = (z * MulAut.conj s * z⁻¹) * z := by rw [h1]
        _ = z * MulAut.conj s := by group
  let f : ↥(fixedSubgroup K z) →* ↥D :=
    (ι.comp (fixedSubgroup K z).subtype).codRestrict D (fun x => (hmemD x).2 x.2)
  have hfs : Function.Surjective f := by
    rintro ⟨x, hxD⟩
    obtain ⟨⟨s, rfl⟩, hxc⟩ := Subgroup.mem_inf.1 hxD
    exact ⟨⟨s, (hmemD s).1 hxD⟩, rfl⟩
  have hfn : f.range.Normal := by
    rw [MonoidHom.range_eq_top_of_surjective f hfs]
    infer_instance
  have hsubD := CFSG.GH74.Generic.S45.LAlt.isSubnormal_map_of_normal_range f hfn hB.2
  let L' : Subgroup (MulAut K) := B.map ι
  have hL'D : L' ≤ D := by
    rintro _ ⟨l, hl, rfl⟩
    exact (hmemD l).2 (hBle hl)
  have heq : ((B.subgroupOf (fixedSubgroup K z)).map f) = L'.subgroupOf D := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hc, hcx⟩
      exact ⟨c, hc, congrArg Subtype.val hcx⟩
    · rintro ⟨l, hl, hlx⟩
      exact ⟨⟨l, hBle hl⟩, hl, Subtype.ext hlx⟩
  let eLb : ↥B ≃* ↥L' :=
    MulEquiv.ofBijective (ι.subgroupMap B)
      ⟨fun a b hab => Subtype.ext (hι (congrArg Subtype.val hab)), ι.subgroupMap_surjective B⟩
  let e2 : ↥(L'.subgroupOf D) ≃* ↥(B.subgroupOf (fixedSubgroup K z)) :=
    (Subgroup.subgroupOfEquivOfLe hL'D).trans
      (eLb.symm.trans (Subgroup.subgroupOfEquivOfLe hBle).symm)
  refine ⟨L', ?_, ⟨eLb⟩⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL'D]
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv e2.symm hB.1, by rw [← heq]; exact hsubD⟩

theorem center_eq_bot_of_simple_of_nonab {K : Type} [Group K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) : center K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

end CFSG.GH74.GLS.IVK.Proofs2

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS.IVK.Proofs2
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem Ivk714Hyp.nonabelian {K : Type} [Group K] [Finite K] {z : MulAut K} (h : Ivk714Hyp K z) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨H, -, x, -, y, -, hxy⟩ := h.exists_nonabelian_two_subgroup
  exact ⟨x, y, hxy⟩

theorem Ivk714Hyp.exists_inner_component {K : Type} [Group K] [Finite K] (hZ : center K = ⊥)
    {z : MulAut K} (h : Ivk714Hyp K z) :
    ∃ L : Subgroup (MulAut K), L ≤ inner K ∧
      CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({z} : Set (MulAut K))) ∧
      Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 7)) ∧ Odd (Nat.card ↥(center ↥L)) := by
  obtain ⟨B, hB, -, ⟨hq⟩, hodd⟩ := h.exists_component
  have hBle : B ≤ fixedSubgroup K z := hB.1
  have hBn : CFSG.IsComponent (B.subgroupOf (fixedSubgroup K z)) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hBle).1 hB
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_conj_component hZ z hBle hBn
  refine ⟨L, hL.1.trans inf_le_left,
    CFSG.GH74.Generic.S45.isComponentOf_of_normal_inf' (inner_normal K) hL, ?_, ?_⟩
  · exact ⟨(CFSG.ComponentClassification.ExcSelector.centralQuotientCongr e).symm.trans hq⟩
  · have hc : (center ↥B).map e.toMonoidHom = center ↥L := Subgroup.map_center_eq e
    rw [← hc, Subgroup.card_map_of_injective e.injective]
    exact hodd

end CFSG.GH74.GLS.IVK
