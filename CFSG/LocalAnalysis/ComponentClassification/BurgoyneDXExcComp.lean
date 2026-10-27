module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup CFSG.ComponentClassification.TBLit

variable {L P : Type} [Group L] [Group P]

theorem mem_autFixed_iff {G : Type*} [Group G] (σ : MulAut G) (x : G) :
    x ∈ autFixed σ ↔ σ x = x := Iff.rfl

theorem autFixed_le_comap (ν : L →* P) {s : MulAut L} {s' : MulAut P}
    (hs : ∀ x, ν (s x) = s' (ν x)) : autFixed s ≤ (autFixed s').comap ν := by
  intro x hx
  rw [mem_comap, mem_autFixed_iff, ← hs]
  rw [mem_autFixed_iff] at hx
  rw [hx]

theorem autFixed_normal_comap (ν : L →* P) (hker : ν.ker ≤ center L) {s : MulAut L}
    {s' : MulAut P} (hs : ∀ x, ν (s x) = s' (ν x)) :
    ((autFixed s).subgroupOf ((autFixed s').comap ν)).Normal := by
  refine ⟨fun f hf d => ?_⟩
  rw [mem_subgroupOf, mem_autFixed_iff] at hf ⊢
  have hd : s d * (d : L)⁻¹ ∈ center L := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs]
    have := d.2
    rw [mem_comap, mem_autFixed_iff] at this
    rw [this, mul_inv_cancel]
  set z := s d * (d : L)⁻¹ with hz
  have hsd : s d = z * d := by rw [hz, inv_mul_cancel_right]
  have hzc : ∀ y : L, y * z = z * y := fun y => mem_center_iff.mp hd y
  change s ((d : L) * f * (d : L)⁻¹) = (d : L) * f * (d : L)⁻¹
  rw [map_mul, map_mul, map_inv, hsd, hf]
  calc z * ↑d * ↑f * (z * ↑d)⁻¹ = z * (↑d * ↑f * (↑d)⁻¹) * z⁻¹ := by group
    _ = ↑d * ↑f * (↑d)⁻¹ := by rw [← hzc, mul_assoc, mul_inv_cancel, mul_one]

variable [Finite L] [Finite P]

theorem isPComponent_map_autFixed (ν : L →* P) (hν : Function.Surjective ν)
    (hker : ν.ker ≤ center L) (h2 : IsPGroup 2 ν.ker) {s : MulAut L} {s' : MulAut P}
    (hs : ∀ x, ν (s x) = s' (ν x)) {Q : Subgroup L} (hQs : Q ≤ autFixed s)
    (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s))) :
    Q.map ν ≤ autFixed s' ∧ IsPComponent 2 ((Q.map ν).subgroupOf (autFixed s')) := by
  set D := (autFixed s').comap ν with hD
  have hsD : autFixed s ≤ D := autFixed_le_comap ν hs
  have hQs' : Q.map ν ≤ autFixed s' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsD (hQs hx)
  refine ⟨hQs', ?_⟩
  have hQc' := (CatalogueBAlternating.pComponent_two_iff _).mp hQc
  have hQD := TwoComponentTransport.extend_nested Q (autFixed s) D hQs hsD
    (autFixed_normal_comap ν hker hs).isSubnormal hQc'
  let νD : D →* autFixed s' := (ν.comp D.subtype).codRestrict (autFixed s') fun d => d.2
  have hνD : Function.Surjective νD := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hν y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hkerD : ∀ d : D, νD d = 1 ↔ ν d = 1 := fun d =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcen : νD.ker ≤ center D := by
    intro d hd
    have h1 : (d : L) ∈ center L := hker ((hkerD d).mp hd)
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp h1 g)
  have h2D : IsPGroup 2 νD.ker := by
    intro d
    obtain ⟨k, hk⟩ := h2 ⟨((d : D) : L), (hkerD d).mp d.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : ν.ker => (y : L)) hk
    simpa using this
  have himg := CentralTwoKernelComponents.image νD hνD hcen h2D (Q.subgroupOf D) hQD
  have hmap : (Q.subgroupOf D).map νD = (Q.map ν).subgroupOf (autFixed s') := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hx
      rw [mem_subgroupOf]
      exact ⟨x, hx, rfl⟩
    · intro hy
      rw [mem_subgroupOf] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hxD : x ∈ D := by
        rw [hD, mem_comap, hxy]
        exact y.2
      exact ⟨⟨x, hxD⟩, mem_subgroupOf.mpr hx, Subtype.ext hxy⟩
  rw [hmap] at himg
  exact (CatalogueBAlternating.pComponent_two_iff _).mpr himg

end CFSG.ComponentClassification.Burgoyne.DX
