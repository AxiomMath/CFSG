module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem aor_conjugate_centralizer (L : Subgroup G) (g : G) :
    CFSG.conjugate (centralizer (L : Set G)) g =
      centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' : g * y * g⁻¹ ∈ L := (mem_conjugate_iff L g y).mp hy
    have h1 : (g * y * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * y * g⁻¹) := h _ hy'
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (x * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ CFSG.conjugate L g := by
      rw [mem_conjugate_iff]
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    have h1 := h (g⁻¹ * y * g) hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * y := by group

theorem aor_oddInner_conjugate {L : Subgroup G} (h : Asc82OddInner L) (g : G) :
    Asc82OddInner (CFSG.conjugate L g) := by
  intro y hy hodd
  set y' : G := g * y * g⁻¹ with hy'def
  have hy'mem : y' ∈ normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hz' : g⁻¹ * z * g ∈ CFSG.conjugate L g := by
        rw [mem_conjugate_iff]
        rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
      have h1 : y * (g⁻¹ * z * g) * y⁻¹ ∈ CFSG.conjugate L g :=
        ((Subgroup.mem_normalizer_iff.mp hy) (g⁻¹ * z * g)).mp hz'
      have h2 : g * (y * (g⁻¹ * z * g) * y⁻¹) * g⁻¹ ∈ L :=
        (mem_conjugate_iff L g (y * (g⁻¹ * z * g) * y⁻¹)).mp h1
      rwa [show y' * z * y'⁻¹ = g * (y * (g⁻¹ * z * g) * y⁻¹) * g⁻¹ by
        rw [hy'def]; group]
    · intro hz
      have h1 : y * (g⁻¹ * z * g) * y⁻¹ ∈ CFSG.conjugate L g :=
        (mem_conjugate_iff L g (y * (g⁻¹ * z * g) * y⁻¹)).mpr (by
          rwa [show g * (y * (g⁻¹ * z * g) * y⁻¹) * g⁻¹ = y' * z * y'⁻¹ by
            rw [hy'def]; group])
      have hz' : g⁻¹ * z * g ∈ CFSG.conjugate L g :=
        ((Subgroup.mem_normalizer_iff.mp hy) (g⁻¹ * z * g)).mpr h1
      have h2 : g * (g⁻¹ * z * g) * g⁻¹ ∈ L :=
        (mem_conjugate_iff L g (g⁻¹ * z * g)).mp hz'
      rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h2
  have hodd' : Odd (orderOf y') := by
    have h1 : orderOf y' = orderOf y := by
      rw [hy'def]
      rw [show g * y * g⁻¹ = (g⁻¹)⁻¹ * y * g⁻¹ by rw [inv_inv]]
      exact orderOf_conjugate_eq y g⁻¹
    rwa [h1]
  have hy'in : y' ∈ L ⊔ centralizer (L : Set G) := h y' hy'mem hodd'
  have hyconj : y ∈ CFSG.conjugate (L ⊔ centralizer (L : Set G)) g := by
    rw [CFSG.conjugate, Subgroup.mem_map_equiv]
    simpa [hy'def] using hy'in
  have hsup : CFSG.conjugate (L ⊔ centralizer (L : Set G)) g
      = CFSG.conjugate L g ⊔ centralizer (CFSG.conjugate L g : Set G) := by
    rw [← aor_conjugate_centralizer L g]
    exact Subgroup.map_sup L (centralizer (L : Set G)) _
  rwa [hsup] at hyconj

theorem aor_cyclic_conjugate [Finite G] {L : Subgroup G}
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P) (g : G) :
    ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) → IsCyclic P := by
  intro P hP hPC
  have hP'p : IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) :=
    hP.map (MulAut.conj g).toMonoidHom
  have hP'le : P.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set G) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hpC : p ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := hPC hp
    rw [Subgroup.mem_centralizer_iff] at hpC
    have hl' : g⁻¹ * l * g ∈ CFSG.conjugate L g := by
      rw [mem_conjugate_iff]
      rwa [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
    have hcomm := hpC (g⁻¹ * l * g) hl'
    show l * (MulAut.conj g) p = (MulAut.conj g) p * l
    rw [MulAut.conj_apply]
    calc l * (g * p * g⁻¹) = g * ((g⁻¹ * l * g) * p) * g⁻¹ := by group
      _ = g * (p * (g⁻¹ * l * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * p * g⁻¹) * l := by group
  have hsub_p : IsPGroup 2
      ↥((P.map (MulAut.conj g).toMonoidHom).subgroupOf (centralizer (L : Set G))) :=
    hP'p.of_equiv (Subgroup.subgroupOfEquivOfLe hP'le).symm
  obtain ⟨Q, hQ⟩ := hsub_p.exists_le_sylow
  have hQsyl : IsSylow2Of
      ((Q : Subgroup ↥(centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
      (centralizer (L : Set G)) :=
    isSylow2Of_map_sylow Q
  have hQcyc : IsCyclic
      ↥((Q : Subgroup ↥(centralizer (L : Set G))).map (centralizer (L : Set G)).subtype) :=
    hcyc _ hQsyl
  have hle : P.map (MulAut.conj g).toMonoidHom ≤
      (Q : Subgroup ↥(centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := by
    intro x hx
    exact ⟨⟨x, hP'le hx⟩, hQ (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have hP'cyc : IsCyclic ↥(P.map (MulAut.conj g).toMonoidHom) := by
    haveI : IsCyclic
        ↥((Q : Subgroup ↥(centralizer (L : Set G))).map (centralizer (L : Set G)).subtype) :=
      hQcyc
    exact Subgroup.isCyclic_of_le hle
  exact (MulEquiv.isCyclic
    (Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).mpr hP'cyc

end CFSG.OddStandard.SmallF3.Omega
