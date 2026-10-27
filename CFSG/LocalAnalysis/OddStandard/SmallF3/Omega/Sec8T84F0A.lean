module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem oddCoreIn_le_X {G : Type} [Group G] (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

private theorem oddCoreIn_normal {G : Type} [Group G] (N : Subgroup G) :
    ((oddCoreIn N).subgroupOf N).Normal := by
  have hOsub : (oddCoreIn N).subgroupOf N = CFSG.oddCore N := by
    show ((CFSG.oddCore N).map N.subtype).subgroupOf N = CFSG.oddCore N
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  rw [hOsub]
  infer_instance

private theorem map_conj_eq_self_of_mem_normalizer {G : Type} [Group G] {H : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj u).toMonoidHom = H := by
  have h := (Subgroup.mem_normalizer_iff_map_conj_eq (H := H) (g := u)).mp hu
  simpa using h

private theorem mem_normalizer_of_mem {G : Type} [Group G] {H : Subgroup G} {u : G}
    (hu : u ∈ H) : u ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact H.mul_mem (H.mul_mem hu hx) (H.inv_mem hu)
  · intro hx
    have hx' : u⁻¹ * (u * x * u⁻¹) * u ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hu) hx) hu
    have hx'' : u⁻¹ * (u * x * u⁻¹) * u = x := by group
    rw [hx''] at hx'
    exact hx'

private theorem map_conj_eq_self_of_mem {G : Type} [Group G] {H : Subgroup G} {u : G}
    (hu : u ∈ H) : H.map (MulAut.conj u).toMonoidHom = H :=
  map_conj_eq_self_of_mem_normalizer (mem_normalizer_of_mem hu)

private theorem isElemAbelian_map_conj {G : Type} [Group G] {E : Subgroup G} (u : G)
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.map (MulAut.conj u).toMonoidHom) := by
  haveI : IsMulCommutative E := hE.1
  refine ⟨inferInstance, ?_⟩
  rintro x hx
  obtain ⟨e, he, rfl⟩ := hx
  rw [← map_pow, hE.2 e he, map_one]

private theorem conj_apply_eq_of_comm {G : Type} [Group G] {u b : G} (hb : u * b = b * u) :
    ((MulAut.conj u).toMonoidHom) b = b := by
  change MulAut.conj u b = b
  rw [MulAut.conj_apply, hb, mul_assoc, mul_inv_cancel, mul_one]

private theorem conj_mul_conj {G : Type} [Group G] {u t e : G} (hut : u * t = t * u) :
    ((MulAut.conj u).toMonoidHom) (t * e * t⁻¹)
      = t * ((MulAut.conj u).toMonoidHom) e * t⁻¹ := by
  have hft := conj_apply_eq_of_comm hut
  simp only [map_mul, map_inv, hft]

private theorem conj_commutator {G : Type} [Group G] {u t e : G} (hut : u * t = t * u)
    (hb : u * (e * t * e⁻¹ * t⁻¹) = (e * t * e⁻¹ * t⁻¹) * u) :
    ((MulAut.conj u).toMonoidHom) e * t * (((MulAut.conj u).toMonoidHom) e)⁻¹ * t⁻¹
      = e * t * e⁻¹ * t⁻¹ := by
  have hft := conj_apply_eq_of_comm hut
  calc ((MulAut.conj u).toMonoidHom) e * t * (((MulAut.conj u).toMonoidHom) e)⁻¹ * t⁻¹
      = ((MulAut.conj u).toMonoidHom) (e * t * e⁻¹ * t⁻¹) := by
        simp only [map_mul, map_inv, hft]
    _ = u * (e * t * e⁻¹ * t⁻¹) * u⁻¹ := by
        change MulAut.conj u (e * t * e⁻¹ * t⁻¹) = u * (e * t * e⁻¹ * t⁻¹) * u⁻¹
        rw [MulAut.conj_apply]
    _ = e * t * e⁻¹ * t⁻¹ := by
        rw [hb, mul_assoc, mul_inv_cancel, mul_one]

theorem sec8E_conj_oddCore (h8A : Asc82Lemma8A) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B E : Subgroup G} (hE : Sec8E G t L S z g B E) {u : G}
    (hu : u ∈ oddCoreIn (Nsub8 t B)) :
    Sec8E G t L S z g B (E.map (MulAut.conj u).toMonoidHom) := by
  have h8A1 := h8A G t L S z g B hE.ctx
  have hcentA : centralizer (Asub8 t B : Set G) = Asub8 t B ⊔ oddCoreIn (Nsub8 t B) :=
    (h8A1.1.trans h8A1.2).symm
  have huN : u ∈ Nsub8 t B := oddCoreIn_le_X _ hu
  have hcent : u ∈ centralizer (Asub8 t B : Set G) := by
    rw [hcentA]
    exact (le_sup_right : oddCoreIn (Nsub8 t B) ≤ Asub8 t B ⊔ oddCoreIn (Nsub8 t B)) hu
  have htA : t ∈ Asub8 t B := (le_sup_left : zpowers t ≤ Asub8 t B) (Subgroup.mem_zpowers t)
  have hut : u * t = t * u := ((Subgroup.mem_centralizer_iff.mp hcent) t htA).symm
  have hcommB : ∀ b ∈ B, u * b = b * u := fun b hb =>
    ((Subgroup.mem_centralizer_iff.mp hcent) b ((le_sup_right : B ≤ Asub8 t B) hb)).symm
  have hC : u ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hut
  refine ⟨hE.ctx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hx
    exact (Nsub8 t B).mul_mem ((Nsub8 t B).mul_mem huN (hE.le_N he))
      ((Nsub8 t B).inv_mem huN)
  · refine ⟨isElemAbelian_map_conj u hE.elem.1, ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj u).injective, hE.elem.2]
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hx
    exact Subgroup.mem_map.mpr ⟨t * e * t⁻¹, hE.t_norm e he, conj_mul_conj hut⟩
  · apply le_antisymm
    · rintro x ⟨hxE, hxC⟩
      obtain ⟨e, he, rfl⟩ := hxE
      have hmapC : (centralizer ({t} : Set G)).map (MulAut.conj u).toMonoidHom
          = centralizer ({t} : Set G) :=
        map_conj_eq_self_of_mem hC
      have hfe : ((MulAut.conj u).toMonoidHom) e
          ∈ (centralizer ({t} : Set G)).map (MulAut.conj u).toMonoidHom := by
        rw [hmapC]
        exact hxC
      have heC : e ∈ centralizer ({t} : Set G) :=
        (Subgroup.mem_map_iff_mem (MulAut.conj u).injective).mp hfe
      have heB : e ∈ B := by
        have h' : e ∈ E ⊓ centralizer ({t} : Set G) := ⟨he, heC⟩
        rwa [hE.cent_t] at h'
      rw [conj_apply_eq_of_comm (hcommB e heB)]
      exact heB
    · intro b hb
      have hb' : b ∈ E ⊓ centralizer ({t} : Set G) := by
        rw [hE.cent_t]
        exact hb
      have hbmap : ((MulAut.conj u).toMonoidHom) b = b :=
        conj_apply_eq_of_comm (hcommB b hb)
      exact ⟨Subgroup.mem_map.mpr ⟨b, hb'.1, hbmap⟩, hb'.2⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hx
    have hmem : e * t * e⁻¹ * t⁻¹ ∈ B := hE.comm_le e he
    rw [conj_commutator hut (hcommB _ hmem)]
    exact hmem
  · intro b hb
    obtain ⟨e, he, hcomm⟩ := hE.comm_onto b hb
    have hmem : e * t * e⁻¹ * t⁻¹ ∈ B := hE.comm_le e he
    refine ⟨((MulAut.conj u).toMonoidHom) e, Subgroup.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    rw [conj_commutator hut (hcommB _ hmem), hcomm]
  · have hNmap : (Nsub8 t B).map (MulAut.conj u).toMonoidHom = Nsub8 t B :=
      map_conj_eq_self_of_mem huN
    have hNCmem : u ∈ Nsub8 t B ⊓ centralizer ({t} : Set G) := ⟨huN, hC⟩
    have hNCmap : (Nsub8 t B ⊓ centralizer ({t} : Set G)).map (MulAut.conj u).toMonoidHom
        = Nsub8 t B ⊓ centralizer ({t} : Set G) :=
      map_conj_eq_self_of_mem hNCmem
    have hmap := congrArg (fun H => Subgroup.map (MulAut.conj u).toMonoidHom H) hE.decomp
    rw [Subgroup.map_sup, hNmap, hNCmap] at hmap
    exact hmap
  · have hOnorm : ((oddCoreIn (Nsub8 t B)).subgroupOf (Nsub8 t B)).Normal :=
      oddCoreIn_normal (Nsub8 t B)
    have hNleO : Nsub8 t B ≤ Subgroup.normalizer (oddCoreIn (Nsub8 t B) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_le_X (Nsub8 t B))).mp hOnorm
    have hOmap : (oddCoreIn (Nsub8 t B)).map (MulAut.conj u).toMonoidHom
        = oddCoreIn (Nsub8 t B) :=
      map_conj_eq_self_of_mem_normalizer (hNleO huN)
    have huEO : u ∈ E ⊔ oddCoreIn (Nsub8 t B) :=
      (le_sup_right : oddCoreIn (Nsub8 t B) ≤ E ⊔ oddCoreIn (Nsub8 t B)) hu
    have hEOmap : (E ⊔ oddCoreIn (Nsub8 t B)).map (MulAut.conj u).toMonoidHom
        = E ⊔ oddCoreIn (Nsub8 t B) :=
      map_conj_eq_self_of_mem huEO
    have heq : E.map (MulAut.conj u).toMonoidHom ⊔ oddCoreIn (Nsub8 t B)
        = E ⊔ oddCoreIn (Nsub8 t B) := by
      calc E.map (MulAut.conj u).toMonoidHom ⊔ oddCoreIn (Nsub8 t B)
          = E.map (MulAut.conj u).toMonoidHom
              ⊔ (oddCoreIn (Nsub8 t B)).map (MulAut.conj u).toMonoidHom := by rw [hOmap]
        _ = (E ⊔ oddCoreIn (Nsub8 t B)).map (MulAut.conj u).toMonoidHom :=
              (Subgroup.map_sup E (oddCoreIn (Nsub8 t B))
                (MulAut.conj u).toMonoidHom).symm
        _ = E ⊔ oddCoreIn (Nsub8 t B) := hEOmap
    rw [heq]
    exact hE.normal

end CFSG.OddStandard.SmallF3.Omega
