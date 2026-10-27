module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem sec8cj_oddCoreIn_eq_pPrimeCore {G : Type} [Group G] (K : Subgroup G) :
    oddCoreIn K = (pPrimeCore 2 K).map K.subtype := by
  rw [oddCoreIn, CFSG.inSubgroup, CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]

private theorem sec8cj_oddCoreIn_le {G : Type} [Group G] (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

private theorem sec8cj_oddCoreIn_map_mulEquiv {G : Type} [Group G] (φe : G ≃* G)
    (H : Subgroup G) :
    oddCoreIn (H.map φe.toMonoidHom) = (oddCoreIn H).map φe.toMonoidHom := by
  let e : H ≃* H.map φe.toMonoidHom := H.equivMapOfInjective φe.toMonoidHom φe.injective
  have hmap : (H.map φe.toMonoidHom).subtype.comp e.toMonoidHom =
      φe.toMonoidHom.comp H.subtype := by
    ext x
    rfl
  calc oddCoreIn (H.map φe.toMonoidHom)
      = (pPrimeCore 2 (H.map φe.toMonoidHom)).map (H.map φe.toMonoidHom).subtype :=
        sec8cj_oddCoreIn_eq_pPrimeCore _
    _ = ((pPrimeCore 2 H).map e.toMonoidHom).map (H.map φe.toMonoidHom).subtype := by
        rw [← CFSG.pPrimeCore_map_iso 2 e]
    _ = (pPrimeCore 2 H).map (φe.toMonoidHom.comp H.subtype) := by
        rw [Subgroup.map_map, hmap]
    _ = ((pPrimeCore 2 H).map H.subtype).map φe.toMonoidHom := by
        rw [Subgroup.map_map]
    _ = (oddCoreIn H).map φe.toMonoidHom := by
        rw [← sec8cj_oddCoreIn_eq_pPrimeCore H]

private theorem sec8cj_mem_centralizer_mulEquiv {G : Type} [Group G] {t : G} (φe : G ≃* G)
    (hft : φe t = t) {e : G} :
    φe e ∈ centralizer ({t} : Set G) ↔ e ∈ centralizer ({t} : Set G) := by
  have hfts : φe.symm t = t := (MulEquiv.symm_apply_eq φe).mpr hft.symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (fun x => φe.symm x) h
    simpa only [map_mul, hfts, MulEquiv.symm_apply_apply] using h'
  · intro h
    have h' := congrArg (fun x => φe x) h
    simpa only [map_mul, hft] using h'

private theorem sec8cj_normal_subgroupOf_map {G : Type} [Group G] {N K : Subgroup G}
    (hKN : K ≤ N) (h : (K.subgroupOf N).Normal) (φe : G ≃* G) :
    ((K.map φe.toMonoidHom).subgroupOf (N.map φe.toMonoidHom)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hKN)]
  have hN := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp h
  calc N.map φe.toMonoidHom ≤ (Subgroup.normalizer (K : Set G)).map φe.toMonoidHom :=
        Subgroup.map_mono hN
    _ = Subgroup.normalizer (K.map φe.toMonoidHom : Set G) :=
        Subgroup.map_equiv_normalizer_eq K φe

private theorem sec8cj_isElemAbelian_map {G : Type} [Group G] (φe : G ≃* G)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.map φe.toMonoidHom) := by
  haveI : IsMulCommutative E := hE.1
  refine ⟨inferInstance, ?_⟩
  rintro x hx
  obtain ⟨e, he, rfl⟩ := hx
  rw [← map_pow, hE.2 e he, map_one]

variable {G : Type} [Group G] [Finite G]

theorem sec8E_conj_cent {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}
    (hE : Sec8E G t L S z g B E) {v : G} (hv : v ∈ centralizer ({t} : Set G))
    (hB : B.map (MulAut.conj v).toMonoidHom ≤ L ⊓ S) :
    Sec8E G t L S z g (B.map (MulAut.conj v).toMonoidHom)
      (E.map (MulAut.conj v).toMonoidHom) := by
  let φe : G ≃* G := MulAut.conj v
  have hvt : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hv
  have hft : φe t = t := by
    change MulAut.conj v t = t
    rw [MulAut.conj_apply, hvt, mul_assoc, mul_inv_cancel, mul_one]
  have hftH : φe.toMonoidHom t = t := hft
  have hftV : (MulAut.conj v).toMonoidHom t = t := hft
  have hAmap : (Asub8 t B).map φe.toMonoidHom = Asub8 t (B.map φe.toMonoidHom) := by
    rw [Asub8, Asub8, Subgroup.map_sup, MonoidHom.map_zpowers, hftH]
  have hNmap : (Nsub8 t B).map φe.toMonoidHom = Nsub8 t (B.map φe.toMonoidHom) := by
    rw [Nsub8, Nsub8, Subgroup.map_equiv_normalizer_eq (Asub8 t B) φe, hAmap]
  have hCmap : (centralizer ({t} : Set G)).map φe.toMonoidHom = centralizer ({t} : Set G) := by
    apply le_antisymm
    · rintro x ⟨e, he, rfl⟩
      exact (sec8cj_mem_centralizer_mulEquiv φe hft).mpr he
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨φe.symm x, ?_, ?_⟩
      · refine (sec8cj_mem_centralizer_mulEquiv φe hft).mp ?_
        simpa using hx
      · simp
  have hBe16 : IsElemAb2 (B.map φe.toMonoidHom) 4 :=
    ⟨sec8cj_isElemAbelian_map φe hE.ctx.B_e16.1, by
      rw [Subgroup.card_map_of_injective φe.injective, hE.ctx.B_e16.2]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact { hE.ctx with B_le := hB, B_e16 := hBe16 }
  · rw [← hNmap]
    rintro x hx
    obtain ⟨e, he, rfl⟩ := hx
    exact ⟨e, hE.le_N he, rfl⟩
  · refine ⟨sec8cj_isElemAbelian_map φe hE.elem.1, ?_⟩
    rw [Subgroup.card_map_of_injective φe.injective, hE.elem.2]
  · rintro x hx
    obtain ⟨e, he, rfl⟩ := hx
    refine Subgroup.mem_map.mpr ⟨t * e * t⁻¹, hE.t_norm e he, ?_⟩
    simp only [map_mul, map_inv, hftV]
  · apply le_antisymm
    · rintro x ⟨hxE, hxC⟩
      obtain ⟨e, he, rfl⟩ := hxE
      refine Subgroup.mem_map.mpr ⟨e, ?_, rfl⟩
      have heC : e ∈ centralizer ({t} : Set G) :=
        (sec8cj_mem_centralizer_mulEquiv φe hft).mp hxC
      have h' : e ∈ E ⊓ centralizer ({t} : Set G) := ⟨he, heC⟩
      rwa [hE.cent_t] at h'
    · rintro x hx
      obtain ⟨b, hb, rfl⟩ := hx
      have hbC : b ∈ centralizer ({t} : Set G) := by
        have h' : b ∈ E ⊓ centralizer ({t} : Set G) := by rw [hE.cent_t]; exact hb
        exact h'.2
      have hbE : b ∈ E := by
        have h' : b ∈ E ⊓ centralizer ({t} : Set G) := by rw [hE.cent_t]; exact hb
        exact h'.1
      exact ⟨Subgroup.mem_map.mpr ⟨b, hbE, rfl⟩,
        (sec8cj_mem_centralizer_mulEquiv φe hft).mpr hbC⟩
  · rintro x hx
    obtain ⟨e, he, rfl⟩ := hx
    refine Subgroup.mem_map.mpr ⟨e * t * e⁻¹ * t⁻¹, hE.comm_le e he, ?_⟩
    simp only [map_mul, map_inv, hftV]
  · rintro b hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    obtain ⟨e, he, hcomm⟩ := hE.comm_onto b0 hb0
    refine ⟨(MulAut.conj v).toMonoidHom e, Subgroup.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    rw [← hcomm]
    simp only [map_mul, map_inv, hftV]
  · have hmap := congrArg (fun H : Subgroup G => H.map φe.toMonoidHom) hE.decomp
    rw [Subgroup.map_sup,
      Subgroup.map_inf_eq (Nsub8 t B) (centralizer ({t} : Set G)) φe.toMonoidHom
        φe.injective, hCmap] at hmap
    rw [hNmap] at hmap
    exact hmap
  · have hOmap : oddCoreIn (Nsub8 t (B.map φe.toMonoidHom))
        = (oddCoreIn (Nsub8 t B)).map φe.toMonoidHom := by
      rw [← hNmap]
      exact sec8cj_oddCoreIn_map_mulEquiv φe (Nsub8 t B)
    have hsup : E.map φe.toMonoidHom ⊔ oddCoreIn (Nsub8 t (B.map φe.toMonoidHom))
        = (E ⊔ oddCoreIn (Nsub8 t B)).map φe.toMonoidHom := by
      rw [hOmap, ← Subgroup.map_sup]
    rw [hsup, ← hNmap]
    exact sec8cj_normal_subgroupOf_map (N := Nsub8 t B)
      (K := E ⊔ oddCoreIn (Nsub8 t B))
      (sup_le hE.le_N (sec8cj_oddCoreIn_le (Nsub8 t B))) hE.normal φe

end CFSG.OddStandard.SmallF3.Omega
