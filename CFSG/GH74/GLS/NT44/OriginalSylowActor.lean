module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Transport
import CFSG.GH74.GLS.NT44.SwappedDiagonal
import CFSG.GH74.GLS.NT44.IntrinsicCore
import CFSG.GH74.GLS.Bg.Pu5.Statements

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.GH74.GLS.Stage1.Thm2.Recip
open CFSG.GH74.GLS.Stage1.Thm3.Sec4
open CFSG.GH74.GLS.Bg.Pu5

theorem exists_conjugate_mem_sylow_normalizing_not_mem_core
    {G : Type} [Group G] [Finite G]
    {x y u : G} {K T : Subgroup G}
    (hK : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) K)
    (hx2 : orderOf x = 2)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G)))
    (hyT : y ∈ T)
    (hconj : IsConj x y)
    (huT : u ∈ T)
    (huK : u ∈ K)
    (hu2 : orderOf u = 2)
    (huZ : u ∉ zStar K)
    (hyK : y ∉ Subgroup.normalizer (K : Set G)) :
    ∃ v : G, v ∈ T ∧ IsConj x v ∧ orderOf v = 2 ∧
      v ∈ Subgroup.normalizer (K : Set G) ∧
      v ∉ CFSG.GH74.GLS.Stage1.Thm2.Recip.O22
        (Subgroup.centralizer ({x} : Set G)) := by
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set Cy : Subgroup G := Subgroup.centralizer ({y} : Set G) with hCy
  have hK' : IsPCompIn 2 Cx K := by simpa [hCx] using hK
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T Cx := by simpa [hCx] using hT
  have hT2 : IsPGroup 2 T := CFSG.ABGLocalTools.IsSylowOf.isPGroup hT
  have hy2 : orderOf y = 2 := by rw [← hconj.orderOf_eq, hx2]
  have hyCx : y ∈ Subgroup.centralizer ({x} : Set G) :=
    CFSG.ABGLocalTools.IsSylowOf.le hT hyT
  have hxy : x * y = y * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp hyCx).symm
  set z0 : G := u * (y * u * y⁻¹) with hz0
  obtain ⟨hz0ordRaw, hz0LayerRaw, hz0notO22Raw, hz0eq⟩ :=
    swapped_diagonal_involution_mem_layer_not_mem_core
      hK hx2 hy2 hxy hT2 hyT huT huK hu2 huZ hyK
  have hz0ord : orderOf z0 = 2 := by simpa [hz0] using hz0ordRaw
  have hz0Layer : z0 ∈ pLayerOf 2 Cy := by
    simpa [hz0, hCy] using hz0LayerRaw
  have hz0notO22 : z0 ∉ O22 Cy := by
    simpa [hz0, hCy] using hz0notO22Raw
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  let g : G := c⁻¹
  have hgyx : g * y * g⁻¹ = x := by
    dsimp [g]
    rw [← hc]
    group
  set z1 : G := g * z0 * g⁻¹ with hz1
  have hz1ord : orderOf z1 = 2 := by
    rw [hz1, orderOf_conj_eq' g z0, hz0ord]
  have hCycmap : cmap g Cy = Cx := by
    change Cy.map (MulAut.conj g).toMonoidHom = Cx
    rw [hCy, hCx]
    rw [map_centralizer_singleton_conj y g, hgyx]
  have hz1Layer : z1 ∈ pLayerOf 2 Cx := by
    have hz1map : z1 ∈ cmap g (pLayerOf 2 Cy) := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz0Layer
      simpa [hz1, MulAut.conj_apply] using h
    rw [← pLayerOf_cmap g Cy, hCycmap] at hz1map
    exact hz1map
  have hO22g : O22 (cmap g Cy) =
      (O22 Cy).map (MulAut.conj g).toMonoidHom := by
    change CFSG.GH74.GLS.Stage2.Local.O22Of (cmap g Cy) =
      (CFSG.GH74.GLS.Stage2.Local.O22Of Cy).map (MulAut.conj g).toMonoidHom
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.O22Of_map
      (MulAut.conj g).injective Cy
  have hz1notO22 : z1 ∉ O22 Cx := by
    intro hz1O
    have hz1map : z1 ∈ (O22 Cy).map (MulAut.conj g).toMonoidHom := by
      rw [← hO22g, hCycmap]
      exact hz1O
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz1map
    have hwz0 : w = z0 := (MulAut.conj g).injective (by
      change (MulAut.conj g).toMonoidHom w = (MulAut.conj g).toMonoidHom z0
      rw [hwz]
      simp [hz1, MulAut.conj_apply])
    exact hz0notO22 (hwz0 ▸ hw)
  have hconj_eq : (g * u * g⁻¹) * x * (g * u * g⁻¹)⁻¹ = x * z1 := by
    calc
      (g * u * g⁻¹) * x * (g * u * g⁻¹)⁻¹
          = (g * u * g⁻¹) * (g * y * g⁻¹) * (g * u * g⁻¹)⁻¹ := by
              rw [← hgyx]
      _ = g * (u * y * u⁻¹) * g⁻¹ := by group
      _ = g * (y * z0) * g⁻¹ := by rw [hz0eq]
      _ = (g * y * g⁻¹) * (g * z0 * g⁻¹) := by group
      _ = x * z1 := by rw [hgyx, hz1]
  have hconj_xz1 : IsConj x (x * z1) :=
    isConj_iff.mpr ⟨g * u * g⁻¹, hconj_eq⟩
  have hxz1Cx : x * z1 ∈ Cx := by
    have hxCx : x ∈ Cx := by
      rw [hCx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hz1Cx : z1 ∈ Cx := (CFSG.GH74.GLS.TwoThin.pLayerOf_le 2 Cx) hz1Layer
    exact Cx.mul_mem hxCx hz1Cx
  have hxz1ord : orderOf (x * z1) = 2 := by
    rw [← hconj_xz1.orderOf_eq, hx2]
  obtain ⟨q, hqCx, hvT'⟩ :=
    exists_conj_mem_of_isSylowOf' (K := Cx) (T := T) hT' hxz1Cx
      ⟨1, by simpa using hxz1ord⟩
  set z2 : G := q * z1 * q⁻¹ with hz2
  set v : G := q * (x * z1) * q⁻¹ with hv
  have hvT : v ∈ T := by simpa [hv] using hvT'
  have hqx : q * x = x * q := by
    have hqCx' : q ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa [hCx] using hqCx
    exact Subgroup.mem_centralizer_singleton_iff.mp hqCx'
  have hqconj : q * (x * z1) * q⁻¹ = x * z2 := by
    calc
      q * (x * z1) * q⁻¹ = (q * x) * z1 * q⁻¹ := by group
      _ = (x * q) * z1 * q⁻¹ := by rw [hqx]
      _ = x * (q * z1 * q⁻¹) := by group
      _ = x * z2 := by rw [hz2]
  have hvEq : v = x * z2 := hv.trans hqconj
  have hconj_z1v : IsConj (x * z1) v :=
    isConj_iff.mpr ⟨q, hv.symm⟩
  have hconj_v : IsConj x v := hconj_xz1.trans hconj_z1v
  have hvord : orderOf v = 2 := by
    rw [← hconj_v.orderOf_eq, hx2]
  have hnormq : q ∈ Subgroup.normalizer ((pLayerOf 2 Cx : Subgroup G) : Set G) :=
    mem_normalizer_pLayerOf (X := Cx) hqCx
  have hz2Layer : z2 ∈ pLayerOf 2 Cx := by
    rw [hz2]
    exact (Subgroup.mem_normalizer_iff.mp hnormq z1).mp hz1Layer
  have hz2N : z2 ∈ Subgroup.normalizer (K : Set G) :=
    pLayerOf_le_normalizer (X := Cx) (K := K) hK' hz2Layer
  have hxCent : x ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkCx : k ∈ Cx := by simpa [hCx] using hK.1 hk
    have hk' : k ∈ Subgroup.centralizer ({x} : Set G) := by simpa [hCx] using hkCx
    exact Subgroup.mem_centralizer_singleton_iff.mp hk'
  have hxN : x ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) hxCent
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := by
    rw [hvEq]
    exact (Subgroup.normalizer (K : Set G)).mul_mem hxN hz2N
  have hqxconj : q * x * q⁻¹ = x := by
    rw [hqx]
    group
  have hCxcmapq : cmap q Cx = Cx := by
    change Cx.map (MulAut.conj q).toMonoidHom = Cx
    rw [hCx]
    rw [map_centralizer_singleton_conj x q, hqxconj]
  have hO22q : O22 (cmap q Cx) =
      (O22 Cx).map (MulAut.conj q).toMonoidHom := by
    change CFSG.GH74.GLS.Stage2.Local.O22Of (cmap q Cx) =
      (CFSG.GH74.GLS.Stage2.Local.O22Of Cx).map (MulAut.conj q).toMonoidHom
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.O22Of_map
      (MulAut.conj q).injective Cx
  have hz2notO22 : z2 ∉ O22 Cx := by
    intro hz2O
    have hz2map : z2 ∈ (O22 Cx).map (MulAut.conj q).toMonoidHom := by
      rw [← hO22q, hCxcmapq]
      exact hz2O
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz2map
    have hwz1 : w = z1 := (MulAut.conj q).injective (by
      change (MulAut.conj q).toMonoidHom w = (MulAut.conj q).toMonoidHom z1
      rw [hwz]
      simp [hz2, MulAut.conj_apply])
    exact hz1notO22 (hwz1 ▸ hw)
  have hxZ : x ∈ zStar Cx :=
    mem_zStar_of_forall_comm (X := Cx) (c := x) (by
      rw [hCx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      (by
        intro k hk
        have hk' : k ∈ Subgroup.centralizer ({x} : Set G) := by
          simpa [hCx] using hk
        exact Subgroup.mem_centralizer_singleton_iff.mp hk')
  have hWz : Subgroup.zpowers x ≤ zStar Cx := Subgroup.zpowers_le.mpr hxZ
  have hW2 : IsPGroup 2 (Subgroup.zpowers x) :=
    isPGroup_zpowers_of_pow_eq_one (exists_two_pow_eq_one_of_orderOf hx2)
  have hWOp : Subgroup.zpowers x ≤ (CFSG.Op_p'p 2 ↥Cx).map Cx.subtype :=
    le_Op_p'p_of_le_zStar hW2 hWz
  have hxO22 : x ∈ O22 Cx := by
    change x ∈ (CFSG.Op_p'p 2 ↥Cx).map Cx.subtype
    exact hWOp (Subgroup.mem_zpowers x)
  have hvnotO22 : v ∉ O22 Cx := by
    intro hvO
    have hz2O : z2 ∈ O22 Cx := by
      have h : x⁻¹ * v ∈ O22 Cx :=
        (O22 Cx).mul_mem ((O22 Cx).inv_mem hxO22) hvO
      have hz2eq : x⁻¹ * v = z2 := by
        rw [hvEq]
        group
      rwa [hz2eq] at h
    exact hz2notO22 hz2O
  refine ⟨v, hvT, hconj_v, hvord, hvN, ?_⟩
  simpa [hCx] using hvnotO22

end CFSG.GH74.GLS.NT44

end
