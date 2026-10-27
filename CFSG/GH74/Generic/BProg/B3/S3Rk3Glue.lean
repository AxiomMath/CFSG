module

public import CFSG.GH74.Generic.BProg.B3.S3Pump304

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Rk3Glue

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_map_eq {H : Subgroup G} {c : G}
    (h : H.map (MulAut.conj c).toMonoidHom = H) : c ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have : c * g * c⁻¹ ∈ H.map (MulAut.conj c).toMonoidHom :=
      ⟨g, hg, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hg
    rw [← h] at hg
    obtain ⟨l, hl, hlg⟩ := hg
    have hlg' : c * l * c⁻¹ = c * g * c⁻¹ := by simpa [MulAut.conj_apply] using hlg
    have hlg2 : l = g := mul_left_cancel (mul_right_cancel hlg')
    rwa [← hlg2]

theorem conj_mem_of_mem_normalizer {H : Subgroup G} {c h : G} (hc : c ∈ normalizer (H : Set G))
    (hh : h ∈ H) : c * h * c⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hc h).mp hh

variable [Finite G] {x y : G} {K T : Subgroup G}

theorem imgBar_map_conj (hc : Cfg x y K T) {c : G} (hcC : c ∈ centralizer ({x} : Set G)) :
    S3.imgBar x (K.map (MulAut.conj c).toMonoidHom) = S3.imgBar x K := by
  have hKC : K ≤ centralizer ({x} : Set G) := hc.hK.1
  set cc : ↥(centralizer ({x} : Set G)) := ⟨c, hcC⟩ with hcc
  have hnorm := hc.shape.normal
  ext z
  rw [S3.mem_imgBar, S3.mem_imgBar]
  constructor
  · rintro ⟨g, ⟨k, hk, hkg⟩, rfl⟩
    have hkC : k ∈ centralizer ({x} : Set G) := hKC hk
    have hg : g = cc * ⟨k, hkC⟩ * cc⁻¹ := Subtype.ext (by
      simp [hcc, ← hkg, MulAut.conj_apply])
    have hmem : proj x g ∈ S3.imgBar x K := by
      rw [hg, map_mul, map_mul, map_inv]
      exact hnorm.conj_mem _ (S3.mem_imgBar.2 ⟨⟨k, hkC⟩, hk, rfl⟩) _
    exact S3.mem_imgBar.1 hmem
  · rintro ⟨g, hgK, rfl⟩
    have hw : (proj x cc)⁻¹ * proj x g * proj x cc ∈ S3.imgBar x K := by
      have := hnorm.conj_mem (proj x g) (S3.mem_imgBar.2 ⟨g, hgK, rfl⟩) (proj x cc)⁻¹
      simpa using this
    obtain ⟨k, hk, hkw⟩ := S3.mem_imgBar.1 hw
    refine ⟨cc * k * cc⁻¹, ⟨k, hk, ?_⟩, ?_⟩
    · simp [hcc, MulAut.conj_apply]
    · rw [map_mul, map_mul, map_inv, hkw]
      group

theorem K_map_conj_eq (hc : Cfg x y K T) {c : G} (hcC : c ∈ centralizer ({x} : Set G)) :
    K.map (MulAut.conj c).toMonoidHom = K :=
  S3Pump304.eq_of_imgBar_eq (FalseCtxS45Comp.isPCompIn_conj hc.hK hcC) hc.hK
    (imgBar_map_conj hc hcC)

theorem K_conj_mem (hc : Cfg x y K T) {c k : G} (hcC : c ∈ centralizer ({x} : Set G))
    (hk : k ∈ K) : c * k * c⁻¹ ∈ K := by
  have : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
    ⟨k, hk, by simp [MulAut.conj_apply]⟩
  rwa [K_map_conj_eq hc hcC] at this

theorem mem_normalizer_K (hc : Cfg x y K T) {c : G} (hcC : c ∈ centralizer ({x} : Set G)) :
    c ∈ normalizer (K : Set G) :=
  mem_normalizer_of_map_eq (K_map_conj_eq hc hcC)

omit [Finite G] in
theorem mem_normalizer_pPrimeCoreOf {J : Subgroup G} {c : G} (hc : c ∈ normalizer (J : Set G)) :
    c ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_eq
  have hJ : J.map (MulAut.conj c).toMonoidHom = J := by
    ext g
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa [MulAut.conj_apply] using conj_mem_of_mem_normalizer hc hl
    · intro hg
      have hc' := (Subgroup.mem_normalizer_iff.mp hc (c⁻¹ * g * c)).mpr (by
        rw [show c * (c⁻¹ * g * c) * c⁻¹ = g by group]
        exact hg)
      exact ⟨c⁻¹ * g * c, hc', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have := pPrimeCoreOf_map_conj c J
  rw [hJ] at this
  exact this.symm

end S3Rk3Glue

end CFSG.GH74.Generic.BProg.B3
