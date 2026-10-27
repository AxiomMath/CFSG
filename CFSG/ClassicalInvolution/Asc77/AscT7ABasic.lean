module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7a

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G]

structure TwinFrameData (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z u : G) (J : Subgroup G)
    (t : G) : Prop where
  mem : K ∈ Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  hu : u ∈ K ⊔ K'
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  hJ : J ∈ omegaOfSet Ω (twinSet Ω K)
  ht : IsUniqueInvolution J t
  htu : t * u = u * t

section Conversions

variable {p f : ℕ} [Fact p.Prime] [Finite G] {Ω : Set (Subgroup G)} {K K' J W : Subgroup G}
  {z u t : G}

theorem Hyp21.twinFrameData (h : Hyp21 p f Ω K K' z u J t W) : TwinFrameData Ω K K' z u J t where
  mem := h.std.stand.mem
  hz := h.std.hz
  hK' := h.std.hK'
  hne := h.std.hne
  hu := h.hu
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  hJ := h.hJ
  ht := h.ht
  htu := h.htu

theorem Hyp21.of_twinFrameData (hs : Std7 p f Ω K K' z) (h : TwinFrameData Ω K K' z u J t)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) (htW : t ∈ W) : Hyp21 p f Ω K K' z u J t W where
  std := hs
  hu := h.hu
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  hJ := h.hJ
  ht := h.ht
  htu := h.htu
  hW := hW
  hzW := hzW
  htW := htW

end Conversions

section Twins

variable {Ω : Set (Subgroup G)} {K L : Subgroup G} {z : G}

theorem isUniqueInvolution_of_mem_twinSet (hz : IsUniqueInvolution K z) (hL : L ∈ twinSet Ω K) :
    IsUniqueInvolution L z := by
  obtain ⟨-, z', hzK, hzL⟩ := hL
  rwa [hz.eq hzK]

theorem mem_of_mem_twinSet (hL : L ∈ twinSet Ω K) : L ∈ Ω := hL.1

theorem twinSet_eq_of_mem_twinSet (hz : IsUniqueInvolution K z) (hL : L ∈ twinSet Ω K) :
    twinSet Ω L = twinSet Ω K := by
  have hzL := isUniqueInvolution_of_mem_twinSet hz hL
  ext M
  constructor
  · rintro ⟨hM, z', hz'L, hz'M⟩
    exact ⟨hM, z', by rwa [← hzL.eq hz'L], hz'M⟩
  · rintro ⟨hM, z', hz'K, hz'M⟩
    have hzz : z' = z := (hz.eq hz'K).symm
    subst hzz
    exact ⟨hM, z', hzL, hz'M⟩

theorem TwinFrameData.t_ne_z {K' J : Subgroup G} {u t : G}
    (h : TwinFrameData Ω K K' z u J t) : t ≠ z := by
  intro htz
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJt : J ∈ twinSet Ω K := ⟨hJΩ, z, h.hz, htz ▸ h.ht⟩
  have := h.hJ.2 J hJt
  exact this.2.1 rfl

end Twins

section Transport

variable {p f : ℕ} [Fact p.Prime] [Finite G] {Ω : Set (Subgroup G)} {K L : Subgroup G}

theorem AscStand.of_mem (h : AscStand p f Ω K) (hL : L ∈ Ω) : AscStand p f Ω L where
  odd := h.odd
  five := h.five
  hyp := h.hyp
  below := h.below
  ih := h.ih
  aEmpty := h.aEmpty
  mem := hL
  trans := by
    obtain ⟨g₀, hg₀⟩ := h.trans L hL
    intro J hJ
    obtain ⟨g, hg⟩ := h.trans J hJ
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [conjSub_mul, ← hg₀, conjSub_inv_conjSub, hg]
  gen := h.gen

theorem Std7.of_twin {K' L' : Subgroup G} {z : G} (hs : Std7 p f Ω K K' z)
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) :
    Std7 p f Ω L L' z where
  stand := hs.stand.of_mem hL.1
  disconnected := hs.disconnected
  hz := isUniqueInvolution_of_mem_twinSet hs.hz hL
  hK' := by rw [twinSet_eq_of_mem_twinSet hs.hz hL]; exact hL'
  hne := hne
  cex := hs.cex

end Transport

end CFSG.ClassicalInvolution.Asc77
