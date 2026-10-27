module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Perfect

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613B

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem plane65_of_situation {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} {x z : G} (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) :
    Plane65 p P M x z where
  prime := hS.prime
  five_le := hS.p_ge
  catalog := CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper M
    (fun h => hx.not_le (h ▸ le_top))
  plane := plane_of_central hS hx hz
  sylow_le := hS.sylow_le
  z_central := hz.centralizes
  four_le := hS.four_le_pRank
  rank_centralizer := hx.pRank_centralizer_le hS
  sylow_centralizer := hx.sylow
  perfect := fun N _ hN => eq_top_of_isPGroup_quotient hS N hN

theorem hasNormalPComplement_of_unique {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} {x z : G} (h : KD291a3) (hpl : Plane65 p P M x z)
    (hN : normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M)
    (L : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p)) (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p), IsComponentOf K ⊤ → K = L) :
    CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) := by
  classical
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPM : (P : Subgroup G) ≤ M := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.plane.isIsolatedPlane.1
  have hxM : x ∈ M := hPM (hBP (mem_sup_left (mem_zpowers x)))
  have hzM : z ∈ M := hPM (hBP (mem_sup_right (mem_zpowers z)))
  have hPxM : L6Delta.Pxc (P : Subgroup G) x ≤ M := fun y hy => hPM (L6Delta.mem_Pxc.mp hy).1
  have hK : CFSG.HasNormalPComplement p ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M)) :=
    h ↥M p (P.subtype hPM) ⟨x, hxM⟩ ⟨z, hzM⟩ (plane63_of_plane65 hpl hxM hzM) L hL hLu
  unfold CFSG.HasNormalPComplement at hK
  obtain ⟨N, hNn, hNcop, hNq⟩ := hK
  haveI := hNn
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p
      ((L6Delta.Pxc (P : Subgroup G) x).subgroupOf M)
      (centralizer ({(⟨x, hxM⟩ : M)} : Set M)) := by
    have hmapC : (centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map M.subtype =
        M ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyM, hyC⟩
        exact ⟨⟨y, hyM⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M,
      Subgroup.map_subgroupOf_eq_of_le hPxM, hmapC]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le hpl.sylow_centralizer
      (inf_le_inf_right _ hPM) inf_le_right
  obtain ⟨QK, hQK⟩ := hsyl
  have hmemQK : ∀ s : ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M)),
      s ∈ (QK : Subgroup ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M))) ↔
        ((s : M) : G) ∈ L6Delta.Pxc (P : Subgroup G) x :=
    fun s => (mem_iff_mem_of_map_eq hQK s).trans mem_subgroupOf
  have hsup := L6Delta.sylow_sup_normal_eq_top N hNq QK
  have hcommK : ∀ a ∈ (QK : Subgroup ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M))),
      ∀ b ∈ (QK : Subgroup ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M))),
        a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    apply Subtype.ext
    exact L6Delta.comm_Pxc hpl ((hmemQK a).mp ha) ((hmemQK b).mp hb)
  have hKcomm : ∀ g : G, g ∈ M → g ∈ centralizer ({x} : Set G) →
      (∀ y ∈ L6Delta.Pxc (P : Subgroup G) x, g * y * g⁻¹ ∈ L6Delta.Pxc (P : Subgroup G) x) →
      (∀ y ∈ L6Delta.Pxc (P : Subgroup G) x,
        g⁻¹ * y * g⁻¹⁻¹ ∈ L6Delta.Pxc (P : Subgroup G) x) →
      ∀ q ∈ L6Delta.Pxc (P : Subgroup G) x, q * g = g * q := by
    intro g hgM hgC hfw hbw q hq
    have hgCM : (⟨g, hgM⟩ : M) ∈ centralizer ({(⟨x, hxM⟩ : M)} : Set M) :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hgC))
    have hnorm : (⟨⟨g, hgM⟩, hgCM⟩ : ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M))) ∈
        Subgroup.normalizer ((QK : Subgroup ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M))) :
          Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      rw [hmemQK s, hmemQK (⟨⟨g, hgM⟩, hgCM⟩ * s * (⟨⟨g, hgM⟩, hgCM⟩)⁻¹)]
      constructor
      · intro hs
        exact hfw _ hs
      · intro hs
        have h1 : g⁻¹ * (g * ((s : M) : G) * g⁻¹) * g⁻¹⁻¹ ∈
            L6Delta.Pxc (P : Subgroup G) x :=
          hbw (g * ((s : M) : G) * g⁻¹) hs
        have e : g⁻¹ * (g * ((s : M) : G) * g⁻¹) * g⁻¹⁻¹ = ((s : M) : G) := by group
        rwa [e] at h1
    have hcent := L6Delta.centralizes_of_normalizer N hNcop QK hsup hcommK _ hnorm
    have hqM : q ∈ M := hPxM hq
    have hqC : (⟨q, hqM⟩ : M) ∈ centralizer ({(⟨x, hxM⟩ : M)} : Set M) :=
      mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp (L6Delta.mem_Pxc.mp hq).2))
    have hsK : (⟨⟨q, hqM⟩, hqC⟩ : ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M))) ∈
        (QK : Subgroup ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M))) :=
      (hmemQK ⟨⟨q, hqM⟩, hqC⟩).mpr hq
    exact congrArg (fun k : ↥(centralizer ({(⟨x, hxM⟩ : M)} : Set M)) => ((k : M) : G))
      (hcent _ hsK)
  obtain ⟨QC, hQC⟩ := hpl.sylow_centralizer
  have hmemQC : ∀ s : ↥(centralizer ({x} : Set G)),
      s ∈ (QC : Subgroup ↥(centralizer ({x} : Set G))) ↔
        (s : G) ∈ L6Delta.Pxc (P : Subgroup G) x :=
    fun s => mem_iff_mem_of_map_eq hQC s
  have hnormQ : ∀ m : ↥(centralizer ({x} : Set G)),
      m ∈ Subgroup.normalizer ((QC : Subgroup ↥(centralizer ({x} : Set G))) : Set _) →
        ∀ y ∈ L6Delta.Pxc (P : Subgroup G) x,
          (m : G) * y * (m : G)⁻¹ ∈ L6Delta.Pxc (P : Subgroup G) x := by
    intro m hm y hy
    have hy' : (⟨y, (L6Delta.mem_Pxc.mp hy).2⟩ : ↥(centralizer ({x} : Set G))) ∈
        (QC : Subgroup ↥(centralizer ({x} : Set G))) :=
      (hmemQC ⟨y, (L6Delta.mem_Pxc.mp hy).2⟩).mpr hy
    exact (hmemQC (m * ⟨y, (L6Delta.mem_Pxc.mp hy).2⟩ * m⁻¹)).mp
      ((Subgroup.mem_normalizer_iff.mp hm _).mp hy')
  have hBurn : CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) := by
    apply L6Delta.hasNormalPComplement_of_normalizer_le QC
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hfw : ∀ y ∈ L6Delta.Pxc (P : Subgroup G) x,
        (g : G) * y * (g : G)⁻¹ ∈ L6Delta.Pxc (P : Subgroup G) x :=
      hnormQ g hg
    have hbw : ∀ y ∈ L6Delta.Pxc (P : Subgroup G) x,
        (g : G)⁻¹ * y * (g : G)⁻¹⁻¹ ∈ L6Delta.Pxc (P : Subgroup G) x :=
      hnormQ g⁻¹ (inv_mem hg)
    have hgM : (g : G) ∈ M := hN (L6Delta.mem_normalizer_plane hpl hfw hbw)
    exact hKcomm (g : G) hgM g.2 hfw hbw (q : G) ((hmemQC q).mp hq)
  exact hBurn

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613B
