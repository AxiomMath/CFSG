module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaGroup
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaKD
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaPx
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622SingleDelta

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem mem_iff_mem_of_map_eq {G : Type} [Group G] {K : Subgroup G} {S : Subgroup K}
    {T : Subgroup G} (hST : S.map K.subtype = T) (s : K) : s ∈ S ↔ (s : G) ∈ T := by
  rw [← hST]
  exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm

theorem s622DeltaNPC_of_kd291a3 (h : KD291a3) : S622DeltaNPC := by
  intro A _ _ p P X x z hpl hN L hL hLu _hlu
  classical
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPX : (P : Subgroup A) ≤ X := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hxX : x ∈ X := hPX (hBP (mem_sup_left (mem_zpowers x)))
  have hzX : z ∈ X := hPX (hBP (mem_sup_right (mem_zpowers z)))
  have hPxX : L6Delta.Pxc (P : Subgroup A) x ≤ X := fun y hy => hPX (L6Delta.mem_Pxc.mp hy).1
  have hK : CFSG.HasNormalPComplement p ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X)) :=
    h ↥X p (P.subtype hPX) ⟨x, hxX⟩ ⟨z, hzX⟩ (plane63_of_plane65 hpl hxX hzX) L hL hLu
  unfold CFSG.HasNormalPComplement at hK
  obtain ⟨N, hNn, hNcop, hNq⟩ := hK
  haveI := hNn
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p
      ((L6Delta.Pxc (P : Subgroup A) x).subgroupOf X)
      (centralizer ({(⟨x, hxX⟩ : X)} : Set X)) := by
    have hmapC : (centralizer ({(⟨x, hxX⟩ : X)} : Set X)).map X.subtype =
        X ⊓ centralizer ({x} : Set A) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyX, hyC⟩
        exact ⟨⟨y, hyX⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X,
      Subgroup.map_subgroupOf_eq_of_le hPxX, hmapC]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le hpl.sylow_centralizer
      (inf_le_inf_right _ hPX) inf_le_right
  obtain ⟨QK, hQK⟩ := hsyl
  have hmemQK : ∀ s : ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X)),
      s ∈ (QK : Subgroup ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X))) ↔
        ((s : X) : A) ∈ L6Delta.Pxc (P : Subgroup A) x :=
    fun s => (mem_iff_mem_of_map_eq hQK s).trans mem_subgroupOf
  have hsup := L6Delta.sylow_sup_normal_eq_top N hNq QK
  have hcommK : ∀ a ∈ (QK : Subgroup ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X))),
      ∀ b ∈ (QK : Subgroup ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X))),
        a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    apply Subtype.ext
    exact L6Delta.comm_Pxc hpl ((hmemQK a).mp ha) ((hmemQK b).mp hb)
  have hKcomm : ∀ g : A, g ∈ X → g ∈ centralizer ({x} : Set A) →
      (∀ y ∈ L6Delta.Pxc (P : Subgroup A) x, g * y * g⁻¹ ∈ L6Delta.Pxc (P : Subgroup A) x) →
      (∀ y ∈ L6Delta.Pxc (P : Subgroup A) x,
        g⁻¹ * y * g⁻¹⁻¹ ∈ L6Delta.Pxc (P : Subgroup A) x) →
      ∀ q ∈ L6Delta.Pxc (P : Subgroup A) x, q * g = g * q := by
    intro g hgX hgC hfw hbw q hq
    have hgCX : (⟨g, hgX⟩ : X) ∈ centralizer ({(⟨x, hxX⟩ : X)} : Set X) :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hgC))
    have hnorm : (⟨⟨g, hgX⟩, hgCX⟩ : ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X))) ∈
        Subgroup.normalizer ((QK : Subgroup ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X))) :
          Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      rw [hmemQK s, hmemQK (⟨⟨g, hgX⟩, hgCX⟩ * s * (⟨⟨g, hgX⟩, hgCX⟩)⁻¹)]
      constructor
      · intro hs
        exact hfw _ hs
      · intro hs
        have h1 : g⁻¹ * (g * ((s : X) : A) * g⁻¹) * g⁻¹⁻¹ ∈
            L6Delta.Pxc (P : Subgroup A) x :=
          hbw (g * ((s : X) : A) * g⁻¹) hs
        have e : g⁻¹ * (g * ((s : X) : A) * g⁻¹) * g⁻¹⁻¹ = ((s : X) : A) := by group
        rwa [e] at h1
    have hcent := L6Delta.centralizes_of_normalizer N hNcop QK hsup hcommK _ hnorm
    have hqX : q ∈ X := hPxX hq
    have hqC : (⟨q, hqX⟩ : X) ∈ centralizer ({(⟨x, hxX⟩ : X)} : Set X) :=
      mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp (L6Delta.mem_Pxc.mp hq).2))
    have hsK : (⟨⟨q, hqX⟩, hqC⟩ : ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X))) ∈
        (QK : Subgroup ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X))) :=
      (hmemQK ⟨⟨q, hqX⟩, hqC⟩).mpr hq
    exact congrArg (fun k : ↥(centralizer ({(⟨x, hxX⟩ : X)} : Set X)) => ((k : X) : A))
      (hcent _ hsK)
  obtain ⟨QC, hQC⟩ := hpl.sylow_centralizer
  have hmemQC : ∀ s : ↥(centralizer ({x} : Set A)),
      s ∈ (QC : Subgroup ↥(centralizer ({x} : Set A))) ↔
        (s : A) ∈ L6Delta.Pxc (P : Subgroup A) x :=
    fun s => mem_iff_mem_of_map_eq hQC s
  have hnormQ : ∀ m : ↥(centralizer ({x} : Set A)),
      m ∈ Subgroup.normalizer ((QC : Subgroup ↥(centralizer ({x} : Set A))) : Set _) →
        ∀ y ∈ L6Delta.Pxc (P : Subgroup A) x,
          (m : A) * y * (m : A)⁻¹ ∈ L6Delta.Pxc (P : Subgroup A) x := by
    intro m hm y hy
    have hy' : (⟨y, (L6Delta.mem_Pxc.mp hy).2⟩ : ↥(centralizer ({x} : Set A))) ∈
        (QC : Subgroup ↥(centralizer ({x} : Set A))) :=
      (hmemQC ⟨y, (L6Delta.mem_Pxc.mp hy).2⟩).mpr hy
    exact (hmemQC (m * ⟨y, (L6Delta.mem_Pxc.mp hy).2⟩ * m⁻¹)).mp
      ((Subgroup.mem_normalizer_iff.mp hm _).mp hy')
  have hBurn : CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set A)) := by
    apply L6Delta.hasNormalPComplement_of_normalizer_le QC
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hfw : ∀ y ∈ L6Delta.Pxc (P : Subgroup A) x,
        (g : A) * y * (g : A)⁻¹ ∈ L6Delta.Pxc (P : Subgroup A) x :=
      hnormQ g hg
    have hbw : ∀ y ∈ L6Delta.Pxc (P : Subgroup A) x,
        (g : A)⁻¹ * y * (g : A)⁻¹⁻¹ ∈ L6Delta.Pxc (P : Subgroup A) x :=
      hnormQ g⁻¹ (inv_mem hg)
    have hgX : (g : A) ∈ X := hN (L6Delta.mem_normalizer_plane hpl hfw hbw)
    exact hKcomm (g : A) hgX g.2 hfw hbw (q : A) ((hmemQC q).mp hq)
  exact hBurn

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
