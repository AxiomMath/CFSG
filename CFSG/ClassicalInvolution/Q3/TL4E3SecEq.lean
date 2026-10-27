module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMaxOrb
public import CFSG.ClassicalInvolution.Q3.TL4E3S3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Gen

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}

theorem E3.secH_eq_orbGen_of {J : Subgroup Y} {u : Y}
    (hF : GraphFam (CoreAssembly.conjClass (tightCore R))
      (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))))
    (hmax : orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) ∈
      maxOrbs (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)
    (hJΩ : J ∈ CoreAssembly.conjClass (tightCore R))
    (hXC : E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤
      Subgroup.centralizer ({u} : Set Y))
    (hCJ : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (J : Set Y)) :
    secH R u = (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)).subgroupOf
      (Subgroup.centralizer ({u} : Set Y)) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set π := orbOf (TC.nbrAdj Ω) J (tightCore R) with hπdef
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set X := E3.orbGen Ω J (tightCore R) with hX
  have hK₀π : tightCore R ∈ π := mem_orbOf_self _ _
  have hKX : tightCore R ≤ X := le_iSup₂ (f := fun M (_ : M ∈ π) => M) _ hK₀π
  have hKC : tightCore R ≤ C := hKX.trans hXC
  have hXn' : ∀ c ∈ C, conjSub c X = X := by
    intro c hc
    have hcJ : conjSub c J = J := mem_normalizer_iff_conjSub_eq.mp (hCJ hc)
    have h1 := isMaxOrb_conj hF hmax c
    rw [hcJ] at h1
    have h2 := maxOrb_unique hF hJΩ h1 hmax
    show conjSub c (piGen π) = piGen π
    rw [← piGen_conj, h2]
  have hXn : (X.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).mpr fun c hc =>
      Generic.mem_normalizer_of_conjSub_eq (hXn' c hc)
  apply le_antisymm
  · refine subnormalClosure_le ?_ ?_
    · rw [tightCore_subgroupOf hKC]
      exact Subgroup.subgroupOf_mono C hKX
    · exact isSubnormal_of_normal_subgroupOf le_top inferInstance
  · have claim : ∀ H M : Subgroup C, IsSubnormal H M → M = ⊤ →
        (tightCore R).subgroupOf C ≤ H → X ≤ H.map C.subtype := by
      intro H M hsub
      induction hsub with
      | refl H =>
        intro hH _
        rw [hH, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact hXC
      | @step H M K hHM hN hMK ih =>
        intro hK hKH
        have hXM : X ≤ M.map C.subtype := ih hK (hKH.trans hHM)
        refine iSup₂_le fun L hL => ?_
        obtain ⟨l, hl, rfl⟩ := transitive_of_maxOrb hF hmax _ hK₀π L hL
        obtain ⟨m, hmM, rfl⟩ := hXM hl
        rintro _ ⟨k, hk, rfl⟩
        have hkC : k ∈ C := hKC hk
        have hkH : (⟨k, hkC⟩ : C) ∈ H := hKH (Subgroup.mem_subgroupOf.mpr hk)
        have hkM : (⟨k, hkC⟩ : C) ∈ M := hHM hkH
        have h1 := hN.conj_mem ⟨⟨k, hkC⟩, hkM⟩ (Subgroup.mem_subgroupOf.mpr hkH) ⟨m, hmM⟩
        rw [Subgroup.mem_subgroupOf] at h1
        exact ⟨_, h1, rfl⟩
    intro x hx
    show x ∈ subnormalClosure (tightCore (R.subgroupOf C))
    rw [tightCore_subgroupOf hKC]
    refine (le_sInf fun H hH => ?_ : (X.subgroupOf C) ≤ _) hx
    intro y hy
    obtain ⟨h, hh, hhy⟩ := claim H ⊤ hH.2 rfl hH.1 (Subgroup.mem_subgroupOf.mp hy)
    have : h = y := Subtype.ext hhy
    rwa [← this]

end Gen

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem E3.secH_eq_orbGen_of_oddCent (hL : TightLargeHypR 3 n Y R S t) (hO : TightOddCent t)
    (hcn : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) {J : Subgroup Y}
    (hJ : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J) {u : Y}
    (hu : IsUniqueInvolution J u) :
    secH R u = (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)).subgroupOf
      (Subgroup.centralizer ({u} : Set Y)) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have h2 : ∀ J' ∈ Ω, IsPGroup 2 J' := hd.isPGroup_member hO
  have htr : ∀ J' ∈ Ω, ∃ g : Y, conjSub g (tightCore R) = J' := fun J' hJ' => hJ'
  have hgen : (⨆ J' ∈ Ω, J') = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
  have hstd : OrbitStd Ω := ⟨hΩ, h2, hF⟩
  have hmax := orbOf_mem_maxOrbs hF hJ.1 hJ.2
  exact E3.secH_eq_orbGen_of hF hmax hJ.1.2.1 (hstd.piGen_le_centralizer hmax hu)
    ((TightLargeHypR.typeRFam hL).tight J hJ.1.2.1 u hu)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
