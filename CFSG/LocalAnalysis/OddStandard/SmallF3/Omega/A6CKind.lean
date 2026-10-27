module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem a6c_cover_of_model [Finite G] (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hss : s * s ∈ centralizer (L : Set G)) :
    ∃ ρ : ↥(L ⊓ centralizer ({s} : Set G)) →* ↥(ffFix hQ (by omega) x), OddCentralCover ρ := by
  obtain ⟨ρ, hρ, -⟩ := a6c_exists_centCover hQ (by omega) e (ff6m_odd_center h) hs hss
  exact ⟨ρ, hρ⟩

theorem a6c_layerCent_le (L : Subgroup G) (s : G) :
    layerCent L s ≤ L ⊓ centralizer ({s} : Set G) := by
  rw [layerCent, CFSG.inSubgroup]
  exact Subgroup.map_subtype_le _

theorem a6c_not_isOmega5_of_isOm6M [Finite G] (h : IsOm6M L) : ¬ IsOmega5 L := by
  intro h5
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus h
  have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 3265920 := by
    rw [Nat.card_congr e.toEquiv, ff_natCard_omegaProj_six_minus hQ hdim hsgn]
  have h25 := ff_card_isOmega5 h5
  rw [← ff_center_eq_oddCore_six_minus h, hcard] at h25
  omega

theorem a6c_isOmega5_of_KM2 [Finite G] (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hss : s * s ∈ centralizer (L : Set G)) (hx : KM2 x) : IsOmega5 (layerCent L s) := by
  obtain ⟨ρ, hρ⟩ := a6c_cover_of_model h hdim hs hss
  exact (ff6m_cover_isOmega5 hρ (ff6m_K2_layerModel hQ hdim hsgn hx)).1

theorem a6c_KM2_of_isOmega5 [Finite G] (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hss : s * s ∈ centralizer (L : Set G)) (hx2 : x * x = 1)
    (hΩ : IsOmega5 (layerCent L s)) : KM2 x := by
  obtain ⟨ρ, hρ⟩ := a6c_cover_of_model h hdim hs hss
  rcases ff6m_model_classify hQ hdim hsgn hx2 with h1 | h0 | hn1 | h2 | h3 | hn2 | h4
  · exfalso
    have hc : s ∈ centralizer (L : Set G) :=
      (ff6m_centralizer_iff_eq_one h.1 hQ (by omega) e hs).mpr h1
    rw [sec5_layerCent_of_mem_centralizer h.1 hc] at hΩ
    exact a6c_not_isOmega5_of_isOm6M h hΩ
  · exact absurd (ff6m_cover_layer_eq_bot hρ (ff6m_K0_solvable hQ hdim hsgn h0))
      (ff_isOmega5_ne_bot hΩ)
  · exact absurd (ff6m_cover_isL29 hρ (ff6m_N1_layerModel hQ hdim hsgn hn1)).1
      (ff_not_isOmega5_and_isL29 hΩ)
  · exact h2
  · exact absurd (ff6m_cover_layer_eq_bot hρ (ff6m_K3_solvable hQ hdim hsgn h3))
      (ff_isOmega5_ne_bot hΩ)
  · exact absurd hΩ (ff_not_isU33_and_isOmega5
      (ff6m_cover_isU33 hρ (ff6m_N2_layerModel hQ hdim hsgn hn2)).1)
  · exact absurd (ff6m_cover_isL29 hρ (ff6m_K4_layerModel hQ hdim hsgn hx2 h4)).1
      (ff_not_isOmega5_and_isL29 hΩ)

theorem a6c_le_layerCent [Finite G] (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hss : s * s ∈ centralizer (L : Set G)) (hx : KM2 x) {X : Subgroup G}
    (hX : Group.IsPerfect ↥X) (hXL : X ≤ L) (hXs : X ≤ centralizer ({s} : Set G)) :
    X ≤ layerCent L s := by
  obtain ⟨ρ, E, hE, hρ, -, -, hp, hmap⟩ := a6c_cover_data h hdim hsgn (by omega) hs hss hx
  haveI : E.Normal := hE
  have hXH : X ≤ L ⊓ centralizer ({s} : Set G) := le_inf hXL hXs
  have hperf : Group.IsPerfect ↥(X.subgroupOf (L ⊓ centralizer ({s} : Set G))) := by
    haveI := hX
    have h' := Group.IsPerfect.range (Subgroup.inclusion hXH)
    rwa [Subgroup.inclusion_range] at h'
  have hle := a6c_perfect_le_layer hρ E hmap hp _ hperf
  intro g hg
  exact Subgroup.mem_map.mpr ⟨⟨g, hXH hg⟩, hle (show (⟨g, hXH hg⟩ :
    ↥(L ⊓ centralizer ({s} : Set G))) ∈ X.subgroupOf _ from hg), rfl⟩

theorem a6c_layerCent_image [Finite G] (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hss : s * s ∈ centralizer (L : Set G)) (hx : KM2 x) :
    ∃ E₀ : Subgroup ↥(omegaProj hQ), Group.IsPerfect ↥E₀ ∧ Nat.card ↥E₀ = 25920 ∧
      ∀ w ∈ E₀, ∃ c : ↥L, (c : G) ∈ layerCent L s ∧ ff6mPhi e c = w := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨ρ, E, hE, hρ, hρφ, hlie, hp, hmap⟩ := a6c_cover_data h hdim hsgn h2 hs hss hx
  haveI : E.Normal := hE
  haveI hLperf : Group.IsPerfect ↥(CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))) :=
    CFSG.LocalCores.layer_isPerfect
  haveI hEperf : Group.IsPerfect ↥E := by
    haveI : Group.IsPerfect ↥((CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).map ρ) :=
      Group.IsPerfect.map (f := ρ)
    rwa [hmap] at this
  refine ⟨E.map (ffFix hQ h2 x).subtype, Group.IsPerfect.map (f := (ffFix hQ h2 x).subtype),
    ?_, ?_⟩
  · rw [← ff_card_model_psp hlie]
    exact (Nat.card_congr (E.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv).symm
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    rw [← hmap] at hv
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hv
    exact ⟨⟨(l : G), (Subgroup.mem_inf.mp l.2).1⟩, Subgroup.mem_map.mpr ⟨l, hl, rfl⟩,
      (hρφ l).symm⟩

end CFSG.OddStandard.SmallF3.Omega
