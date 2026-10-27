module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGKind2Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOrderNine
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBSwapFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

@[expose] noncomputable def FGKind2Quot (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ}
    (hφ : IsCoverMap L φ) {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) :
    ↥(layerCent L s) →* ↥(FGKind2E0 hQ hgg) :=
  ((FGKind2Rho hact).comp (Subgroup.inclusion
      (Subgroup.map_subtype_le _ : layerCent L s ≤ L ⊓ centralizer ({s} : Set G)))).codRestrict
    (FGKind2E0 hQ hgg) (fun k => by
      obtain ⟨e, he, hek⟩ := Subgroup.mem_map.mp (show (k : G) ∈
        (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).map
          (L ⊓ centralizer ({s} : Set G)).subtype from k.2)
      have hk : Subgroup.inclusion
          (Subgroup.map_subtype_le _ : layerCent L s ≤ L ⊓ centralizer ({s} : Set G)) k = e :=
        Subtype.ext hek.symm
      rw [MonoidHom.comp_apply, hk, ← fg_kind2_layer_map hL hφ hs2 hgg hty hact]
      exact Subgroup.mem_map_of_mem _ he)

theorem fg_kind2_quot_surjective (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ}
    (hφ : IsCoverMap L φ) {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) :
    Function.Surjective (FGKind2Quot hL hφ hs2 hgg hty hact) := by
  rintro ⟨y, hy⟩
  rw [← fg_kind2_layer_map hL hφ hs2 hgg hty hact] at hy
  obtain ⟨e, he, hey⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨(e : G), Subgroup.mem_map_of_mem (L ⊓ centralizer ({s} : Set G)).subtype he⟩,
    Subtype.ext hey⟩

theorem fg_kind2_quot_ker (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) :
    (FGKind2Quot hL hφ hs2 hgg hty hact).ker = Subgroup.center ↥(layerCent L s) := by
  have hsurj := fg_kind2_quot_surjective hL hφ hs2 hgg hty hact
  obtain ⟨hsE, hnc⟩ := ff_simple_of_lieModel_psp (fg_kind2_E0_lieModel hQ hφ.finrank_eq hgg hty)
  haveI := hsE
  have hcE : Subgroup.center ↥(FGKind2E0 hQ hgg) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(FGKind2E0 hQ hgg))
      with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  apply le_antisymm
  · intro k hk
    have h1 : FGKind2Rho hact (Subgroup.inclusion
        (Subgroup.map_subtype_le _ : layerCent L s ≤ L ⊓ centralizer ({s} : Set G)) k) = 1 :=
      congrArg (fun z : ↥(FGKind2E0 hQ hgg) => (z : ↥(FGKind2D hQ g)))
        (MonoidHom.mem_ker.mp hk)
    have hcen := (fg_kind2_rho_oddCentralCover hL hφ hs2 hact).ker_le_center
      (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_center_iff]
    intro k'
    have h2 := Subgroup.mem_center_iff.mp hcen (Subgroup.inclusion
      (Subgroup.map_subtype_le _ : layerCent L s ≤ L ⊓ centralizer ({s} : Set G)) k')
    exact Subtype.ext (congrArg (fun z : ↥(L ⊓ centralizer ({s} : Set G)) => (z : G)) h2)
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hfz : FGKind2Quot hL hφ hs2 hgg hty hact z ∈ Subgroup.center ↥(FGKind2E0 hQ hgg) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k', rfl⟩ := hsurj y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k']
    rw [hcE] at hfz
    exact Subgroup.mem_bot.mp hfz

theorem fg_kind2_I1_equiv (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) :
    ∃ e : ↥(layerCent L s) ⧸ Subgroup.center ↥(layerCent L s) ≃* ↥(FGKind2E0 hQ hgg),
      ∀ k : ↥(layerCent L s), e (QuotientGroup.mk k) = FGKind2Quot hL hφ hs2 hgg hty hact k :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (fg_kind2_quot_ker hL hφ hs2 hgg hty hact).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (fg_kind2_quot_surjective hL hφ hs2 hgg hty hact)), fun _ => rfl⟩

theorem fg_kind2_I1_quasisimple (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ}
    (hφ : IsCoverMap L φ) {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) :
    IsQuasisimple (layerCent L s) := by
  obtain ⟨e, -⟩ := fg_kind2_I1_equiv hL hφ hs2 hgg hty hact
  obtain ⟨hsE, hnc⟩ := ff_simple_of_lieModel_psp (fg_kind2_E0_lieModel hQ hφ.finrank_eq hgg hty)
  haveI := hsE
  haveI : Group.IsPerfect ↥(CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))) :=
    CFSG.LocalCores.layer_isPerfect
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · exact Group.IsPerfect.map (L ⊓ centralizer ({s} : Set G)).subtype
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem fg_kind2_I1_nine (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ}
    (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) :
    ∃ k : ↥(layerCent L s),
      orderOf (QuotientGroup.mk k : ↥(layerCent L s) ⧸ Subgroup.center ↥(layerCent L s)) = 9 := by
  obtain ⟨e, -⟩ := fg_kind2_I1_equiv hL hφ hs2 hgg hty hact
  obtain ⟨k₀, hk₀⟩ := fg_exists_orderNine_of_lieModel_psp
    (fg_kind2_E0_lieModel hQ hφ.finrank_eq hgg hty)
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm k₀)
  exact ⟨k, by rw [hk, MulEquiv.orderOf_eq]; exact hk₀⟩

theorem fg_asc82FactI1Layer (hS : Asc82SchurU43) : Asc82FactI1Layer := by
  intro G _ _ L hL r hr2 hα
  obtain ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hind, hxt⟩ := hα
  obtain ⟨φ, hφ, he⟩ := t5_cover_of_model hS hL hdim hsgn e
  obtain ⟨y, hyx, hy1, g, hgg, hgty, hgy⟩ := hxt
  have hxg : x = projOrthToProjSim Q (toProj Q g) := by rw [← hyx, ← hgy]
  have hact : CoverAct L φ r (orthToSim Q g) :=
    t5_coverAct_of_inducesViaP hL hφ he hind (by rw [hxg]; exact (projOrthToProjSim_toProj g).symm)
  have hr2' : r * r = 1 := by rw [← pow_two, ← hr2]; exact pow_orderOf_eq_one r
  exact ⟨fg_kind2_I1_quasisimple hL hφ hr2' hgg hgty hact,
    fg_kind2_I1_nine hL hφ hr2' hgg hgty hact⟩

end CFSG.OddStandard.SmallF3.Omega
