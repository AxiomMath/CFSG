module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXAut6Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParCA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGKind2I1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Center
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem fx_aut6_oddCoreIn_eq_bot {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hL : IsOm6Z2 L) (ht2 : orderOf t = 2) (hcen : centerIn L = zpowers t) :
    oddCoreIn L = ⊥ := by
  have htmem : t ∈ centerIn L := by rw [hcen]; exact Subgroup.mem_zpowers t
  obtain ⟨hsup, hinf⟩ := t5_centerIn_eq hL htmem ht2
  have hle : oddCoreIn L ≤ zpowers t := by
    rw [← hcen, hsup]
    exact le_sup_right
  exact eq_bot_iff.mpr (hinf ▸ le_inf hle le_rfl)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} {φ : ↥L →* omegaGroup hQ}

theorem fx_aut6_coverAct_mul_piSim {s : G} {x k : simGroup Q} (hk : k ∈ piSim Q)
    (h : CoverAct L φ s (x * k)) : CoverAct L φ s x := by
  refine ⟨h.1, fun l l' hl => ?_⟩
  have h1 := h.2 l l' hl
  rwa [map_mul, MulAut.mul_apply, om6par_fixed_of_mem_piSim hk] at h1

theorem fx_aut6_mem_layer_of_odd (hL : IsOm6Z2 L) (hφ : IsCoverMap L φ)
    (hinj : Function.Injective φ) {s : G} (hs2 : s * s = 1) {g : OGroup Q} (hgg : g * g = 1)
    {α : ℤˣ} (hty : invType g = (1, α)) (hact : CoverAct L φ s (orthToSim Q g)) {u : G}
    (hu : u ∈ L ⊓ centralizer ({s} : Set G)) (hodd : Odd (orderOf u)) :
    u ∈ layerCent L s := by
  haveI := fg_kind2_E0_normal hQ hgg
  let c : ↥(L ⊓ centralizer ({s} : Set G)) := ⟨u, hu⟩
  have hρinj : Function.Injective (FGKind2Rho hact) := by
    intro a b h
    have h1 : φ ⟨(a : G), (Subgroup.mem_inf.mp a.2).1⟩ = φ ⟨(b : G), (Subgroup.mem_inf.mp b.2).1⟩ :=
      Subtype.ext (congrArg (fun z : ↥(FGKind2D hQ g) => (z : OGroup Q)) h)
    have h2 := congrArg Subtype.val (hinj h1)
    exact Subtype.ext h2
  have hpg := fg_kind2_E0_isPGroup_quotient hQ hgg hty
  have hcodd : Odd (orderOf c) := by rwa [← Subgroup.orderOf_coe c]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpg)
    (QuotientGroup.mk (FGKind2Rho hact c) : ↥(FGKind2D hQ g) ⧸ FGKind2E0 hQ hgg)
  have hdvd : 2 ^ k ∣ orderOf c := by
    rw [← hk]
    exact (orderOf_map_dvd (QuotientGroup.mk' (FGKind2E0 hQ hgg)) (FGKind2Rho hact c)).trans
      (orderOf_map_dvd (FGKind2Rho hact) c)
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf c := (dvd_pow_self 2 hne).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr h2)
  have hone : (QuotientGroup.mk (FGKind2Rho hact c) : ↥(FGKind2D hQ g) ⧸ FGKind2E0 hQ hgg) = 1 := by
    rw [← orderOf_eq_one_iff, hk, hk0, pow_zero]
  have hE0 : FGKind2Rho hact c ∈ FGKind2E0 hQ hgg := (QuotientGroup.eq_one_iff _).mp hone
  rw [← fg_kind2_layer_map hL hφ hs2 hgg hty hact] at hE0
  obtain ⟨c', hc', hcc'⟩ := Subgroup.mem_map.mp hE0
  have hc'c : c' = c := hρinj hcc'
  show u ∈ (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).map
    (L ⊓ centralizer ({s} : Set G)).subtype
  exact Subgroup.mem_map.mpr ⟨c, hc'c ▸ hc', rfl⟩

theorem fx_aut6_of (hS : Asc82SchurU43) : Asc82FactAutOm6 := by
  intro G _ _ L hL t ht2 hcen z hz b hb2 hbN hbK
  have hodd : oddCoreIn L = ⊥ := fx_aut6_oddCoreIn_eq_bot hL ht2 hcen
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  have hker : CFSG.oddCore ↥L = ⊥ := by
    have h : (CFSG.oddCore ↥L).map L.subtype = ⊥ := hodd
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥L) L.subtype_injective).mp h
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hker]
  have hsurj := hφ.surjective
  have h3 : 3 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  obtain ⟨hz2, K₁, hK₁⟩ := hz
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hK₁.2.1 hK₁.1)).1
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2]; exact pow_orderOf_eq_one b
  have hz' : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hz2])
  have htt : ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hz', map_one]
    rfl
  let D : Om6Par Q (sec5cdPhi φ ⟨z, hzL⟩) := Om6Par.mk' hQ hdim hsgn htt
    (t5_phi_pocket_invType hφ hL ⟨hz2, K₁, hK₁⟩ hzL)
  obtain ⟨x, hx⟩ := t5_exists_coverAct hL hφ hbN
  have hfix : ∀ u ∈ D.L ⊔ D.R, simAct Q x u = u := by
    intro u hu
    obtain ⟨l, hl⟩ := hsurj ⟨u, (D.le_omega_cent hu).1⟩
    have hΦl : sec5cdPhi φ l = u := congrArg Subtype.val hl
    have hmem : (l : G) ∈ twoRes (L ⊓ centralizer ({z} : Set G)) :=
      (sec5cd_mem_twoRes_iff_sup hinj hsurj hzL D l).mpr (hΦl ▸ hu)
    have hcomm : b * (l : G) = (l : G) * b :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hbK hmem)).symm
    rw [← hΦl]
    exact t5_cent_map_mem hx hcomm
  have hcent := fun {s : G} {y : simGroup Q} (hy : CoverAct L φ s y) =>
    om6par_cent_iff hsurj hinj h3 hy
  have hx2 : x * x ∈ piSim Q :=
    (hcent (by rw [← hbb]; exact om6par_coverAct_mul hx hx)).mp (one_mem _)
  have hxz := om6par_coverAct_of_mem (φ := φ) hzL
  rcases fx_aut6_cent_cases D hfix hx2 with h1 | h2 | ⟨g, hgg, ⟨α, hα⟩, k, hk, hxg⟩
  · left
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr (((hcent hx).mpr h1) l hl)
  · right
    left
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (((hcent (om6par_coverAct_mul hx hxz)).mpr h2) l hl)
  · right
    right
    have hact : CoverAct L φ b (orthToSim Q g) :=
      fx_aut6_coverAct_mul_piSim hk (hxg ▸ hx)
    refine ⟨fg_kind2_I1_quasisimple hL hφ hbb hgg hα hact, ?_⟩
    refine (Subgroup.closure_le _).2 ?_
    rintro u ⟨hu, huodd⟩
    have huL : u ∈ L := (Subgroup.mem_inf.mp hu).1
    exact fx_aut6_mem_layer_of_odd hL hφ hinj hbb hgg hα hact
      ⟨huL, hbK (Subgroup.subset_closure ⟨hu, huodd⟩)⟩ huodd

end CFSG.OddStandard.SmallF3.Omega
