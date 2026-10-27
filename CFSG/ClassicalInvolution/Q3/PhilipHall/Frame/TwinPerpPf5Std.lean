module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Stand

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem ascStand_of_twinCore (h : TwinPerp.CoreData n Y R S t) :
    Asc77.AscStand (CoreAssembly.conjClass (tightCore R)) (tightCore R) where
  hyp := h.hyp
  cls := h.classicalClause
  aEmpty := h.aEmpty_all
  mem := CoreAssembly.mem_conjClass_self _
  trans := fun J hJ => by
    obtain ⟨g, hg⟩ := hJ
    exact ⟨g, hg⟩
  gen := iSup_conjClass_eq_top h.gen
  gen2 := by
    intro J hJ N hN
    obtain ⟨g, hg⟩ := hJ
    have hJe : J = tightCore (conjSub g R) := by
      rw [← hg]; exact conjSub_tightCore R g
    have h2 : tightCore (conjSub g R) ≤ N := (Subgroup.closure_le _).mpr
      (fun x hx => hN x (by rw [hJe]; exact Subgroup.subset_closure hx) hx.2)
    rw [hJe]
    exact h2
  card8 := by
    intro J hJ P hP
    have hS : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := h.datum.sylow_core
    have hc : Nat.card ↥((S : Subgroup R).map R.subtype) = 8 := by
      obtain ⟨e⟩ := h.q8
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
        R.subtype_injective).toEquiv, Nat.card_congr e.toEquiv]
      simp [QuaternionGroup.card]
    rw [← hc]
    exact (h.hyp.omega3 _ hJ _ (CoreAssembly.mem_conjClass_self _) P _ hP hS)

end Stand

namespace Asc77

theorem c25_16_proved : C25_16 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS hF
  obtain ⟨-, -, Q, R₀, -, hQq, hR₀, hcard⟩ := hF
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hyp.hR'.1
  have h8 : Nat.card R' = 8 := hyp.std.1.stand.card8 J hJ R' hRJ
  have hle : Nat.card R₀ ≤ Nat.card R' := Subgroup.card_le_of_le hR₀.1
  have hQ8 := hQq.eight_le
  omega

theorem c25_E4_of_c25_11 (h11 : C25_11) : C25_E4 :=
  T7Q.c25_E4_of_11_16 h11 c25_16_proved

end Asc77

section Perp25

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp23_of_core (h : TwinPerp.CoreData n Y R S t) (hE : TwinThmE.EIHAll n)
    (hdisc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hperp : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
      twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h2 : TwinPerp.TwoTwins R) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) :
    Asc77.Hyp23 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' t :=
  ⟨⟨ascStand_of_twinCore h, hdisc, Inner.isUniqueInvolution_core h.datum, hK', hne,
    by rw [h.card]; exact hE,
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) h.datum.twoGroup)⟩,
    hperp.trans (TwinPerp.twinSet_eq_pair h2 hK' hne)⟩

theorem tf4_of_core_E4 [Asc77.CoreLike Y] (h11 : Asc77.C25_11)
    (h : TwinPerp.CoreData n Y R S t) (hE : TwinThmE.EIHAll n)
    (hdisc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hperp : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
      twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h2 : TwinPerp.TwoTwins R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW : t ∈ W)
    (hE4 : ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W') :
    TwoSubgroupsFourGenerated Y := by
  obtain ⟨K', hK', hne⟩ := h.twin
  exact Asc77.c25_E4_of_c25_11 h11 Y _ (tightCore R) K' t
    (hyp23_of_core h hE hdisc hperp h2 hK' hne) W hW htW hE4

end Perp25

section TF4

theorem tf4_of_le {Y : Type} [Group Y] (L : Subgroup Y) (h : TwoSubgroupsFourGenerated Y) :
    TwoSubgroupsFourGenerated ↥L := by
  classical
  intro P hP
  obtain ⟨s, hs, hcl⟩ := h (P.map L.subtype) (hP.map L.subtype)
  have hsL : ∀ x ∈ s, x ∈ L := fun x hx => by
    have : x ∈ Subgroup.closure (s : Set Y) := Subgroup.subset_closure hx
    rw [hcl] at this
    obtain ⟨y, -, rfl⟩ := this
    exact y.2
  refine ⟨s.subtype (· ∈ L), ((Finset.card_subtype _ _).trans_le ((Finset.card_filter_le _ _).trans hs)), ?_⟩
  apply Subgroup.map_injective L.subtype_injective
  rw [← hcl, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨⟨x, hsL x hx⟩, by simpa using hx, rfl⟩

end TF4

section Final

theorem coreLike_of_core {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : TwinPerp.CoreData n Y R S t) : Asc77.CoreLike Y where
  oddCore_eq_bot := h.oddFree
  center_eq_bot := by
    haveI := h.simple
    have hC := CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot h.nonab
    refine le_antisymm (fun z hz => ?_) bot_le
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp hz) g
  fstar_simple := h.simple
  fstar_nonab := h.nonab

end Final

end CFSG.ClassicalInvolution.Q8P
