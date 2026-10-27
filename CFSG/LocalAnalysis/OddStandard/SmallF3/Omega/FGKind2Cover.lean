module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGKind2Char
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem fg_kind2_comm {φ : ↥L →* omegaGroup hQ} {s : G} {g : OGroup Q}
    (hact : CoverAct L φ s (orthToSim Q g)) {c : G} (hcL : c ∈ L) (hcs : s * c = c * s) :
    g * ((φ ⟨c, hcL⟩ : omegaGroup hQ) : OGroup Q) =
      ((φ ⟨c, hcL⟩ : omegaGroup hQ) : OGroup Q) * g := by
  have h := t5_cent_map_mem hact (l := ⟨c, hcL⟩) hcs
  rw [simAct_orthToSim] at h
  exact mul_inv_eq_iff_eq_mul.mp h

@[expose] noncomputable def FGKind2Rho {φ : ↥L →* omegaGroup hQ} {s : G} {g : OGroup Q}
    (hact : CoverAct L φ s (orthToSim Q g)) :
    ↥(L ⊓ centralizer ({s} : Set G)) →* ↥(FGKind2D hQ g) where
  toFun c := ⟨((φ ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ : omegaGroup hQ) : OGroup Q),
    (φ ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩).2,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (fg_kind2_comm hact (Subgroup.mem_inf.mp c.2).1
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2).symm).symm⟩
  map_one' := Subtype.ext (congrArg (fun z : ↥(omegaGroup hQ) => (z : OGroup Q)) (map_one φ))
  map_mul' a b := Subtype.ext (congrArg (fun z : ↥(omegaGroup hQ) => (z : OGroup Q))
    (map_mul φ ⟨(a : G), (Subgroup.mem_inf.mp a.2).1⟩ ⟨(b : G), (Subgroup.mem_inf.mp b.2).1⟩))

theorem fg_kind2_rho_oddCentralCover (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ}
    (hφ : IsCoverMap L φ) {s : G} (hs2 : s * s = 1) {g : OGroup Q}
    (hact : CoverAct L φ s (orthToSim Q g)) : OddCentralCover (FGKind2Rho hact) := by
  have hoc := hφ.oddCentralCover hL
  refine ⟨?_, ?_, ?_⟩
  · intro y
    have hy : (y : OGroup Q) ∈ omegaGroup hQ ⊓ fixSub (simAct Q (orthToSim Q g)) := by
      refine Subgroup.mem_inf.mpr ⟨y.2.1, mem_fixSub_iff.mpr ?_⟩
      rw [simAct_orthToSim]
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp y.2.2).symm
    obtain ⟨l, hls, hly⟩ := t5_cent_exists hL hφ hact hs2 hy
    exact ⟨⟨(l : G), l.2, Subgroup.mem_centralizer_singleton_iff.mpr hls.symm⟩, Subtype.ext hly⟩
  · intro c hc
    have h0 : FGKind2Rho hact c = 1 := hc
    have hφc : φ ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ = 1 :=
      Subtype.ext (congrArg (fun z : ↥(FGKind2D hQ g) => (z : OGroup Q)) h0)
    have hcen : (⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ : ↥L) ∈ Subgroup.center ↥L :=
      hoc.ker_le_center (MonoidHom.mem_ker.mpr hφc)
    rw [Subgroup.mem_center_iff]
    intro d
    have h := Subgroup.mem_center_iff.mp hcen ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩
    exact Subtype.ext (congrArg (fun z : ↥L => (z : G)) h)
  · let ι : ↥(L ⊓ centralizer ({s} : Set G)) →* ↥L := Subgroup.inclusion inf_le_left
    have hle : ((FGKind2Rho hact).ker).map ι ≤ φ.ker := by
      rintro _ ⟨c, hc, rfl⟩
      have h0 : FGKind2Rho hact c = 1 := hc
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (congrArg (fun z : ↥(FGKind2D hQ g) => (z : OGroup Q)) h0)
    have hcard : Nat.card ((FGKind2Rho hact).ker) = Nat.card (((FGKind2Rho hact).ker).map ι) :=
      Nat.card_congr (((FGKind2Rho hact).ker).equivMapOfInjective ι
        (Subgroup.inclusion_injective _)).toEquiv
    rw [hcard]
    exact hoc.odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hle)

end CFSG.OddStandard.SmallF3.Omega
