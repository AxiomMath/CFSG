module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G Pr : Type} [Group G] [Group Pr] {L : Subgroup G} {s : G} {X : Subgroup Pr} [X.Normal]
  {y : Pr} {ρ : ↥L →* ↥X}

theorem Sec4FDCover.dvd_of_component [Finite G] [Finite Pr] (h : Sec4FDCover L s X y ρ) {v : G}
    (hvL : v ∈ L) {K : Subgroup G}
    (hK : IsComponentIn K (L ⊓ centralizer ({s} : Set G) ⊓ centralizer ({v} : Set G)))
    (hlie : LieModel (↥K ⧸ oddCore ↥K) .PSp 2 3 1) :
    25920 ∣ Nat.card ↥(X ⊓ centralizer ({y} : Set Pr) ⊓
      centralizer ({((ρ ⟨v, hvL⟩ : ↥X) : Pr)} : Set Pr)) := by
  have hKL : K ≤ L := hK.1.trans (inf_le_left.trans inf_le_left)
  let Z : Subgroup Pr := X ⊓ centralizer ({y} : Set Pr) ⊓
    centralizer ({((ρ ⟨v, hvL⟩ : ↥X) : Pr)} : Set Pr)
  let g : ↥K →* ↥X := ρ.comp (Subgroup.inclusion hKL)
  have hmem : ∀ d : ↥K, (g d : Pr) ∈ Z := by
    intro d
    have hdL : (d : G) ∈ L := hKL d.2
    have hds : (d : G) * s = s * (d : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hK.1 d.2)).1).2
    have hdv : (d : G) * v = v * (d : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hK.1 d.2)).2
    have hy : (g d : Pr) * y = y * (g d : Pr) :=
      Sec4FDCover.image_comm h hdL hds
    have hv : (g d : Pr) * ((ρ ⟨v, hvL⟩ : ↥X) : Pr) =
        ((ρ ⟨v, hvL⟩ : ↥X) : Pr) * (g d : Pr) := by
      have h : (Subgroup.inclusion hKL d : ↥L) * ⟨v, hvL⟩ =
          ⟨v, hvL⟩ * (Subgroup.inclusion hKL d : ↥L) := Subtype.ext hdv
      have hmul : ρ (Subgroup.inclusion hKL d) * ρ ⟨v, hvL⟩ =
          ρ ⟨v, hvL⟩ * ρ (Subgroup.inclusion hKL d) := by
        rw [← map_mul, ← map_mul, h]
      exact congrArg (fun z : ↥X => (z : Pr)) hmul
    exact Subgroup.mem_inf.mpr
      ⟨⟨(g d).2, Subgroup.mem_centralizer_singleton_iff.mpr hy⟩,
       Subgroup.mem_centralizer_singleton_iff.mpr hv⟩
  let f : ↥K →* ↥Z :=
    { toFun := fun d => ⟨(g d : Pr), hmem d⟩
      map_one' := by
        apply Subtype.ext
        change ((g 1 : ↥X) : Pr) = (1 : Pr)
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((g (a * b) : ↥X) : Pr) =
          ((g a : ↥X) : Pr) * ((g b : ↥X) : Pr)
        rw [map_mul]
        rfl }
  have hfker : f.ker ≤ Subgroup.center ↥K := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have hd1 : (g d : Pr) = 1 := congrArg (fun z : ↥Z => (z : Pr)) hd
    have hdX : g d = 1 := Subtype.ext hd1
    have hker : Subgroup.inclusion hKL d ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact hdX
    have hcent := h.cover.ker_le_center hker
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact congrArg (fun z : ↥L => (z : G))
      (Subgroup.mem_center_iff.mp hcent (Subgroup.inclusion hKL k))
  have hdvd : ctrQ K ∣ Nat.card ↥Z := by
    rw [show ctrQ K = Nat.card (↥K ⧸ Subgroup.center ↥K) from rfl]
    exact sec4FD_natCard_quotient_center_dvd f hfker
  rw [ctrQ_of_psp4 hK.isQuasisimple hlie] at hdvd
  exact hdvd

end CFSG.OddStandard.SmallF3.Omega
