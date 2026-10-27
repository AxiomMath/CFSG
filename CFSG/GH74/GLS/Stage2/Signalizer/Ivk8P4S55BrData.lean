module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FrameParts
public import CFSG.GH74.GLS.Stage1.Main.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

namespace Cfg55

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G}

theorem prime (h : Cfg55 G z k S T Tstar p H P g X Y) : p.Prime := h.c51.prime

theorem odd (h : Cfg55 G z k S T Tstar p H P g X Y) : p ≠ 2 := h.c51.odd

theorem T_eq (h : Cfg55 G z k S T Tstar p H P g X Y) : T = S := by
  rcases h.c51.T5 with ⟨-, hT, -⟩ | ⟨hno, -⟩
  · exact hT
  · exact absurd h.one hno

theorem T_sylow (h : Cfg55 G z k S T Tstar p H P g X Y) :
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  rw [h.T_eq]
  exact CFSG.GH74.GLS.Stage1.Main.sylow_top_of_central h.ctx.central h.ctx.sylow

theorem T_le (h : Cfg55 G z k S T Tstar p H P g X Y) : T ≤ H := h.c51.T_le

theorem P_le (h : Cfg55 G z k S T Tstar p H P g X Y) : P ≤ H := h.c51.maxi.1.1

theorem P_pgroup (h : Cfg55 G z k S T Tstar p H P g X Y) : IsPGroup p ↥P := h.c51.maxi.1.2.1

theorem T_norm (h : Cfg55 G z k S T Tstar p H P g X Y) : T ≤ normalizer (P : Set G) :=
  h.c51.maxi.1.2.2.1

theorem g_mem (h : Cfg55 G z k S T Tstar p H P g X Y) : g ∈ P := h.s53.1

theorem g_mem_H (h : Cfg55 G z k S T Tstar p H P g X Y) : g ∈ H := h.P_le h.g_mem

theorem chief (h : Cfg55 G z k S T Tstar p H P g X Y) : IsChiefFactorIn H X Y := h.s53.2.2.2.1

theorem X_pgroup (h : Cfg55 G z k S T Tstar p H P g X Y) : IsPGroup p ↥X := by
  have hp : Fact p.Prime := ⟨h.prime⟩
  have hOp : IsPGroup p ↥(Op p H) := (pCore_isPGroup (G := ↥H) (p := p)).map H.subtype
  exact hOp.to_le h.s53.2.2.1

theorem quad_comm (h : Cfg55 G z k S T Tstar p H P g X Y) :
    ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y := fun _ hx =>
  h.s53.2.2.2.2.1 (Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers g)) (Subgroup.mem_zpowers g))

theorem H_ne_top (h : Cfg55 G z k S T Tstar p H P g X Y) : H ≠ ⊤ := by
  intro hH
  have hp : Fact p.Prime := ⟨h.prime⟩
  have hF : Fs H = Op p H := h.c51.fstar
  have hsimple : IsSimpleGroup G := h.ctx.std.kps.1
  have hnab : ∃ a b : G, a * b ≠ b * a := h.ctx.std.kps.2.1
  subst hH
  have hgen : generalizedFitting ↥(⊤ : Subgroup G) = pCore p ↥(⊤ : Subgroup G) :=
    Subgroup.map_injective (⊤ : Subgroup G).subtype_injective hF
  let e : ↥(⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  have hsimple' : IsSimpleGroup ↥(⊤ : Subgroup G) := (e.isSimpleGroup_congr).2 hsimple
  rcases hsimple'.eq_bot_or_eq_top_of_normal (pCore p ↥(⊤ : Subgroup G)) with hbot | htop
  · have hc := centralizer_generalizedFitting_le ↥(⊤ : Subgroup G)
    rw [hgen, hbot] at hc
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(⊤ : Subgroup G))
    apply hx
    have hx' : x ∈ Subgroup.centralizer (((⊥ : Subgroup ↥(⊤ : Subgroup G)) :
        Subgroup ↥(⊤ : Subgroup G)) : Set ↥(⊤ : Subgroup G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have : y = 1 := hy
      rw [this]
      simp
    exact Subgroup.mem_bot.mp (hc hx')
  · have hP' : IsPGroup p ↥(⊤ : Subgroup G) := by
      intro y
      have hy : y ∈ pCore p ↥(⊤ : Subgroup G) := by rw [htop]; trivial
      obtain ⟨m, hm⟩ := (pCore_isPGroup (p := p) (G := ↥(⊤ : Subgroup G))) ⟨y, hy⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hnil : Group.IsNilpotent ↥(⊤ : Subgroup G) := hP'.isNilpotent
    have hsol : Group.IsSolvable ↥(⊤ : Subgroup G) := @IsNilpotent.to_isSolvable _ _ hnil
    have hcomm := hsimple'.comm_iff_isSolvable.mpr hsol
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (by
      have := congrArg e (hcomm (e.symm a) (e.symm b))
      simpa using this)

end Cfg55

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
