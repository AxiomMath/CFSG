module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g4_twist (F : Sec8T84Base) (hSw : Sec8T84OuterSwaps) (hTw : Sec8T84FactTwist)
    {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) {γ : G} (hγS : γ ∈ S) (hγ2 : γ * γ = 1)
    (hout : InducesOutsideGStar L 6 (-1) γ) :
    B.map (MulAut.conj γ).toMonoidHom ≤ S ⊓ L ∧
      ∃ r ∈ S ⊓ L, (γ * r) * (γ * r) = 1 ∧ InducesOutsideGStar L 6 (-1) (γ * r) ∧
        IsElemAb2 ((B ⊔ B.map (MulAut.conj γ).toMonoidHom) ⊓
          centralizer ({γ * r} : Set G)) 2 := by
  have hL : IsOm6M L := ⟨hctx.component.isQuasisimple, hctx.omega6m⟩
  have hSyl : IsSylow2Of (S ⊓ L) L :=
    sec4_isSylow2Of_inf hctx.component.le (sec4_mem_normalizer F.h36 hctx.toSec3SettingLB)
      hctx.sylow
  obtain ⟨B', hB'le, hB'e, -, hBn, hB'n, honly⟩ := sec8t84_SL_E16 F hctx
  have hγC : γ ∈ centralizer ({t} : Set G) := hctx.sylow.1 hγS
  have hγL : γ ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer F.h36 hctx.toSec3SettingLB γ hγC
  have hγSn : γ ∈ normalizer (S : Set G) := Subgroup.le_normalizer hγS
  have hγP : γ ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp hγSn x, Subgroup.mem_normalizer_iff.mp hγL x]
  have hBL : B ≤ L := hctx.B_le.trans inf_le_left
  have hBle : B ≤ S ⊓ L := by
    rw [inf_comm]
    exact hctx.B_le
  have hBγle : B.map (MulAut.conj γ).toMonoidHom ≤ S ⊓ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact (Subgroup.mem_normalizer_iff.mp hγP x).mp (hBle hx)
  have hBγe : IsElemAb2 (B.map (MulAut.conj γ).toMonoidHom) 4 :=
    ⟨hctx.B_e16.1.map _, by
      rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective, hctx.B_e16.2]⟩
  have hne : B.map (MulAut.conj γ).toMonoidHom ≠ B := fun h =>
    hSw G L hL γ hγL hout B hBL hctx.B_e16 (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hBγ : B.map (MulAut.conj γ).toMonoidHom = B' := by
    rcases honly _ hBγle hBγe with h | h
    · exact absurd h hne
    · exact h
  have hP1 : IsNormalE16In (S ⊓ L) B := ⟨hBle, hctx.B_e16, hBn⟩
  have hP2 : IsNormalE16In (S ⊓ L) (B.map (MulAut.conj γ).toMonoidHom) := by
    rw [hBγ]
    exact ⟨hB'le, hB'e, hB'n⟩
  have honly' : ∀ U : Subgroup G, U ≤ S ⊓ L → IsElemAb2 U 4 →
      U = B ∨ U = B.map (MulAut.conj γ).toMonoidHom := by
    intro U hU hUe
    rw [hBγ]
    exact honly U hU hUe
  obtain ⟨r, hrP, hr2, hrout, -, hea⟩ := hTw G L (S ⊓ L) B
    (B.map (MulAut.conj γ).toMonoidHom) hL hSyl hne.symm hP1 hP2 honly' γ hγP hγ2 hout
  exact ⟨hBγle, r, hrP, hr2, hrout, hea⟩

end CFSG.OddStandard.SmallF3.Omega
