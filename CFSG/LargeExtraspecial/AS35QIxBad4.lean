module

public import CFSG.LargeExtraspecial.AS35QIxBad3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxBad

variable (T : IxBad S)

theorem conj_inv_mem_Qa {r : G} (hr : r ∈ S.QG) : T.g⁻¹ * r * T.g ∈ S.Qa T.g := by
  rw [← S.Qa_eq_of_conj_eq (g := T.g⁻¹) (h := T.g) (by rw [inv_inv]; exact T.g_inv_z),
    S.mem_Qa_iff_inv_conj_mem, inv_inv]
  rw [show T.g * (T.g⁻¹ * r * T.g) * T.g⁻¹ = r by group]
  exact hr

theorem exists_astar (hS : S.SixHyp) :
    ∃ a : G, ∃ ha : a ∈ S.M, a * a = 1 ∧ a * T.t = T.t * a ∧ a * T.xh = T.xh * a ∧
      S.ρ ⟨a, ha⟩ = T.F ∧ ∃ hg : T.g⁻¹ * a * T.g ∈ S.M,
        S.ρ ⟨_, hg⟩ * T.ζ ≠ T.ζ * S.ρ ⟨_, hg⟩ := by
  have := AS35QTh.finite_O S
  set ψ := T.psi hS with hψ
  have hPM : ψ.range ≤ S.Mbar := by
    rintro _ ⟨r, rfl⟩
    exact ⟨_, rfl⟩
  have hP2 : IsPGroup 2 ψ.range := T.isPGroup_RS.of_surjective ψ.rangeRestrict
    ψ.rangeRestrict_surjective
  have hcard : 16 ≤ Nat.card ψ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (T.psi_injective hS)).toEquiv]
    exact T.le_card_RS
  obtain ⟨σ, ⟨r, rfl⟩, hσσ, hσζ⟩ := T.exists_outer_involution hS T.hm₁ T.hm₁ζ hPM hP2 hcard
  have hrr : (r : G) * r = 1 := by
    have h1 : ψ (r * r) = 1 := by rw [map_mul, hσσ]
    exact congrArg Subtype.val (T.psi_injective hS (h1.trans (map_one ψ).symm))
  have hrM := T.RS_mem_M r.2
  have hgM := T.conj_mem_M (T.RS_comm_t hS r.2)
  refine ⟨r, hrM, hrr, T.RS_comm_t hS r.2, T.RS_comm_xh r.2, ?_, hgM, hσζ⟩
  rcases r.2 with hrC | ⟨u, hu, hru⟩
  · exfalso
    apply hσζ
    have hQt := T.conj_inv_mem_Qa (T.CQ_le_QG hrC)
    exact T.pbar_comm_zeta hS (T.rho_mem_Pbar hgM hQt)
  · have huM := S.QG_le_M (T.CQ_le_QG hu)
    rw [show (⟨r, hrM⟩ : S.M) = ⟨u, huM⟩ * ⟨T.a0, T.ha0M⟩ from Subtype.ext hru, map_mul,
      (S.ρ_eq_one_iff _).mpr (T.CQ_le_QG hu), one_mul, T.ha0ρ]

end IxBad

end CFSG.LargeExtraspecial.AS35QIx
