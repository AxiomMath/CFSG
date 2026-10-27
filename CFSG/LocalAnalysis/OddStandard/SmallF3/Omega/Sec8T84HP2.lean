module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec8t84h_simHasType_conj (hQ : Q.Nondegenerate) {x : ProjSim Q} {r : ℕ} {α : ℤˣ}
    (h : SimHasType x r α) (δ : ProjSim Q) :
    ∃ α' : ℤˣ, SimHasType (δ * x * δ⁻¹) r α' := by
  obtain ⟨y, hyx, hy1, t, htt, hty, hty'⟩ := h
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨c, hc⟩ := γ.2
  have hγt : simAct Q γ t = simConj hc t := Subtype.ext (by rw [coe_simAct, coe_simConj])
  obtain ⟨hsq, htype⟩ := invType_simConj hQ hc htt
  simp only [invType, Prod.mk.injEq] at hty
  have hx_eq : QuotientGroup.mk (orthToSim Q t) = x := by
    rw [← projOrthToProjSim_toProj t, hty', hyx]
  refine ⟨toSign c ^ r * α, toProj Q (simConj hc t), ?_, ?_, simConj hc t, hsq, ?_, rfl⟩
  · calc projOrthToProjSim Q (toProj Q (simConj hc t))
        = projOrthToProjSim Q (toProj Q (simAct Q γ t)) := by rw [hγt]
      _ = QuotientGroup.mk (orthToSim Q (simAct Q γ t)) := projOrthToProjSim_toProj _
      _ = QuotientGroup.mk (γ * orthToSim Q t * γ⁻¹) := by rw [sec9u_orthToSim_simAct]
      _ = QuotientGroup.mk γ * QuotientGroup.mk (orthToSim Q t) *
            (QuotientGroup.mk γ)⁻¹ := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = QuotientGroup.mk γ * x * (QuotientGroup.mk γ)⁻¹ := by rw [hx_eq]
  · intro h1
    have hkey : toProj Q (simConj hc t) = projSimAct Q (QuotientGroup.mk γ) y := by
      rw [← hγt, ← projSimActO_mk, toProj_projSimActO, hty']
    have hconj : projSimAct Q (QuotientGroup.mk γ) y = 1 := by rw [← hkey]; exact h1
    exact hy1 ((projSimAct Q (QuotientGroup.mk γ)).map_eq_one_iff.mp hconj)
  · simp only [htype, hty.1, hty.2]

end CFSG.OddStandard.SmallF3.Omega
