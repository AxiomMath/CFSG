module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
import CFSG.GH74.GLS.C3.Layer1.St1RigOrd

public section

namespace CFSG.GH74.GLS.NT44

theorem card_bar_eq_of_isPRigid
    {G : Type} [Group G] [Finite G]
    {x t : G} {K K' Λ : Subgroup G}
    (hrig : CFSG.GH74.GLS.IsPRigid 2 x K)
    (hlt : CFSG.GH74.GLS.PumpUpLT 2 x K t K')
    (hΛ : CFSG.GH74.GLS.C3.Layer1.PumpCalc.IsLam x t K Λ) :
    Nat.card ↥(CFSG.GH74.GLS.C3.Layer1.PumpCalc.bar t Λ) =
      Nat.card (CFSG.GH74.GLS.kBar K) := by
  obtain ⟨eK⟩ := hrig.2 t K' (CFSG.GH74.GLS.C3.Layer1.PumpRigid.LongPumpUp.single' hlt)
  have hle : CFSG.GH74.GLS.TwoThin.hatCard K' ≤ CFSG.GH74.GLS.TwoThin.hatCard K :=
    (Nat.card_congr eK.toEquiv).le
  have hxY : x ∈ Subgroup.centralizer ({t} : Set G) :=
    CFSG.GH74.GLS.TwoThin.mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ', hΛ', _, ⟨eΛ⟩, _, _, _⟩ :=
    CFSG.GH74.GLS.C3.Layer1.PumpRigid.rigid_step hlt hxY hle
  have heq : Λ' = Λ := hΛ'.layer.symm.trans hΛ.layer
  rw [← heq]
  exact (Nat.card_congr eΛ.toEquiv).symm

end CFSG.GH74.GLS.NT44
