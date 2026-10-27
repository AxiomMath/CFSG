module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ThetaCore
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusIntersection

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem d4_false_of_qplus {p f r : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hr : r.Prime) (hr3 : 3 < r) (hrq : r ∣ p ^ f + 1)
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) r V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : False := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  set B := planeOverGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z with hB
  have hVB : V ≤ B := V_le_planeOverGroup V Z
  have hE : IsElementaryAbelian r (V.subgroupOf B) := isElementaryAbelian_subgroupOf hVB hVe
  have hEcard : Nat.card (V.subgroupOf B) = r ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVB).toEquiv]
    exact hVc
  have h := triality_thetaT_eq_bot_qplus hp hf K hK σ hσ hr hr3 hrq B
    (conj_range_le_planeOverGroup V Z) (V.subgroupOf B) hE hEcard
  exact false_of_thetaT_eq_bot hcen h2 h3 hinn h

end CFSG.GH74.GLS.Stage2.Bender.Thm1
