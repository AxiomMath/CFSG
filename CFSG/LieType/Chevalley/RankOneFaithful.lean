module

public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

variable {τ : Tag} {K : Type} [Field K]

theorem exists_cartan_odd (τ : Tag) (i : Fin τ.rank) :
    ∃ j, τ.cartan i j = -1 ∨ τ.cartan i j = -3 := by
  cases τ <;> fin_cases i <;> decide

theorem torusElt_neg_one_ne_one
    (hK : ringChar K ≠ 2) (i : Fin τ.rank) :
    torusElt τ K i (-1) ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := exists_cartan_odd τ i
  have hc := (simple_torus_root_conjugation τ K i j (-1) 1).1
  rw [h, one_mul, inv_one, mul_one] at hc
  have hodd : Odd (τ.cartan i j) := by rcases hj with hj | hj <;> rw [hj] <;> decide
  rw [hodd.neg_one_zpow, Units.val_neg, Units.val_one, mul_one] at hc
  have h1 : (1 : K) = -1 := xOp_injective j (by rw [← coe_xUnit, ← coe_xUnit, hc])
  exact hK (neg_one_eq_one_iff.1 h1.symm)

theorem odd_Chevalley_simple_root_SL2_faithful
    (τ : Tag) (K : Type) [Field K]
    (hK : ringChar K ≠ 2) (i : Fin τ.rank) :
    (∀ ρ : SL2 K →* ModGL τ K, (∀ c, ρ (uSL c) = xUnit τ K i c) →
      (∀ c, ρ (vSL c) = yUnit τ K i c) → Function.Injective ρ) ∧
    ∃ e : SL2 K ≃* Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)),
      (∀ c, (e (uSL c) : ModGL τ K) = xUnit τ K i c) ∧
      (∀ c, (e (vSL c) : ModGL τ K) = yUnit τ K i c) ∧
      (∀ t, (e (HSL t) : ModGL τ K) = torusElt τ K i t) ∧
      (e WSL : ModGL τ K) = weylElt τ K i 1 := by
  obtain ⟨ρ₀, hu, hv, hH, hW, hrange, hker, -, -⟩ :=
    exceptional_ordinary_rank_one_central_image τ K i
  have hinj₀ : Function.Injective ρ₀ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl, hgl⟩ := hker g hg
    rcases mul_self_eq_one_iff.1 (by rw [← sq]; exact hl : (l : K) * l = 1) with h1 | h1
    · ext p q
      rw [hgl, h1, one_smul]
      rfl
    · exfalso
      have hgH : g = HSL (-1) := by
        ext p q
        rw [hgl, h1, coe_HSL]
        fin_cases p <;> fin_cases q <;> simp
      rw [hgH, hH] at hg
      exact torusElt_neg_one_ne_one hK i hg
  refine ⟨fun ρ hρu hρv => ?_, ?_⟩
  · have hρ : ρ = ρ₀ := MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact (hρu c).trans (hu c).symm
      · exact (hρv c).trans (hv c).symm
    rw [hρ]
    exact hinj₀
  · refine ⟨(MonoidHom.ofInjective hinj₀).trans (MulEquiv.subgroupCongr hrange),
      fun c => hu c, fun c => hv c, fun t => hH t, hW⟩

end CFSG.LieType.Chevalley
