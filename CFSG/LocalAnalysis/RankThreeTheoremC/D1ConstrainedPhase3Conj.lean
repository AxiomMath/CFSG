module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Lift
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Decomp
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Cyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1CentralizerInput3.exists_factorization {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} (hS : Setting G) (hz : D1CentralizerInput3 p P M z)
    (hlayer : CFSG.layer (ReducedCentralizer p z) = ⊥) (h : D1Extremal p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) (hzR : z ∈ R) :
    ∃ Z₁ : Subgroup G, Z₁ ≤ (P : Subgroup G) ∧ (∀ y ∈ Z₁, ∀ r ∈ R, y * r * y⁻¹ ∈ R) ∧
      ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∃ y ∈ Z₁,
        ∃ x ∈ H ⊓ Subgroup.centralizer ({z} : Set G),
        ∃ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), c = y * x * o := by
  have hp : p.Prime := Fact.out
  have hPC := hz.le_centralizer
  have hzc : z ∈ Subgroup.centralizer (R : Set G) :=
    Subgroup.centralizer_le h.le_P hz.mem_centralizer
  obtain ⟨Pbar, zbar, E, C, hEn, e, hdata, hstr⟩ :=
    hz.exists_reducedStructure3 hS.simple hS.nonab hS.kProper hlayer
  obtain ⟨F, hFR, hFcard, hFexp, hFZ, eF, hSL⟩ :=
    h.toD1Escape.exists_sl_two_of_hasPrimeConstraint hcon hzR hzc hz.orderOf_eq
  have hFP : F ≤ (P : Subgroup G) := hFR.trans h.le_P
  have hFC : F ≤ Subgroup.centralizer ({z} : Set G) := hFP.trans hPC
  have hLC : H ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    inf_le_right
  have hdec := hdata.exists_decomposition hstr hPC hFP hFcard hFexp hFZ eF
    (le_inf (hFR.trans h.le_H) hFC) hLC hSL
  have hSLC : StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set G)).subgroupOf
      (Subgroup.normalizer (F : Set G))).map (centerQuotientAction F eF) :=
    hSL.trans (Subgroup.map_mono (Subgroup.comap_mono hLC))
  have hFE := hdata.map_sl_eq hstr hPC hFP hFcard hFexp hFZ eF hSLC
  obtain ⟨hFQ, hFn⟩ := hdata.sl_le_constrainedQ_and_normal hstr hPC hFP hFcard hFexp hFZ eF hSLC
  obtain ⟨hQ, hcyc, hΩ, -⟩ := hdata.constrainedQ_eq_sup hstr hPC hFP hFZ hFE
  have hidx := hdata.relIndex_constrainedQ hstr hPC
  rw [hQ] at hidx
  have hzF : Subgroup.zpowers z ≤ F := hFZ ▸ Subgroup.map_subtype_le _
  have hnorm := mul_mem_of_mem_centralizer_of_relIndex_eq hp h.ne_two hFR h.le_P
    hFP hFn rfl hcyc (P.isPGroup'.to_inf_left) (fun y hy hyp => hzF (hΩ y hy hyp)) hidx
  exact ⟨(P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G), inf_le_left, hnorm, hdec⟩

theorem D1CentralizerInput3.conj_le_of_extremal {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} (hS : Setting G) (hz : D1CentralizerInput3 p P M z)
    (hlayer : CFSG.layer (ReducedCentralizer p z) = ⊥) (h : D1Extremal p P M H R)
    (hcon : HasPrimeConstraint (G := H) p) (hzR : z ∈ R) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R, c⁻¹ * r * c ∈ H := by
  have hzc : z ∈ Subgroup.centralizer (R : Set G) :=
    Subgroup.centralizer_le h.le_P hz.mem_centralizer
  have hO : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ H :=
    (h.toPhaseThree3 hS hcon).primeCore_centralizer_le hcon hzR hzc hz.orderOf_eq hz.core_le
  obtain ⟨Z₁, -, hZ₁, hfac⟩ := hz.exists_factorization hS hlayer h hcon hzR
  intro c hc r hr
  obtain ⟨y, hy, x, hx, o, ho, rfl⟩ := hfac c hc
  have hy' : y⁻¹ * r * y ∈ R := by
    have := hZ₁ y⁻¹ (Z₁.inv_mem hy) r hr
    simpa using this
  have hxo : (y * x * o)⁻¹ * r * (y * x * o) = o⁻¹ * (x⁻¹ * (y⁻¹ * r * y) * x) * o := by group
  rw [hxo]
  exact H.mul_mem (H.mul_mem (H.inv_mem (hO ho)) (H.mul_mem (H.mul_mem (H.inv_mem hx.1)
    (h.le_H hy')) hx.1)) (hO ho)

theorem D1CentralizerInput3.centralizer_le_of_eq_sylow {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H : Subgroup G} {z : G} (hS : Setting G) (hz : D1CentralizerInput3 p P M z)
    (hlayer : CFSG.layer (ReducedCentralizer p z) = ⊥) (h : D1Extremal p P M H (P : Subgroup G))
    (hcon : HasPrimeConstraint (G := H) p) (hzR : z ∈ (P : Subgroup G)) :
    Subgroup.centralizer ({z} : Set G) ≤ H := by
  have hzc : z ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := hz.mem_centralizer
  have hO : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ H :=
    (h.toPhaseThree3 hS hcon).primeCore_centralizer_le hcon hzR hzc hz.orderOf_eq hz.core_le
  obtain ⟨Z₁, hZP, -, hfac⟩ := hz.exists_factorization hS hlayer h hcon hzR
  intro c hc
  obtain ⟨y, hy, x, hx, o, ho, rfl⟩ := hfac c hc
  exact H.mul_mem (H.mul_mem (h.le_H (hZP hy)) hx.1) (hO ho)

end CFSG.LocalAnalysis.RankThreeTheoremC
