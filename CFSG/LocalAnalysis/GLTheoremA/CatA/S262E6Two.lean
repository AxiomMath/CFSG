module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262E6TwoLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262GF2Cls
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoBalance
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcE6
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTorus
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusion
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.LargeExtraspecial.S5Gen2
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthogonalRank
import CFSG.CGT.PushingUpLit.CGT6.EmbEndQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem gf2E6_cases {e : TauCeti.LieTypeIndex} (h : gf2E6 e) :
    ∃ q : TauCeti.PrimePower, e = .E6 q ∧ q.card = 2 := by
  cases e <;> simp only [gf2E6] at h
  · exact ⟨_, rfl, h⟩
  all_goals exact h.elim

theorem exists_perfect_fixSubgroup_of_congr {T X : Type*} [Group T] [Group X]
    (e : T ≃* X) {a : MulAut T} {x : X} (hβ : MulAut.congr e a = MulAut.conj x)
    {Q : Subgroup X} (hQ : Q ≤ Subgroup.centralizer ({x} : Set X))
    (hQperf : ⁅Q, Q⁆ = Q) (hQ3 : 3 ∣ Nat.card Q) :
    ∃ P : Subgroup T, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  refine ⟨Q.map (e.symm : X →* T), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    have hq' : q ∈ fixSubgroup (MulAut.conj x) := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj]
      exact hQ hq
    have hβ' : q ∈ fixSubgroup (MulAut.congr e a) := by rwa [hβ]
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e a] at hβ'
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp hβ'
    have hqy : e.symm q = y := by
      rw [← hyq]
      exact e.symm_apply_apply y
    simpa [hqy] using hy
  · rw [← Subgroup.map_commutator, hQperf]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hQ3

end CFSG.LocalAnalysis.GLTheoremA.S262

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
open CFSG.StandardType.TableBExc.E6Three
open CFSG.StandardType.E6ThreeEnd
open scoped MatrixGroups commutatorElement


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem phi0_zSL_e3 (hK : Nat.card K = 2) :
    phi0 K (zSL ![0, 0, 1]) = uE6Two (K := K) 3 := by
  change phi0 K (tvSLWord ([(4, 1), (1, 4)] : List (Fin 6 × Fin 6))) =
    uE6Two (K := K) 3
  exact phi0_of_conj conj_uE6Two_three

theorem phi0_zSL_e2e3 (hK : Nat.card K = 2) :
    phi0 K (zSL ![0, 1, 1]) = uE6Two (K := K) 2 * uE6Two (K := K) 3 := by
  change phi0 K (tvSLWord ([(0, 2), (2, 0)] ++ [(4, 1), (1, 4)] :
    List (Fin 6 × Fin 6))) = uE6Two (K := K) 2 * uE6Two (K := K) 3
  rw [tvSLWord_append, map_mul, phi0_of_conj conj_uE6Two_two,
    phi0_of_conj conj_uE6Two_three]

theorem perfect_leviB0 (hK : Nat.card K = 2) :
    ⁅leviB0 K,
      leviB0 K⁆ =
      leviB0 K ∧
    3 ∣ Nat.card (leviB0 K) := by
  have hq := isQuasisimple_leviB0 (K := K)
  have hq' : CFSG.Open.IsQuasisimple (leviB0 K) :=
    CFSG.CGT.PushingUpLit.CGT6.EndQuot.isQuasisimple_iff_open _ |>.1 hq
  refine ⟨CFSG.LargeExtraspecial.S5.commutator_eq_self_of_isQuasisimple hq', ?_⟩
  have hmem : uE6Two (K := K) 2 ∈ leviB0 K := by
    rw [← range_phi0 (K := K)]
    refine ⟨zSL ![0, 1, 0], ?_⟩
    change phi0 K (tvSLWord ([(0, 2), (2, 0)] : List (Fin 6 × Fin 6))) =
      uE6Two (K := K) 2
    exact phi0_of_conj conj_uE6Two_two
  have hord : orderOf (⟨uE6Two (K := K) 2, hmem⟩ :
      leviB0 K) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (uE6Two_pow_three (CharP.cast_eq_zero K 2) 2)
      (uE6Two_ne_one 2)
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem exists_perfect_centralizer_u0 (hK : Nat.card K = 2) :
    ∃ P : Subgroup (adjointGroup .E6 K),
      P ≤ Subgroup.centralizer ({uE6Two (K := K) 0} : Set (adjointGroup .E6 K)) ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  obtain ⟨hperf, h3⟩ := perfect_leviB0 (K := K) hK
  refine ⟨leviB0 K, ?_, hperf, h3⟩
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (uE6Two_zero_comm_of_mem_leviB0 hx).symm

theorem exists_perfect_centralizer_u0_mul (hK : Nat.card K = 2) {g : SL(6, K)}
    {S : Subgroup (SL(6, K))} (hSc : S ≤ Subgroup.centralizer ({g} : Set (SL(6, K))))
    (hSperf : ⁅S, S⁆ = S) (hS3 : 3 ∣ Nat.card S) :
    ∃ P : Subgroup (adjointGroup .E6 K),
      P ≤ Subgroup.centralizer
        ({uE6Two (K := K) 0 * phi0 K g} : Set (adjointGroup .E6 K)) ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  refine ⟨S.map (phi0 K), ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    have h0 : phi0 K s * uE6Two (K := K) 0 = uE6Two (K := K) 0 * phi0 K s :=
      (uE6Two_zero_comm_of_mem_leviB0 (by
        rw [← range_phi0]
        exact MonoidHom.mem_range.mpr ⟨s, rfl⟩)).symm
    have hg : phi0 K s * phi0 K g = phi0 K g * phi0 K s := by
      simpa only [map_mul] using
        congrArg (phi0 K) (Subgroup.mem_centralizer_singleton_iff.mp (hSc hs))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.mul_right h0 hg)
  · rw [← Subgroup.map_commutator, hSperf]
  · rw [Subgroup.card_map_of_injective (phi0_injective (K := K) hK)]
    exact hS3

theorem exists_perfect_centralizer_u0u3 (hK : Nat.card K = 2) :
    ∃ P : Subgroup (adjointGroup .E6 K),
      P ≤ Subgroup.centralizer
        ({uE6Two (K := K) 0 * uE6Two (K := K) 3} : Set (adjointGroup .E6 K)) ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  obtain ⟨S, hSc, hSperf, hS3⟩ := E6TwoLin.exists_perfect_centralizing_e3 (K := K)
  rw [← phi0_zSL_e3 hK]
  exact exists_perfect_centralizer_u0_mul hK hSc hSperf hS3

theorem exists_perfect_centralizer_u0u2u3 (hK : Nat.card K = 2) :
    ∃ P : Subgroup (adjointGroup .E6 K),
      P ≤ Subgroup.centralizer
        ({uE6Two (K := K) 0 * uE6Two (K := K) 2 * uE6Two (K := K) 3} :
          Set (adjointGroup .E6 K)) ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  obtain ⟨S, hSc, hSperf, hS3⟩ := E6TwoLin.exists_perfect_centralizing_e2e3 (K := K)
  rw [mul_assoc, ← phi0_zSL_e2e3 hK]
  exact exists_perfect_centralizer_u0_mul hK hSc hSperf hS3

end CFSG.LocalAnalysis.GLTheoremA.S262

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc.E6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
open CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement


theorem fixed_perfect_gf2E6 :
    ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
      gf2E6 d.1 → ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧
          ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  intro d hfin hd a ha1 ha3
  obtain ⟨e, hv⟩ := d
  change gf2E6 e at hd
  obtain ⟨q, rfl, hq⟩ := gf2E6_cases hd
  obtain ⟨K, _, hKfin, hKcard, hCharP, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hK2 : Nat.card K = 2 := hKcard.trans hq
  obtain ⟨hp2, -⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.primePower_card_two' hq
  letI := hKfin
  haveI : CharP K 2 := by rw [← hp2]; exact hCharP
  let β : MulAut (adjointGroup .E6 K) := MulAut.congr eK a
  have hβ3 : β ^ 3 = 1 := by
    change (MulAut.congr eK a) ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    exact ha1 ((MulAut.congr eK).injective (h.trans (map_one _).symm))
  obtain ⟨x, hx⟩ := e6_aut_cube_inner hK2 β hβ3
  have hx3 : x ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Timmesfeld.CrossChar.mulAut_conj_injective_adjointGroup
      (τ := Tag.E6) (K := K)
    rw [map_pow, hx, hβ3, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    exact hβ1 (by rw [← hx, h, map_one])
  obtain ⟨c, hc⟩ := exists_conj_eq_rep_E6_two hK2 x hx3 hx1
  have finish : ∀ r : adjointGroup .E6 K,
      (∃ P : Subgroup (adjointGroup .E6 K),
        P ≤ Subgroup.centralizer ({r} : Set (adjointGroup .E6 K)) ∧
        ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P) →
      c * x * c⁻¹ = r →
      ∃ P : Subgroup (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group,
        P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
    intro r hrep hcr
    obtain ⟨Q, hQc, hQperf, hQ3⟩ := exists_perfect_le_centralizer_of_conj (g := c⁻¹) hrep
    rw [show c⁻¹ * r * c⁻¹⁻¹ = x by rw [← hcr]; group] at hQc
    exact exists_perfect_fixSubgroup_of_congr eK (by exact hx.symm) hQc hQperf hQ3
  rcases hc with hc | hc | hc
  · exact finish (uE6Two (K := K) 0) (exists_perfect_centralizer_u0 hK2) hc
  · exact finish (uE6Two (K := K) 0 * uE6Two (K := K) 3)
      (exists_perfect_centralizer_u0u3 hK2) hc
  · exact finish (uE6Two (K := K) 0 * uE6Two (K := K) 2 * uE6Two (K := K) 3)
      (exists_perfect_centralizer_u0u2u3 hK2) hc

theorem good3On_gf2E6
    (hPL : KD264PL 3) : Good3On gf2E6 :=
  good3On_of_fixed_perfect hPL (fun e he => by
    obtain ⟨q, rfl, hq⟩ := gf2E6_cases he
    exact three_ne_characteristic_of_card_two
      (TauCeti.LieTypeIndex.characteristic_E6 q) hq)
    (fun d _ hd => fixed_perfect_gf2E6 d hd)

theorem e9GoodOn_gf2E6
    (hPL : KD264PL 3) : E9GoodOn gf2E6 :=
  e9GoodOn_of_good3On (good3On_gf2E6 hPL)

end CFSG.LocalAnalysis.GLTheoremA.S262
end
