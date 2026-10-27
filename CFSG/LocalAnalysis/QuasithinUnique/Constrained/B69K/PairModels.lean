module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairPSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairPSp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PairPSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbReduceBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual

public section

namespace CFSG.Quasithin

namespace B69K

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem pairData_of_mulEquiv {C D : Type} [Group C] [Group D] (e : C ≃* D)
    (h : ∃ U : Subgroup D, IsSylowTwoOf U ⊤ ∧ ParabolicPair U) :
    ∃ U : Subgroup C, IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  obtain ⟨U, hU, hP⟩ := h
  refine ⟨U.map e.symm.toMonoidHom, ?_, ParabolicPair.map_mulEquiv e.symm hP⟩
  have h1 := CFSG.AGLEmbeddingD2.Tits.GN516.GOrbReduce.isSylowTwoOf_map e.symm.toMonoidHom hU
  have h2 : (⊤ : Subgroup D).map e.symm.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.symm.surjective
  rwa [h2] at h1

theorem pairData_of_statedPSL {C : Type} [Group C] {n f : ℕ} (hn : 4 ≤ n)
    (hmc : StatedClassicalModel C .PSL n 2 f) :
    ∃ U : Subgroup C, IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  obtain ⟨hadm, K, hF, hFin, hcard, ⟨e⟩⟩ := hmc
  have hCh : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hadm.2.1 hcard
  let e' : C ≃* projectiveSL n K := e.trans (Setup.X7a.statedSLEquivProjectiveSL n K)
  exact pairData_of_mulEquiv e' (parabolicPair_projectiveSL hn)

theorem pairData_of_statedPSp {C : Type} [Group C] {r f : ℕ} (hr : 3 ≤ r)
    (hmc : StatedClassicalModel C .PSp r 2 f) :
    ∃ U : Subgroup C, IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  obtain ⟨hadm, K, hF, hFin, hcard, ⟨e⟩⟩ := hmc
  have hCh : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hadm.2.1 hcard
  exact pairData_of_mulEquiv e (parabolicPair_projectiveSp hr)

open CFSG.ClassicalGroups.UnitaryFlag in
theorem pairData_of_statedPSU {C : Type} [Group C] {n f : ℕ} (hn : 4 ≤ n)
    (hmc : StatedClassicalModel C .PSU n 2 f) :
    ∃ U : Subgroup C, IsSylowTwoOf U ⊤ ∧ ParabolicPair U := by
  obtain ⟨hadm, K, hF, hFin, hcard, ⟨e⟩⟩ := hmc
  obtain ⟨r, ε, rfl, hε⟩ : ∃ r ε : ℕ, n = 2 * r + ε ∧ ε ≤ 1 :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hU : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hadm.2.1, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) hU
  have hn1 : 1 ≤ 2 * r + ε := by omega
  have hr : 2 ≤ r := by omega
  let eH : C ≃* hypPSU hU r ε := e.trans (hypPSUEquivStatedProj hU hR hn1).symm
  exact pairData_of_mulEquiv eH (parabolicPair_hypPSU hU r ε hr hε)

end B69K

end CFSG.Quasithin
