module

public import CFSG.ClassicalInvolution.SmallCases.A7Q3B
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylCalc
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp22Wyl

section Sizes


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem h16_of_perpHypR (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup Y, IsSylow2In P J →
      16 ≤ Nat.card P := by
  have hquat : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨g', rfl⟩
    refine ⟨conjSub g' ((S : Subgroup R).map R.subtype), h.core.datum.sylow_core.conj g', ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom
      (MulAut.conj g').injective).symm.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
        h.core.quat.some)
  exact WTool.sylow16_of_quat hr h.core.hyp hquat

end Sizes

section Squares


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}

theorem a_eq_sq (hr : 4 ≤ r) (h : PerpHypR r n Y R S t)
    (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
    (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t) (i : Fin 4) :
    ∃ x ∈ (F.ρ i).K ⊓ W, F.a i = x * x := by
  classical
  obtain ⟨hRW, -, hcyc, -, hcard⟩ :=
    Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW (F.ρ i).hR (F.ρ i).hK (F.ρ i).hRK
  have h16 := h16_of_perpHypR hr h (F.ρ i).K (F.ρ i).hK (F.ρ i).R (F.ρ i).hRK
  have h8 : 8 ≤ Nat.card ↥((F.ρ i).R ⊓ W) := by omega
  have hp2 : IsPGroup 2 ↥((F.ρ i).R ⊓ W) := (F.ρ i).hRK.2.1.to_le inf_le_left
  obtain ⟨s, hs⟩ := hp2.exists_card_eq
  have hs3 : 3 ≤ s := by
    by_contra hlt
    have : 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8d : 8 ∣ Nat.card ↥((F.ρ i).R ⊓ W) := by
    rw [hs]
    exact (Nat.pow_dvd_pow 2 hs3 : 2 ^ 3 ∣ 2 ^ s)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card ↥((F.ρ i).R ⊓ W) := orderOf_eq_card_of_forall_mem_zpowers hg
  have hmem : (⟨F.a i, (F.ha i).1⟩ : ↥((F.ρ i).R ⊓ W)) ∈ Submonoid.powers g :=
    mem_powers_iff_mem_zpowers.mpr (hg _)
  obtain ⟨k, hk0⟩ := hmem
  have hk : g ^ k = (⟨F.a i, (F.ha i).1⟩ : ↥((F.ρ i).R ⊓ W)) := hk0
  have h4 : (⟨F.a i, (F.ha i).1⟩ : ↥((F.ρ i).R ⊓ W)) ^ 4 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one (F.a i)
    rw [(F.ha i).2] at this
    simpa using this
  have hdvd : orderOf g ∣ k * 4 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hk]
    exact h4
  rw [hord] at hdvd
  have h8k : 8 ∣ k * 4 := h8d.trans hdvd
  obtain ⟨k', hk'⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
  refine ⟨((g ^ k' : ↥((F.ρ i).R ⊓ W)) : Y), ?_, ?_⟩
  · rw [← hRW]
    exact (g ^ k').2
  · have e : g ^ k' * g ^ k' = ⟨F.a i, (F.ha i).1⟩ := by
      rw [← pow_add, ← two_mul, ← hk', hk]
    exact (congrArg Subtype.val e).symm

end Squares

section InO2


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}

theorem oddQuotMk_eq_one_of_mem {y : Y} (hyC : y ∈ Subgroup.centralizer ({t} : Set Y))
    (hy : y ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y))) : oddQuotMk t ⟨y, hyC⟩ = 1 := by
  rw [oddQuotMk_eq_one_iff]
  obtain ⟨z, hz, hzy⟩ := hy
  have : z = ⟨y, hyC⟩ := Subtype.ext hzy
  rw [← this]
  exact hz

theorem mem_pCore_of_mem_twin (h : PerpHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) (hz : IsUniqueInvolution J t) {x : Y}
    (hx : x ∈ J) (hxC : x ∈ Subgroup.centralizer ({t} : Set Y)) :
    oddQuotMk t ⟨x, hxC⟩ ∈ pCoreOf 2 (⊤ : Subgroup (OddQuot t)) := by
  have hsub : IsSubnormal J (Subgroup.centralizer ({t} : Set Y)) :=
    h.partIHypG.cls.isSubnormal_of_uniqueInvolution hJ hz
  have hOJ : oddCoreIn J ≤ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
    oddCoreIn_le_of_isSubnormal hsub
  have h2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J) := Perp23.isPGroup_quot_of_member h hJ
  have hp : IsPGroup 2 ↥(modOdd t J) := by
    rintro ⟨x₀, hx₀⟩
    obtain ⟨k, hkJ, rfl⟩ := mem_modOdd_iff.mp hx₀
    obtain ⟨m, hm⟩ := Perp23.exists_pow_mem_oddCoreIn h2 hkJ
    refine ⟨m, Subtype.ext ?_⟩
    show (oddQuotMk t k) ^ 2 ^ m = 1
    rw [← map_pow]
    have hkC : (k : Y) ^ 2 ^ m ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.pow_mem _ k.2 _
    have e : k ^ 2 ^ m = ⟨(k : Y) ^ 2 ^ m, hkC⟩ := Subtype.ext (by simp)
    rw [e]
    exact oddQuotMk_eq_one_of_mem hkC (hOJ hm)
  have hsubM : (modOdd t J).IsSubnormal := A7Q.Vertex.isSubnormal_modOdd hsub
  have hsubO : IsSubnormal (modOdd t J) ⊤ := CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hsubM
  exact CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsubO hp
    (oddQuotMk_mem_modOdd hx hxC)

theorem t'_mem_centralizer (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
    (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    F.t' ∈ Subgroup.centralizer ({t} : Set Y) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (F.zt' c hc).symm

theorem tightInO2_t' (h : PerpHypR r n Y R S t)
    (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
    (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    TightInO2 (oddQuotMk t ⟨F.t', t'_mem_centralizer F c hc⟩) := by
  have haC : ∀ i, F.a i ∈ Subgroup.centralizer ({t} : Set Y) := fun i =>
    isUniqueInvolution_le_centralizer (F.hz i) (F.a_mem_K i)
  have hmem : ∀ i, oddQuotMk t ⟨F.a i, haC i⟩ ∈ pCoreOf 2 (⊤ : Subgroup (OddQuot t)) := fun i =>
    mem_pCore_of_mem_twin h (F.ρ i).hK (F.hz i) (F.a_mem_K i) (haC i)
  have e : (⟨F.t', t'_mem_centralizer F c hc⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) =
      ⟨F.a 0, haC 0⟩ * ⟨F.a 1, haC 1⟩ * ⟨F.a 2, haC 2⟩ * ⟨F.a 3, haC 3⟩ :=
    Subtype.ext F.hrel
  refine ⟨pCoreOf 2 (⊤ : Subgroup (OddQuot t)),
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_of_normal 2 ⊤ inferInstance,
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 ⊤, ?_⟩
  rw [e, map_mul, map_mul, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem 0) (hmem 1)) (hmem 2))
    (hmem 3)

end InO2

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
