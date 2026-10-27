module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnRad
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Sub
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Tr

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def RadFixPow (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) : Prop :=
  ∀ b : MulAut (hypPSU h r ε),
    (∀ g ∈ unRad h hε hd, b (hypProj h r ε g) = hypProj h r ε g) → b ^ p = 1

theorem std_data_hyp [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (h : UnitaryFieldData p f K)
    (hr : 1 ≤ r) (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) (hstd : RadFixPow h hε hd) :
    ∃ Rs : Subgroup (hypPSU h r ε), IsPGroup p ↥Rs ∧
      Rs ≤ projIsoStabilizer h r ε (hypFlag h r ε d) ∧
      projIsoStabilizer h r ε (hypFlag h r ε d) ≤ normalizer (Rs : Set (hypPSU h r ε)) ∧
      ∀ b : MulAut (hypPSU h r ε), (∀ y ∈ Rs, b y = y) → b ^ p = 1 := by
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have : Nonempty (HypIndex r ε) := ⟨Sum.inl ⟨0, hr⟩⟩
  obtain ⟨h1, h2⟩ := map_le_normalizer_map (hypProj h r ε) (unRad_le_isoStabilizer h hε hd)
    (fun s hs g hg => conj_mem_unRad h hε hd hs hg)
  refine ⟨(unRad h hε hd).map (hypProj h r ε), ?_, h1, h2, fun b hb => ?_⟩
  · exact isPGroup_map_of_forall_pow _ fun g hg => pow_eq_one_of_mem_radFl hp3 hg
  · exact hstd b fun g hg => hb _ ⟨g, hg, rfl⟩

theorem e1Core_hyp [Finite K] [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (h : UnitaryFieldData p f K)
    (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hstd : ∀ (d : ℕ) (_ : 1 ≤ d) (hd : d ≤ r), RadFixPow h hε hd)
    (hBT : LieType.BorelTits.Holds (hypPSU h r ε) p) : E1Core p (hypPSU h r ε) := by
  intro b hb1 hbr hHH E hE hinv
  by_contra hne
  obtain ⟨M, S, hM, hS, hR⟩ := e1_engine hBT b hHH hE hinv hne
  have hmem : M ∈ maximalParabolics h r ε := ⟨hM, _, ⟨S, rfl⟩, hS⟩
  obtain ⟨W, ⟨hW0, hWiso⟩, rfl⟩ :=
    ((unitary_maximal_parabolics h hr hε).1 ▸ hmem :
      M ∈ projIsoStabilizer h r ε '' {W | W ≠ ⊥ ∧ ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0})
  obtain ⟨hd1, hdr, g, hg⟩ := exists_smul_hypFlag_eq h hε hW0 hWiso
  rw [← hg, ← projIsoStabilizer_map_conj] at hR
  obtain ⟨Rs, hRp, hRle, hRnorm, hpow⟩ :=
    std_data_hyp hp2 h hr hε hdr (hstd _ hd1 hdr)
  set x := hypProj h r ε g with hx
  have hnorm : ∀ s ∈ projIsoStabilizer h r ε (hypFlag h r ε (Module.finrank K W)),
      ∀ y ∈ Rs, s * y * s⁻¹ ∈ Rs :=
    fun s hs y hy => (Subgroup.mem_normalizer_iff.mp (hRnorm hs) y).mp hy
  obtain ⟨h1, h2⟩ := map_le_normalizer_map (MulAut.conj x).toMonoidHom hRle hnorm
  have hfix := hR _ (hRp.map _) h1 h2
  have hb' := hpow ((MulAut.conj x)⁻¹ * b * MulAut.conj x) (fix_conj_of_fix x b hfix)
  have hbeq : b = MulAut.conj x * ((MulAut.conj x)⁻¹ * b * MulAut.conj x) * (MulAut.conj x)⁻¹ := by
    group
  have hbr1 : b ^ p = 1 := by
    rw [hbeq, conj_pow, hb', mul_one, mul_inv_cancel]
  have hdvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hbr1
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with hord | hord
  · exact hb1 (orderOf_eq_one_iff.mp hord)
  · exact hbr ⟨1, by rw [hord, mul_one]⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
