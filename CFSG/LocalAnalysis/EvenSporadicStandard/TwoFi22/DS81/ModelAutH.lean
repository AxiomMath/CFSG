module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutTheta
public import Certificates.Certificate25290

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore
open CFSG.Monster.B.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_centralizerCore_elementary_abelian :
    ∃ N0 : Subgroup fi22P, (∀ v ∈ N0, v ^ 2 = 1) ∧ Nat.card N0 = 2 ^ 10 ∧ CentralizerCore N0 := by
  obtain ⟨N, hNP, hsq, hcomm, hcard, hreg, huniq, hgen⟩ := Certificates.certificate25290
  have hmem : ∀ v : fi22P, v ∈ N.subgroupOf fi22P ↔ (v : Equiv.Perm (Fin 3510)) ∈ N :=
    fun v => Subgroup.mem_subgroupOf
  refine ⟨N.subgroupOf fi22P, fun v hv => ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact hsq _ ((hmem v).1 hv)
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  · refine centralizerCore_of_orbit (N.subgroupOf fi22P) 0
      (fun v hv w hw => Subtype.ext ?_) (fun v hv h => Subtype.ext ?_) (fun q hq => ?_) ?_
    · rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm _ ((hmem v).1 hv) _ ((hmem w).1 hw)
    · exact hreg _ ((hmem v).1 hv) h
    · obtain ⟨v, hv, hv0⟩ := huniq q fun v hv hvq => by
        have h1 := hq ⟨v, hNP hv⟩ ((hmem ⟨v, hNP hv⟩).2 hv) hvq
        exact congrArg Subtype.val h1
      exact ⟨⟨v, hNP hv⟩, (hmem ⟨v, hNP hv⟩).2 hv, hv0⟩
    · refine hgen.trans (Subgroup.closure_mono ?_)
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨(v : Equiv.Perm (Fin 3510)) 0, ⟨⟨v, hNP hv⟩, (hmem ⟨v, hNP hv⟩).2 hv, rfl⟩, ?_⟩
      dsimp only
      rw [fi22Theta_eq (g := ⟨v, hNP hv⟩) (i := v 0) rfl]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, fi22OuterZP_eq]

end CFSG.EvenSporadicStandard.TwoFi22.DS81
