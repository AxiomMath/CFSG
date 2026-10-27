module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Sev3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW

section Orbit4

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

theorem e187Orbit4Q8_proved : E187Orbit4Q8 := by
  intro G _ _ Ω K S R W H c z g t d₁ d₂ hz hzW hzH hSylz hg ht htS hCS hCSyl g₁ g₂ g₃ hc hd₁W hd₂W
    hshape m₁ m₂ m₃
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have hM : EtaMeet Ω := etaMeet_of_gen hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  have hSH : (S : Subgroup G) ≤ H := c.sylow_le hA
  have hbad := c.hbad_of_conj hA hM hz hg
  rw [← ht] at hbad
  obtain ⟨A, hA₁, -, hAN, hAD⟩ := hshape
  have hK₀ : conjSub g K ∈ Ω := hΩ.conjInvariant g K c.stand.mem
  have hK₀t : IsUniqueInvolution (conjSub g K) t := by rw [ht]; exact hz.conj g
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ c.stand.mem hRR hRK
  have hR₀ : IsSylow2In (conjSub g R) (conjSub g K) := hRsyl.conj g
  have hq8 : IsQ8 (conjSub g R) :=
    TwinDisc.forall_sylow_iso_of_exists (c.stand.q8 _ hK₀) _ hR₀
  have hS₁ : IsPGroup 2 ↥(conjSub g (S : Subgroup G)) := isPGroup_conjSub g S.isPGroup'
  have hR₀S : conjSub g R ≤ conjSub g (S : Subgroup G) := conjSub_mono hRS
  have hd₁S : d₁ ∈ conjSub g (S : Subgroup G) := hCS d₁ (hWS hd₁W) g₁.comm_t.symm
  have hd₂S : d₂ ∈ conjSub g (S : Subgroup G) := hCS d₂ (hWS hd₂W) g₂.comm_t.symm
  have hF6 : ∀ v ∈ conjSub g (S : Subgroup G), v * t = t * v → v ∈ H → v ∈ (S : Subgroup G) := by
    intro v hvS₁ hvt hvH
    have hPS₁ : (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ≤ conjSub g (S : Subgroup G) :=
      fun x hx => hCS x hx.1 (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    have hvC : v ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hvt
    have hM2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ⊔
        Subgroup.zpowers v) :=
      hS₁.to_le (sup_le hPS₁ (Subgroup.zpowers_le.mpr hvS₁))
    have hMle : (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ⊔ Subgroup.zpowers v ≤
        Subgroup.centralizer ({t} : Set G) ⊓ H :=
      sup_le (le_inf inf_le_right (inf_le_left.trans hSH))
        (Subgroup.zpowers_le.mpr ⟨hvC, hvH⟩)
    have heq := hCSyl.eq_of_le hM2 hMle le_sup_left
    have hv : v ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ⊔ Subgroup.zpowers v :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    rw [heq] at hv
    exact hv.1
  exact orbit4_core (S := (S : Subgroup G)) hΩ hK₀ hK₀t hR₀.1 hq8 hS₁ hR₀S g₁ g₂ g₃ hc hd₁S hd₂S m₁ m₂ m₃
    hF6 (fun u hu hu4 => hbad _ hK₀ hK₀t u hu hu4) hA₁ hAN hAD

end Orbit4

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
