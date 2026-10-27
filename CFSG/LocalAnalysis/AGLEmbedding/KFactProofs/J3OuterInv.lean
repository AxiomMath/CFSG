module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverA6
public import Certificates.Certificate9466
import all CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvGroup

public section

namespace CFSG.AGLEmbedding

open KFactProofs.J3Sylow KFactProofs.J3OuterInv CFSG.Quasithin CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem outer_check : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → ∃ (T : Sylow 3 J) (φ : MulAut J),
        (∀ x ∈ (T : Subgroup J), φ x ∈ (T : Subgroup J)) ∧
        φ ∉ (MulAut.conj : J →* MulAut J).range ∧
        (∀ z ∈ centerOf (T : Subgroup J), z ≠ 1 →
          Subgroup.centralizer {z} ≤ Subgroup.normalizer ((T : Subgroup J) : Set J) →
          Subgroup.centralizer {z} ≤ T) ∧
        (∀ x ∈ Subgroup.normalizer ((T : Subgroup J) : Set J), (MulAut.conj x * φ) ^ 2 = 1 →
          ∀ E : Subgroup J, E ≤ T → IsMulCommutative E → (∀ y ∈ E, y ^ 3 = 1) →
            Nat.card E = 9 → ∃ y ∈ E, (MulAut.conj x * φ) y ≠ y) :=
  Certificates.certificate9466

theorem outer_mul_inv_mem {J : Type*} [Group J] [Finite J] (hOut : Nat.card (Outer J) ≤ 2)
    {β γ : MulAut J} (hβ : β ∉ (MulAut.conj : J →* MulAut J).range)
    (hγ : γ ∉ (MulAut.conj : J →* MulAut J).range) :
    β * γ⁻¹ ∈ (MulAut.conj : J →* MulAut J).range := by
  by_contra h
  have : Finite (Outer J) := inferInstance
  let q : MulAut J →* Outer J := QuotientGroup.mk' (inner J)
  have hβ' : β ∉ inner J := hβ
  have hγ' : γ ∉ inner J := hγ
  have h' : β * γ⁻¹ ∉ inner J := h
  have h1 : q β ≠ 1 := fun e => hβ' ((QuotientGroup.eq_one_iff β).1 e)
  have h2 : q γ ≠ 1 := fun e => hγ' ((QuotientGroup.eq_one_iff γ).1 e)
  have h3 : q β ≠ q γ := fun e => h' (QuotientGroup.eq_iff_div_mem.1 e)
  have hinj : Function.Injective (![1, q β, q γ] : Fin 3 → Outer J) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fin] at this
  omega

theorem kFactJ3OuterInvolution_of
    (hOR : KFactJ3OuterRank) : KFactJ3OuterInvolution := by
  intro J _ _ hJ α hα2 hαout E hE hE9
  obtain ⟨-, hover⟩ := j3CoverFacts J hJ
  obtain ⟨hOut, hrk⟩ := hOR J hJ
  obtain ⟨eJ⟩ := hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let f := eJ.trans b.symm
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsimple : IsSimpleGroup J := MulEquiv.isSimpleGroup (H := Blueprint.NativeSporadic.J3) f
  have hJcard : Nat.card J = 50232960 := by
    rw [Nat.card_congr f.toEquiv]; exact CFSG.Sporadic.J3.card_J3
  obtain ⟨PJS, φ, hφT, hφout, hcent, hfinal⟩ := outer_check J ⟨eJ⟩ hsimple hJcard
  have hF : J3SylowFacts J (PJS : Subgroup J) := kFactJ3Sylow J ⟨eJ⟩ PJS
  have hnonab : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, -, y, -, hxy⟩ := hF.nonabelian
    exact ⟨x, y, hxy⟩
  have hsetup : OuterSetup J (PJS : Subgroup J) (centerOf (PJS : Subgroup J)) φ :=
    { cen := fun z hz => by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
        · have : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g => hz g
          rwa [h, Subgroup.mem_bot] at this
        · obtain ⟨x, y, hxy⟩ := hnonab
          have hx : x ∈ Subgroup.center J := h ▸ Subgroup.mem_top x
          exact absurd (Subgroup.mem_center_iff.1 hx y).symm hxy
      overgroup := hover PJS
      Zc := fun z hz x hx => (mem_centerOf.1 hz).2 x hx
      Zcomm := by
        have := hF.center_elem.1.1
        exact this
      Z3 := hF.center_elem.1.2
      Z9 := hF.center_elem.2
      rank := by
        rintro ⟨W, hW1, hW2, hW3⟩
        have h4 : 4 ≤ Open.pRank 3 (⊤ : Subgroup J) :=
          le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three _)
            ⟨W, le_top, ⟨hW1, hW2⟩, by rw [hW3]; norm_num⟩
        omega
      cent := hcent
      out := fun β γ hβ hγ => outer_mul_inv_mem hOut hβ hγ
      phiT := hφT
      phiOut := hφout
      final := hfinal }
  exact no_fixed_elem hsetup hα2 hαout hE.1 hE.2 hE9

end CFSG.AGLEmbedding
