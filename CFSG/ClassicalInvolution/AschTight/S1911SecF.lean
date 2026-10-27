module

public import CFSG.ClassicalInvolution.AschTight.S1911SecE
public import CFSG.ClassicalInvolution.AschTight.S1911F0c
public import CFSG.ClassicalInvolution.AschTight.S1911FusG

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem sectionData_fieldInvolution (hd : Sec19Data p f K z S W) (h9 : p ^ f ≠ 9) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩ ∧
      HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)) ∧
      Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)) ∧
      Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G ∧
      CITBelowU p e₀ (Nat.card G) ∧
      LieSystemMod p e₀ (restrictFamily (conjFamily (perfectCoreIn K a))
        (conjGen (perfectCoreIn K a))) := by
  obtain ⟨e₀, hf, h5, hzA, hmem, hLS⟩ := lieSystemMod_fieldInvolution factF0 hd h9 haS ha2 haX
  exact ⟨e₀, hf, h5, hzA, hmem, hypOmegaMod_conjFamily hd hzA hmem,
    dEdgeless_conjFamily hd h5 hzA hmem, card_centralizer_lt hd haS haX, hd.ih e₀ h5, hLS⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
