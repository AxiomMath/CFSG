module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34LocalC
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.GH74.QTGen4.DSGen4.OpenLeavesAmal

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem leafL34Local [DSLeaf LeafDSAA6] [DSLeaf LeafDSACaseIFrattini] [DSLeaf LeafDSACaseIStep4]
    [DSLeaf LeafDSACaseIOffender] [DSLeaf LeafSylowS] : LeafL34Local := by
  intro Mdl hMdl G _ _ L1 L2 S h c1 c2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite Mdl.Y := by
    obtain ⟨_, F, hFF, hFfin, _, _, hiso⟩ := CFSG.Quasithin.H13.F431.L3.exists_equiv_projSL3 Mdl.lie
    obtain ⟨e⟩ := hiso
    exact Finite.of_equiv _ e.symm.toEquiv
  have hB : bigB L1 L2 S ≤ L1 ⊓ L2 := dsaa6 h c1 c2
  have hB1 : L1 ⊔ bigB L1 L2 S = L1 := sup_eq_left.mpr (hB.trans inf_le_left)
  have hB2 : L2 ⊔ bigB L1 L2 S = L2 := sup_eq_left.mpr (hB.trans inf_le_right)
  have hfr := dsa_case_i_frattini h c1 c2
  obtain ⟨hsum, hSc, ⟨hQ1e0, hQ1c0⟩, ⟨hQ2e0, hQ2c0⟩⟩ := dsa_case_i_step4 h c1 c2
  obtain ⟨-, -, hN1, hN2, -, -, hcard4⟩ := dsa_case_i_offender h c1 c2
  have hsyl1 := sylow_s h.hyp
  have hsyl2 := sylow_s h.hyp.symm
  rw [bigB_comm] at hsyl2
  have hsylS1 : IsSylowTwoOf S L1 := by
    have := hsyl1.2.1
    rwa [hB1] at this
  have hsylS2 : IsSylowTwoOf S L2 := by
    have := hsyl2.2.1
    rwa [hB2] at this
  have hQ1S : pCoreOf 2 L1 ≤ S := by
    have := hsyl1.2.2
    rwa [hB1] at this
  have hQ2S : pCoreOf 2 L2 ≤ S := by
    have := hsyl2.2.2
    rwa [hB2] at this
  have hQ1eq : dsQ L1 L2 S = pCoreOf 2 L1 := by
    unfold dsQ
    rw [hB1]
  have hQ2eq : dsQ L2 L1 S = pCoreOf 2 L2 := by
    unfold dsQ
    rw [bigB_comm, hB2]
  have hZ1 : dsZi L1 S = pCoreOf 2 L1 := hfr.1.symm.trans hQ1eq
  have hZ2 : dsZi L2 S = pCoreOf 2 L2 := hfr.2.symm.trans hQ2eq
  rw [hQ1eq] at hQ1e0 hQ1c0
  rw [hQ2eq] at hQ2e0 hQ2c0
  rw [hZ1] at hN1
  rw [hZ2] at hN2
  rw [hZ1, hZ2] at hcard4
  have hS64 : Nat.card S = 64 := by rw [hSc]; norm_num
  have hquot1 : IsL2Quot 2 (oTwoQuot ↥L1) := (A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1).quot
  have hquot2 : IsL2Quot 2 (oTwoQuot ↥L2) := (A5Par.of_hyp111R Finite4.gen4 h.hyp.symm h.ns2).quot
  have hnt1 : ∃ l ∈ L1, ∃ e ∈ pCoreOf 2 L1, ⁅l, e⁆ ∉ (⊥ : Subgroup G) := by
    rw [hZ1] at c1
    by_contra hcon
    push_neg at hcon
    apply c1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : ⁅l, e⁆ = 1 := Subgroup.mem_bot.mp (hcon l hl e he)
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hnt2 : ∃ l ∈ L2, ∃ e ∈ pCoreOf 2 L2, ⁅l, e⁆ ∉ (⊥ : Subgroup G) := by
    rw [hZ2] at c2
    by_contra hcon
    push_neg at hcon
    apply c2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : ⁅l, e⁆ = 1 := Subgroup.mem_bot.mp (hcon l hl e he)
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hEcard : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 4 := hcard4
  have hEcard' : Nat.card ↥(pCoreOf 2 L2 ⊓ pCoreOf 2 L1) = 4 := by rw [inf_comm]; exact hEcard
  have hL1B : L1 ⊓ L2 = bigB L1 L2 S := by
    have := F1.parabolic_inf_parabolic h.hyp
    rwa [hB1, hB2] at this
  have hL2B : L2 ⊓ L1 = bigB L1 L2 S := by
    have := F1.parabolic_inf_parabolic h.hyp.symm
    rw [bigB_comm, hB2, hB1] at this
    exact this
  have hBN1 : bigB L1 L2 S = L1 ⊓ Subgroup.normalizer (S : Set G) := by
    have := F1.bigB_eq_parabolic_inf h.hyp
    rw [hB1, inf_eq_left.mpr hsylS1.1] at this
    exact this
  have hBN2 : bigB L1 L2 S = L2 ⊓ Subgroup.normalizer (S : Set G) := by
    have := F1.bigB_eq_parabolic_inf h.hyp.symm
    rw [bigB_comm, hB2, inf_eq_left.mpr hsylS2.1] at this
    exact this
  obtain ⟨x, hx3⟩ : ∃ x : ↥(Mdl.M1 ⊓ Mdl.M2), orderOf x = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [hMdl.card_B0]; norm_num)
  have hx3' : orderOf (x : Mdl.Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hx3
  obtain ⟨ψ₁, hS1, hQ1, hN1'⟩ :=
    L34Loc.side_iso hsylS1 hS64 hQ1S hQ1e0 hQ1c0 hQ2S hQ2e0 hQ2c0 hEcard hN1 hquot1 hnt1
      hMdl.sylow1 hMdl.card_T0 hMdl.elem1 hMdl.card1 hMdl.nat1 hMdl.quot1 hMdl.elem2 hMdl.card2
      hMdl.le1 hMdl.le2 hMdl.ne x.2 hx3'
  obtain ⟨ψ₂, hS2, hQ2, hN2'⟩ :=
    L34Loc.side_iso hsylS2 hS64 hQ2S hQ2e0 hQ2c0 hQ1S hQ1e0 hQ1c0 hEcard' hN2 hquot2 hnt2
      hMdl.sylow2 hMdl.card_T0 hMdl.elem2 hMdl.card2 hMdl.nat2 hMdl.quot2 hMdl.elem1 hMdl.card1
      hMdl.le2 hMdl.le1 (Ne.symm hMdl.ne) ⟨x.2.2, x.2.1⟩ hx3'
  rw [hB1, hB2]
  refine ⟨ψ₁, ψ₂, hS1, hS2, ?_, ?_, ?_, ?_⟩
  · intro x
    calc (x : G) ∈ L2 ↔ (x : G) ∈ L1 ⊓ L2 := by
          rw [Subgroup.mem_inf]
          exact ⟨fun h2 => ⟨x.2, h2⟩, fun h2 => h2.2⟩
      _ ↔ (x : G) ∈ bigB L1 L2 S := by rw [hL1B]
      _ ↔ (x : G) ∈ Subgroup.normalizer (S : Set G) := by
          rw [hBN1, Subgroup.mem_inf]
          exact ⟨fun h2 => h2.2, fun h2 => ⟨x.2, h2⟩⟩
      _ ↔ (ψ₁ x : Mdl.Y) ∈ Subgroup.normalizer (Mdl.T0 : Set Mdl.Y) := hN1' x
      _ ↔ (ψ₁ x : Mdl.Y) ∈ Mdl.M2 := by
          rw [hMdl.normalizer_T0, Subgroup.mem_inf]
          exact ⟨fun h2 => h2.2, fun h2 => ⟨(ψ₁ x).2, h2⟩⟩
  · intro x
    calc (x : G) ∈ L1 ↔ (x : G) ∈ L2 ⊓ L1 := by
          rw [Subgroup.mem_inf]
          exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
      _ ↔ (x : G) ∈ bigB L1 L2 S := by rw [hL2B]
      _ ↔ (x : G) ∈ Subgroup.normalizer (S : Set G) := by
          rw [hBN2, Subgroup.mem_inf]
          exact ⟨fun h1 => h1.2, fun h1 => ⟨x.2, h1⟩⟩
      _ ↔ (ψ₂ x : Mdl.Y) ∈ Subgroup.normalizer (Mdl.T0 : Set Mdl.Y) := hN2' x
      _ ↔ (ψ₂ x : Mdl.Y) ∈ Mdl.M1 := by
          rw [hMdl.normalizer_T0, Subgroup.mem_inf]
          exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, (ψ₂ x).2⟩⟩
  · intro x
    rw [hQ1eq]
    exact hQ1 x
  · intro x
    rw [hQ2eq]
    exact hQ2 x

end CFSG.GH74.QTGen4.DSGen4
