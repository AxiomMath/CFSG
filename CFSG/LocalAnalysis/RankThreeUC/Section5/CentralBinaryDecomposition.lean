module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinarySubgroup
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralMovedFixedSubgroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryDecomposition

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem p_ne_two (hc : BinaryActionRankCounterexample G p P T B e ρ) : p ≠ 2 := by
  rintro rfl
  exact absurd hc.oddPrimeClassTwoAction.setting.odd (by decide)

theorem fixedSpace_eq_bot (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e)
    (hXne : X hc ≠ ⊥) : BinaryRepresentations.fixedSpace (sigma hc) (X hc) = ⊥ := by
  have hcb := CentralBinarySubgroup.central_binary hc he
  have h := CentralMovedFixedSubgroup.fixed_eq_one hc he (X hc) hXne hcb.2.2.2.1
    hcb.2.2.2.2.1 hcb.2.2.2.2.2.1
  rw [eq_bot_iff]
  intro v hv
  rw [BinaryRepresentations.mem_fixedSpace_iff] at hv
  have h1 : v.val = 1 := h v.val fun ψ hψ => by
    have := hv ψ hψ
    have h2 := sigma_apply hc ψ v
    rw [this] at h2
    exact h2.symm
  rw [Submodule.mem_bot]
  exact h1

theorem commSpace_eq_top (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e)
    (hXne : X hc ≠ ⊥) : BinaryRepresentations.commSpace (sigma hc) (X hc) = ⊤ := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcb := CentralBinarySubgroup.central_binary hc he
  have hel := hcb.2.2.1
  haveI : Finite (X hc) := inferInstance
  have hcard : ((Nat.card (X hc) : ℕ) : ZMod p) ≠ 0 :=
    BinaryRepresentations.natCard_ne_zero_of_le (p := 2) (q := p) (fun h => p_ne_two hc h.symm) hel le_rfl
  have hsplit := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeCommSpaceAveraging.split (sigma hc) (X hc) hel.1 hcard
  rw [fixedSpace_eq_bot hc he hXne, sup_bot_eq] at hsplit
  exact hsplit

theorem decomposition (hc : BinaryActionRankCounterexample G p P T B e ρ) (he : Odd e)
    (hXne : X hc ≠ ⊥) :
    iSupIndep (fun K : BinaryRepresentations.hyperplanes 2 (X hc) => E hc K.val) ∧
      (⨆ K : BinaryRepresentations.hyperplanes 2 (X hc), E hc K.val) = ⊤ := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  have hel := (CentralBinarySubgroup.central_binary hc he).2.2.1
  have htop := commSpace_eq_top hc he hXne
  have h1 := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BinaryCenterDecomposition.iSupIndep_inf (p_ne_two hc) (sigma hc) (X hc) hel
  have h2 := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BinaryCenterDecomposition.iSup_eq (p_ne_two hc) (sigma hc) (X hc) hel
  rw [htop] at h1 h2
  simp only [top_inf_eq] at h1 h2
  exact ⟨h1, h2⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryDecomposition
