module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSOverDefs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import Certificates.Certificate31073
import CFSG.Adapters.TauCetiLieModels
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveU35
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5I50
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Restrict
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbeddingD2 Certificates.ThreeFourTwoHSU35

@[expose] def threeFourTwoQFive : TauCeti.PrimePower := ⟨5, 1, Nat.prime_five, Nat.one_pos⟩

theorem valid_twistedA_two_threeFourTwoQFive :
    (TauCeti.LieTypeIndex.twistedA 2 threeFourTwoQFive).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  refine ⟨⟨le_rfl, fun _ => ?_⟩, not_false⟩
  rw [TauCeti.PrimePower.card_def]
  show 3 ≤ 5 ^ 1
  norm_num

@[expose] def threeFourTwoU35Index : TauCeti.ValidLieTypeIndex :=
  ⟨.twistedA 2 threeFourTwoQFive, valid_twistedA_two_threeFourTwoQFive⟩

private theorem statedClassicalModel_catU35 :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (TauCeti.CFSGIndex.lie threeFourTwoU35Index).Group
      .PSU 3 5 1 := by
  have hL := CFSG.Models.lieModel_twistedA 2 threeFourTwoQFive
    valid_twistedA_two_threeFourTwoQFive (MulEquiv.refl _)
  simp only [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
    TauCeti.LieTypeIndex.characteristic_twistedA, TauCeti.LieTypeIndex.fieldExponent_twistedA]
    at hL
  exact hL.2.resolve_right fun h => absurd h.1 (by norm_num)

@[expose] def hsU35Label (i : Fin 50) : Fin 100 :=
  ⟨hsU35Labels[(i : ℕ)]! % 100, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def hsU35Gen (k : Fin 6) : Equiv.Perm (Fin 100) :=
  wordVal [hsOX, hsOY] (hsU35GenWords.getD k [])

theorem hsU35Gen_mem (k : Fin 6) : hsU35Gen k ∈ hsOUA := by
  refine wordVal_mem _ hsOUA (fun g hg => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

private theorem hsU35_label_facts :
    Function.Injective hsU35Label ∧ ∀ (k : Fin 6) (i : Fin 50),
      ((hsU35Gen k (hsU35Label i) : Fin 100) : ℕ) =
        hsU35Labels[(HNUnitaryBridge.smallPerms[(k : ℕ)]!)[(i : ℕ)]!]! := by
  have h := Certificates.certificate31073
  simp only [hsU35Check, labelsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨-, hlt⟩, hdist⟩, hacts⟩ := h
  have hmod : ∀ i < 50, hsU35Labels[i]! % 100 = hsU35Labels[i]! := fun i hi =>
    Nat.mod_eq_of_lt (hlt i hi)
  refine ⟨fun i j hij => ?_, fun k i => ?_⟩
  · have h1 : hsU35Labels[(i : ℕ)]! = hsU35Labels[(j : ℕ)]! := by
      have := congrArg Fin.val hij
      simp only [hsU35Label] at this
      rwa [hmod i i.2, hmod j j.2] at this
    rcases hdist i i.2 j j.2 with h2 | h2
    · exact Fin.ext h2
    · exact absurd h1 h2
  · have hrep := CFSG.AGLEmbedding.MaxD2.wT_rep hsU35_gsU hsU35_giU (hsU35GenWords.getD k [])
    have hk := hacts k k.2
    simp only [actsOK, allBelow_eq_true, beq_iff_eq] at hk
    have hi := hk i i.2
    show ((wordVal hsU35S (hsU35GenWords.getD k []) (hsU35Label i) : Fin 100) : ℕ) = _
    rw [← hrep.apply (hsU35Label i)]
    simp only [hsU35Label, hmod i i.2]
    exact hi

theorem nonempty_hsOUA_mulEquiv_catU35 :
    Nonempty (↥hsOUA ≃* (TauCeti.CFSGIndex.lie threeFourTwoU35Index).Group) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hι, hact⟩ := hsU35_label_facts
  obtain ⟨σ, hσ, hσgen⟩ := CFSG.EvenSporadicStandard.HNRecog.Simple2S5.exists_gens_i50
  have hgσ : ∀ (k : Fin 6) (i : Fin 50), hsU35Gen k (hsU35Label i) = hsU35Label (σ k i) := by
    intro k i
    apply Fin.ext
    rw [hact k i]
    have h1 : (σ k i : ℕ) = (HNUnitaryBridge.smallPerms[(k : ℕ)]!)[(i : ℕ)]! := hσ k i
    simp only [hsU35Label, ← h1]
    have h := Certificates.certificate31073
    simp only [hsU35Check, labelsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true,
      decide_eq_true_eq] at h
    exact (Nat.mod_eq_of_lt (h.1.1.2 _ (σ k i).2)).symm
  set St := CFSG.EvenSporadicStandard.HNRecog.Simple2S5.stabEmb
    (G := Equiv.Perm (Fin 100)) hsU35Label with hSt
  have hgSt : ∀ k, hsU35Gen k ∈ St := fun k =>
    ⟨σ k, fun b => by rw [Equiv.Perm.smul_def, hgσ k b]⟩
  set I' : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure (Set.range hsU35Gen) with hI'
  have hI'St : I' ≤ St := (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact hgSt k)
  have hI'U : I' ≤ hsOUA := (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact hsU35Gen_mem k)
  obtain ⟨ρ, hρ⟩ := CFSG.EvenSporadicStandard.HNRecog.Simple2S5.exists_restrictHom
    (G := Equiv.Perm (Fin 100)) hsU35Label hι
  let ρ' : ↥I' →* Equiv.Perm (Fin 50) := ρ.comp (Subgroup.inclusion hI'St)
  have hρ' : ∀ k, ρ' ⟨hsU35Gen k, Subgroup.subset_closure ⟨k, rfl⟩⟩ = σ k := by
    intro k
    ext b
    have h1 := hρ ⟨hsU35Gen k, hgSt k⟩ b
    rw [Equiv.Perm.smul_def] at h1
    change hsU35Gen k (hsU35Label b) =
      hsU35Label (ρ' ⟨hsU35Gen k, Subgroup.subset_closure ⟨k, rfl⟩⟩ b) at h1
    rw [hgσ k b] at h1
    exact congrArg Fin.val (hι h1).symm
  have hle : CFSG.EvenSporadicStandard.HNRecog.Simple2S5.i50 ≤ ρ'.range := by
    rw [← hσgen, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hρ' k⟩
  have hcardU : Nat.card ↥hsOUA = 126000 := card_hsOUA
  have hge : 126000 ≤ Nat.card ↥I' := by
    have h1 := Subgroup.card_le_of_le hle
    rw [CFSG.EvenSporadicStandard.HNRecog.Simple2S5.card_i50] at h1
    exact h1.trans (Nat.card_le_card_of_surjective _ ρ'.rangeRestrict_surjective)
  have hcard : Nat.card ↥I' = 126000 :=
    le_antisymm (hcardU ▸ Subgroup.card_le_of_le hI'U) hge
  have hI'eq : I' = hsOUA := Subgroup.eq_of_le_of_card_ge hI'U (by rw [hcardU, hcard])
  obtain ⟨e₁⟩ := CFSG.EvenSporadicStandard.HNRecog.Simple2S5.nonempty_mulEquiv_i50_of_le_range
    ρ' hcard hle
  obtain ⟨e₂⟩ := CFSG.EvenSporadicStandard.HNRecog.Simple2S5.nonempty_psu3_mulEquiv_i50
  obtain ⟨e₃⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    CFSG.EvenSporadicStandard.HNRecog.Section3Model.psu3_five_statedClassicalModel
    statedClassicalModel_catU35
  exact ⟨((MulEquiv.subgroupCongr hI'eq.symm).trans (e₁.trans e₂.symm)).trans e₃⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
