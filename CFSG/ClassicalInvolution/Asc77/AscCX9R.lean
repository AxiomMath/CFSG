module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Odd

variable {H T : Type} [Group H] [Group T] [Finite H] [Finite T]

theorem ker_eq_oddCore_of_surjective (φ : H →* T) (hφ : Function.Surjective φ)
    (hT : classicalInvolutionOddCore T = ⊥) (hodd : Odd (Nat.card φ.ker)) :
    φ.ker = classicalInvolutionOddCore H := by
  apply le_antisymm
  · exact CFSG.ComponentClassification.OddCore.maximal H φ.ker φ.normal_ker hodd
  · intro x hx
    have hN : ((classicalInvolutionOddCore H).map φ).Normal :=
      Subgroup.Normal.map inferInstance φ hφ
    have hoddN : Odd (Nat.card ((classicalInvolutionOddCore H).map φ)) :=
      (CFSG.ComponentClassification.OddCore.odd_card H).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hle := CFSG.ComponentClassification.OddCore.maximal T _ hN hoddN
    have h1 : φ x ∈ classicalInvolutionOddCore T := hle (Subgroup.mem_map_of_mem φ hx)
    rw [hT, Subgroup.mem_bot] at h1
    exact h1

end Odd

section Twin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {K : Subgroup G}

@[expose] noncomputable def twinQuot (K : Subgroup G) (w : G) :
    ↥(exactCore w K) →* ↥K ⧸ classicalInvolutionOddCore ↥K :=
  toOddQuot (exactCore_le_left w K)

@[expose] noncomputable def twinBar (hK₂ : K ∈ tqMembers Ω w) :
    ↥(exactCore w K) →* ↥(T7H.exactImg Ω w K) :=
  ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω w))).comp
    (Subgroup.inclusion (exactCore_le_exactLayer hK₂))).codRestrict (T7H.exactImg Ω w K)
    fun m => T7H.mem_exactImg (Ω := Ω) m.2 (exactCore_le_exactLayer hK₂ m.2)

theorem coe_twinBar (hK₂ : K ∈ tqMembers Ω w) (m : ↥(exactCore w K)) :
    ((twinBar hK₂ m : ↥(T7H.exactImg Ω w K)) :
      ↥(exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w)) =
      T7H.toBar Ω w m (exactCore_le_exactLayer hK₂ m.2) := rfl

theorem twinBar_surjective (hK₂ : K ∈ tqMembers Ω w) :
    Function.Surjective (twinBar (Ω := Ω) hK₂) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem odd_natCard_ker_twinBar (hK₂ : K ∈ tqMembers Ω w) :
    Odd (Nat.card (twinBar (Ω := Ω) hK₂).ker) := by
  set X := exactLayer Ω w with hX
  have hle : (twinBar (Ω := Ω) hK₂).ker.map (exactCore w K).subtype ≤ oddCoreOf X := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : twinBar (Ω := Ω) hK₂ m = 1 := hm
    have h1 : ((twinBar (Ω := Ω) hK₂ m : ↥(T7H.exactImg Ω w K)) :
        ↥X ⧸ classicalInvolutionOddCore ↥X) = 1 := by rw [hm']; rfl
    rw [coe_twinBar] at h1
    unfold T7H.toBar at h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_map_of_mem X.subtype h1
  have hO : Odd (Nat.card (oddCoreOf X)) := by
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥X
  rw [← Subgroup.card_map_of_injective (exactCore w K).subtype_injective]
  exact hO.of_dvd_nat (Subgroup.card_dvd_of_le hle)

variable {p f : ℕ} [Fact p.Prime]

theorem ker_twinQuot_eq (hK₂ : K ∈ tqMembers Ω w)
    (hcov : ∀ x ∈ K, ∃ i ∈ exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) :
    (twinQuot K w).ker = (twinBar (Ω := Ω) hK₂).ker := by
  have hsurj : Function.Surjective (twinQuot K w) := toOddQuot_surjective _ hcov
  have hT : classicalInvolutionOddCore ↥(T7H.exactImg Ω w K) = ⊥ := by
    unfold oddCoreOf at hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hO
  rw [ker_eq_oddCore_of_surjective _ (twinBar_surjective hK₂) hT (odd_natCard_ker_twinBar hK₂)]
  exact (classicalInvolutionOddCore_eq_ker (exactCore_le_left w K) hsurj).symm

@[expose] noncomputable def twinEquiv (hK₂ : K ∈ tqMembers Ω w)
    (hcov : ∀ x ∈ K, ∃ i ∈ exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) :
    (↥K ⧸ classicalInvolutionOddCore ↥K) ≃* ↥(T7H.exactImg Ω w K) :=
  (QuotientGroup.quotientKerEquivOfSurjective (twinQuot K w)
      (toOddQuot_surjective _ hcov)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_twinQuot_eq hK₂ hcov hO)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (twinBar hK₂) (twinBar_surjective hK₂)))

theorem twinEquiv_mk (hK₂ : K ∈ tqMembers Ω w)
    (hcov : ∀ x ∈ K, ∃ i ∈ exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) {m : G} (hm : m ∈ exactCore w K) :
    ((twinEquiv hK₂ hcov hO (QuotientGroup.mk ⟨m, exactCore_le_left w K hm⟩) :
      ↥(T7H.exactImg Ω w K)) : ↥(exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w)) =
      T7H.toBar Ω w m (exactCore_le_exactLayer hK₂ hm) := by
  have h1 : (QuotientGroup.mk ⟨m, exactCore_le_left w K hm⟩ :
      ↥K ⧸ classicalInvolutionOddCore ↥K) = twinQuot K w ⟨m, hm⟩ := rfl
  have h2 : (QuotientGroup.quotientKerEquivOfSurjective (twinQuot K w)
      (toOddQuot_surjective _ hcov)).symm (twinQuot K w ⟨m, hm⟩) =
      (QuotientGroup.mk ⟨m, hm⟩ : ↥(exactCore w K) ⧸ (twinQuot K w).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1, twinEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h2]
  rfl

end Twin

section Sec

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem secMember_le_exactCore (hΩ : HypOmegaMod p f Ω) {F : Subgroup G} {w : G} {K : Subgroup G}
    (hwF : w ∈ F) (hw2 : IsPGroup 2 (Subgroup.zpowers w)) (hKΩ : K ∈ Ω)
    (hwK : w ∈ trivialOnQuot K) : AscE184Sect.secMember F K ≤ exactCore w K := by
  rw [← secMember_zpowers_eq_exactCore hΩ hw2 hKΩ hwK]
  refine iSup₂_le fun T hT => AscE184Sect.le_secMember ⟨hT.1, ?_⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_iff.mp (hT.2 hx) y (Subgroup.zpowers_le.mpr hwF hy)

end Sec

end CFSG.ClassicalInvolution.Asc77.CX
