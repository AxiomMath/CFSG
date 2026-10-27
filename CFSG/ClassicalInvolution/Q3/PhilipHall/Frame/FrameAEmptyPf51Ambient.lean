module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem FrameTightDatum.eq_top_of_normal {T : Type} [Group T] {R : Subgroup T} {t : T}
    (hd : FrameTightDatum R t) {N : Subgroup T} (hN : N.Normal) (hRN : R ≤ N) : N = ⊤ := by
  rw [eq_top_iff, ← hd.selfGen]
  refine iSup_le fun g => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hN.conj_mem x (hRN hx) g

namespace FrameAEmptyPf

class CaseIAmbient (T : Type) [Group T] : Prop where
  fstar_simple : IsSimpleGroup ↥(genFittingFStar T)
  fstar_nonabelian : ∃ a b : ↥(genFittingFStar T), a * b ≠ b * a
  oddCore_eq_bot : classicalInvolutionOddCore T = ⊥

attribute [instance] CaseIAmbient.fstar_simple

namespace CaseIAmbient

variable {T : Type} [Group T]

theorem of_simple [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) {t : T}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : CaseIAmbient T := by
  have hnab' : ∃ a b : ↥(⊤ : Subgroup T), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  have : IsSimpleGroup ↥(⊤ : Subgroup T) := (Subgroup.topEquiv (G := T)).isSimpleGroup
  have hC : Subgroup.centralizer ((⊤ : Subgroup T) : Set T) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center T := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have htop : genFittingFStar T = ⊤ := genFittingFStar_eq_of_normal_simple ⊤ hnab' hC
  refine ⟨?_, ?_, ?_⟩
  · exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnab
    refine ⟨⟨a, htop ▸ Subgroup.mem_top a⟩, ⟨b, htop ▸ Subgroup.mem_top b⟩, fun h => hab ?_⟩
    exact congrArg Subtype.val h
  · rcases (classicalInvolutionOddCore_normal T).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card (classicalInvolutionOddCore T)) :=
        CFSG.ComponentClassification.OddCore.odd_card T
      rw [h, Subgroup.card_top] at hodd
      have h2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
      have hdvd := orderOf_dvd_natCard t
      rw [h2] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

variable [Finite T] [CaseIAmbient T]

theorem centralizer_fstar_eq_bot :
    Subgroup.centralizer (genFittingFStar T : Set T) = ⊥ :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.centralizer_fstar_eq_bot fstar_nonabelian

theorem fstar_le_of_normal {N : Subgroup T} (hN : N.Normal) (hN1 : N ≠ ⊥) :
    genFittingFStar T ≤ N :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.fstar_le_of_normal fstar_nonabelian hN hN1

theorem center_eq_bot : Subgroup.center T = ⊥ := by
  by_contra h
  obtain ⟨a, b, hab⟩ := (fstar_nonabelian : ∃ a b : ↥(genFittingFStar T), a * b ≠ b * a)
  have hle := fstar_le_of_normal (inferInstance : (Subgroup.center T).Normal) h
  exact hab (Subtype.ext (Subgroup.mem_center_iff.mp (hle b.2) a))

theorem not_mem_center {a : T} (ha : a ≠ 1) : a ∉ Subgroup.center T := by
  rw [center_eq_bot, Subgroup.mem_bot]
  exact ha

theorem isSimpleGroup_generalizedFitting : IsSimpleGroup (CFSG.generalizedFitting T) := by
  rw [← CFSG.Adapters.genFittingFStar_eq_foundations T]
  exact fstar_simple

end CaseIAmbient

end FrameAEmptyPf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
