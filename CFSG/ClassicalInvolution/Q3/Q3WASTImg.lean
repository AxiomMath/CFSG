module

public import CFSG.ClassicalInvolution.Q3.Q3WASTTags
public import CFSG.ClassicalInvolution.Q3.Q3WASTLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)


section Unique

variable {G : Type} [Group G]

theorem isUniqueInvolution_of_exact3 [Finite G] {L : Subgroup G}
    (hL : classicalInvolutionOddCore L = ⊥) {z : G} (hz : IsClassicalMember3 L z) :
    IsUniqueInvolution L z where
  mem := hz.mem
  ne_one := by
    intro h
    have := hz.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  sq := by
    have := pow_orderOf_eq_one z
    rwa [hz.orderOf_eq_two, pow_two] at this
  unique := by
    intro y hy hyy
    have hodd : Odd (Nat.card (ZMod 3)) := by
      rw [Nat.card_zmod]; decide
    obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hL
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have h2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
      have h3 : orderOf (⟨y, hy⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h2
      have h4 : orderOf (⟨z, hz.mem⟩ : ↥L) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact hz.orderOf_eq_two
      have := ((CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp h3).trans
        ((CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp h4).symm
      exact congrArg Subtype.val this

end Unique

section Sign

theorem chainSign_of_lifts3_comp {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n)
    (hcls : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n 3 1) {X : Type} [Group X] (φ : c.G →* X)
    (hker : φ.ker ≤ Subgroup.center c.G) {R₁ R₂ R₃ : Subgroup c.G} (h₁ : R₁ ∈ c.fund)
    (h₂ : R₂ ∈ c.fund) (h₃ : R₃ ∈ c.fund) {a₁ a₂ a₃ : X}
    (ha₁ : IsUniqueInvolution (R₁.map φ) a₁) (ha₂ : IsUniqueInvolution (R₂.map φ) a₂)
    (ha₃ : IsUniqueInvolution (R₃.map φ) a₃) (hcen : ∀ y : X, a₁ * a₃ * y = y * (a₁ * a₃))
    (hnorm : conjSub a₂ (R₁.map φ) = R₁.map φ) (hR₁₃ : Commutes (R₁.map φ) (R₃.map φ))
    (hne₁₂ : R₁.map φ ≠ R₂.map φ) (hne₃₂ : R₃.map φ ≠ R₂.map φ)
    (hnc₁₂ : ¬ Commutes (R₁.map φ) (R₂.map φ)) (hnc₃₂ : ¬ Commutes (R₃.map φ) (R₂.map φ)) :
    ((∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₂.map φ) (R₃.map φ)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (R₂.map φ) (R₃.map φ)) := by
  subst hc
  exact chainSign_of_lifts3 hcls hadm φ hker h₁ h₂ h₃ ha₁ ha₂ ha₃ hcen hnorm hR₁₃ hne₁₂ hne₃₂
    hnc₁₂ hnc₃₂

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)}

theorem chainSign_images3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hIH : LocalLieSystems3 Ω)
    {x : G} (hxc : ¬ ({x} : Set G) ⊆ Subgroup.center G) (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {K β M : Subgroup G} {z v w : G}
    (hz : IsClassicalMember3 K z) (hv : IsClassicalMember3 β v) (hw : IsClassicalMember3 M w)
    (hKx : K ∈ centralizingMembers Ω {x}) (hβx : β ∈ centralizingMembers Ω {x})
    (hMx : M ∈ centralizingMembers Ω {x}) (hxzw : z * w = x) (hzw : z ≠ w)
    (hKM : Commutes K M) (hKM' : K ≠ M) (hKβ : K ≠ β) (hβM : β ≠ M) (hnKβ : ¬ Commutes K β)
    (hnβM : ¬ Commutes β M) (hvK : conjSub v K = K)
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, (N = K ∨ Commutes N K) ↔ (N = M ∨ Commutes N M)) :
    ((∃ W, LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω x β) (locImg Ω x M)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x β)
          (locImg Ω x M)) := by
  obtain ⟨ι, hι, ⟨D⟩⟩ := hIH {x} hxc
  obtain ⟨i, hKi, hβi, hrest⟩ := exists_pair3 hΩ hex hP1 hO3 D hKx hβx hnKβ
  have hMi : M ∈ compMembers3 Ω x D i := hrest M hMx (fun h => hnβM h.symm)
  obtain ⟨t, n, hk, hfund, hadm, hcls⟩ :=
    tag_of_twins3 hΩ hex hP1 hO3 D hKi hMi hKM hKM' hz hw hxzw hzw htwin
  obtain ⟨R₁, hR₁⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hKi
  obtain ⟨R₂, hR₂⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hβi
  obtain ⟨R₃, hR₃⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hMi
  have hzY : z ∈ locLayer Ω x := le_centralizingLayer hKx hz.mem
  have hvY : v ∈ locLayer Ω x := le_centralizingLayer hβx hv.mem
  have hwY : w ∈ locLayer Ω x := le_centralizingLayer hMx hw.mem
  have hu₁ := ConnectedA2.isUniqueInvolution_locImg hex hKx
    (isUniqueInvolution_of_exact3 (hex K hKx.1) hz)
  have hu₂ := ConnectedA2.isUniqueInvolution_locImg hex hβx
    (isUniqueInvolution_of_exact3 (hex β hβx.1) hv)
  have hu₃ := ConnectedA2.isUniqueInvolution_locImg hex hMx
    (isUniqueInvolution_of_exact3 (hex M hMx.1) hw)
  rw [hR₁.2.2] at hu₁
  rw [hR₂.2.2] at hu₂
  rw [hR₃.2.2] at hu₃
  have hnorm : conjSub (Gaps.locMk Ω x ⟨v, hvY⟩) (R₁.map (D.hom i)) = R₁.map (D.hom i) := by
    have h := Gaps.locImg_conjSub_layer (Ω := Ω) (x := x) K ⟨v, hvY⟩
    rw [show ((⟨v, hvY⟩ : ↥(locLayer Ω x)) : G) = v from rfl, hvK] at h
    rw [← hR₁.2.2]
    exact h.symm
  have key := chainSign_of_lifts3_comp hk hcls hadm (D.hom i) (D.ker_le_center i) hR₁.2.1
    hR₂.2.1 hR₃.2.1 hu₁ hu₂ hu₃ (locMk_mul_central hzY hwY hxzw) hnorm
    (by
      rw [← hR₁.2.2, ← hR₃.2.2]
      exact commutes_locImg_of_commutes hKM)
    (by
      rw [← hR₁.2.2, ← hR₂.2.2]
      intro h
      exact hKβ (locImg_injOn3 hΩ hex hP1 hO3 hKx hβx h))
    (by
      rw [← hR₃.2.2, ← hR₂.2.2]
      intro h
      exact hβM (locImg_injOn3 hΩ hex hP1 hO3 hβx hMx h.symm))
    (by
      rw [← hR₁.2.2, ← hR₂.2.2]
      exact fun h => hnKβ (commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hKx hβx h))
    (by
      rw [← hR₃.2.2, ← hR₂.2.2]
      exact fun h => hnβM (commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hβx hMx h.symm))
  rw [← hR₁.2.2, ← hR₂.2.2, ← hR₃.2.2] at key
  exact key

theorem linear_of_chainSign_images3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {K β M : Subgroup G}
    (hKx : K ∈ centralizingMembers Ω {x}) (hβx : β ∈ centralizingMembers Ω {x})
    (hMx : M ∈ centralizingMembers Ω {x})
    (hs : ((∃ W, LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (locImg Ω x β) (locImg Ω x M)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x K) (locImg Ω x β)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (locImg Ω x β) (locImg Ω x M)))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β M := by
  have h1 := linearBlockStandardPair_locImg (p := 3) (f := 1) hP1 (le_centralizingLayer hKx)
    (le_centralizingLayer hβx) hlin
  rcases hs with ⟨-, ⟨W, hW⟩⟩ | ⟨hu, -⟩
  · exact linearBlockStandardPair_of_locImg3' hΩ hex hP1 hO3 hβx hMx hW
  · exact (false_of_linear_of_unitary3 h1 hu).elim

end Sign

end CFSG.ClassicalInvolution.Q3.Q3W
