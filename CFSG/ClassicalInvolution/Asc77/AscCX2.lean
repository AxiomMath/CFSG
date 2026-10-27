module

public import CFSG.Goldschmidt75.CorollaryB1
public import CFSG.ClassicalInvolution.Asc77.AscP1Strong
public import CFSG.ClassicalInvolution.Asc77.AscT7TC15

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem mem_trivialOnQuot_of_mem_A (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) :
    x ∈ trivialOnQuot K ∧ x ∈ trivialOnQuot K' := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hcpg : IsPGroup 2 (Subgroup.zpowers x) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hx.1)
  have hcent := Subgroup.mem_centralizer_iff.mp hx.2
  have hRc : R ≤ Subgroup.centralizer ({x} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent r (Subgroup.mem_sup_left hr))
  have hR'c : R' ≤ Subgroup.centralizer ({x} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent r (Subgroup.mem_sup_right hr))
  have hK₂ : K ∈ tqMembers Ω x :=
    (mem_tqMembers_iff_exists_sylow hst.odd hst.five hst.hyp hcpg).mpr
      ⟨hst.mem, R, h.hRsyl, hRc⟩
  have hK₂' : K' ∈ tqMembers Ω x :=
    (mem_tqMembers_iff_exists_sylow hst.odd hst.five hst.hyp hcpg).mpr
      ⟨hs.hK'.1, R', h.hR'syl, hR'c⟩
  exact ⟨hK₂.2, hK₂'.2⟩

section Engine

theorem false_of_stronglyClosed (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {E : Subgroup G}
    (hEA : E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hE1 : E ≠ ⊥) (hsc : fusionStronglyClosed (E : Set G) S) : False := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hKns := not_isSolvable_of_mem_mod hs.stand.hyp hs.stand.mem hs.hz
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    exact hKns (Group.isSolvable_of_comm fun a b => Subtype.ext (hab a b))
  have hES : E ≤ (S : Subgroup G) := fun x hx => (hEA hx).1
  have hB := CFSG.Goldschmidt75.goldschmidtB1_simple hnonab S hES hE1 hsc
  rw [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hB
  have : Group.IsSolvable ↥(Subgroup.centralizer (E : Set G)) :=
    (CFSG.perfect_residual_characterization
      (G := ↥(Subgroup.centralizer (E : Set G)))).2.2.2.2.2.mp hB
  have hEp : IsPGroup 2 E := S.isPGroup'.to_le hES
  have hEK : E ≤ trivialOnQuot K := fun x hx => (mem_trivialOnQuot_of_mem_A hyp (hEA hx)).1
  have hcov : ∀ x ∈ K, ∃ s ∈ K ⊓ Subgroup.centralizer (E : Set G), ∃ n ∈ oddCoreIn K,
      x = s * n := fun x hx => exists_mem_inf_centralizer_mul hEp hEK hx
  have : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer (E : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)
  have : Group.IsSolvable (↥K ⧸ classicalInvolutionOddCore ↥K) :=
    Group.isSolvable_of_surjective (toOddQuot_surjective inf_le_left hcov)
  have : Group.IsSolvable ↥(oddCoreIn K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreIn K)
  apply hKns
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (oddCoreIn_le K))
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) ?_
  rw [QuotientGroup.ker_mk']
  intro x hx
  exact ⟨⟨x, mem_oddCoreIn_of_mem_classicalInvolutionOddCore hx⟩, rfl⟩

end Engine

end CFSG.ClassicalInvolution.Asc77.CX
