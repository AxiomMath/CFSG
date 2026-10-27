module

public import CFSG.ClassicalInvolution.SmallCases.TwinChainRows

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem conjClass_eq_of_mem {K β : Subgroup G} (hβ : β ∈ conjClass K) :
    conjClass β = conjClass K := by
  obtain ⟨g₀, rfl⟩ := hβ
  ext L
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * g₀, by show conjSub (g * g₀) K = conjSub g (conjSub g₀ K); rw [conjSub_mul]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * g₀⁻¹, by
      show conjSub (g * g₀⁻¹) (conjSub g₀ K) = conjSub g K
      rw [conjSub_mul, conjSub_inv_conjSub]⟩

end CFSG.ClassicalInvolution.RouteD

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem RouteDSetup.of_mem_conjClass [Finite G] {K β : Subgroup G} {z t : G}
    (S : RouteDSetup p f K z) (hβ : β ∈ conjClass K) (ht : IsClassicalMember p f β t) :
    RouteDSetup p f β t where
  odd := S.odd
  five := S.five
  cls := ht
  inClass := by rw [conjClass_eq_of_mem hβ]; exact S.inClass
  conn := by rw [conjClass_eq_of_mem hβ]; exact S.conn
  exact := by rw [conjClass_eq_of_mem hβ]; exact S.exact
  p1 := by
    rw [conjClass_eq_of_mem hβ]
    obtain ⟨g, hg⟩ := hβ
    have htg : t = g * z * g⁻¹ :=
      unique_involution_of_isClassicalMember
        (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd)
        (S.exact β ⟨g, hg⟩) ht (hg ▸ S.cls.conj g)
    rw [htg]
    exact Gaps.localOddCentral_conj S.inClass.conjInvariant g z S.p1
  ih := by rw [conjClass_eq_of_mem hβ]; exact S.ih
  below := S.below

theorem RouteDSetup.cp_at_member [Finite G] {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hcen : Subgroup.center G = ⊥) {N : Subgroup G} (hN : N ∈ conjClass K) {y : G}
    (hy : IsClassicalMember p f N y) {L : Subgroup G}
    (hL : L ∈ centralizingMembers (conjClass K) {y}) : Commutes N L ∨ L = N := by
  have hzc : ¬ ({z} : Set G) ⊆ Subgroup.center G := by
    intro h
    have h1 : z ∈ Subgroup.center G := h rfl
    rw [hcen, Subgroup.mem_bot] at h1
    have := S.cls.orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨Dz⟩ := exists_lieSystemData S.ih hzc
  exact commutes_or_eq_at_member_involution (Gaps.fundNoncentral p) S.inClass S.exact S.odd
    (single_class K) S.cls S.p1 Dz hN hy ⟨hN, le_centralizer_of_isClassicalMember hy⟩ hL

theorem RouteDSetup.not_le_centralizer_of_linear [Finite G] {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) (hcen : Subgroup.center G = ⊥) {A B : Subgroup G}
    (hA : A ∈ conjClass K) (hB : B ∈ conjClass K) {y : G} (hy : IsClassicalMember p f B y)
    (h : ∃ W, LinearBlockStandardPair (GaloisField p f) W A B) :
    ¬ A ≤ Subgroup.centralizer ({y} : Set G) := by
  intro hle
  obtain ⟨W, hW⟩ := h
  rcases S.cp_at_member hcen hB hy (L := A) ⟨hA, hle⟩ with hc | he
  · exact not_commutes_of_linearBlockStandardPair hW (Commutes.symm hc)
  · exact ne_of_linearBlockStandardPair hW he

end CFSG.ClassicalInvolution.Generic.CoreAssembly

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Twin

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_twin_of_layer (hMFZ : Gaps.FundNoncentral p) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i₁ : Fin D.card)
    (hcard : D.card = 3) (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2)
    (hbig : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2)) {B : Subgroup G} (hB : B ∈ Ω)
    (hz : IsClassicalMember p f B x) :
    ∃ T ∈ centralizingMembers Ω {x}, T ≠ B ∧
      ∀ N ∈ centralizingMembers Ω {x}, N ≠ T → Commutes T N := by
  have hBx : B ∈ centralizingMembers Ω {x} := ⟨hB, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨j₀, hBj₀⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨B, hBx, rfl⟩)
  have hj₀ : j₀ ≠ i₁ := by
    intro h
    subst h
    exact not_mem_of_nonA1_comp hMFZ hΩ hex D hbig ⟨hBx, hBj₀⟩ hz.orderOf_eq_two hz.mem
  obtain ⟨a₀, a₂, h0, h2, h02, hall⟩ := exists_three_indices hcard i₁
  obtain ⟨j', hj'₁, hj'₀⟩ : ∃ j', j' ≠ i₁ ∧ j' ≠ j₀ := by
    rcases hall j₀ with h | h | h
    · exact ⟨a₂, h2, fun e => h02 (h.symm.trans e.symm)⟩
    · exact absurd h hj₀
    · exact ⟨a₀, h0, fun e => h02 (e.trans h)⟩
  obtain ⟨hj'tag, hj'rank⟩ := hrest j' hj'₁
  obtain ⟨T, hT, hTimg⟩ := mem_locFamily_iff.mp (range_mem_of_A1 D j' hj'tag hj'rank)
  have hTj' : locImg Ω x T ≤ (D.hom j').range := hTimg.le
  have hTB : T ≠ B := by
    rintro rfl
    exact hj'₀ (eq_of_locImg_le_range hΩ hex D hT hTj' hBj₀)
  refine ⟨T, hT, hTB, ?_⟩
  intro N hN hNT
  obtain ⟨m, hm⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  by_cases hmj : m = j'
  · subst hmj
    exfalso
    apply hNT
    have e1 : locImg Ω x N = (D.hom m).range :=
      Subgroup.eq_of_le_of_card_ge hm (by
        rw [card_locImg hΩ hex hN]
        exact card_range_le_of_psl_two D m hj'tag hj'rank)
    exact locImg_injOn hΩ hP1 hN hT (e1.trans hTimg.symm)
  · exact commutes_of_ne_comp hΩ hP1 D (Ne.symm hmj) ⟨hT, hTj'⟩ ⟨hN, hm⟩

end Twin

end CFSG.ClassicalInvolution.RouteD
