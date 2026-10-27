module

public import CFSG.ClassicalInvolution.Q3.Q3NGInv
public import CFSG.ClassicalInvolution.Q3.Q3NGCent
public import CFSG.ClassicalInvolution.Q3.Q3WAStarMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement


section Shared

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem eq_involution_of_commuting_in_g2d43 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} {t : StatedLieTag} {n : ℕ}
    (ht : t = .G2 ∨ t = .trialityD4) (hadm : StatedLieAdmissible t n 3 1)
    (hk : D.kind i = CompData.model t n) {c b₁ b₂ : Subgroup G} {w₀ w₁ w₂ : G}
    (hc : c ∈ compMembers3 Ω x D i) (hb₁ : b₁ ∈ compMembers3 Ω x D i)
    (hb₂ : b₂ ∈ compMembers3 Ω x D i) (hw₀ : IsClassicalMember3 c w₀)
    (hw₁ : IsClassicalMember3 b₁ w₁) (hw₂ : IsClassicalMember3 b₂ w₂)
    (cb₁ : Commutes c b₁) (cb₂ : Commutes c b₂) : w₁ = w₂ := by
  obtain ⟨R_c, hRc⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hc
  obtain ⟨hw₀Y, hw₀m, hw₀sq, hw₀1, hw₀c⟩ := image_involution_facts3 hc.1 hw₀
  obtain ⟨hw₁Y, hw₁m, hw₁sq, hw₁1, hw₁c⟩ := image_involution_facts3 hb₁.1 hw₁
  obtain ⟨hw₂Y, hw₂m, hw₂sq, hw₂1, hw₂c⟩ := image_involution_facts3 hb₂.1 hw₂
  have inj : Function.Injective (D.hom i) := by
    have key : ∀ c' : CompData, c' = CompData.model t n → ∀ φ : c'.G →* locQuot Ω x,
        φ.ker ≤ Subgroup.center c'.G → Function.Injective φ := by
      rintro c' rfl φ hker
      exact G2D4.injective_of_ker_le_center (p := 3) (by norm_num) ht n le_rfl φ hker
    exact key _ hk (D.hom i) (D.ker_le_center i)
  have shared : ∀ c' : CompData, c' = CompData.model t n → ∀ φ : c'.G →* locQuot Ω x,
      Function.Injective φ → ∀ R ∈ c'.fund, locImg Ω x c = R.map φ →
      locImg Ω x c ≤ φ.range → locImg Ω x b₁ ≤ φ.range → locImg Ω x b₂ ≤ φ.range →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w₁, hw₁Y⟩ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w₂, hw₂Y⟩ := by
    rintro c' rfl φ hφ R hR hcR hr₀ hr₁ hr₂
    have hφR : ∀ r ∈ R, φ r ∈ locImg Ω x c := fun r hr => by
      rw [hcR]
      exact Subgroup.mem_map_of_mem φ hr
    have e₁ := eq_of_involutions_centralizing3 ht hadm φ hφ hR (hr₁ hw₁m) (hr₀ hw₀m) hw₁sq hw₀sq
      hw₁1 hw₀1
      (fun r hr => commutes_locImg_of_commutes cb₁ (φ r) (hφR r hr) _ hw₁m)
      (fun r hr => (hw₀c (φ r) (hφR r hr)).symm)
    have e₂ := eq_of_involutions_centralizing3 ht hadm φ hφ hR (hr₂ hw₂m) (hr₀ hw₀m) hw₂sq hw₀sq
      hw₂1 hw₀1
      (fun r hr => commutes_locImg_of_commutes cb₂ (φ r) (hφR r hr) _ hw₂m)
      (fun r hr => (hw₀c (φ r) (hφR r hr)).symm)
    exact e₁.trans e₂.symm
  exact G2D4.eq_of_mk_eq_of_involutions hP1 hw₁Y hw₂Y (mul_self_eq_one_of_isClassicalMember3 hw₁)
    (mul_self_eq_one_of_isClassicalMember3 hw₂)
    (shared _ hk (D.hom i) inj R_c hRc.2.1 hRc.2.2 hc.2 hb₁.2 hb₂.2)

end Shared

section Star

variable {G : Type} [Group G] [Finite G] {ι : Type}

theorem tag3_ne_of_commuting_star [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {K : Subgroup G} {z : G} (h : RouteD3Setup K z) (hc : LocCtx3 K z)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z)) {i : ι}
    {c b₁ b₂ : Subgroup G} (hcm : c ∈ compMembers3 (conjClass3 K) z D i)
    (hb₁ : b₁ ∈ compMembers3 (conjClass3 K) z D i) (hb₂ : b₂ ∈ compMembers3 (conjClass3 K) z D i)
    (hne : b₁ ≠ b₂) (cb₁ : Commutes c b₁) (cb₂ : Commutes c b₂) (hn : ¬ Commutes b₁ b₂)
    {t : StatedLieTag} {n : ℕ} (hadm : StatedLieAdmissible t n 3 1)
    (hk : D.kind i = CompData.model t n) : t ≠ .G2 ∧ t ≠ .trialityD4 := by
  by_contra hcon
  have ht : t = .G2 ∨ t = .trialityD4 := by
    by_cases h' : t = .G2
    · exact Or.inl h'
    · refine Or.inr ?_
      by_contra h''
      exact hcon ⟨h', h''⟩
  have hΩ := hc.hΩ
  have hex := hc.hex
  obtain ⟨w₀, hw₀⟩ := hΩ.classical c hcm.1.1
  obtain ⟨w₁, hw₁⟩ := hΩ.classical b₁ hb₁.1.1
  obtain ⟨w₂, hw₂⟩ := hΩ.classical b₂ hb₂.1.1
  have hw : w₁ = w₂ := eq_involution_of_commuting_in_g2d43 hΩ hex hc.hP1 hc.hO3 D ht hadm hk hcm
    hb₁ hb₂ hw₀ hw₁ hw₂ cb₁ cb₂
  subst hw
  obtain ⟨hP1w, hO3w⟩ := local_conj3 hc hb₁.1.1 hw₁
  have hync : ¬ ({w₁} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : w₁ ∈ Subgroup.center G := hsub rfl
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hw₁.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨ιw, hιw, ⟨Dw⟩⟩ := h.ih {w₁} hync
  have hb₁w : b₁ ∈ centralizingMembers (conjClass3 K) {w₁} :=
    ⟨hb₁.1.1, isSubnormal_le hw₁.subnormal⟩
  have hb₂w : b₂ ∈ centralizingMembers (conjClass3 K) {w₁} :=
    ⟨hb₂.1.1, isSubnormal_le hw₂.subnormal⟩
  rcases commutes_or_eq_of_involution3 (RouteD.Gaps.fundNoncentral 3) hΩ hex hP1w hO3w Dw hb₁w
    hb₂w hw₁ with h' | h'
  · exact hn h'
  · exact hne h'.symm

end Star

end CFSG.ClassicalInvolution.Q3.Q3W
