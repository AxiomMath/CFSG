module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceModel
public import CFSG.ClassicalInvolution.Balance.PassTwoWeak
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

section Definitions

variable {G : Type} [Group G]

@[expose] def LayerGenerationAt (E : Subgroup G) (a : G) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
    ∀ F₀ : Subgroup G, F₀ ≤ E → Nat.card F₀ = 4 →
      modOdd a F₀ ≤ Subgroup.normalizer (L : Set (OddQuot a)) →
      (∀ f ∈ modOdd a F₀, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
        OddCentralizerFree (modOdd a F₀) L

end Definitions

@[expose] def IsOddLieBig (L : Type) [Group L] : Prop :=
  ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ), p ≠ 2 ∧ 5 ≤ p ^ f ∧
    (t = .PSL → 3 ≤ n) ∧ (t ∈ CFSG.Blueprint.classicalTags ∨
      t ∈ CFSG.Blueprint.chevalleyExceptionalTags) ∧
    CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n p f

@[expose] def IsOddLieComponentBig {X : Type} [Group X] (L : Subgroup X) : Prop :=
  IsOddLieBig ↥L

theorem IsOddLieComponentBig.isOddLieComponent {X : Type} [Group X] {L : Subgroup X}
    (h : IsOddLieComponentBig L) : IsOddLieComponent L := by
  obtain ⟨t, n, p, f, hp, -, hn, ht, hm⟩ := h
  exact ⟨t, n, p, f, hp, hn, ht, hm⟩

@[expose] def LayerGenerationModel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), CFSG.IsComponent L →
    IsOddLieComponentBig L → ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
      F ≤ Subgroup.normalizer (L : Set X) → (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
        L ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f

section Reductions

variable {G : Type} [Group G] [Finite G] {E : Subgroup G}

theorem LayerGenerationAt.of_model (hE2 : ∀ x ∈ E, x * x = 1) (hmodel : LayerGenerationModel)
    {a : G} (ha : a ∈ E)
    (hbig : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      IsOddLieComponentBig L) : LayerGenerationAt E a := by
  intro L hL hlie F₀ hF₀E h4 hFn hfaith
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => hE2 f (hF₀E hf)
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  exact OddCentralizerFree.of_le_layers
    (hmodel (OddQuot a) L hL (hbig L hL hlie) (modOdd a F₀)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar hFn hfaith)

theorem LayerGenerationAt.of_centralizedGenerated {Ω : Set (Subgroup G)} (hE2 : ∀ x ∈ E, x * x = 1)
    (hΩ : ∀ K ∈ Ω, IsInvolutionMember K) {a : G}
    (hgen : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      ∀ F₀ : Subgroup G, F₀ ≤ E → Nat.card F₀ = 4 →
        modOdd a F₀ ≤ Subgroup.normalizer (L : Set (OddQuot a)) →
        (∀ f ∈ modOdd a F₀, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
          CentralizedGeneratedAt Ω a F₀ L) :
    LayerGenerationAt E a := by
  intro L hL hlie F₀ hF₀E h4 hFn hfaith
  have hB := involutionCentralizerB_of_isOddLieComponent
    ((CFSG.isComponent_iff_open L).mp hL).2.2 hlie
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hE2 _ (hF₀E hx'))
    rw [this, map_one]
  exact OddCentralizerFree.of_members l2PrimeBalance hL
    (fun f hf hf1 => hB f hf1 (hF2bar f hf) (hFn hf))
    ((hgen L hL hlie F₀ hF₀E h4 hFn hfaith).oddCentralizerFreeMembers hΩ)

end Reductions

section Classical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem _root_.CFSG.ClassicalInvolution.Generic.IsClassicalMember.isInvolutionMember
    {K : Subgroup G} {z : G} (h : IsClassicalMember p f K z) (hq : 5 ≤ p ^ f) :
    IsInvolutionMember K := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  exact IsInvolutionMember.of_weakMember
    (⟨h.orderOf_eq_two, h.mem, h.perfect, h.subnormal, h.nonempty_equiv⟩ :
      WeakMember (GaloisField p f) K z) (by rw [hcard]; omega)

omit [Finite G] in
theorem InClass.isInvolutionMember {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hq : 5 ≤ p ^ f) : ∀ K ∈ Ω, IsInvolutionMember K := fun K hK => by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact hz.isInvolutionMember hq

end Classical

section Frame

variable {F : Type*} [Field F] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
private theorem exists_two_ne_one_of_card_eq_four' {F₀ : Subgroup G} (h4 : Nat.card F₀ = 4) :
    ∃ x ∈ F₀, ∃ y ∈ F₀, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F₀ := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F₀
  have hc : 2 < Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha1.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha1.trans (Subtype.ext h).symm)
  · by_cases hb1 : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h), ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (hb1.trans (Subtype.ext h).symm)
    · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

omit [Finite G] in
theorem exists_mem_ne_one_mem_axisSub_weak (Fr : WeakPreFrame F Ω E S) {K : Subgroup G}
    (hK : K ∈ S) {F₀ : Subgroup G} (hF₀ : F₀ ≤ E) (h4 : Nat.card F₀ = 4) :
    ∃ f ∈ F₀, f ≠ 1 ∧ f ∈ axisSub E K := by
  obtain ⟨a, haE, -, hsplit⟩ := (Fr.weakInSigma hK).exists_split
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one_of_card_eq_four' h4
  by_cases hxK : x ∈ axisSub E K
  · exact ⟨x, hx, hx1, hxK⟩
  by_cases hyK : y ∈ axisSub E K
  · exact ⟨y, hy, hy1, hyK⟩
  have hxa : x * a ∈ axisSub E K := (hsplit x (hF₀ hx)).resolve_left hxK
  have hya : y * a ∈ axisSub E K := (hsplit y (hF₀ hy)).resolve_left hyK
  have hxy' : x * y ∈ axisSub E K := by
    have e1 : x * a * (y * a) = x * y := by
      calc x * a * (y * a) = x * (a * y) * a := by group
        _ = x * (y * a) * a := by rw [Fr.comm haE (hF₀ hy)]
        _ = x * y * (a * a) := by group
        _ = x * y := by rw [Fr.elem a haE, mul_one]
    rw [← e1]
    exact (axisSub E K).mul_mem hxa hya
  refine ⟨x * y, F₀.mul_mem hx hy, ?_, hxy'⟩
  intro h
  apply hxy
  have hyy : y * y = 1 := Fr.elem y (hF₀ hy)
  calc x = x * (y * y) := by rw [hyy, mul_one]
    _ = (x * y) * y := (mul_assoc _ _ _).symm
    _ = y := by rw [h, one_mul]

theorem exists_mem_modOdd_ne_one_centralizes_weak (Fr : WeakPreFrame F Ω E S) {a : G}
    (ha : a ∈ E) {K : Subgroup G} (hK : K ∈ S) {F₀ : Subgroup G} (hF₀ : F₀ ≤ E)
    (h4 : Nat.card F₀ = 4) :
    ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ modOdd a K ≤ Subgroup.centralizer ({f} : Set (OddQuot a)) := by
  obtain ⟨f, hfF, hf1, hfax⟩ := exists_mem_ne_one_mem_axisSub_weak Fr hK hF₀ h4
  have hfC : f ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Fr.comm ha (hF₀ hfF)).symm
  refine ⟨oddQuotMk a ⟨f, hfC⟩, oddQuotMk_mem_modOdd hfF hfC, ?_, ?_⟩
  · intro h
    have hsq : (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨f, hfC⟩ = 1 :=
      Subtype.ext (Fr.elem f (hF₀ hfF))
    exact hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  · intro y hy
    obtain ⟨k, hkK, rfl⟩ := mem_modOdd_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext ((mem_axisSub_iff.mp hfax).2 (k : G) hkK))

theorem FrameGeneratedAt.centralizedGeneratedAt_weak (Fr : WeakPreFrame F Ω E S) {a : G}
    (ha : a ∈ E) {L : Subgroup (OddQuot a)} (h : FrameGeneratedAt E S a L) {F₀ : Subgroup G}
    (hF₀ : F₀ ≤ E) (h4 : Nat.card F₀ = 4) : CentralizedGeneratedAt S a F₀ L := by
  refine h.trans (iSup₂_le fun K hK => iSup_le fun haK => iSup_le fun hKL => ?_)
  exact le_iSup₂_of_le K hK (le_iSup_of_le (le_centralizer_of_mem_axisSub haK)
    (le_iSup_of_le (exists_mem_modOdd_ne_one_centralizes_weak Fr ha hK hF₀ h4)
      (le_iSup_of_le hKL le_rfl)))

theorem LayerGenerationAt.of_frameGenerated (Fr : WeakPreFrame F Ω E S) {a : G} (ha : a ∈ E)
    (hgen : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      FrameGeneratedAt E S a L) : LayerGenerationAt E a := by
  have := Fr.finite
  have h4 : 4 ≤ Nat.card F := by have := Fr.five; omega
  refine LayerGenerationAt.of_centralizedGenerated Fr.elem (Ω := S) (fun K hK => ?_) ?_
  · obtain ⟨z, -, hz⟩ := Fr.exists_weakMember hK
    exact IsInvolutionMember.of_weakMember hz h4
  · intro L hL hlie F₀ hF₀E h4' _ _
    exact (hgen L hL hlie).centralizedGeneratedAt_weak Fr ha hF₀E h4'

end Frame

end CFSG.ClassicalInvolution.Balance
