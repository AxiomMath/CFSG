module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3E27Classes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3PGL

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint CFSG.SectionRank.Native
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.RankThree.Asc83Table

section Main


set_option linter.unusedSectionVars false

theorem card_cent_J3_eq {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.J3) (q : Q) :
    Nat.card (centralizer ({e q} : Set NativeSporadic.J3)) = Nat.card (centralizer ({q} : Set Q)) := by
  have hcard1 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    Item228CensusProof.j3CarrierEquiv (e q)
  have hcard2 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
    (e.trans Item228CensusProof.j3CarrierEquiv) q
  have h3 : Nat.card (centralizer ({e q} : Set (NativeSporadic.Carrier .J3))) =
      Nat.card (centralizer ({q} : Set Q)) := hcard1.trans hcard2.symm
  exact h3

theorem card_cent_conj {Q : Type*} [Group Q] (g t : Q) :
    Nat.card (centralizer ({g * t * g⁻¹} : Set Q)) = Nat.card (centralizer ({t} : Set Q)) := by
  rw [centralizer_conj_map' g t, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]

theorem exists_F1_of_class {X : Type} [Group X] [Finite X] (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3) {F : Subgroup X}
    (hF : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F) (hF81 : Nat.card F = 81) :
    ∃ F₁ : Subgroup X, center X ≤ F₁ ∧ F₁ ≤ F ∧ Nat.card F₁ = 27 ∧
      (∀ y ∈ normalizer (F : Set X), ∀ s ∈ F₁, y * s * y⁻¹ ∈ F₁) ∧
      (∀ a ∈ F, a ∉ center X →
        5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3)) → a ∉ F₁) ∧
      (∀ a ∈ F, a ∉ F₁ →
        5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3))) ∧
      ∀ a ∈ F₁, a ∉ center X →
        Nat.card (centralizer ({(a : X ⧸ center X)} : Set (X ⧸ center X))) = 243 := by
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπ
  have hker : π.ker = center X := QuotientGroup.ker_mk' _
  have hFbar : Nat.card (F.map π) = 27 := by
    have := card_map_mul_ker π F (hker.le.trans hZF)
    rw [hker, hZ3, hF81] at this
    omega
  obtain ⟨B₁, hB₁F, hB₁c, hB₁3B, hB₁3A⟩ := j3_e27_class_split e hF hFbar
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set F₁ : Subgroup X := B₁.comap π with hF₁
  have hZF₁ : center X ≤ F₁ := fun z hz => by
    show π z ∈ B₁
    have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    rw [h1]; exact Subgroup.one_mem _
  have hF₁F : F₁ ≤ F := by
    intro s hs
    have hsB : π s ∈ F.map π := hB₁F hs
    obtain ⟨f, hf, hfs⟩ := hsB
    have : f⁻¹ * s ∈ center X := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hfs, inv_mul_cancel]
    have h2 := Subgroup.mul_mem _ hf (hZF this)
    simpa using h2
  have hF₁card : Nat.card F₁ = 27 := by
    have := card_map_mul_ker π F₁ (hker.le.trans hZF₁)
    rw [hF₁, Subgroup.map_comap_eq_self_of_surjective hsurj, hB₁c, hker, hZ3] at this
    omega
  refine ⟨F₁, hZF₁, hF₁F, hF₁card, ?_, ?_, ?_, ?_⟩
  · intro y hy s hs
    have hsF : s ∈ F := hF₁F hs
    have hysF : y * s * y⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 hy s).1 hsF
    show π (y * s * y⁻¹) ∈ B₁
    have hw : π (y * s * y⁻¹) ∈ F.map π := ⟨_, hysF, rfl⟩
    have hw' : π (y * s * y⁻¹) = π y * π s * (π y)⁻¹ := by simp
    by_cases ht : π s = 1
    · rw [hw', ht]; simp
    · have ht243 := hB₁3B (π s) hs ht
      by_contra hwn
      have h1080 := hB₁3A _ hw hwn
      rw [hw', card_cent_conj, ht243] at h1080
      omega
  · intro a haF ha hc haF₁
    have hne : π a ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff a).1 h)
    have h243 := hB₁3B (π a) haF₁ hne
    have h5 : 5 ∣ Nat.card (centralizer ({π a} : Set (X ⧸ center X))) := by
      rw [← card_cent_J3_eq e]; exact hc
    rw [h243] at h5
    omega
  · intro a haF haF₁
    have hw : π a ∈ F.map π := ⟨a, haF, rfl⟩
    have hwn : π a ∉ B₁ := haF₁
    have h1080 := hB₁3A _ hw hwn
    rw [card_cent_J3_eq e]
    show 5 ∣ Nat.card (centralizer ({π a} : Set (X ⧸ center X)))
    rw [h1080]; norm_num
  · intro a haF₁ ha
    have hne : π a ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff a).1 h)
    exact hB₁3B (π a) haF₁ hne


set_option maxRecDepth 20000 in
theorem exists_pgl29_u_of_class {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3) {F : Subgroup X}
    (hF : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F) (hF81 : Nat.card F = 81) {a : X} (haF : a ∈ F) (ha : a ∉ center X)
    (h5 : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3))) :
    ∃ (u : X) (I : Subgroup X), u ∈ normalizer (F : Set X) ∧ orderOf u = 8 ∧
      u ∈ normalizer ((zpowers a ⊔ center X : Subgroup X) : Set X) ∧
      u ∉ centralizer ({a} : Set X) ∧ I ≤ centralizer ({a} : Set X) ∧ ⁅I, I⁆ = I ∧
      Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧
      (∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ I) ∧
      IsPGL29 (I ⊔ zpowers u) I := by
  obtain ⟨F₁, hZF₁, hF₁F, hF₁27, hF₁inv, hnot, -, -⟩ := exists_F1_of_class hZ3 e hF hZF hF81
  exact exists_pgl29_u hX hZ3 e hF hZF hF81 hZF₁ hF₁F hF₁27 hF₁inv haF (hnot a haF ha h5) h5

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
