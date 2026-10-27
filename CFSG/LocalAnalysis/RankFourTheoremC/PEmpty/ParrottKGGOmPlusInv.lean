module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualStable
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Types

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Bridge

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem matrixProjectiveConjugationHom_apply_eq_of_commute (g : similarityPairs Q)
    (X : matrixDerived Q)
    (h : ∀ v, coordinateSemilinearMap g.val (matrixLinearIso (X : GL (Fin d) K) v) =
      matrixLinearIso (X : GL (Fin d) K) (coordinateSemilinearMap g.val v)) :
    matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q X) =
      matrixProjectiveProjection Q X := by
  change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q X) = _
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  change matrixConjugation g.val (X : GL (Fin d) K) = X
  apply matrixLinearIso.injective
  apply LinearEquiv.ext
  intro v
  change matrixLinearEquiv (matrixConjugation g.val (X : GL (Fin d) K)) v = _
  rw [matrixConjugation_vector]
  have hv := h ((coordinateSemilinearMap g.val).symm v)
  rw [AddEquiv.apply_symm_apply] at hv
  exact hv

end Bridge

section Involutions

namespace KGC

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem mul_mul_mul_eq_one {G : Type*} [Group G] {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) : s * t * (s * t) = 1 := by
  calc s * t * (s * t) = s * (t * s) * t := by group
    _ = s * (s * t) * t := by rw [← hst]
    _ = s * s * (t * t) := by group
    _ = 1 := by rw [hs, ht, one_mul]

variable {K : Type} [Field K] {d f : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem conclusion_of_reps (hR : EvenOrthogonalRealization Q f) {g₁ g₂ : similarityPairs Q}
    (hg₁ : g₁ ∈ unitMultiplierPairs Q) (hg₂ : g₂ ∈ unitMultiplierPairs Q)
    (h₁ : matrixProjectiveConjugationHom Q g₁ ≠ 1) (h₂ : matrixProjectiveConjugationHom Q g₂ ≠ 1)
    (h₁₁ : matrixProjectiveConjugationHom Q g₁ * matrixProjectiveConjugationHom Q g₁ = 1)
    (h₂₂ : matrixProjectiveConjugationHom Q g₂ * matrixProjectiveConjugationHom Q g₂ = 1)
    (h₁₂ : matrixProjectiveConjugationHom Q g₁ * matrixProjectiveConjugationHom Q g₂ =
      matrixProjectiveConjugationHom Q g₂ * matrixProjectiveConjugationHom Q g₁)
    (hσ₂ : g₂.val.right = 1) :
    g₁.val.right * g₁.val.right = 1 ∧
      (∀ v, Q (coordinateSemilinearMap g₁.val v) = g₁.val.right (Q v)) ∧
      (∀ v, coordinateSemilinearMap g₁.val (coordinateSemilinearMap g₁.val v) = v) ∧
      (∀ v, Q (coordinateSemilinearMap g₂.val v) = Q v) ∧
      (∀ v, coordinateSemilinearMap g₂.val (coordinateSemilinearMap g₂.val v) = v) ∧
      ∀ v, coordinateSemilinearMap g₂.val (coordinateSemilinearMap g₁.val v) =
        coordinateSemilinearMap g₁.val (coordinateSemilinearMap g₂.val v) := by
  obtain ⟨-, -, -, huniq, _Fp, -, -, -, hinv⟩ := hR
  have ho₁ : orderOf (matrixProjectiveConjugationHom Q g₁) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact h₁₁) h₁
  have ho₂ : orderOf (matrixProjectiveConjugationHom Q g₂) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact h₂₂) h₂
  obtain ⟨hgg₁, hT₁, -⟩ := hinv _ ⟨g₁, rfl⟩ ho₁ g₁ hg₁ rfl
  obtain ⟨-, hT₂, -⟩ := hinv _ ⟨g₂, rfl⟩ ho₂ g₂ hg₂ rfl
  have hc : g₁ * g₂ = g₂ * g₁ :=
    (huniq _ ⟨g₁ * g₂, rfl⟩).unique ⟨mul_mem hg₁ hg₂, rfl⟩
      ⟨mul_mem hg₂ hg₁, by rw [map_mul, map_mul]; exact h₁₂.symm⟩
  refine ⟨?_, hg₁, hT₁, fun v => ?_, hT₂, fun v => ?_⟩
  · have h := congrArg (fun g : similarityPairs Q => g.val.right) hgg₁
    exact h
  · rw [(mem_unitMultiplierPairs_iff Q g₂).1 hg₂ v, hσ₂]
    rfl
  · have h := congrArg (fun g : similarityPairs Q => coordinateSemilinearMap g.val v) hc
    change coordinateSemilinearMap (g₁.val * g₂.val) v =
      coordinateSemilinearMap (g₂.val * g₁.val) v at h
    rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul] at h
    exact h.symm

theorem exists_linear_rep (hR : EvenOrthogonalRealization Q f)
    {S : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) {g x : similarityPairs Q}
    (hg : g ∈ unitMultiplierPairs Q) (hx : x ∈ unitMultiplierPairs Q)
    (hgS : matrixProjectiveConjugationHom Q g ∈ S) (hxS : matrixProjectiveConjugationHom Q x ∈ S)
    (hg1 : matrixProjectiveConjugationHom Q g ≠ 1) (hx1 : matrixProjectiveConjugationHom Q x ≠ 1)
    (hgx : matrixProjectiveConjugationHom Q g ≠ matrixProjectiveConjugationHom Q x)
    (hgg : matrixProjectiveConjugationHom Q g * matrixProjectiveConjugationHom Q g = 1)
    (hxx : matrixProjectiveConjugationHom Q x * matrixProjectiveConjugationHom Q x = 1)
    (hσ : g.val.right ≠ 1) :
    ∃ y : similarityPairs Q, y ∈ unitMultiplierPairs Q ∧ matrixProjectiveConjugationHom Q y ∈ S ∧
      matrixProjectiveConjugationHom Q y ≠ 1 ∧
      matrixProjectiveConjugationHom Q y * matrixProjectiveConjugationHom Q y = 1 ∧
      y.val.right = 1 := by
  by_cases hxσ : x.val.right = 1
  · exact ⟨x, hx, hxS, hx1, hxx, hxσ⟩
  obtain ⟨-, -, -, -, _Fp, -, -, -, hinv⟩ := hR
  have ho₁ : orderOf (matrixProjectiveConjugationHom Q g) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hgg) hg1
  have ho₂ : orderOf (matrixProjectiveConjugationHom Q x) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  obtain ⟨hgg', -, hgσ⟩ := hinv _ ⟨g, rfl⟩ ho₁ g hg rfl
  obtain ⟨-, -, hxσ'⟩ := hinv _ ⟨x, rfl⟩ ho₂ x hx rfl
  have hxg : x.val.right = g.val.right :=
    (hgσ.resolve_left hσ).2.1 _ (hxσ'.resolve_left hxσ).1
  refine ⟨g * x, mul_mem hg hx, ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact S.mul_mem hgS hxS
  · rw [map_mul]
    intro h
    exact hgx ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hgg)).symm
  · rw [map_mul]
    exact mul_mul_mul_eq_one hgg hxx (hcomm _ hgS _ hxS)
  · change g.val.right * x.val.right = 1
    rw [hxg]
    have h := congrArg (fun g : similarityPairs Q => g.val.right) hgg'
    exact h

end KGC

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}

theorem exists_field_and_linear_involution (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {S : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)))}
    (hSE : S ≤ matrixProjectiveImage (coordinateQuadPlus n F))
    (hSI : S ⊓ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range = ⊥)
    (hS2 : IsPGroup 2 ↥S) (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) (hnc : ¬ IsCyclic ↥S) :
    ∃ g₁ g₂ : similarityPairs (coordinateQuadPlus n F),
      matrixProjectiveConjugationHom (coordinateQuadPlus n F) g₁ ∈ S ∧
      matrixProjectiveConjugationHom (coordinateQuadPlus n F) g₂ ∈ S ∧
      matrixProjectiveConjugationHom (coordinateQuadPlus n F) g₁ ≠ 1 ∧
      matrixProjectiveConjugationHom (coordinateQuadPlus n F) g₂ ≠ 1 ∧
      g₁.val.right ≠ 1 ∧ g₁.val.right * g₁.val.right = 1 ∧
      (∀ v, coordinateQuadPlus n F (coordinateSemilinearMap g₁.val v) =
        g₁.val.right (coordinateQuadPlus n F v)) ∧
      (∀ v, coordinateSemilinearMap g₁.val (coordinateSemilinearMap g₁.val v) = v) ∧
      g₂.val.right = 1 ∧
      (∀ v, coordinateQuadPlus n F (coordinateSemilinearMap g₂.val v) =
        coordinateQuadPlus n F v) ∧
      (∀ v, coordinateSemilinearMap g₂.val (coordinateSemilinearMap g₂.val v) = v) ∧
      ∀ v, coordinateSemilinearMap g₂.val (coordinateSemilinearMap g₁.val v) =
        coordinateSemilinearMap g₁.val (coordinateSemilinearMap g₂.val v) := by
  have h3 : 3 ≤ n := by omega
  have hR := CFSG.SeitzReduction.OmegaPilot.plusRealization hf hF h3
  obtain ⟨a, ha, b, hb, ha1, hb1, hab, haa, hbb⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.exists_two_involutions_of_noncyclic hS2
      hcomm hnc
  obtain ⟨ga, ⟨hga, rfl⟩, -⟩ := hR.2.2.2.1 a (hSE ha)
  obtain ⟨gb, ⟨hgb, rfl⟩, -⟩ := hR.2.2.2.1 b (hSE hb)
  have hnot : ¬ (ga.val.right = 1 ∧ gb.val.right = 1) := by
    rintro ⟨hra, hrb⟩
    have hA := CFSG.SeitzReduction.OmegaPilot.card_abelianization_isometries_plus_le_two hf hF hn
    have hIa := (CFSG.SeitzReduction.OmegaPilot.plusImageFieldPart_eq_one_iff hf hF h3
      ⟨_, ⟨ga, rfl⟩⟩).1
      ((CFSG.SeitzReduction.OmegaPilot.plusImageFieldPart_kappa hf hF h3 ga).trans hra)
    have hIb := (CFSG.SeitzReduction.OmegaPilot.plusImageFieldPart_eq_one_iff hf hF h3
      ⟨_, ⟨gb, rfl⟩⟩).1
      ((CFSG.SeitzReduction.OmegaPilot.plusImageFieldPart_kappa hf hF h3 gb).trans hrb)
    have hnI : ∀ s ∈ S, s ≠ 1 → s ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived (coordinateQuadPlus n F)) := by
      intro s hs hs1 hsI
      have hmem : s ∈ S ⊓ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
          MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range :=
        Subgroup.mem_inf.mpr ⟨hs, hsI⟩
      rw [hSI] at hmem
      exact hs1 hmem
    have key := CFSG.SeitzReduction.OmegaPilot.inv_mul_mem_inner_of_not_mem
      (β₁ := matrixProjectiveConjugationHom (coordinateQuadPlus n F) ga)
      (β₂ := matrixProjectiveConjugationHom (coordinateQuadPlus n F) gb) _ hA hIa hIb
      (hnI _ ha ha1) (hnI _ hb hb1)
    have hmem : (matrixProjectiveConjugationHom (coordinateQuadPlus n F) ga)⁻¹ *
        matrixProjectiveConjugationHom (coordinateQuadPlus n F) gb ∈
        S ⊓ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
          MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range :=
      Subgroup.mem_inf.mpr ⟨S.mul_mem (S.inv_mem ha) hb, key⟩
    rw [hSI, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hab hmem
  obtain ⟨g, x, hg, hx, hgS, hxS, hg1, hx1, hgx, hgg, hxx, hσ⟩ :
      ∃ g x : similarityPairs (coordinateQuadPlus n F),
        g ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitMultiplierPairs _ ∧
        x ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitMultiplierPairs _ ∧
        matrixProjectiveConjugationHom _ g ∈ S ∧ matrixProjectiveConjugationHom _ x ∈ S ∧
        matrixProjectiveConjugationHom _ g ≠ 1 ∧ matrixProjectiveConjugationHom _ x ≠ 1 ∧
        matrixProjectiveConjugationHom _ g ≠ matrixProjectiveConjugationHom _ x ∧
        matrixProjectiveConjugationHom _ g * matrixProjectiveConjugationHom _ g = 1 ∧
        matrixProjectiveConjugationHom _ x * matrixProjectiveConjugationHom _ x = 1 ∧
        g.val.right ≠ 1 := by
    by_cases hra : ga.val.right = 1
    · exact ⟨gb, ga, hgb, hga, hb, ha, hb1, ha1, Ne.symm hab, hbb, haa, fun h => hnot ⟨hra, h⟩⟩
    · exact ⟨ga, gb, hga, hgb, ha, hb, ha1, hb1, hab, haa, hbb, hra⟩
  obtain ⟨y, hy, hyS, hy1, hyy, hσy⟩ :=
    KGC.exists_linear_rep hR hcomm hg hx hgS hxS hg1 hx1 hgx hgg hxx hσ
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ :=
    KGC.conclusion_of_reps hR hg hy hg1 hy1 hgg hyy (hcomm _ hgS _ hyS) hσy
  exact ⟨g, y, hgS, hyS, hg1, hy1, hσ, c₁, c₂, c₃, hσy, c₄, c₅, c₆⟩

end Involutions

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus
