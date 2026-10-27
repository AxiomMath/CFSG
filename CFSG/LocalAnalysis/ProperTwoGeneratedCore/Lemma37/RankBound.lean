module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBoundSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBoundAut

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {t : X}

@[expose] noncomputable def componentQuotientAction (J : Subgroup X) [J.Normal] :
    X →* MulAut (J ⧸ Subgroup.center J) :=
  (PerfectAutomorphisms.centerQuotientHom J).comp (MulAut.conjNormal (H := J))

omit [Finite X] in
theorem mem_centralizer_of_componentQuotientAction_eq_one (J : Subgroup X) [J.Normal]
    [Group.IsPerfect J] {x : X} (hx : componentQuotientAction J x = 1) :
    x ∈ Subgroup.centralizer (J : Set X) := by
  have hconj : MulAut.conjNormal (H := J) x = 1 := by
    apply PerfectAutomorphisms.centerQuotientHom_injective J
    rw [map_one]
    exact hx
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := congrArg (fun α : MulAut J => ((α ⟨j, hj⟩ : J) : X)) hconj
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc j * x = x * j * x⁻¹ * x := by rw [h1]
    _ = x * j := by group

omit [Finite X] in
theorem componentQuotientAction_coe (J : Subgroup X) [J.Normal] (j : J) :
    componentQuotientAction J (j : X) =
      MulAut.conj ((QuotientGroup.mk' (Subgroup.center J)) j) := by
  have hconj : MulAut.conjNormal (H := J) (j : X) = MulAut.conj j := by
    ext y
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  change PerfectAutomorphisms.centerQuotientHom J (MulAut.conjNormal (H := J) (j : X)) = _
  rw [hconj, centerQuotient_conj]

omit [Finite X] in
theorem componentQuotientAction_eq_one_of_mem_center (J : Subgroup X) [J.Normal] {x : X}
    (hx : x ∈ Subgroup.center X) : componentQuotientAction J x = 1 := by
  have hconj : MulAut.conjNormal (H := J) x = 1 := by
    ext y
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [(Subgroup.mem_center_iff.mp hx y).symm, mul_inv_cancel_right]
  change PerfectAutomorphisms.centerQuotientHom J (MulAut.conjNormal (H := J) x) = 1
  rw [hconj, map_one]

namespace RankBoundHyp

theorem twoRank_le
    (h : RankBoundHyp X t) : CFSG.Open.twoRank X ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, hJ⟩ := h.exists_component
  have : J.Normal := h.component_normal hJ
  have : Group.IsPerfect J := hJ.1.1
  set φ := componentQuotientAction J with hφ
  have hker : ∀ x, φ x = 1 → x ∈ J := fun x hx =>
    h.centralizer_le hJ (mem_centralizer_of_componentQuotientAction_eq_one J hx)
  have hφt : φ t = 1 := componentQuotientAction_eq_one_of_mem_center J h.central
  apply CFSG.SectionRank.pRank_le (by decide)
  intro E _ hE
  have hEJ : ∀ e ∈ E, e ∈ J → e = 1 ∨ e = t := by
    intro e he heJ
    by_cases he1 : e = 1
    · exact Or.inl he1
    · exact Or.inr (h.eq_of_mem_component hJ heJ (orderOf_eq_prime (hE.2 e he) he1))
  have hF2 : ∀ y ∈ E.map φ, y * y = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← pow_two, hE.2 e he, map_one]
  have hFI : E.map φ ⊓ inner (J ⧸ Subgroup.center J) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨e, he, rfl⟩, ⟨q, hq⟩⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) q
    have hj : φ (j : X) = φ e := (componentQuotientAction_coe J j).trans hq
    have hej : e * (j : X)⁻¹ ∈ J := hker _ (by rw [map_mul, map_inv, ← hj, mul_inv_cancel])
    have heJ : e ∈ J := by simpa using J.mul_mem hej j.2
    rcases hEJ e he heJ with he1 | het
    · rw [he1, map_one]
      exact Subgroup.one_mem _
    · rw [het, hφt]
      exact Subgroup.one_mem _
  have hFcard : Nat.card (E.map φ) ≤ 2 :=
    card_le_two_of_inf_inner_eq_bot (h.quotient_classification hJ) _ hF2 hFI
  let ψ : E →* MulAut (J ⧸ Subgroup.center J) := φ.comp E.subtype
  have hψker : Nat.card ψ.ker ≤ 2 := by
    apply card_le_two_of_forall_ne_one
    have hmem : ∀ x : ψ.ker, x ≠ 1 → ((x : E) : X) = t := by
      rintro ⟨⟨a, ha⟩, ha'⟩ ha1
      rcases hEJ a ha (hker a (MonoidHom.mem_ker.mp ha')) with ha1' | hat
      · subst ha1'
        exact absurd rfl ha1
      · exact hat
    intro x y hx hy
    exact Subtype.ext (Subtype.ext ((hmem x hx).trans (hmem y hy).symm))
  have hψrange : ψ.range = E.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc Nat.card E = Nat.card ψ.ker * ψ.ker.index := (Subgroup.card_mul_index _).symm
    _ = Nat.card ψ.ker * Nat.card (E.map φ) := by rw [Subgroup.index_ker, hψrange]
    _ ≤ 2 * 2 := Nat.mul_le_mul hψker hFcard
    _ = 2 ^ 2 := by norm_num

end RankBoundHyp

theorem generalizedFittingUniqueInvolutionRankBound :
    Assembly.GeneralizedFittingUniqueInvolutionRankBound :=
  fun _ _ _ _ hcore hcentral horder hlayer hunique =>
    RankBoundHyp.twoRank_le ⟨hcore, hcentral, horder, hlayer, hunique⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
