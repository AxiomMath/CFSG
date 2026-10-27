module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternPattern
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.Blueprint.Chevalley (Tag)

variable {p f : ℕ} [Fact p.Prime]

namespace TypeEPattern

theorem edgeD6_far : ∀ a : Fin 6, ∃ b, b ≠ a ∧ ¬ edgeD 6 b a ∧ ¬ edgeD 6 a b := by
  intro a
  fin_cases a
  · exact ⟨2, by decide, by simp [edgeD], by simp [edgeD]⟩
  · exact ⟨3, by decide, by simp [edgeD], by simp [edgeD]⟩
  · exact ⟨0, by decide, by simp [edgeD], by simp [edgeD]⟩
  · exact ⟨0, by decide, by simp [edgeD], by simp [edgeD]⟩
  · exact ⟨0, by decide, by simp [edgeD], by simp [edgeD]⟩
  · exact ⟨0, by decide, by simp [edgeD], by simp [edgeD]⟩

theorem edgeE7_far : ∀ a : Fin 7, ∃ b, b ≠ a ∧ ¬ edgeE 7 b a ∧ ¬ edgeE 7 a b := by
  intro a
  fin_cases a
  · exact ⟨1, by decide, by simp [edgeE], by simp [edgeE]⟩
  · exact ⟨0, by decide, by simp [edgeE], by simp [edgeE]⟩
  · exact ⟨1, by decide, by simp [edgeE], by simp [edgeE]⟩
  · exact ⟨0, by decide, by simp [edgeE], by simp [edgeE]⟩
  · exact ⟨0, by decide, by simp [edgeE], by simp [edgeE]⟩
  · exact ⟨0, by decide, by simp [edgeE], by simp [edgeE]⟩
  · exact ⟨0, by decide, by simp [edgeE], by simp [edgeE]⟩

theorem patternLemma_plus {m : ℕ} (hm : 4 ≤ m) :
    PatternLemma (modelUniv .POmegaPlus m p f Fact.out).D.cartan := by
  obtain ⟨e, he⟩ := exists_equiv_cartan_plus (p := p) (f := f) (by omega : 3 ≤ m)
  exact PatternLemma.of_equiv e (fun a b => by rw [he, Spin.cartanD_eq]) (patternLemma_D hm)

theorem patternLemma_E7_model :
    PatternLemma (modelUniv .E7 0 p f Fact.out).D.cartan := by
  refine PatternLemma.of_equiv (Equiv.refl (Fin 7)) (fun x y => ?_) patternLemma_E7
  show Tag.cartan .E7 x y = (CartanMatrix.E 7).transpose x y
  fin_cases x <;> fin_cases y <;> decide

theorem layerGeom_lift_E7 (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (ψ : (modelUniv .E7 0 p f Fact.out).K →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {R₁ R₂ : Subgroup (modelUniv .E7 0 p f Fact.out).K}
    (h₁ : R₁ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
    (h₂ : R₂ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
    (hl : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂ := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  have hY := yData_E7 hadm (by omega)
  have hfin : Finite (modelUniv .E7 0 p f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup _ _
  have hperf : ∀ R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D, ⁅R, R⁆ = R :=
    fun R hR => le_antisymm (Subgroup.commutator_le.2 fun a ha b hb =>
      R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) (hY.perfR R hR)
  have hC : ¬ p ∣ Nat.card (Subgroup.center (modelUniv .E7 0 p f Fact.out).K) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.hC_E7 (GaloisField p f) _ le_rfl
  have hcard : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]; omega
  exact Gaps.exists_lin_of_map hcard hC ψ hψ (hperf R₁ h₁) (hperf R₂ h₂) hl

theorem layerGeom_E7_of_signPerp (hq : 5 ≤ p ^ f)
    (h : SignPerp (fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
      (GaloisField p f)) :
    LayerGeom (fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D) (GaloisField p f) :=
  ⟨h, fun ψ hψ _ h₁ _ h₂ hl => layerGeom_lift_E7 hq ψ hψ h₁ h₂ hl⟩

end TypeEPattern

section Rows

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_partnerAt_E7 (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z) (hP1 : LocalOddCentral Ω {z})
    (hTor : ∀ c : ETCtx p f .POmegaPlus 6 Ω K z, ∀ j : Fin 6 → Subgroup G,
      NodeSystem p f (edgeD 6) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ) →
      ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z,
          TorusFixedP (by norm_num : 3 ≤ 6) c ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f
            Fact.out).D.rank) ht)
    (hExcl : ∀ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j →
      ∀ β ∈ Ω, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
      ∀ p₀ : Fin 6, (∀ a, a ≠ p₀ → Commutes β (j a)) →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j p₀)) →
        p₀ = 4 ∨ p₀ = 5) :
    ∃ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) Ω K z j ∧
      (PartnerAt p f Ω j 4 ∨ PartnerAt p f Ω j 5) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num⟩
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 6 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .POmegaPlus 6 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_D6 hadmY (by omega) }
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_D6' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := partner_involution_commutes hp2 hz htβ hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htβ.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := by
    obtain ⟨W, hW⟩ := hKβ
    exact Gaps.conjSub_eq_of_standardPair
      (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2) hW htβ.mem
      htβ.orderOf_eq_two
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hLG := (Gaps.orthFacts_plus (p := p) (f := f) (m := 6) hp2 (by norm_num) hq).toLayerGeom
  have hfix0 : ∀ x ∈ (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup
      ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank)).map c.d.ψ,
      Gaps.locAut c.hΩ.conjInvariant ht x = x := by
    rw [← hjimg 0]
    exact c.fixed_of_commutes ht htβ (hj.mem 0) hβ0
  have hTN := c.toralNormal_plus (m := 6) (by norm_num) (by norm_num) ht h2t hKt
    ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank) hfix0
    (hTor c j hj hjimg β hβΩ t htβ hKβ hβ0 ht)
  obtain ⟨j', hj', p₀, ⟨W, hW⟩, hc⟩ := c.exists_attached_of_toralNormal hsingle hshape hMFZ hS3 hD4
    trivial hadmY (TypeEPattern.patternLemma_plus (by norm_num)) hLG
    (adj := edgeD 6) TypeEPattern.edgeD6_far hj hjimg hβΩ htβ hKβ hβ0 ht hTN
  refine ⟨j', hj', ?_⟩
  rcases hExcl j' hj' β hβΩ hKβ p₀ hc ⟨W, hW⟩ with rfl | rfl
  · exact Or.inl ⟨β, hβΩ, ⟨W, hW⟩, hc⟩
  · exact Or.inr ⟨β, hβΩ, ⟨W, hW⟩, hc⟩

theorem exists_partnerAt_E8 (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeT p f 1 .E7 0 Ω z) (hP1 : LocalOddCentral Ω {z})
    (hGeom : LayerGeom (fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D)
      (GaloisField p f))
    (hTor : ∀ c : ETCtx p f .E7 0 Ω K z, ∀ j : Fin 7 → Subgroup G,
      NodeSystem p f (edgeE 7) Ω K z j →
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ) →
      ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, TorusFixedE7 c ht)
    (hExcl : ∀ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j →
      ∀ β ∈ Ω, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
      ∀ p₀ : Fin 7, (∀ a, a ≠ p₀ → Commutes β (j a)) →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j p₀)) → p₀ = 6) :
    ∃ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) Ω K z j ∧ PartnerAt p f Ω j 6 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hadmY : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  have hsc : FundamentalSingleClass .E7 (modelUniv .E7 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E7 0 p f hp trivial hadmY (by decide) (by decide)
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT (by decide) hsc hΩ hK hz hshape
  let c : ETCtx p f .E7 0 Ω K z :=
    { hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz, hP1 := hP1, d := d,
      hF := oddCoverSL3_of_five_le hq, hY := yData_E7 hadmY (by omega) }
  obtain ⟨j, hj, hjimg⟩ := c.exists_nodeSystem_E7' hadmY
  obtain ⟨β, hβΩ, hKβ, hβ0⟩ :=
    c.exists_partner_transport hsingle (hj.mem 0).1 (hj.ne_K 0) (hj.commK 0)
  obtain ⟨t, htβ⟩ := hΩ.classical β hβΩ
  have ht : t * z * t⁻¹ = z := partner_involution_commutes hp2 hz htβ hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [htβ.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := by
    obtain ⟨W, hW⟩ := hKβ
    exact Gaps.conjSub_eq_of_standardPair
      (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2) hW htβ.mem
      htβ.orderOf_eq_two
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hfix0 : ∀ x ∈ (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup
      ((0 : Fin 7) : Fin (modelUniv .E7 0 p f Fact.out).D.rank)).map c.d.ψ,
      Gaps.locAut c.hΩ.conjInvariant ht x = x := by
    rw [← hjimg 0]
    exact c.fixed_of_commutes ht htβ (hj.mem 0) hβ0
  have hTN := c.toralNormal_E7 ht h2t hKt hfix0 (hTor c j hj hjimg β hβΩ t htβ hKβ hβ0 ht)
  obtain ⟨j', hj', p₀, ⟨W, hW⟩, hc⟩ := c.exists_attached_of_toralNormal hsingle hshape hMFZ hS3 hD4
    trivial hadmY TypeEPattern.patternLemma_E7_model hGeom
    (adj := edgeE 7) TypeEPattern.edgeE7_far hj hjimg hβΩ htβ hKβ hβ0 ht hTN
  refine ⟨j', hj', ?_⟩
  rcases hExcl j' hj' β hβΩ hKβ p₀ hc ⟨W, hW⟩ with rfl
  exact ⟨β, hβΩ, ⟨W, hW⟩, hc⟩

end Rows

end CFSG.ClassicalInvolution.RouteD
