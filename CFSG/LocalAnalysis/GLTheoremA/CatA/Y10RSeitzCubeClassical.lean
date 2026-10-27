module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTag
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwTag
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313TwoAux

theorem statedClassicalModel_POmegaMinus_unique_even {X Y : Type} [Group X] [Group Y] {n f : ℕ}
    (hX : StatedClassicalModel X .POmegaMinus n 2 f)
    (hY : StatedClassicalModel Y .POmegaMinus n 2 f) : Nonempty (X ≃* Y) := by
  obtain ⟨hadm, K₁, hF₁, hFin₁, hc₁, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := hX
  obtain ⟨-, K₂, hF₂, hFin₂, hc₂, b₂, c₂, hirr₂, ⟨e₂⟩⟩ := hY
  letI := hF₁
  letI := hFin₁
  letI := hF₂
  letI := hFin₂
  let φ : K₁ ≃+* K₂ := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hc₁.trans hc₂.symm)
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  obtain ⟨e₃⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) hn
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr₁) hirr₂
  exact ⟨e₁.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ rfl rfl))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
    (e₃.trans e₂.symm))⟩

section Certs


theorem exists_cover_POmegaMinus {n f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 2 f)
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .POmegaMinus n 2 f) :
    ∃ ψ₀ : (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K →* X,
      Function.Surjective ψ₀ ∧
        ψ₀.ker ≤ Subgroup.center (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K ∧
          IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hquasi, hY⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    .POmegaMinus n 2 f Nat.prime_two trivial hadm
  change CFSG.Open.IsQuasisimple (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K at hquasi
  change CFSG.Blueprint.LieModel
    ((lieUniversal .POmegaMinus n 2 f Nat.prime_two).K ⧸
      Subgroup.center (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K) .POmegaMinus n 2 f at hY
  have hXc : StatedClassicalModel X .POmegaMinus n 2 f :=
    hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hYc : StatedClassicalModel
      ((lieUniversal .POmegaMinus n 2 f Nat.prime_two).K ⧸
        Subgroup.center (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K)
      .POmegaMinus n 2 f :=
    hY.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨E⟩ := statedClassicalModel_POmegaMinus_unique_even hYc hXc
  haveI : IsSimpleGroup
      ((lieUniversal .POmegaMinus n 2 f Nat.prime_two).K ⧸
        Subgroup.center (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K) := hquasi.2
  let ψ₀ : (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K →* X :=
    E.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center
      (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K))
  have hsurj : Function.Surjective ψ₀ :=
    E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ₀.ker ≤ Subgroup.center (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K := by
    intro k hk
    have h1 : E (QuotientGroup.mk' (Subgroup.center
        (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K) k) = 1 := hk
    rw [map_eq_one_iff _ E.injective] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1
  refine ⟨ψ₀, hsurj, hker, MulEquiv.isSimpleGroup E.symm, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have hcom : commutator (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K ≤ ψ₀.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (hcomm _ _)
  rw [hquasi.1] at hcom
  haveI := (MulEquiv.isSimpleGroup E.symm).toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨k, rfl⟩ := hsurj x
  exact hx (hcom (Subgroup.mem_top k))

theorem seitzTwoGen_of_cover {S : Type} [Group S] [Finite S] {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f)
    (hrank : 2 ≤ (CFSG.StandardType.ggU t n f).D.rank)
    (hLM : CFSG.Blueprint.LieModel S t n 2 f)
    (ψ₀ : (lieUniversal t n 2 f Nat.prime_two).K →* S)
    (hsurj : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center (lieUniversal t n 2 f Nat.prime_two).K)
    (hsimple : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) : SeitzTwoGen S := by
  intro q hq hq2 E hE ⟨U, hU0, hU2, hUinv⟩
  haveI : Fact q.Prime := ⟨hq⟩
  let ψ : (lieUniversal t n 2 f Nat.prime_two).K →* Hol S E :=
    (SemidirectProduct.inl : S →* Hol S E).comp ψ₀
  have hrange : ψ.range = holK S E := by
    have h1 : ψ₀.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
    rw [show ψ = (SemidirectProduct.inl : S →* Hol S E).comp ψ₀ from rfl,
      MonoidHom.range_comp, h1, ← MonoidHom.range_eq_map]
    exact range_inl_eq_holK
  have hψker : ψ.ker ≤ Subgroup.center (lieUniversal t n 2 f Nat.prime_two).K := by
    intro k hk
    exact hker (by
      have h1 : SemidirectProduct.inl (ψ₀ k) = (1 : Hol S E) := hk
      exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm))
  have hquasi := holK_isQuasisimple (E := E) hsimple hnab
  obtain ⟨eq⟩ := holK_quot_equiv (E := E) hsimple hnab (MulEquiv.refl S)
  have hpres : CFSG.StandardType.GGPresentsG0 (holK S E) (CFSG.StandardType.ggU t n f).D t n f ψ :=
    ⟨⟨hadm, hrank⟩, ⟨hrange, hψker⟩, hquasi.1, hLM.of_mulEquiv eq.symm⟩
  have hEp : IsPGroup q ↥(holE S E) := IsPGroup.of_equiv hE (holEEquiv S E)
  have hEN : holE S E ≤ Subgroup.normalizer ((holK S E : Subgroup (Hol S E)) : Set (Hol S E)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 (holK_normal S E)]
    exact le_top
  set T : Subgroup (Hol S E) := U.map (SemidirectProduct.inl : S →* Hol S E) with hT
  have hTK : T ≤ holK S E := fun x hx => by
    obtain ⟨u, -, rfl⟩ := hx
    exact mem_holK.2 ⟨u, rfl⟩
  have hT0 : T ≠ ⊥ := fun h =>
    hU0 ((Subgroup.map_eq_bot_iff_of_injective U SemidirectProduct.inl_injective).1 h)
  have hT2 : IsPGroup 2 ↥T :=
    hU2.of_equiv (Subgroup.equivMapOfInjective U (SemidirectProduct.inl : S →* Hol S E)
      SemidirectProduct.inl_injective)
  have hET : holE S E ≤ Subgroup.normalizer (T : Set (Hol S E)) := holE_le_normalizer_map hUinv
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h2₁, h2₂, hn₁, hn₂, hgen⟩ :=
    CFSG.StandardType.ggTwoSignalizerGenInput_holds (Hol S E) t n f ψ (holK S E) hpres q hq hq2
      (holE S E) hEp hEN T hTK hT0 hT2 hET
  refine ⟨Q₁.comap (SemidirectProduct.inl : S →* Hol S E),
    Q₂.comap (SemidirectProduct.inl : S →* Hol S E), isPGroup_comap_inl h2₁, isPGroup_comap_inl h2₂,
    invariant_comap_inl hn₁, invariant_comap_inl hn₂, ?_⟩
  apply Subgroup.map_injective (SemidirectProduct.inl_injective (N := S) (G := ↥E))
  rw [Subgroup.map_sup, Subgroup.map_comap_eq, Subgroup.map_comap_eq, range_inl_eq_holK,
    inf_of_le_right hQ₁, inf_of_le_right hQ₂, hgen, Subgroup.map_top, range_inl_eq_holK]

theorem seitzTwoGen_of_lieModel {S : Type} [Group S] [Finite S] {t : StatedLieTag} {n f : ℕ}
    (ht : Seitz2313Cover.EvenTag t ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n 2 f)
    (h1 : ¬ (t = .PSL ∧ n = 2)) (h2 : ¬ (t = .PSU ∧ n = 3))
    (hLM : CFSG.Blueprint.LieModel S t n 2 f) : SeitzTwoGen S := by
  have hfund : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    rcases ht with ht | rfl
    · exact ht.isFundTag'
    · trivial
  have hmodelUniv : CFSG.ClassicalInvolution.ModelFacts.modelUniv t n 2 f Nat.prime_two =
      CFSG.StandardType.ggU t n f := by
    rcases ht with ht | rfl
    · exact Seitz2313Cover.modelUniv_eq' ht n 2 f Nat.prime_two
    · rfl
  have hrank : 2 ≤ (CFSG.StandardType.ggU t n f).D.rank := by
    have := CFSG.ClassicalInvolution.ModelFacts.two_le_rank t n 2 f Nat.prime_two hfund hadm h1 h2
    rwa [hmodelUniv] at this
  rcases ht with ht | rfl
  · obtain ⟨ψ₀, hsurj, hker, hsimple, hnab⟩ := Seitz2313Cover.exists_cover_even ht hadm hLM
    exact seitzTwoGen_of_cover hadm hrank hLM ψ₀ hsurj hker hsimple hnab
  · obtain ⟨ψ₀, hsurj, hker, hsimple, hnab⟩ := exists_cover_POmegaMinus hadm hLM
    exact seitzTwoGen_of_cover hadm hrank hLM ψ₀ hsurj hker hsimple hnab

theorem seitzTwoGen_of_statedClassicalModel {S : Type} [Group S] [Finite S]
    {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h1 : ¬ (t = .PSL ∧ n = 2)) (h2 : ¬ (t = .PSU ∧ n = 3))
    (h : StatedClassicalModel S t n 2 f) : SeitzTwoGen S := by
  have hLM : CFSG.Blueprint.LieModel S t n 2 f := by
    refine Or.inl ⟨?_, h⟩
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      simp [CFSG.Blueprint.classicalTags]
  have htag : Seitz2313Cover.EvenTag t ∨ t = .POmegaMinus := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl trivial
    · exact Or.inl trivial
    · exact Or.inl trivial
    · exact Or.inl trivial
    · exact Or.inr rfl
  exact seitzTwoGen_of_lieModel htag h.1 h1 h2 hLM

theorem seitzTwoGen_of_G2 {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 2 f) : SeitzTwoGen S := by
  obtain ⟨⟨-, -, -, h3⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  letI := hfield
  letI := hfinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := f) hK
  have hcard : 3 ≤ Nat.card K := by rw [hK]; exact h3
  have hq : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hcard
  obtain ⟨hfin, -, hH⟩ := CFSG.StandardType.GGOppRadExc.universal_conclusion_adjointGroup
    (τ := .G2) (K := K) hq
  letI : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := hfin
  let ψ : ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) →* S :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center
      ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)))
  have hrange : ψ.range = ⊤ := by
    have h1 : (QuotientGroup.mk' (Subgroup.center
        ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K))).range = ⊤ :=
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)
    rw [show ψ = e.symm.toMonoidHom.comp (QuotientGroup.mk' _) from rfl,
      MonoidHom.range_comp, h1, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 e.symm.surjective
  have hker : ψ.ker ≤ Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
    intro z hz
    have h1 : QuotientGroup.mk' (Subgroup.center
        ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) z = 1 := by
      have h2 : e.symm (QuotientGroup.mk' (Subgroup.center
          ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) z) = 1 := hz
      exact e.symm.injective (by simpa using h2)
    exact (QuotientGroup.eq_one_iff z).1 h1
  have hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1 := by
    intro z hz _
    have hzc := hker hz
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hzc
    exact hzc
  refine seitzTwoGen_of_oppRadGood (fun Q hQ0 hQ => ?_)
  have hQ' : CFSG.StandardType.GGRadicalTwo ψ.range Q := by rwa [hrange]
  have hgood := CFSG.StandardType.GGOppRad.GGOppRadGood.of_lift ψ hker hinv hH hQ0 hQ'
  rwa [hrange] at hgood

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
