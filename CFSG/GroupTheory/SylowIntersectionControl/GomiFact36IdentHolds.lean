module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Ident
import CFSG.Quasithin.Background.SmithB42L2L32
import CFSG.Quasithin.Background.SmithB42Sp4Real
import CFSG.Quasithin.Vol2.E2TenEight
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Component
import CFSG.Adapters.LinearCatalogStated
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
import CFSG.Quasithin.Background.SmithB42Alt6Norm
import CFSG.Quasithin.Background.SmithB42HatA6Dim
import CFSG.Quasithin.Background.SmithB42SL3Base
import CFSG.Quasithin.Background.SmithB42SL3Key

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique TauCeti
open CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Layer
open CFSG.QuasithinUnique.Setup.Family
open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix

private theorem gomiType_of_isGomiL3
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X)))
    (h : IsGomiL3 (X ⧸ Subgroup.center X)) :
    B42TypeL3Even X ∨ B42TypeL32 X := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  rcases hd with ⟨q, hq2, hd⟩ | ⟨q, hq7, hd⟩
  · simp only at hd
    subst hd
    have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 q.p q.exponent :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [hq2] at hmodel
    by_cases hf : q.exponent = 1
    · right
      rw [hf] at hmodel
      have hm2 : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 7 1 :=
        CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hmodel
      obtain ⟨eY⟩ :=
        CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven hm2
      have hZ : Subgroup.center X = ⊥ :=
        CFSG.QuasithinUnique.Setup.Family.center_eq_bot_of_odd_central_extension_GL3
          hq.1 (eY.trans CFSG.Quasithin.B42L2.slEquivGL32) hodd
      exact ⟨hZ, hmodel⟩
    · left
      have hpos := q.exponent_pos
      exact ⟨q.exponent, by omega, hmodel⟩
  · simp only at hd
    subst hd
    have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 q.p q.exponent :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hcard : q.p ^ q.exponent = 7 := (PrimePower.card_def q).symm.trans hq7
    have hp7 : q.p = 7 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_seven).1
      (hcard ▸ dvd_pow_self q.p q.exponent_pos.ne')
    rw [hp7] at hcard hmodel
    have hex : q.exponent = 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 7) (hcard.trans (pow_one 7).symm)
    rw [hex] at hmodel
    have hm3 : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 1 :=
      CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven hmodel
    obtain ⟨eY⟩ :=
      CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven hmodel
    have hZ : Subgroup.center X = ⊥ :=
      CFSG.QuasithinUnique.Setup.Family.center_eq_bot_of_odd_central_extension_GL3
        hq.1 (eY.trans CFSG.Quasithin.B42L2.slEquivGL32) hodd
    exact Or.inr ⟨hZ, hm3⟩

private theorem gomiType_of_isGomiSp4
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X)))
    (h : IsGomiSp4 (X ⧸ Subgroup.center X)) :
    B42TypeSp4Even X ∨ B42TypeAlt6 X ∨ B42TypeHatA6 X := by
  have hperf : Group.IsPerfect X := hq.1
  rcases h with ⟨⟨eA6⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq2, hd⟩, ⟨e⟩⟩
  · let π : X →* alternatingGroup (Fin 6) :=
      eA6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    have hπ : Function.Surjective π :=
      eA6.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center X := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hoddker : Odd (Nat.card π.ker) := by rw [hker]; exact hodd
    have hb := CFSG.SectionRank.alternating_small_odd_cover_bound (n := 6)
      (by norm_num) (by norm_num) π hπ hker.le hoddker
    have hZ13 : Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3 := by
      have h1 := hb.2 (Or.inl rfl)
      rwa [hker] at h1
    rcases hZ13 with h1 | h3
    · exact Or.inr (Or.inl ⟨Subgroup.card_eq_one.1 h1, ⟨eA6⟩⟩)
    · exact Or.inr (Or.inr ⟨hq, h3, ⟨eA6⟩⟩)
  · simp only at hd
    subst hd
    have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    rw [hq2] at hmodel
    have hf : 2 ≤ q.exponent := by
      have hpos := q.exponent_pos
      by_contra hlt
      have h1 : q.exponent = 1 := by omega
      exact hmodel.1.2.2.2 (by simp [h1])
    have hZ : Subgroup.center X = ⊥ :=
      CFSG.Quasithin.E2.center_eq_bot_of_isPSp4 hmodel (MulEquiv.refl _)
    exact Or.inl ⟨hZ, q.exponent, hf, hmodel⟩

private theorem gomiTypes_of_chevTwo
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hChev : IsGomiChevTwo ↥L)
    (hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨
      IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) :
    B42TypeL3Even ↥L ∨ B42TypeL32 ↥L ∨ B42TypeSp4Even ↥L ∨
      B42TypeAlt6 ↥L ∨ B42TypeHatA6 ↥L := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  have : Finite ↥L :=
    Finite.of_injective (fun x : ↥L => (x : MulAut V)) Subtype.coe_injective
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.QuasithinUnique.Setup.Family.odd_card_center_of_irreducible hV'
      (CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hHyp.2.2)
  rcases hLie with h3 | hSp4
  · rcases gomiType_of_isGomiL3 hChev.1 hodd h3 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases gomiType_of_isGomiSp4 hChev.1 hodd hSp4 with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

private theorem realizesVia_nat_statedSL {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F]
    {π : ↥(StatedSL 3 F) →* ↥L} (hπ : Function.Surjective π)
    {e : V ≃* Multiplicative (Fin 3 → F)}
    (he : ∀ (γ : ↥(StatedSL 3 F)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 F) γ (e v)) :
    (FFModel.nat (StatedSL 3 F)).RealizesVia L ⊤ ⊥ π :=
  CFSG.Quasithin.G64.realizesVia_nat_of hπ bot_le (fun _ _ _ => trivial)
    (fun h z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one])
    (e.toMonoidHom.comp (⊤ : Subgroup V).subtype)
    (fun x => ⟨⟨e.symm x, trivial⟩, by simp⟩)
    (fun u => by
      rw [Subgroup.mem_bot]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulEquivClass.map_eq_one_iff])
    (fun γ u _ => he γ u)

private theorem nontrivial_binModel_of_irr {V : Type} [CommGroup V] [Finite V]
    {W : Type} [AddCommGroup W] {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (θ : V ≃* Multiplicative W) : Nontrivial W := by
  obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.1
  replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
  refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
  have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
  simpa using congrArg θ.symm h1

private theorem natural_of_l3Even
    {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hP : B42TypeL3Even ↥L) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    ∃ a : ℕ, 1 ≤ a ∧ BinaryNaturalSL L ⊤ ⊥ 3 a := by
  obtain ⟨f, hf, hmodel⟩ := hP
  obtain ⟨-, F, _, _, φ₀, hFcard, hcov⟩ :=
    CFSG.Quasithin.B42SL3.exists_cover_core hV hHyp (by omega) hmodel
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary hV'
  have hirrV := CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hHyp.2.2
  have hntW := nontrivial_binModel_of_irr hHyp θ
  have hker := CFSG.Quasithin.B42SL3.repOf_ker θ hcov
  have hirr := CFSG.Quasithin.B42SL3.repOf_irreducible θ hirrV hcov.surjective
  obtain ⟨Q, -, hQ, hQq, -⟩ := CFSG.Quasithin.exists_quadratic_offender_le hV hA
  have : CFSG.IsElementaryAbelian 2 ↥(Q.map (binPsi θ).toMonoidHom) :=
    (CFSG.QuasithinUnique.Setup.Layer.Actor.isElemAbelian2_iff_map θ Q).1 hQ.2.2.1
  have hQ1 : Q.map (binPsi θ).toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective Q (binPsi θ).injective]
    exact hQ.2.1
  obtain ⟨ψ, hψ, E, hE⟩ := CFSG.Quasithin.B42SL3.natural_of_offender
    (CFSG.Quasithin.B42SL3.repOf θ φ₀) hker (Q.map (binPsi θ).toMonoidHom)
    (CFSG.Quasithin.B42SL3.intertwines_map θ hcov.surjective
      (hQ.1.trans (CFSG.Quasithin.B42L2.le_normalizer_of_b4HypCore hHyp)))
    (by omega) (by rw [Fintype.card_eq_nat_card]; exact hFcard) hirr hQ1
    (CFSG.Quasithin.B42SL3.quad_map θ hQq)
    (CFSG.Quasithin.B42SL3.card_le_map θ hQ)
  let ε := specialLinearGroupEquivStatedSL 3 F
  let π : ↥(StatedSL 3 F) →* ↥L := φ₀.comp (ψ.comp ε.symm.toMonoidHom)
  have hπ : Function.Surjective π := fun l => by
    obtain ⟨x, rfl⟩ := hcov.surjective l
    exact ⟨ε (ψ x), by simp [π, hψ]⟩
  let e : V ≃* Multiplicative (Fin 3 → F) := θ.trans (AddEquiv.toMultiplicative E)
  have he : ∀ (γ : ↥(StatedSL 3 F)) (v : V),
      e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 F) γ (e v) := by
    intro γ v
    obtain ⟨g, rfl⟩ := ε.surjective γ
    show Multiplicative.ofAdd (E (Multiplicative.toAdd
      (θ (((π (ε g) : ↥L) : MulAut V) v)))) =
      Multiplicative.ofAdd (((((ε g : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ E (Multiplicative.toAdd (θ v))))
    rw [show π (ε g) = φ₀ (ψ g) by simp [π],
      ← CFSG.Quasithin.B42SL3.repOf_toAdd θ φ₀ (ψ g) v, hE, hψ]
    rfl
  exact ⟨f, by omega, F, inferInstance, inferInstance, hFcard,
    ⟨π, realizesVia_nat_statedSL hπ he⟩⟩

private theorem natural_of_l32 {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hP : B42TypeL32 ↥L) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    ∃ a : ℕ, 1 ≤ a ∧ BinaryNaturalSL L ⊤ ⊥ 3 a := by
  classical
  obtain ⟨hZ, hmodel⟩ := hP
  obtain ⟨eL⟩ := CFSG.Quasithin.B42L2.exists_gl32_of_model hZ hmodel
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary hV'
  have hirr := CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hHyp.2.2
  have hntW := nontrivial_binModel_of_irr hHyp θ
  have hGL : G = L := CFSG.Quasithin.B42L2.eq_of_l32_core θ hHyp hZ eL hA
  have hoffL : ∀ B, IsFFStarOffender G B → IsFFStarOffender L B := fun B hB => hGL ▸ hB
  obtain ⟨h3, -⟩ := CFSG.Quasithin.B42L2.l32_offender_data θ hirr eL (hoffL A hA)
  obtain ⟨π', hπ's, f, hf⟩ := CFSG.Quasithin.B42L2.exists_natural_l32 θ hirr eL h3
  let Γ := StatedSL 3 (ZMod 2)
  let π : ↥Γ →* ↥L := π'.comp Γ.subtype
  have hπ : Function.Surjective π := by
    intro l
    obtain ⟨g, rfl⟩ := hπ's l
    exact ⟨⟨g, Subgroup.subset_closure (CFSG.Quasithin.B42L2.det_eq_one_GL32 g)⟩, rfl⟩
  refine ⟨1, by norm_num, ZMod 2, inferInstance, inferInstance, ?_, ⟨π, ?_⟩⟩
  · rw [Nat.card_zmod, pow_one]
  · exact realizesVia_nat_statedSL (e := f) hπ (fun γ u => hf (γ : GL32) u)

private theorem natural_of_sp4Even
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hP : B42TypeSp4Even ↥L) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    ∃ a : ℕ, 2 ≤ a ∧ BinaryNaturalSp4 L ⊤ ⊥ a := by
  obtain ⟨hZ, f, hf, hmodel⟩ := hP
  exact ⟨f, hf,
    CFSG.Quasithin.B42Sp4.binaryNaturalSp4_of_offender_core hV hHyp hZ hf hmodel hA⟩

private theorem natural_of_alt6 {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hP : B42TypeAlt6 ↥L) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    AlternatingNatural L ⊤ ⊥ 6 := by
  have C := CFSG.Quasithin.B42Alt6.ctx_of_b4Hyp_core hHyp hP
  have hS2 : ∀ s : V, s * s = 1 := fun s => by rw [← pow_two]; exact hV s
  have h64 := CFSG.Quasithin.B42Alt6.card_le_sixtyfour C hHyp.2.2 hA
  obtain ⟨M⟩ := CFSG.Quasithin.B42Alt6.exists_n6Model hS2 C hHyp.2.2 h64
  exact M.alternatingNatural

private theorem natural_of_hatA6 {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hP : B42TypeHatA6 ↥L) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    TripleA6Six L ⊤ ⊥ := by
  have hcard := CFSG.Quasithin.HatA6.card_V_core hV hHyp hP hA
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hP
  exact CFSG.Quasithin.HatA6.hatA6SixModel (V := V) hV hcard L hq.1 hZ ⟨e⟩


theorem gomiB42CoreNatural_holds :
    GomiB42CoreNatural := by
  intro V _ _ hV G L hHyp hChev hLie A hA
  rcases gomiTypes_of_chevTwo hV hHyp hChev hLie with hP | hP | hP | hP | hP
  · exact Or.inl (natural_of_l3Even hV hHyp hP hA)
  · exact Or.inl (natural_of_l32 hV hHyp hP hA)
  · exact Or.inr (Or.inl (natural_of_sp4Even hV hHyp hP hA))
  · exact Or.inr (Or.inr (Or.inl (natural_of_alt6 hV hHyp hP hA)))
  · exact Or.inr (Or.inr (Or.inr (natural_of_hatA6 hV hHyp hP hA)))

theorem gomiFact36Identification_holds :
    GomiFact36Identification :=
  gomiFact36Identification_of_b42CoreNatural gomiB42CoreNatural_holds

end CFSG.GroupTheory
