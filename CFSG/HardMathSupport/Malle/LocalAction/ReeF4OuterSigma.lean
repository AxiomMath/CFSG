module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeF4Target
import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
import CFSG.CharacterTheory.Semidihedral.FixedFieldData
import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
import CFSG.LocalAnalysis.SectionRank.SylowWitness
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


section Abstract

theorem exists_sigma_of_outer
    {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] {Γ : Type} [Group Γ] [Finite Γ]
    (eK : K ≃* Γ) (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hK : K ≠ ⊤)
    (hOut : Nat.card (Outer Γ) ∣ 5) (τ : MulAut Γ) (hτ : orderOf τ = 5) (hni : τ ∉ inner Γ) :
    K.index = 5 ∧ ∃ σ : Y, σ ∉ K ∧ orderOf σ = 5 ∧
      ∀ (k : Y) (hk : k ∈ K) (hk' : σ * k * σ⁻¹ ∈ K),
        eK ⟨σ * k * σ⁻¹, hk'⟩ = τ (eK ⟨k, hk⟩) := by
  set ρ : Y →* MulAut Γ := (MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal with hρdef
  have hρ : ∀ (y k : Y) (hk : k ∈ K) (hk' : y * k * y⁻¹ ∈ K),
      ρ y (eK ⟨k, hk⟩) = eK ⟨y * k * y⁻¹, hk'⟩ := by
    intro y k hk hk'
    simp [hρdef]
    rfl
  have hρK : ∀ (y : Y) (hy : y ∈ K), ρ y = MulAut.conj (eK ⟨y, hy⟩) := by
    intro y hy
    ext g
    obtain ⟨k, rfl⟩ := eK.surjective g
    rw [hρ y k.1 k.2 (K.mul_mem (K.mul_mem hy k.2) (K.inv_mem hy))]
    simp only [MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hmem : y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : y * k * y⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance k hk y
      have h1 := hρ y k hk hk'
      rw [hy] at h1
      have h2 : (⟨y * k * y⁻¹, hk'⟩ : K) = ⟨k, hk⟩ := eK.injective h1.symm
      have h3 : y * k * y⁻¹ = k := congrArg Subtype.val h2
      calc k * y = (y * k * y⁻¹) * y := by rw [h3]
        _ = y * k := by group
    rw [hC] at hmem
    exact hmem
  set ψ : Y →* Outer Γ := (QuotientGroup.mk' (inner Γ)).comp ρ with hψdef
  have hker : ψ.ker = K := by
    ext y
    rw [MonoidHom.mem_ker]
    simp only [hψdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := eK.surjective x
      have h1 : ρ y = ρ k := by rw [hρK k k.2]; exact hx.symm
      rw [hρinj h1]
      exact k.2
    · intro hy
      exact ⟨eK ⟨y, hy⟩, (hρK y hy).symm⟩
  have hidx : K.index = Nat.card ψ.range := by rw [← hker]; exact Subgroup.index_ker ψ
  have hdvd : K.index ∣ 5 := hidx ▸ (Subgroup.card_subgroup_dvd_card ψ.range).trans hOut
  have hidx5 : K.index = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · exact absurd (Subgroup.index_eq_one.1 h) hK
    · exact h
  refine ⟨hidx5, ?_⟩
  have hrange : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h5 : 5 ∣ Nat.card (Outer Γ) := by
      rw [← hidx5, hidx]; exact Subgroup.card_subgroup_dvd_card _
    rw [← hidx, hidx5]
    exact (Nat.dvd_antisymm hOut h5).symm
  obtain ⟨y, hy⟩ := MonoidHom.range_eq_top.1 hrange (QuotientGroup.mk τ)
  have hy' : (ρ y)⁻¹ * τ ∈ inner Γ := by
    have : QuotientGroup.mk (ρ y) = (QuotientGroup.mk τ : Outer Γ) := hy
    exact QuotientGroup.eq.1 this
  obtain ⟨x, hx⟩ := hy'
  have hxτ : τ = ρ y * MulAut.conj x := by
    rw [hx]; simp
  set k₀ : K := eK.symm x with hk₀
  have hρσ : ρ (y * (k₀ : Y)) = τ := by
    rw [map_mul, hρK (k₀ : Y) k₀.2, hxτ]
    congr 2
    simp [hk₀]
  refine ⟨y * (k₀ : Y), fun hσ => hni ?_, ?_, ?_⟩
  · rw [← hρσ, hρK _ hσ]
    exact ⟨_, rfl⟩
  · rw [← hτ, ← hρσ]
    exact (orderOf_injective ρ hρinj _).symm
  · intro k hk hk'
    rw [← hρσ]
    exact (hρ _ k hk hk').symm

theorem exists_subgroup_map_of_le {Y : Type} [Group Y] (K : Subgroup Y) {Γ : Type} [Group Γ]
    (eK : K ≃* Γ) (F : Subgroup Y) (hFK : F ≤ K) :
    ∃ F' : Subgroup Γ, Nonempty (F' ≃* F) ∧
      ∀ γ ∈ F', ∃ k : K, (k : Y) ∈ F ∧ eK k = γ :=
  ⟨(F.subgroupOf K).map eK.toMonoidHom,
    ⟨(Subgroup.equivMapOfInjective (F.subgroupOf K) eK.toMonoidHom eK.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hFK)⟩,
    by rintro _ ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩⟩

theorem exists_elemAbelian_map_of_le {Y : Type} [Group Y] (K : Subgroup Y) {Γ : Type} [Group Γ]
    (eK : K ≃* Γ) (E : Subgroup Y) (hEK : E ≤ K) (hE : CFSG.Open.IsElemAbelian 5 E) :
    ∃ E' : Subgroup Γ, CFSG.Open.IsElemAbelian 5 E' ∧ Nat.card E' = Nat.card E := by
  have hE' : CFSG.Open.IsElemAbelian 5 (E.subgroupOf K) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have h := congrArg Subtype.val (hE.1.is_comm.comm (⟨a.1.1, a.2⟩ : E) ⟨b.1.1, b.2⟩)
      exact h
    · exact Subtype.ext (by simpa using hE.2 (x : Y) hx)
  refine ⟨(E.subgroupOf K).map eK.toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 5 eK.toMonoidHom _ hE', ?_⟩
  rw [Subgroup.card_map_of_injective eK.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv

end Abstract

section Ree

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.RankThree.PartOne.K1214 (SylowShape)


theorem card_le_twentyfive_of_elemAbelian_reeGamma
    {F : Type} [Field F] [Finite F] [CharP F F4.prime] (hF : Nat.card F = 2 ^ (2 * 2 + 1))
    (E : Subgroup (F4.reeGamma F 2)) (hE : CFSG.Open.IsElemAbelian 5 E) : Nat.card E ≤ 25 := by
  have : Finite (F4.reeGamma F 2) := Subtype.finite
  have hfac : (((2 ^ (2 * 2 + 1)) ^ 2 + 1 : ℕ).factorization 5) = 2 := by
    have : ((2 ^ (2 * 2 + 1)) ^ 2 + 1 : ℕ) = 5 ^ 2 * 41 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_five]
    have : Nat.factorization 41 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [this]
  have hshape := CFSG.RankThree.PartOne.K128.sylowShape_ree_phi4 hF Nat.prime_five le_rfl
    (by norm_num)
  rw [hfac] at hshape
  have hEp : IsPGroup 5 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  obtain ⟨φ⟩ := hshape (S : Subgroup (F4.reeGamma F 2)) S.isPGroup' S.not_dvd_index
  let ι : E →* (Fin 2 → Multiplicative (ZMod (5 ^ 2))) :=
    φ.toMonoidHom.comp (Subgroup.inclusion hES)
  have hι : Function.Injective ι := φ.injective.comp (Subgroup.inclusion_injective hES)
  let A := {v : Fin 2 → Multiplicative (ZMod (5 ^ 2)) // v ^ 5 = 1}
  have hA : Nat.card A = 25 := by
    rw [Nat.card_eq_fintype_card]
    exact (by decide +kernel : Fintype.card {v : Fin 2 → Multiplicative (ZMod (5 ^ 2)) // v ^ 5 = 1} = 25)
  let j : E → A := fun e => ⟨ι e, by
    rw [← map_pow]
    have : (e : E) ^ 5 = 1 := Subtype.ext (hE.2 e e.2)
    rw [this, map_one]⟩
  have hj : Function.Injective j := fun a b h => hι (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective j hj
  rwa [hA] at this

theorem card_dvd_of_fixed_reeGamma
    {F : Type} [Field F] [Finite F] [CharP F F4.prime]
    (σ₀ : F ≃+* F) (hk1 : Nat.card (fixSubfield σ₀) = 2 ^ 1)
    (H : Subgroup (F4.reeGamma F 2)) (hH : ∀ γ ∈ H, F4.reeGammaFieldAut F 2 σ₀ γ = γ) :
    Nat.card H ∣ 35942400 := by
  have hfix := CFSG.SignalizerFunctorTheorem.CatalogBridge.fixed_reeGamma_F4_eq_map
    (a := 2) (b := 0) (d := 1) (m := 2) σ₀ hk1 (by norm_num)
  have hk2 : Nat.card (fixSubfield σ₀) = 2 := by simpa using hk1
  have hle : H.map (F4.reeGamma F 2).subtype ≤
      (F4.reeGamma (fixSubfield σ₀) 0).map (baseChangeGL (fixSubfield σ₀).subtype) := by
    rw [← hfix]
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨γ, hH γ hγ, rfl⟩
  have h1 : Nat.card H = Nat.card (H.map (F4.reeGamma F 2).subtype) :=
    (Subgroup.card_map_of_injective Subtype.val_injective).symm
  have h2 : Nat.card ((F4.reeGamma (fixSubfield σ₀) 0).map (baseChangeGL (fixSubfield σ₀).subtype))
      = 35942400 := by
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective _),
      ← Nat.card_congr (ReeTag.reeFixedEquivReeGamma (fixSubfield σ₀) 0).toEquiv]
    exact CFSG.SectionRank.TitsOrder.Tits_card hk2
  rw [h1, ← h2]
  exact Subgroup.card_dvd_of_le hle

theorem card_le_twentyfive_of_fixed_reeGamma
    {F : Type} [Field F] [Finite F] [CharP F F4.prime]
    (σ₀ : F ≃+* F) (hk1 : Nat.card (fixSubfield σ₀) = 2 ^ 1)
    (H : Subgroup (F4.reeGamma F 2)) (hH : ∀ γ ∈ H, F4.reeGammaFieldAut F 2 σ₀ γ = γ)
    (hp : IsPGroup 5 H) : Nat.card H ≤ 25 := by
  have hdvd := card_dvd_of_fixed_reeGamma σ₀ hk1 H hH
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  by_contra hlt
  have hn3 : 3 ≤ n := by
    by_contra h
    have : n ≤ 2 := by omega
    have : 5 ^ n ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have : 5 ^ 3 ∣ 35942400 := (pow_dvd_pow 5 hn3).trans (hn ▸ hdvd)
  norm_num at this

theorem exists_plane_fixed_reeGamma
    {F : Type} [Field F] [Finite F] [CharP F F4.prime]
    (σ₀ : F ≃+* F) (hk1 : Nat.card (fixSubfield σ₀) = 2 ^ 1) :
    ∃ E : Subgroup (F4.reeGamma F 2), CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 ∧
      ∀ γ ∈ E, F4.reeGammaFieldAut F 2 σ₀ γ = γ := by
  have hfix := CFSG.SignalizerFunctorTheorem.CatalogBridge.fixed_reeGamma_F4_eq_map
    (a := 2) (b := 0) (d := 1) (m := 2) σ₀ hk1 (by norm_num)
  have hk2 : Nat.card (fixSubfield σ₀) = 2 := by simpa using hk1
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -, -⟩ :=
    CFSG.SectionRank.Tits_sylow5_square_witness (K := fixSubfield σ₀) hk2
  let D := commutator (reeFixed ReeTag.F4 (fixSubfield σ₀) 0)
  let e₁ := ReeTag.reeFixedEquivReeGamma (fixSubfield σ₀) 0
  let φ := (baseChangeGL (fixSubfield σ₀).subtype).comp
    ((F4.reeGamma (fixSubfield σ₀) 0).subtype.comp (e₁.toMonoidHom.comp D.subtype))
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective _).comp (Subtype.val_injective.comp
      (e₁.injective.comp Subtype.val_injective))
  have hex : ∀ d, ∃ γ : F4.reeGamma F 2,
      F4.reeGammaFieldAut F 2 σ₀ γ = γ ∧ (γ : CFSG.Blueprint.Chevalley.ModGL F4.tag F) = φ d := by
    intro d
    have : φ d ∈ (F4.reeGamma (fixSubfield σ₀) 0).map (baseChangeGL (fixSubfield σ₀).subtype) :=
      ⟨_, (e₁ d).2, rfl⟩
    rw [← hfix] at this
    obtain ⟨γ, hγ, hγd⟩ := this
    exact ⟨γ, hγ, hγd⟩
  have hmem : ∀ d, φ d ∈ F4.reeGamma F 2 := by
    intro d
    obtain ⟨γ, -, hγ⟩ := hex d
    rw [← hγ]
    exact γ.2
  let ψ := φ.codRestrict _ hmem
  have hψinj : Function.Injective ψ := fun a b h => hφinj (congrArg Subtype.val h)
  have hψfix : ∀ d, F4.reeGammaFieldAut F 2 σ₀ (ψ d) = ψ d := by
    intro d
    obtain ⟨γ, hγ, hγd⟩ := hex d
    have : ψ d = γ := Subtype.ext hγd.symm
    rw [this]
    exact hγ
  refine ⟨(Subgroup.closure {x, y}).map ψ,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 5 ψ _
      (CFSG.SectionRank.isElemAbelian_closure_pair hx hy hxy), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hψinj, hcard]
  · rintro _ ⟨d, -, rfl⟩
    exact hψfix d

open CFSG.AGLEmbedding (CatGroup IsReeFFourFiveIndex reeTitsModel_of_catGroup_reeF4)


theorem exists_outer_sigma
    {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsReeFFourFiveIndex d) (e : Nonempty (K ≃* CatGroup d))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hrank : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y)) :
    K.index = 5 ∧ ∃ σ : Y, σ ∉ K ∧ orderOf σ = 5 ∧
      (∀ F : Subgroup Y, IsPGroup 5 F → F ≤ K → F ≤ Subgroup.centralizer ({σ} : Set Y) →
        Nat.card F ≤ 25) ∧
      ∃ E : Subgroup Y, E ≤ K ∧ E ≤ Subgroup.centralizer ({σ} : Set Y) ∧
        CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
  classical
  obtain ⟨e⟩ := e
  have hmodel := reeTitsModel_of_catGroup_reeF4 hd
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier (CatGroup d) 2 (2 * 2 + 1) hmodel
  obtain ⟨-, a, hfa, F, _, _, hF, ⟨e'⟩⟩ := hmodel
  have hFc : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have : CharP F F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  obtain ⟨eΓ⟩ := hS.2.2.2.2.2 a F hfa hF ⟨e'⟩
  have ha : a = 2 := by omega
  subst ha
  let eK : K ≃* F4.reeGamma F 2 := e.trans eΓ
  have : Finite (F4.reeGamma F 2) := Subtype.finite
  obtain ⟨σ₀, -, hσ₀, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
      2 5 Nat.prime_two (by norm_num) F (by simpa using hFc)
  have hk := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by norm_num : 1 ≤ 5) (by simpa using hFc) σ₀).2
  rw [hσ₀] at hk
  have hk1 : Nat.card (fixSubfield σ₀) = 2 ^ 1 := by simpa using hk
  obtain ⟨-, hnf⟩ := CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form
    (a := 2) (K := F) (by norm_num) hFc
  have hinj : Function.Injective (F4.reeGammaFieldAutHom F 2) := by
    rw [injective_iff_map_eq_one]
    intro β hβ
    refine hnf β ⟨1, ?_⟩
    rw [← F4.reeGammaFieldAutHom_apply, hβ, map_one]
  set τ : MulAut (F4.reeGamma F 2) := F4.reeGammaFieldAut F 2 σ₀ with hτdef
  have hτ : orderOf τ = 5 := by
    rw [hτdef, ← F4.reeGammaFieldAutHom_apply]
    exact (orderOf_injective _ hinj σ₀).trans hσ₀
  have hni : τ ∉ inner (F4.reeGamma F 2) := by
    intro h
    have h1 := hnf σ₀ h
    rw [h1, orderOf_one] at hσ₀
    omega
  have hOut : Nat.card (Outer (F4.reeGamma F 2)) ∣ 5 :=
    (CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hFc).2
  have hKtop : K ≠ ⊤ := by
    intro hKt
    have h3 : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) := hrank
    rcases Set.eq_empty_or_nonempty
      {k | ∃ E : Subgroup Y, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ k} with h0 | hne
    · have h00 : CFSG.Open.pRank 5 (⊤ : Subgroup Y) = 0 := by
        unfold CFSG.Open.pRank
        rw [h0]
        simp
      omega
    obtain ⟨E, -, hE, hcard⟩ := Nat.sSup_mem hne
      (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 5 Nat.prime_five _)
    obtain ⟨E', hE', hcard'⟩ := exists_elemAbelian_map_of_le K eK E (hKt ▸ le_top) hE
    have h25 := card_le_twentyfive_of_elemAbelian_reeGamma hFc E' hE'
    rw [hcard', hcard] at h25
    have : 5 ^ 3 ≤ 5 ^ (sSup {k | ∃ E : Subgroup Y, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ k}) := Nat.pow_le_pow_right (by norm_num) h3
    omega
  obtain ⟨hidx, σ, hσK, hσ5, hact⟩ :=
    exists_sigma_of_outer K eK hC hKtop hOut τ hτ hni
  have hfixK : ∀ k : K, (k : Y) ∈ Subgroup.centralizer ({σ} : Set Y) → τ (eK k) = eK k := by
    intro k hk
    have h1 : σ * k * σ⁻¹ = k := by
      have := (Subgroup.mem_centralizer_iff.1 hk) σ rfl
      rw [this]; group
    have h2 := hact k k.2 (by rw [h1]; exact k.2)
    rw [← h2]
    congr 1
    exact Subtype.ext h1
  have hcentK : ∀ k : K, τ (eK k) = eK k → (k : Y) ∈ Subgroup.centralizer ({σ} : Set Y) := by
    intro k hk
    have hk' : σ * k * σ⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance (k : Y) k.2 σ
    have h2 := hact k k.2 hk'
    rw [hk] at h2
    have h3 : σ * k * σ⁻¹ = k := congrArg Subtype.val (eK.injective h2)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    calc σ * (k : Y) = (σ * k * σ⁻¹) * σ := by group
      _ = k * σ := by rw [h3]
  refine ⟨hidx, σ, hσK, hσ5, ?_, ?_⟩
  · intro F₀ hF₀ hF₀K hF₀C
    obtain ⟨F', ⟨φ⟩, hF'⟩ := exists_subgroup_map_of_le K eK F₀ hF₀K
    have hp' : IsPGroup 5 F' := hF₀.of_equiv φ.symm
    have hcard : Nat.card F' = Nat.card F₀ := Nat.card_congr φ.toEquiv
    rw [← hcard]
    refine card_le_twentyfive_of_fixed_reeGamma σ₀ hk1 F' ?_ hp'
    intro γ hγ
    obtain ⟨k, hk, rfl⟩ := hF' γ hγ
    exact hfixK k (hF₀C hk)
  · obtain ⟨E', hE', hcard', hfixE'⟩ := exists_plane_fixed_reeGamma σ₀ hk1
    let f : F4.reeGamma F 2 →* Y := K.subtype.comp eK.symm.toMonoidHom
    have hf : Function.Injective f := K.subtype_injective.comp eK.symm.injective
    refine ⟨E'.map f, ?_, ?_, CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 5 f _ hE',
      ?_⟩
    · rintro _ ⟨γ, -, rfl⟩
      exact (eK.symm γ).2
    · rintro _ ⟨γ, hγ, rfl⟩
      refine hcentK (eK.symm γ) ?_
      rw [MulEquiv.apply_symm_apply]
      exact hfixE' γ hγ
    · rw [Subgroup.card_map_of_injective hf, hcard']

end Ree
