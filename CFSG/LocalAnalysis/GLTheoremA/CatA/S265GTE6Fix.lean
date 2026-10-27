module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GTE6Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeLocal
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeMat
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldSubgroup
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaUpgrade
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6OuterRankFourHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThree
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerComponentDvd
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.StandardType (ggFix mem_ggFix)
open scoped Pointwise

set_option linter.unusedSectionVars false

section Helpers

private theorem conj_injective_of_center_eq_bot {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have hc : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun h => by
    have h1 : g * h * g⁻¹ = h := by
      simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut G => φ h) hg
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc

private theorem mul_conj_mul_inv_eq_conj {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv]

private theorem apply_eq_of_mul_conj_comm {G : Type*} [Group G]
    (hZ : Function.Injective (MulAut.conj : G →* MulAut G)) {x : G} {g : MulAut G}
    (h : g * MulAut.conj x = MulAut.conj x * g) : g x = x := by
  apply hZ
  rw [← mul_conj_mul_inv_eq_conj, h, mul_inv_cancel_right]

private theorem card_eq_card_inf_ker_mul_card_map' {Γ Γ' : Type*} [Group Γ] [Group Γ']
    (φ : Γ →* Γ') (S : Subgroup Γ) :
    Nat.card S = Nat.card (S ⊓ φ.ker : Subgroup Γ) * Nat.card (S.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp S.subtype)
  have hker : (φ.comp S.subtype).ker.map S.subtype = S ⊓ φ.ker := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_inf.2 ⟨s.2, hs⟩
    · intro hx
      obtain ⟨hxS, hxk⟩ := Subgroup.mem_inf.1 hx
      exact ⟨⟨x, hxS⟩, hxk, rfl⟩
  have hrange : (φ.comp S.subtype).range = S.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h, hrange, ← hker, Subgroup.card_map_of_injective S.subtype_injective]

private theorem card_le_card_mul_card_inf_of_le_sup {G : Type*} [Group G] [Finite G]
    {N D Y : Subgroup G} [N.Normal] (hY : Y ≤ N ⊔ D) :
    Nat.card Y ≤ Nat.card D * Nat.card ↥(Y ⊓ N) := by
  have h := card_eq_card_inf_ker_mul_card_map' (QuotientGroup.mk' N) Y
  rw [QuotientGroup.ker_mk'] at h
  have hmap : Y.map (QuotientGroup.mk' N) ≤ D.map (QuotientGroup.mk' N) := by
    refine (Subgroup.map_mono hY).trans ?_
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' N).ge, bot_sup_eq]
  have h1 : Nat.card (Y.map (QuotientGroup.mk' N)) ≤ Nat.card D :=
    (Subgroup.card_le_of_le hmap).trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _))
  calc Nat.card Y = Nat.card ↥(Y ⊓ N) * Nat.card (Y.map (QuotientGroup.mk' N)) := h
    _ ≤ Nat.card ↥(Y ⊓ N) * Nat.card D := Nat.mul_le_mul_left _ h1
    _ = Nat.card D * Nat.card ↥(Y ⊓ N) := Nat.mul_comm _ _

private theorem mem_left_of_pow_prime_eq_one {G : Type*} [Group G] [Finite G] {X D : Subgroup G}
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) {p : ℕ} (hp : p.Prime)
    (hD : ¬ p ∣ Nat.card D) {c : G} (hc : c ∈ X ⊔ D) (hcp : c ^ p = 1) : c ∈ X := by
  have hXN : X ≤ Subgroup.normalizer (D : Set G) :=
    hXD.trans (Subgroup.centralizer_le_normalizer _)
  have hc' : c ∈ (X : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X D hXN]
    exact hc
  obtain ⟨x, hx, d, hd, rfl⟩ := Set.mem_mul.1 hc'
  have hxd : Commute x d := (Subgroup.mem_centralizer_iff.1 (hXD hx) d hd).symm
  have hdp : d ^ p ∈ X := by
    have h1 : x ^ p * d ^ p = 1 := by
      rw [← hxd.mul_pow]
      exact hcp
    rw [eq_inv_of_mul_eq_one_right h1]
    exact X.inv_mem (X.pow_mem hx p)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2
    fun h => hD (h.trans (Subgroup.orderOf_dvd_natCard D hd)))
  have hdX : d ∈ X := by
    rw [← hm]
    exact X.pow_mem hdp m
  exact X.mul_mem hx hdX

private theorem card_le_of_le_cyclic {G : Type*} [Group G] [Finite G] {X H : Subgroup G}
    (hX : IsCyclic X) (hHX : H ≤ X) {p : ℕ} (hp : 0 < p) (hH : ∀ h ∈ H, h ^ p = 1) :
    Nat.card H ≤ p := by
  haveI := hX
  haveI := Subgroup.isCyclic_of_le hHX
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  refine Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one ?_)
  exact Subtype.ext (by simpa using hH _ g.2)

private theorem glaPLayer_ne_bot_of_le_glaLayer {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {X P : Subgroup G} (hP : P ≤ GLALayer X) (hpP : p ∣ Nat.card P) :
    GLAPLayer p X ≠ ⊥ := by
  obtain ⟨J, hJ, hpJ⟩ := CFSG.exists_glaPComponent_dvd_card_of_dvd_card_glaLayer hp
    (hpP.trans (Subgroup.card_dvd_of_le hP))
  intro hbot
  have hle : J ≤ GLAPLayer p X := le_sSup hJ
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hpJ
  exact hp.one_lt.ne' (Nat.dvd_one.1 hpJ)

end Helpers

section TwE6Eight


theorem exists_fix_glaPLayer_twE6Eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 3)
    {δ : K ≃+* K} (hδ : orderOf δ = 3)
    {A V : Subgroup ↥(twistedE6RootGroup K σ)} (hA : IsElemAbelian 3 A)
    (hA81 : 3 ^ 4 ≤ Nat.card A) (hAδ : ∀ a ∈ A, fieldActor (t := TwistTag.E6) σ δ a = a)
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set ↥(twistedE6RootGroup K σ))) :
    ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (fixSubgroup (fieldActor (t := TwistTag.E6) σ δ) ⊓
      fixSubgroup (MulAut.conj a)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A₁, hA₁A, hA₁c⟩ : ∃ A₁ : Subgroup ↥(twistedE6RootGroup K σ), A₁ ≤ A ∧
      Nat.card A₁ = 3 ^ 4 := by
    obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
    have h4k : 4 ≤ k := by
      rw [hk] at hA81
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hA81
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 4) (G := ↥A)
      (by rw [hk]; exact Nat.pow_dvd_pow 3 h4k)
    exact ⟨H.map A.subtype, Subgroup.map_subtype_le H, by
      rw [Subgroup.card_map_of_injective A.subtype_injective, hH]⟩
  have hA₁el : IsElemAbelian 3 A₁ := hA.mono hA₁A
  obtain ⟨X, hX⟩ : ∃ X : Subgroup (ModGL TwistTag.E6.tag K),
      X = A₁.map (twistedE6RootGroup K σ).subtype := ⟨_, rfl⟩
  have hXI : X ≤ twistedE6InndiagGL K σ := by
    rw [hX]
    rintro _ ⟨a, -, rfl⟩
    exact Subgroup.mem_sup_left a.2
  have hXδ : ∀ x ∈ X, Units.map (entrywiseHom δ.toRingHom) x = x := by
    rw [hX]
    rintro _ ⟨a, ha, rfl⟩
    exact (coe_fieldActor σ δ a).symm.trans (congrArg Subtype.val (hAδ a (hA₁A ha)))
  have hδodd : Odd (orderOf δ) := by
    rw [hδ]
    decide
  obtain ⟨hXmap, hX₀I⟩ := CFSG.StandardType.TwE6FieldCore.exists_descent_of_entrywise (n := 3)
    (by norm_num) hK hσ δ hδodd hXI hXδ
  obtain ⟨-, hK₀'⟩ := CFSG.StandardType.TwE6FieldCore.fixSubfield_card_of_odd (n := 3)
    (by norm_num) hK δ hδodd
  have hK₀ : Nat.card (fixSubfield δ) = (2 ^ 1) ^ 2 := by
    rw [hK₀', hδ] <;> norm_num
  have hσ₀ : ∀ c, fixSubfieldRestrict σ δ c = c ^ 2 ^ 1 := fun c =>
    CFSG.StandardType.TwE6FieldCore.fixSubfieldRestrict_eq_pow hK₀ (p := 3) (by decide)
      (fun c => (hσ c).trans (by norm_num)) c
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Subgroup (ModGL TwistTag.E6.tag (fixSubfield δ)),
      X₀ = X.comap (baseChangeGL (fixSubfield δ).subtype) := ⟨_, rfl⟩
  rw [← hX₀] at hXmap hX₀I
  have hX₀el : IsElemAbelian 3 X₀ := by
    rw [hX₀, hX]
    exact (hA₁el.map _).comap (baseChangeGL_injective _)
  have hX₀c : Nat.card X₀ = 3 ^ 4 := by
    rw [← Subgroup.card_map_of_injective (baseChangeGL_injective (fixSubfield δ).subtype), hXmap,
      hX, Subgroup.card_map_of_injective (twistedE6RootGroup K σ).subtype_injective, hA₁c]
  have hXI' : X₀.map (baseChangeGL (fixSubfield δ).subtype) ≤ twistedE6InndiagGL K σ := by
    rw [hXmap]
    exact hXI
  have hU : CFSG.StandardType.TwE6RootKill.TwNormTwo K σ
      (X₀.map (baseChangeGL (fixSubfield δ).subtype)) := by
    rw [hXmap, hX]
    refine ⟨V.map (twistedE6RootGroup K σ).subtype, Subgroup.map_subtype_le V, ?_, hV2.map _, ?_⟩
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (twistedE6RootGroup K σ).subtype_injective]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
      exact ⟨a * v * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hAV (hA₁A ha)) v).1 hv, by
        rw [map_mul, map_mul, map_inv]⟩
  obtain ⟨u₀, hu₀C, hu₀1, ⟨n₂, hu₀2⟩, hu₀c⟩ := exists_two_commute_twE6Two
    (fixSubfield δ).subtype hK₀ hK hσ₀ hσ hX₀I hX₀el hX₀c hXI' hU
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup (MulAut ↥(twistedE6RootGroup (fixSubfield δ)
      (fixSubfieldRestrict σ δ))), Y =
        (X₀.comap (twistedE6InndiagGL (fixSubfield δ) (fixSubfieldRestrict σ δ)).subtype).map
          (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ)) := ⟨_, rfl⟩
  have hYel : IsElemAbelian 3 Y := by
    rw [hY]
    exact (hX₀el.comap (Subgroup.subtype_injective _)).map _
  have hYrange : Y ≤ (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ)).range := by
    rw [hY]
    rintro _ ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  have hYI : Y ≤ (CFSG.StandardType.RecipeExcLang.twConj (fixSubfield δ)
      (fixSubfieldRestrict σ δ)).range :=
    hYrange.trans
      (CFSG.StandardType.TwE6EndNode3.range_twistedE6InndiagConj_le (fixSubfieldRestrict σ δ))
  have hinj₀ : Function.Injective
      (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ)) :=
    twistedE6InndiagConj_injective Nat.prime_two (f := 1) le_rfl hK₀ _ hσ₀
  have hX₀le : X₀ ≤
      (twistedE6InndiagGL (fixSubfield δ) (fixSubfieldRestrict σ δ)).subtype.range := by
    rw [Subgroup.range_subtype]
    exact hX₀I
  have hYc : Nat.card Y = 3 ^ 4 := by
    rw [hY, Subgroup.card_map_of_injective hinj₀, ← hX₀c,
      ← Subgroup.card_map_of_injective
        (Subgroup.subtype_injective (twistedE6InndiagGL (fixSubfield δ) (fixSubfieldRestrict σ δ))),
      Subgroup.map_comap_eq_self hX₀le]
  obtain ⟨ε₀, hε₀⟩ := CFSG.StandardType.TwE6DD2.exists_recipeEquiv (n := 1) le_rfl hK₀
    (fixSubfieldRestrict σ δ) hσ₀
  have hZ₀ : Subgroup.center ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 _ (fixSubfieldRestrict σ δ)
  have hconj₀ := conj_injective_of_center_eq_bot hZ₀
  haveI : Finite (MulAut ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  have hV₀1 : Subgroup.zpowers (MulAut.conj (⟨u₀, hu₀C⟩ :
      ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)))) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    have h1 : (⟨u₀, hu₀C⟩ : ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ))) = 1 :=
      hconj₀ (h.trans (map_one _).symm)
    exact hu₀1 (congrArg Subtype.val h1)
  have hpow : (MulAut.conj (⟨u₀, hu₀C⟩ :
      ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)))) ^ 2 ^ n₂ = 1 := by
    have h1 : (⟨u₀, hu₀C⟩ : ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ))) ^
        2 ^ n₂ = 1 := Subtype.ext (by simpa using hu₀2)
    rw [← map_pow, h1, map_one]
  have hV₀2 : IsPGroup 2 (Subgroup.zpowers (MulAut.conj (⟨u₀, hu₀C⟩ :
      ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ))))) :=
    IsPGroup.of_card_dvd_pow (n := n₂) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hpow)
  have hYV : ∀ y ∈ Y, ∀ v ∈ Subgroup.zpowers (MulAut.conj (⟨u₀, hu₀C⟩ :
      ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)))),
      y * v * y⁻¹ ∈ Subgroup.zpowers (MulAut.conj (⟨u₀, hu₀C⟩ :
        ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)))) := by
    rw [hY]
    rintro _ ⟨w, hw, rfl⟩ v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hw' : (w : ModGL TwistTag.E6.tag (fixSubfield δ)) ∈ X₀ := hw
    have hc : u₀ * (w : ModGL TwistTag.E6.tag (fixSubfield δ)) =
        (w : ModGL TwistTag.E6.tag (fixSubfield δ)) * u₀ := hu₀c _ hw'
    have hwc : twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w ⟨u₀, hu₀C⟩ =
        ⟨u₀, hu₀C⟩ := by
      apply Subtype.ext
      rw [twistedE6InndiagConj_apply]
      show (w : ModGL TwistTag.E6.tag (fixSubfield δ)) * u₀ *
        (w : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹ = u₀
      rw [← hc, mul_inv_cancel_right]
    rw [← conj_zpow, mul_conj_mul_inv_eq_conj, hwc]
    exact Subgroup.zpow_mem_zpowers _ k
  obtain ⟨τ, hτY, hτ1, Xc, D', hfix, hXc, hXD, hDq, -, -⟩ :=
    CFSG.StandardType.TwE6EndNode3.exists_coroot_data_of_two_local
      (StandardType.TwE6RootKill.rootKill_of_ennolaKill_weylKill
          (StandardType.TwE6RootKill.ennolaKill_of_steps
              StandardType.TwE6RootKill.leviSplitStep_holds
              StandardType.TwE6RootKill.ennolaSplitStep_holds)
          StandardType.TwE6RootKill.weylKill_holds)
      CFSG.StandardType.TwE6FieldCore.subfieldLangDatumThreeFour_holds
      (CFSG.StandardType.TwE6RootAs.twE6CorootCoreGen_of_upgrade
        CFSG.StandardType.TwE6RootAs.twE6EnnolaUpgrade_holds
        CFSG.StandardType.TwE6RootAs.twE6CorootCore_holds)
      CFSG.StandardType.TwE6RootAs.twE6OuterRankFour_holds (n := 1) le_rfl hK₀
      (fixSubfieldRestrict σ δ) hσ₀ (by norm_num) hZ₀
      (fun φ hφ k hk => CFSG.StandardType.TwE6EndNode3.mem_range_conj_of_two_pow
        (fixSubfieldRestrict σ δ) le_rfl hK₀ hε₀ hφ hk)
      hYel hYI hYc hV₀1 hV₀2 hYV
  have hτY' := hτY
  rw [hY] at hτY'
  obtain ⟨w₀, hw₀, rfl⟩ := hτY'
  have hw₀X : baseChangeGL (fixSubfield δ).subtype (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) ∈
      X := by
    have h : (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) ∈ X₀ := hw₀
    rw [hX₀] at h
    exact h
  rw [hX] at hw₀X
  obtain ⟨a, haA₁, ha⟩ := hw₀X
  have ha' : (a : ModGL TwistTag.E6.tag K) =
      baseChangeGL (fixSubfield δ).subtype (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) := ha
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hτ1
    have h1 : (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) = 1 :=
      baseChangeGL_injective (fixSubfield δ).subtype (by rw [← ha']; simp)
    rw [show w₀ = 1 from Subtype.ext h1, map_one]
  have hYsub : Y ≤ twistedE6Inn (fixSubfield δ) (fixSubfieldRestrict σ δ) ⊔
      twistedE6Diag (fixSubfield δ) (fixSubfieldRestrict σ δ) := by
    rw [← range_twistedE6InndiagConj]
    exact hYrange
  have h81 := card_le_card_mul_card_inf_of_le_sup hYsub
  have hD9 := card_twistedE6Diag_le_nine (fixSubfield δ) (by rw [hK₀] <;> norm_num)
    (fixSubfieldRestrict σ δ) (fun c => (hσ₀ c).trans (by rw [pow_one]))
  have hcardY₀ : Nat.card ↥(Y.comap (MulAut.conj :
      ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)) →* _)) =
      Nat.card ↥(Y ⊓ twistedE6Inn (fixSubfield δ) (fixSubfieldRestrict σ δ)) := by
    rw [← Subgroup.card_map_of_injective hconj₀, Subgroup.map_comap_eq]
    exact congrArg (fun H : Subgroup (MulAut ↥(twistedE6RootGroup (fixSubfield δ)
      (fixSubfieldRestrict σ δ))) => Nat.card ↥H) (inf_comm _ _)
  have h3D : 3 ∣ Nat.card D' := by
    by_contra h3
    have hY₀X : Y.comap (MulAut.conj :
        ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)) →* _) ≤ Xc := by
      intro c hc
      have hcY : MulAut.conj c ∈ Y := hc
      have hcfix : c ∈ ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀) :=
        mem_ggFix.2 (apply_eq_of_mul_conj_comm hconj₀ (hYel.comm hτY hcY))
      rw [hfix] at hcfix
      have hc3 : c ^ 3 = 1 := hconj₀ (by
        rw [map_pow, map_one]
        exact hYel.2 _ hcY)
      exact mem_left_of_pow_prime_eq_one hXD Nat.prime_three h3 hcfix hc3
    have hle3 := card_le_of_le_cyclic (p := 3) hXc hY₀X (by norm_num) fun c hc =>
      hconj₀ (by
        rw [map_pow, map_one]
        exact hYel.2 _ (show MulAut.conj c ∈ Y from hc))
    have hprod := Nat.mul_le_mul hD9 (hcardY₀.symm.trans_le hle3)
    rw [hYc] at h81
    exact absurd (h81.trans hprod) (by norm_num)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)) →*
      ↥(twistedE6RootGroup K σ), ∀ u, (ψ u : ModGL TwistTag.E6.tag K) =
        baseChangeGL (fixSubfield δ).subtype (u : ModGL TwistTag.E6.tag (fixSubfield δ)) :=
    ⟨((baseChangeGL (fixSubfield δ).subtype).comp
      (twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)).subtype).codRestrict _
      fun u => CFSG.StandardType.TwE6FieldCore.baseChangeGL_mem_twistedE6RootGroup σ δ u.2,
      fun u => rfl⟩
  have hψinj : Function.Injective ψ := fun u v h => Subtype.ext
    (baseChangeGL_injective (fixSubfield δ).subtype (by rw [← hψ, ← hψ, h]))
  have hfδ : ∀ c, fieldActor (t := TwistTag.E6) σ δ (ψ c) = ψ c := fun c => by
    apply Subtype.ext
    rw [coe_fieldActor, hψ]
    exact CFSG.LieType.AlgebraicGroups.entrywise_baseChangeGL_fixSubfield δ _
  have hfa : ∀ c ∈ ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀),
      MulAut.conj a (ψ c) = ψ c := by
    intro c hc
    have hc' := congrArg Subtype.val (mem_ggFix.1 hc)
    rw [twistedE6InndiagConj_apply] at hc'
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hψ, ha',
      ← map_mul, ← map_inv, ← map_mul, hc']
  have hMN : (ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀)).map ψ ≤
      fixSubgroup (fieldActor (t := TwistTag.E6) σ δ) ⊓ fixSubgroup (MulAut.conj a) := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_inf.2 ⟨mem_fixSubgroup.2 (hfδ c), mem_fixSubgroup.2 (hfa c hc)⟩
  have hFI : (fixSubgroup (fieldActor (t := TwistTag.E6) σ δ)).map
      (twistedE6RootGroup K σ).subtype ≤ twistedE6InndiagGL K σ := by
    rintro _ ⟨g, -, rfl⟩
    exact Subgroup.mem_sup_left g.2
  have hFδ : ∀ x ∈ (fixSubgroup (fieldActor (t := TwistTag.E6) σ δ)).map
      (twistedE6RootGroup K σ).subtype, Units.map (entrywiseHom δ.toRingHom) x = x := by
    rintro _ ⟨g, hg, rfl⟩
    exact (coe_fieldActor σ δ g).symm.trans (congrArg Subtype.val (mem_fixSubgroup.1 hg))
  obtain ⟨hFmap, hF₀I⟩ := CFSG.StandardType.TwE6FieldCore.exists_descent_of_entrywise (n := 3)
    (by norm_num) hK hσ δ hδodd hFI hFδ
  have hdesc : ∀ g ∈ fixSubgroup (fieldActor (t := TwistTag.E6) σ δ),
      ∃ g₀ ∈ twistedE6InndiagGL (fixSubfield δ) (fixSubfieldRestrict σ δ),
        baseChangeGL (fixSubfield δ).subtype g₀ = (g : ModGL TwistTag.E6.tag K) := by
    intro g hg
    have h1 := Subgroup.mem_map_of_mem (twistedE6RootGroup K σ).subtype hg
    rw [← hFmap] at h1
    obtain ⟨g₀, hg₀, he⟩ := Subgroup.mem_map.1 h1
    exact ⟨g₀, hF₀I hg₀, he⟩
  have hfwd : ∀ g ∈ fixSubgroup (fieldActor (t := TwistTag.E6) σ δ) ⊓ fixSubgroup (MulAut.conj a),
      ∀ m ∈ (ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀)).map ψ,
        g * m * g⁻¹ ∈
          (ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀)).map ψ := by
    intro g hg m hm
    obtain ⟨hgδ, hga⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hm
    obtain ⟨g₀, hg₀I, hg₀⟩ := hdesc g hgδ
    have hag := congrArg Subtype.val (mem_fixSubgroup.1 hga)
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hag
    have hgw : g₀ * (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) =
        (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) * g₀ := by
      apply baseChangeGL_injective (fixSubfield δ).subtype
      rw [map_mul, map_mul, hg₀, ← ha']
      exact (mul_inv_eq_iff_eq_mul.1 hag).symm
    have hcw := congrArg Subtype.val (mem_ggFix.1 hc)
    rw [twistedE6InndiagConj_apply] at hcw
    have hc'C : g₀ * (c : ModGL TwistTag.E6.tag (fixSubfield δ)) * g₀⁻¹ ∈
        twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ) :=
      (Subgroup.mem_normalizer_iff.1 (twistedE6InndiagGL_le_normalizer _ _ hg₀I) _).1 c.2
    have h3 : g₀⁻¹ * (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹ =
        (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹ * g₀⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hgw]
    refine Subgroup.mem_map.2 ⟨⟨_, hc'C⟩, ?_, ?_⟩
    · rw [mem_ggFix]
      apply Subtype.ext
      rw [twistedE6InndiagConj_apply]
      show (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) *
          (g₀ * (c : ModGL TwistTag.E6.tag (fixSubfield δ)) * g₀⁻¹) *
          (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹ =
        g₀ * (c : ModGL TwistTag.E6.tag (fixSubfield δ)) * g₀⁻¹
      calc (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) *
            (g₀ * (c : ModGL TwistTag.E6.tag (fixSubfield δ)) * g₀⁻¹) *
            (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹
          = ((w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) * g₀) *
              (c : ModGL TwistTag.E6.tag (fixSubfield δ)) *
              (g₀⁻¹ * (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹) := by
            simp only [mul_assoc]
        _ = (g₀ * (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))) *
              (c : ModGL TwistTag.E6.tag (fixSubfield δ)) *
              ((w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹ * g₀⁻¹) := by
            rw [← hgw, h3]
        _ = g₀ * ((w₀ : ModGL TwistTag.E6.tag (fixSubfield δ)) *
              (c : ModGL TwistTag.E6.tag (fixSubfield δ)) *
              (w₀ : ModGL TwistTag.E6.tag (fixSubfield δ))⁻¹) * g₀⁻¹ := by
            simp only [mul_assoc]
        _ = g₀ * (c : ModGL TwistTag.E6.tag (fixSubfield δ)) * g₀⁻¹ := by
            rw [hcw]
    · apply Subtype.ext
      simp only [hψ, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [map_mul, map_mul, map_inv, hg₀]
  have hNM : fixSubgroup (fieldActor (t := TwistTag.E6) σ δ) ⊓ fixSubgroup (MulAut.conj a) ≤
      Subgroup.normalizer (((ggFix (twistedE6InndiagConj (fixSubfield δ)
        (fixSubfieldRestrict σ δ) w₀)).map ψ : Subgroup ↥(twistedE6RootGroup K σ)) :
          Set ↥(twistedE6RootGroup K σ)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨hfwd g hg m, fun h => ?_⟩
    have h1 := hfwd g⁻¹ (Subgroup.inv_mem _ hg) _ h
    rwa [show g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m by group] at h1
  have hD'fix : D' ≤ ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀) := by
    rw [hfix]
    exact le_sup_right
  have hD'norm : ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀) ≤
      Subgroup.normalizer (D' : Set ↥(twistedE6RootGroup (fixSubfield δ)
        (fixSubfieldRestrict σ δ))) := by
    rw [hfix]
    exact sup_le (hXD.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  obtain ⟨hDp, hDs, -⟩ := hDq
  have hcomp : CFSG.Open.IsComponentOf D'
      (ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀)) :=
    ⟨hD'fix, CFSG.Open.IsSubnormal.step hD'fix
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hD'fix).2 hD'norm)
      (CFSG.Open.IsSubnormal.refl _), hDp.commutator_eq_top, hDs⟩
  have hψker : ∀ g, ψ g = 1 → g ∈ Subgroup.center
      ↥(twistedE6RootGroup (fixSubfield δ) (fixSubfieldRestrict σ δ)) := fun g hg => by
    rw [hψinj (hg.trans (map_one ψ).symm)]
    exact Subgroup.one_mem _
  have hcompM := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map ψ hψker hcomp
  have hsubM : CFSG.Open.IsSubnormal
      ((ggFix (twistedE6InndiagConj (fixSubfield δ) (fixSubfieldRestrict σ δ) w₀)).map ψ)
      (fixSubgroup (fieldActor (t := TwistTag.E6) σ δ) ⊓ fixSubgroup (MulAut.conj a)) :=
    CFSG.Open.IsSubnormal.step hMN ((Subgroup.normal_subgroupOf_iff_le_normalizer hMN).2 hNM)
      (CFSG.Open.IsSubnormal.refl _)
  have hcompN := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_trans hcompM hsubM
  refine ⟨a, hA₁A haA₁, ha1, glaPLayer_ne_bot_of_le_glaLayer Nat.prime_three
    (CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer hcompN) ?_⟩
  rw [Subgroup.card_map_of_injective hψinj]
  exact h3D

end TwE6Eight

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
