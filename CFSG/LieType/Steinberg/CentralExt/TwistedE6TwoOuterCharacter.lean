module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoNativeActor
public import CFSG.LocalAnalysis.StandardType.GGRootSeparation

public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType CFSG.StandardType.TwE6KG7 CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Overlap CFSG.StandardType.GGQ2Frame.ExcPlacement
open CFSG.EvenSmallLie.TwoE6 CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PerfectCover
open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

variable
  [Finite ↥stdGroup] [Group.IsPerfect ↥stdGroup]

noncomputable abbrev nativeInn : Subgroup (MulAut ↥stdGroup) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner ↥stdGroup

noncomputable abbrev nativeDiag : Subgroup (MulAut ↥stdGroup) :=
  (compatDiagAutHom TwistTag.E6 K barHom).range

noncomputable abbrev nativeTwConj : Subgroup (MulAut ↥stdGroup) :=
  (RecipeExcLang.twConj K barEquivStd).range

private theorem nativeDiag_eq_compatParam :
    nativeDiag = (RootCentExc.compatParamAut barEquivStd.toRingHom).range := by
  change (compatDiagAutHom TwistTag.E6 K barHom).range =
    (RootCentExc.compatParamAut barEquivStd.toRingHom).range
  rw [show (compatDiagAutHom TwistTag.E6 K barHom).range =
    twistedE6Diag K barEquivStd from rfl,
    ← CFSG.StandardType.NoOffTwE6Three.range_compatParamAut_eq_twistedE6Diag
      (K := K) (σ := barEquivStd)]

private theorem nativeTwConj_eq_sup :
    nativeTwConj = nativeInn ⊔ nativeDiag := by
  rw [show nativeInn = (MulAut.conj : ↥stdGroup →* MulAut ↥stdGroup).range from rfl,
    nativeDiag_eq_compatParam]
  exact (inn_sup_compatParamAut_eq_range_twConj (K := K) (σ := barEquivStd)).symm

private theorem nativeDiag_map_mk_card_le
    (_P : Sylow 2 (hopfMultiplier ↥stdGroup)) (_Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    Nat.card (nativeDiag.map (QuotientGroup.mk' nativeInn)) ≤ 3 := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  rw [show nativeDiag = twistedE6Diag K barEquivStd from rfl]
  exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.card_twistedE6Diag_map_le_three
    K natCard_K barEquivStd (fun c => by
      change barEquivStd.toRingHom c = c ^ 2
      rw [show barEquivStd.toRingHom = barHom from rfl, barHom_apply, bar])

private theorem nativeInn_map_mk_eq_bot :
    nativeInn.map (QuotientGroup.mk' nativeInn) = ⊥ := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  rw [eq_bot_iff]
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact (QuotientGroup.eq_one_iff y).2 hy

private theorem nativeDiag_map_mk_eq_zpowers_levi
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    Subgroup.zpowers ((QuotientGroup.mk' nativeInn) levi34Diag) =
      nativeDiag.map (QuotientGroup.mk' nativeInn) := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hleviD : levi34Diag ∈ nativeDiag := ⟨levi34Unit, rfl⟩
  have hleviOut : levi34Diag ∉ nativeInn := by
    change levi34Diag ∉ (MulAut.conj : ↥stdGroup →* MulAut ↥stdGroup).range
    exact levi34Diag_not_mem_inner_std P Q3
  have hπlevi3 : ((QuotientGroup.mk' nativeInn) levi34Diag) ^ 3 = 1 := by
    rw [← map_pow, levi34Diag_pow_three, map_one]
  have hπlevi1 : ((QuotientGroup.mk' nativeInn) levi34Diag) ≠ 1 := by
    intro h
    exact hleviOut ((QuotientGroup.eq_one_iff levi34Diag).1 h)
  have hord : orderOf ((QuotientGroup.mk' nativeInn) levi34Diag) = 3 :=
    orderOf_eq_prime hπlevi3 hπlevi1
  have hzle : Subgroup.zpowers ((QuotientGroup.mk' nativeInn) levi34Diag) ≤
      nativeDiag.map (QuotientGroup.mk' nativeInn) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem _ hleviD
  have hDcard_le := nativeDiag_map_mk_card_le P Q3
  have hDcard_ge : 3 ≤ Nat.card (nativeDiag.map (QuotientGroup.mk' nativeInn)) := by
    calc 3 = orderOf ((QuotientGroup.mk' nativeInn) levi34Diag) := hord.symm
      _ = Nat.card (Subgroup.zpowers ((QuotientGroup.mk' nativeInn) levi34Diag)) :=
        (Nat.card_zpowers _).symm
      _ ≤ Nat.card (nativeDiag.map (QuotientGroup.mk' nativeInn)) :=
        Subgroup.card_le_of_le hzle
  have hDcard_eq : Nat.card (nativeDiag.map (QuotientGroup.mk' nativeInn)) = 3 :=
    le_antisymm hDcard_le hDcard_ge
  exact Subgroup.eq_of_le_of_card_ge hzle (by rw [hDcard_eq, Nat.card_zpowers, hord])

private theorem native_pi_levi_order
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    orderOf ((QuotientGroup.mk' nativeInn) levi34Diag) = 3 := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  have hπlevi3 : ((QuotientGroup.mk' nativeInn) levi34Diag) ^ 3 = 1 := by
    rw [← map_pow, levi34Diag_pow_three, map_one]
  have hπlevi1 : ((QuotientGroup.mk' nativeInn) levi34Diag) ≠ 1 := by
    intro h
    have hout : levi34Diag ∉ nativeInn := by
      change levi34Diag ∉ (MulAut.conj : ↥stdGroup →* MulAut ↥stdGroup).range
      exact levi34Diag_not_mem_inner_std P Q3
    exact hout ((QuotientGroup.eq_one_iff levi34Diag).1 h)
  exact orderOf_eq_prime hπlevi3 hπlevi1

private theorem nativeDiag_map_mk_card
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    Nat.card (nativeDiag.map (QuotientGroup.mk' nativeInn)) = 3 := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  rw [← nativeDiag_map_mk_eq_zpowers_levi P Q3, Nat.card_zpowers, native_pi_levi_order P Q3]

private noncomputable def toDiagQuotient
    (_P : Sylow 2 (hopfMultiplier ↥stdGroup)) (_Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    nativeTwConj →* nativeDiag.map (QuotientGroup.mk' nativeInn) := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  refine
    { toFun := fun x =>
        ⟨(QuotientGroup.mk' nativeInn) (x : MulAut ↥stdGroup), ?_⟩
      map_one' := ?_
      map_mul' := ?_ }
  · have hx : (x : MulAut ↥stdGroup) ∈ nativeInn ⊔ nativeDiag := by
      rw [← nativeTwConj_eq_sup]
      exact x.2
    have hmap : (QuotientGroup.mk' nativeInn) (x : MulAut ↥stdGroup) ∈
        (nativeInn ⊔ nativeDiag).map (QuotientGroup.mk' nativeInn) :=
      Subgroup.mem_map_of_mem _ hx
    rwa [Subgroup.map_sup, nativeInn_map_mk_eq_bot, bot_sup_eq] at hmap
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp

private noncomputable def diagQuotientEquiv
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    Multiplicative (ZMod 3) ≃* nativeDiag.map (QuotientGroup.mk' nativeInn) := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  let g : nativeDiag.map (QuotientGroup.mk' nativeInn) :=
    ⟨(QuotientGroup.mk' nativeInn) levi34Diag,
      Subgroup.mem_map_of_mem _ ⟨levi34Unit, rfl⟩⟩
  have hgen : ∀ x : nativeDiag.map (QuotientGroup.mk' nativeInn),
      x ∈ Subgroup.zpowers g := by
    intro x
    have hx : (x : MulAut ↥stdGroup ⧸ nativeInn) ∈
        Subgroup.zpowers ((QuotientGroup.mk' nativeInn) levi34Diag) := by
      rw [nativeDiag_map_mk_eq_zpowers_levi P Q3]
      exact x.2
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, Subtype.ext hm⟩
  exact zmodMulEquivOfGenerator (g := g) hgen (nativeDiag_map_mk_card P Q3)

noncomputable def outerCharacter
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    nativeTwConj →* Multiplicative (ZMod 3) :=
  (diagQuotientEquiv P Q3).symm.toMonoidHom.comp (toDiagQuotient P Q3)

theorem outerCharacter_eq_one_iff
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    (x : nativeTwConj) :
    outerCharacter P Q3 x = 1 ↔ (x : MulAut ↥stdGroup) ∈ nativeInn := by
  letI : nativeInn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal ↥stdGroup
  constructor
  · intro h
    have hf : toDiagQuotient P Q3 x = 1 := by
      apply (diagQuotientEquiv P Q3).symm.injective
      simpa [outerCharacter] using h
    have hq : (QuotientGroup.mk' nativeInn) (x : MulAut ↥stdGroup) = 1 := by
      have := congrArg Subtype.val hf
      simpa [toDiagQuotient] using this
    exact (QuotientGroup.eq_one_iff (N := nativeInn) (x : MulAut ↥stdGroup)).1 hq
  · intro hx
    have hq : (QuotientGroup.mk' nativeInn) (x : MulAut ↥stdGroup) = 1 :=
      (QuotientGroup.eq_one_iff (N := nativeInn) (x : MulAut ↥stdGroup)).2 hx
    have hf : toDiagQuotient P Q3 x = 1 := by
      apply Subtype.ext
      simpa [toDiagQuotient] using hq
    simp [outerCharacter, hf]

theorem outerCharacter_ne_one_iff
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    (x : nativeTwConj) :
    outerCharacter P Q3 x ≠ 1 ↔ (x : MulAut ↥stdGroup) ∉ nativeInn := by
  rw [ne_eq, outerCharacter_eq_one_iff]

theorem outerCharacter_eq_one_of_mem_inner
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    (x : nativeTwConj) (hx : (x : MulAut ↥stdGroup) ∈ nativeInn) :
    outerCharacter P Q3 x = 1 :=
  (outerCharacter_eq_one_iff P Q3 x).2 hx

theorem congr_mem_inner_iff
    {L : Type} [Field L] (σ : L ≃+* L)
    (eC : twistedE6RootGroup L σ ≃* stdGroup)
    (φ : MulAut (twistedE6RootGroup L σ)) :
    MulAut.congr eC φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥stdGroup ↔
      φ ∈ twistedE6Inn L σ := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨eC.symm g, ?_⟩
    have hconj : MulAut.congr eC.symm (MulAut.conj g) = MulAut.conj (eC.symm g) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eC.symm g
    have hφconj : φ = MulAut.conj (eC.symm g) := by
      calc φ = MulAut.congr eC.symm (MulAut.congr eC φ) := by
            ext x
            simp [MulAut.congr_apply, MulEquiv.trans_apply]
        _ = MulAut.congr eC.symm (MulAut.conj g) := by rw [hg]
        _ = MulAut.conj (eC.symm g) := hconj
    exact hφconj.symm
  · rintro ⟨g, hg⟩
    refine ⟨eC g, ?_⟩
    have hconj : MulAut.congr eC (MulAut.conj g) = MulAut.conj (eC g) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj eC g
    have hφconj : MulAut.congr eC φ = MulAut.conj (eC g) := by
      calc MulAut.congr eC φ = MulAut.congr eC (MulAut.conj g) := by rw [hg]
        _ = MulAut.conj (eC g) := hconj
    exact hφconj.symm

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem ggRootPair_exists_nonzero_outer_actor_in_common_hyperplanes
    {t : CFSG.Open.StatedLieTag} {n f p : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n 2 f)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h3 : 3 ≤ (ggU t n f).D.rank) (hp : p.Prime) (hp2 : p ≠ 2)
    {A T : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup T] [Module (ZMod p) T]
    (φ : A →ₗ[ZMod p] T) (χ : A →ₗ[ZMod p] ZMod p)
    (root : Fin (ggU t n f).D.rank → T →ₗ[ZMod p] ZMod p)
    (coroot : Fin (ggU t n f).D.rank → A)
    (hpair : ∀ i j, root j (φ (coroot i)) = ((ggU t n f).D.cartan i j : ZMod p))
    (hinner : ∀ i, χ (coroot i) = 0)
    {α β : Fin (ggU t n f).D.rank → ℤ}
    (hα : α ∈ (ggU t n f).D.roots) (hβ : β ∈ (ggU t n f).D.roots)
    (hβne : β ≠ α) (hβne' : β ≠ -α)
    {G : Type} [Group G] (η : Multiplicative A →* G) (Hr Hs : Subgroup G)
    (hHr : ∀ a : A, η (Multiplicative.ofAdd a) ∈ Hr ↔
      (∑ j, (α j : ZMod p) • root j) (φ a) = 0)
    (hHs : ∀ a : A, η (Multiplicative.ofAdd a) ∈ Hs ↔
      (∑ j, (β j : ZMod p) • root j) (φ a) = 0)
    (hex : ∃ a : A, χ a ≠ 0) :
    ∃ a : A, η (Multiplicative.ofAdd a) ∈ Hr ⊓ Hs ∧ χ a ≠ 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨a, ha⟩ := hex
  obtain ⟨c, _, hc, hc', hcχ⟩ := ggRootPair_outer_actor_correction
    hadm ht h3 hp hp2 φ χ root coroot hpair hinner hα hβ hβne hβne' a
  refine ⟨a + c, ⟨(hHr _).mpr hc, (hHs _).mpr hc'⟩, ?_⟩
  rw [hcχ]
  exact ha

end CFSG.StandardType

end
