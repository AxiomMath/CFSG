module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverLie
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaPRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowFi24
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
public import CFSG.RankThree.ThinCatalog.MathieuThreeRank
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeCover

open CFSG.Blueprint CFSG.RankThree.PerfectCover

theorem false_of_not_dvd_multiplier {K X : Type} [Group K] [Finite K] [Group X]
    (hq : Open.IsQuasisimple K) (hZ : IsPGroup 3 (Subgroup.center K))
    (hZne : Subgroup.center K ≠ ⊥) (e : K ⧸ Subgroup.center K ≃* X)
    (h : ¬ 3 ∣ Nat.card (hopfMultiplier X)) : False :=
  h ((three_dvd_card_of_isPGroup hZ ((Subgroup.nontrivial_iff_ne_bot _).2 hZne)).trans
    (CFSG.GH74.Generic.card_center_dvd_hopfMultiplier (isQuasisimple_of_open hq) e))

theorem isCyclic_center_of_dvd {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    (hdvd : Nat.card (Subgroup.center K) ∣ 6) : IsCyclic (Subgroup.center K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hZne
  have hk6 : 3 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) (hk ▸ hdvd)
  have hk1 : k ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card).ne'
  have : k = 1 := by omega
  subst this
  exact isCyclic_of_prime_card (p := 3) (by rw [hk]; norm_num)

theorem false_J3
    {K L : Type} [Group K] [Finite K] [Group L]
    (hZ : IsPGroup 3 (Subgroup.center K)) (hL : IsCaseTwoGroup 3 L) (B : Subgroup K)
    (f : B →* L) (hf : Function.Surjective f)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) : False := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have hcard : Nat.card (TauCeti.CFSGIndex.sporadic .J3).Group = 50232960 := by
    rw [← Nat.card_congr b.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  have h7 := seven_dvd_card_quotient hZ B f hf (by rw [(l28_facts hL).1]; norm_num)
  rw [Nat.card_congr e.toEquiv, hcard] at h7
  omega

theorem false_ON
    {K L : Type} [Group K] [Finite K]
    [Group L] (hL : IsCaseTwoGroup 3 L) (B : Subgroup K) (f : B →* L)
    (hf : Function.Surjective f)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic .ONan).Group) := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have h1 : AbelianSylowDatum (NativeSporadic.Carrier .ONan) 3 := abelianSylowDatum_ON_three
  obtain ⟨D, -, -, -, hidx⟩ := AbelianSylowDatum.of_mulEquiv (b.trans e.symm) h1
  exact false_of_exponent_three hL (fun x hx => pow_eq_one_of_elemAbelian_index
    D.isElemAbelian_span hidx x hx) B f hf

theorem false_M22
    {K L : Type} [Group K] [Finite K] [Group L]
    (hL : IsCaseTwoGroup 3 L) (B : Subgroup K) (f : B →* L) (hf : Function.Surjective f)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : (K ⧸ Subgroup.center K) ≃* NativeSporadic.M22 := e.trans b.symm
  have hcard : Nat.card (K ⧸ Subgroup.center K) = 443520 := by
    rw [Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have h2 := CFSG.RankThree.ThinCatalog.two_le_pRank_three_M22_sylow b'
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (⊤ : Subgroup (K ⧸ Subgroup.center K))
  have hdvd : 3 ^ Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ∣ 443520 := by
    rw [← hEc, ← hcard]
    exact Subgroup.card_subgroup_dvd_card E
  have hr : Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) = 2 := by
    by_contra hne
    have h3 : 3 ^ 3 ∣ 3 ^ Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
      Nat.pow_dvd_pow 3 (by omega)
    have := h3.trans hdvd
    norm_num at this
  have hmul := Subgroup.card_mul_index E
  rw [hEc, hr, hcard] at hmul
  have hidx : ¬ 3 ∣ E.index := by
    have : E.index = 49280 := by omega
    rw [this]
    norm_num
  exact false_of_exponent_three hL (fun x hx => pow_eq_one_of_elemAbelian_index hE hidx x hx)
    B f hf

theorem false_of_moduleDatum {K X : Type} [Group K] [Finite K] [Group X]
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    (hZc : IsCyclic (Subgroup.center K)) (hrk : Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (e : K ⧸ Subgroup.center K ≃* X) (hD : ModuleDatum X 3) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set π : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp [π]
  obtain ⟨T⟩ : Nonempty (Sylow 3 K) := inferInstance
  obtain ⟨A, -, -, hA, hcard⟩ := coverModuleLemma K X π hπ hker 3 hp (by norm_num) hZne hZ hZc
    hD T
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have h4 : 4 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hA hk
  omega

theorem false_McL
    {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    (hZc : IsCyclic (Subgroup.center K)) (hrk : Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) : False := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have : IsSimpleGroup TauCeti.SporadicName.McL.Group := e.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL
  have h1 : ModuleDatum (NativeSporadic.Carrier .McL) 3 := moduleDatum_McL_three
  exact false_of_moduleDatum hZ hZne hZc hrk (e.trans b) h1

theorem false_Suz
    {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    (hZc : IsCyclic (Subgroup.center K)) (hrk : Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) : False := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Suz ≃*
      (TauCeti.CFSGIndex.sporadic .Suz).Group) := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have h1 : ModuleDatum (NativeSporadic.Carrier .Suz) 3 := moduleDatum_Suz_three
  exact false_of_moduleDatum hZ hZne hZc hrk (e.trans b.symm) h1

theorem false_Fi22
    {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    (hZc : IsCyclic (Subgroup.center K)) (hrk : Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) : False := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi22).Group) := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have h1 : ModuleDatum (NativeSporadic.Carrier .Fi22) 3 := moduleDatum_Fi22_three
  exact false_of_moduleDatum hZ hZne hZc hrk (e.trans b.symm) h1

theorem false_Fi24
    {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 3 (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    (hZc : IsCyclic (Subgroup.center K)) (hrk : Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) : False := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Fi24Prime ≃*
      (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have h1 : ModuleDatum (NativeSporadic.Carrier .Fi24Prime) 3 := moduleDatum_Fi24_three
  exact false_of_moduleDatum hZ hZne hZc hrk (e.trans b.symm) h1

end CFSG.AGLEmbedding.KFactProofs.ThreeCover
