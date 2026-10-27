module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankAut

public section

namespace CFSG.AGLEmbedding.OutFive

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OutPlaneSeries (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∃ N : Subgroup (MulAut X), N.Normal ∧
    (∀ R : Subgroup (MulAut X), R ≤ N → CFSG.IsElementaryAbelian p R → Nat.card R = p ^ 2 →
      R ⊓ Inn X = ⊥ → False) ∧
    ∀ R : Subgroup (MulAut X), CFSG.IsElementaryAbelian p R → Nat.card R = p ^ 2 →
      R ⊓ N = ⊥ → False

theorem false_of_injective_to_cyclic {p : ℕ} (hp : p.Prime) {R C : Type*} [Group R] [Finite R]
    [CFSG.IsElementaryAbelian p R] (hcard : Nat.card R = p ^ 2) [Group C] [IsCyclic C]
    (f : R →* C) (hf : Function.Injective f) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic R := (MonoidHom.ofInjective hf).isCyclic.mpr inferInstance
  exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard hcyc

theorem false_of_plane_meets_kernel_trivially {p : ℕ} (hp : p.Prime) {H C : Type*} [Group H]
    [Group C] [IsCyclic C] (f : H →* C) {R : Subgroup H} (hR : CFSG.IsElementaryAbelian p R)
    (hcard : Nat.card R = p ^ 2) (hRk : R ⊓ f.ker = ⊥) : False := by
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  refine false_of_injective_to_cyclic hp hcard (f.comp R.subtype) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx1 : (x : H) ∈ R ⊓ f.ker := ⟨x.2, hx⟩
  rw [hRk, Subgroup.mem_bot] at hx1
  exact Subgroup.mem_bot.mpr (Subtype.ext hx1)

theorem false_of_plane_in_cyclic_quotient {p : ℕ} (hp : p.Prime) {H : Type*} [Group H]
    {U T R : Subgroup H} [(T.subgroupOf U).Normal] [IsCyclic (↥U ⧸ T.subgroupOf U)]
    (hRU : R ≤ U) (hR : CFSG.IsElementaryAbelian p R) (hcard : Nat.card R = p ^ 2)
    (hRT : R ⊓ T = ⊥) : False := by
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  refine false_of_injective_to_cyclic hp hcard
    ((QuotientGroup.mk' (T.subgroupOf U)).comp (Subgroup.inclusion hRU)) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hxT : (x : H) ∈ T := by
    have := (QuotientGroup.eq_one_iff _).mp hx
    exact Subgroup.mem_subgroupOf.mp this
  have hx1 : (x : H) ∈ R ⊓ T := ⟨x.2, hxT⟩
  rw [hRT, Subgroup.mem_bot] at hx1
  exact Subgroup.mem_bot.mpr (Subtype.ext hx1)

theorem isCyclic_quotient_of_forall {Γ : Type*} [Group Γ] (D : Subgroup Γ) [D.Normal] (g : Γ)
    (h : ∀ α : Γ, ∃ k : ℤ, g ^ k * α ∈ D) : IsCyclic (Γ ⧸ D) := by
  refine ⟨⟨QuotientGroup.mk g, fun y => ?_⟩⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := h α
  refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
  have h1 : (QuotientGroup.mk (g ^ k * α) : Γ ⧸ D) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
  rw [zpow_neg]
  exact inv_eq_of_mul_eq_one_right h1

theorem OutPlaneSeries.of_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    (h : OutPlaneSeries p Y) : OutPlaneSeries p X := by
  obtain ⟨N, hN, h1, h2⟩ := h
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  have hinner : (Inn X).map φ.toMonoidHom = Inn Y := inner_map_congr e
  have hmem : ∀ α : MulAut X, α ∈ Inn X ↔ φ α ∈ Inn Y := by
    intro α
    rw [← hinner]
    constructor
    · exact fun h => ⟨α, h, rfl⟩
    · rintro ⟨β, hβ, hβα⟩
      have : β = α := φ.injective hβα
      exact this ▸ hβ
  have hcard : ∀ R : Subgroup (MulAut X), Nat.card (R.map φ.toMonoidHom) = Nat.card R :=
    fun R => Subgroup.card_map_of_injective φ.injective
  have hel : ∀ R : Subgroup (MulAut X), CFSG.IsElementaryAbelian p R →
      CFSG.IsElementaryAbelian p (R.map φ.toMonoidHom) := fun R hR => by
    have := hR
    have h3 := CFSG.RankThree.PartOne.isElementaryAbelian_range_of_hom (p := p)
      (φ.toMonoidHom.comp R.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h3
  refine ⟨N.comap φ.toMonoidHom, inferInstance, ?_, ?_⟩
  · intro R hRN hR hc hRI
    refine h1 (R.map φ.toMonoidHom) ?_ (hel R hR) (by rw [hcard, hc]) ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hRN hr
    · rw [eq_bot_iff]
      rintro _ ⟨⟨r, hr, rfl⟩, hI⟩
      have hr1 : r ∈ R ⊓ Inn X := ⟨hr, (hmem r).mpr hI⟩
      rw [hRI, Subgroup.mem_bot] at hr1
      rw [hr1, map_one]
      exact Subgroup.one_mem _
  · intro R hR hc hRN
    refine h2 (R.map φ.toMonoidHom) (hel R hR) (by rw [hcard, hc]) ?_
    rw [eq_bot_iff]
    rintro _ ⟨⟨r, hr, rfl⟩, hI⟩
    have hr1 : r ∈ R ⊓ N.comap φ.toMonoidHom := ⟨hr, hI⟩
    rw [hRN, Subgroup.mem_bot] at hr1
    rw [hr1, map_one]
    exact Subgroup.one_mem _

theorem outPlaneSeries_of_outer_small {X : Type*} [Group X] [Finite X] {p : ℕ} (hp5 : 5 ≤ p)
    (h : Nat.card (Outer X) < 25 ∨ ¬ p ∣ Nat.card (Outer X)) : OutPlaneSeries p X := by
  refine ⟨Inn X, inner_normal X, ?_, ?_⟩
  · intro R hRN _ hcard hRI
    have hR : R = ⊥ := by
      rw [eq_bot_iff, ← hRI]
      exact le_inf le_rfl hRN
    rw [hR, Subgroup.card_bot] at hcard
    nlinarith
  · intro R _ hcard hRI
    let f : R →* Outer X := (QuotientGroup.mk' (inner X)).comp R.subtype
    have hker : f.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (x : MulAut X) ∈ inner X := (QuotientGroup.eq_one_iff _).mp hx
      have h2 : (x : MulAut X) ∈ R ⊓ Inn X := ⟨x.2, h1⟩
      rw [hRI] at h2
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h2))
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    have hdvd : Nat.card R ∣ Nat.card (Outer X) := by
      have h1 : Nat.card R = Nat.card f.range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      rw [h1]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hcard] at hdvd
    rcases h with hlt | hnd
    · have := Nat.le_of_dvd Nat.card_pos hdvd
      nlinarith
    · exact hnd ((dvd_pow_self p two_ne_zero).trans hdvd)

theorem false_of_outPlaneSeries {Y : Type} [Group Y] {p : ℕ} {L E Q : Subgroup Y}
    [Group.IsPerfect L] (hS : OutPlaneSeries p (L ⧸ Subgroup.center L))
    (hEN : E ≤ Subgroup.normalizer (L : Set Y)) (hE : CFSG.Open.IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) (hdisj : E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥)
    (hQL : Q ≤ Subgroup.normalizer (L : Set Y)) (hQE : Q ≤ Subgroup.normalizer (E : Set Y))
    (hirr : ∀ F : Subgroup Y, F ≤ E → Q ≤ Subgroup.normalizer (F : Set Y) → F = ⊥ ∨ F = E) :
    False := by
  obtain ⟨N, hN, h3a, h3b⟩ := hS
  have hEel := CFSG.AGLEmbedding.OutElemRank.isElementaryAbelian_of_open hE
  obtain ⟨α, hα⟩ : ∃ α : E →* MulAut (L ⧸ Subgroup.center L),
      α = (actionOnQuot L).comp (Subgroup.inclusion hEN) := ⟨_, rfl⟩
  have hαe : ∀ e : E, α e = actionOnQuot L ⟨e, hEN e.2⟩ := fun e => by rw [hα]; rfl
  have hαinn : ∀ e : E, α e ∈ Inn (L ⧸ Subgroup.center L) → e = 1 := by
    intro e he
    rw [hαe] at he
    have h1 : (e : Y) ∈ L ⊔ Subgroup.centralizer (L : Set Y) :=
      (actionOnQuot_mem_inner_iff L (hEN e.2)).mp he
    have h2 : (e : Y) ∈ E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) := ⟨e.2, h1⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    exact hαinn e (by rw [MonoidHom.mem_ker.mp he]; exact Subgroup.one_mem _)
  have hRcard : Nat.card α.range = p ^ 2 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hRel : CFSG.IsElementaryAbelian p α.range :=
    CFSG.RankThree.PartOne.isElementaryAbelian_range_of_hom α
  have hRinn : α.range ⊓ Inn (L ⧸ Subgroup.center L) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨e, he⟩, hI⟩
    rw [← he] at hI ⊢
    rw [hαinn e hI, map_one]
    exact Subgroup.one_mem _
  obtain ⟨F, hF⟩ : ∃ F : Subgroup Y, F = (N.comap α).map E.subtype := ⟨_, rfl⟩
  have hFE : F ≤ E := by
    rw [hF]
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hmemF : ∀ e : E, (e : Y) ∈ F ↔ α e ∈ N := by
    intro e
    rw [hF]
    constructor
    · rintro ⟨e', he', he'e⟩
      have : e' = e := Subtype.ext he'e
      exact this ▸ he'
    · intro h
      exact ⟨e, h, rfl⟩
  have hconj : ∀ q ∈ Q, ∀ f ∈ F, q * f * q⁻¹ ∈ F := by
    intro q hq f hf
    have hfE : f ∈ E := hFE hf
    have hqfE : q * f * q⁻¹ ∈ E := ((Subgroup.mem_normalizer_iff.mp (hQE hq)) f).mp hfE
    have hfN : α ⟨f, hfE⟩ ∈ N := (hmemF ⟨f, hfE⟩).mp hf
    have key : α ⟨q * f * q⁻¹, hqfE⟩ = actionOnQuot L ⟨q, hQL hq⟩ * α ⟨f, hfE⟩ *
        (actionOnQuot L ⟨q, hQL hq⟩)⁻¹ := by
      have h1 : (⟨q * f * q⁻¹, hEN hqfE⟩ : Subgroup.normalizer (L : Set Y)) =
          ⟨q, hQL hq⟩ * ⟨f, hEN hfE⟩ * ⟨q, hQL hq⟩⁻¹ := rfl
      rw [hαe, hαe, h1, map_mul, map_mul, map_inv]
    exact (hmemF ⟨_, hqfE⟩).mpr (key ▸ hN.conj_mem _ hfN _)
  have hQF : Q ≤ Subgroup.normalizer (F : Set Y) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · exact fun hf => hconj q hq f hf
    · intro hf
      have := hconj q⁻¹ (Q.inv_mem hq) _ hf
      simpa [mul_assoc] using this
  rcases hirr F hFE hQF with hFbot | hFtop
  · refine h3b α.range hRel hRcard ?_
    rw [eq_bot_iff]
    rintro x ⟨⟨e, he⟩, hNe⟩
    rw [← he] at hNe ⊢
    have hFe : (e : Y) ∈ F := (hmemF e).mpr hNe
    rw [hFbot, Subgroup.mem_bot] at hFe
    have he1 : e = 1 := Subtype.ext hFe
    rw [he1, map_one]
    exact Subgroup.one_mem _
  · refine h3a α.range ?_ hRel hRcard hRinn
    rintro x ⟨e, he⟩
    rw [← he]
    exact (hmemF e).mp (hFtop ▸ e.2)

end CFSG.AGLEmbedding.OutFive
