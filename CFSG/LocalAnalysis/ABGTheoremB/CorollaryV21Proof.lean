module

public import CFSG.LocalAnalysis.ABGTheoremB.V3Defs
public import CFSG.LocalAnalysis.ABGTheoremB.IV4
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

universe u

section General

variable {G : Type u} [Group G]

private theorem eq_one_of_mem_of_pow_two_pow {O : Subgroup G} (hO : Odd (Nat.card O)) {g : G}
    (hg : g ∈ O) {k : ℕ} (hk : g ^ (2 ^ k) = 1) : g = 1 := by
  have hodd : Odd (orderOf g) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hg)
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  exact orderOf_eq_one_iff.mp (((Nat.coprime_two_right.mpr hodd).pow_right k).eq_one_of_dvd h2)

private theorem commutator_mem_centralizer_of_inverts {R : Subgroup G} {a k : G}
    (ha : ∀ y ∈ R, a * y * a⁻¹ = y⁻¹) (hk : k ∈ Subgroup.normalizer (R : Set G)) :
    k * a * k⁻¹ * a⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hs : k⁻¹ * r * k ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) r).mp hr
    simpa using this
  have h1 : a⁻¹ * r = r⁻¹ * a⁻¹ := by
    have e := ha r⁻¹ (R.inv_mem hr)
    rw [inv_inv] at e
    calc a⁻¹ * r = a⁻¹ * (a * r⁻¹ * a⁻¹) := by rw [e]
      _ = r⁻¹ * a⁻¹ := by group
  have h2 : a * (k⁻¹ * r * k)⁻¹ = (k⁻¹ * r * k) * a := by
    have e := ha (k⁻¹ * r * k)⁻¹ (R.inv_mem hs)
    rw [inv_inv] at e
    calc a * (k⁻¹ * r * k)⁻¹ = a * (k⁻¹ * r * k)⁻¹ * a⁻¹ * a := by group
      _ = (k⁻¹ * r * k) * a := by rw [e]
  symm
  calc k * a * k⁻¹ * a⁻¹ * r = k * a * k⁻¹ * (a⁻¹ * r) := by group
    _ = k * a * k⁻¹ * (r⁻¹ * a⁻¹) := by rw [h1]
    _ = k * (a * (k⁻¹ * r * k)⁻¹) * k⁻¹ * a⁻¹ := by group
    _ = k * ((k⁻¹ * r * k) * a) * k⁻¹ * a⁻¹ := by rw [h2]
    _ = r * (k * a * k⁻¹ * a⁻¹) := by group

private theorem normalizer_le_normalizer_centralizer (O : Subgroup G) :
    Subgroup.normalizer (O : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (O : Set G) : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer (O : Set G))

private theorem commutator_mem_centralizer {U : Subgroup G} {a k : G}
    (ha : U ≤ Subgroup.centralizer ({a} : Set G) ∨ ∀ y ∈ U, a * y * a⁻¹ = y⁻¹)
    (hk : k ∈ Subgroup.normalizer (U : Set G)) :
    k * a * k⁻¹ * a⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  rcases ha with hcen | hinv
  · have haC : a ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcen hy)
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ haC)
    exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer U hk) a).mp haC
  · exact commutator_mem_centralizer_of_inverts hinv hk

private theorem le_centralizer_of_pCore_eq_bot [Finite G] {K : Subgroup G}
    (hK : Odd (Nat.card K)) {p : ℕ} [Fact p.Prime] (hKp : CFSG.pCore p K = ⊥) {a : G}
    (hq : ∀ q : ℕ, q.Prime → q ≠ p →
      (CFSG.pCore q K).map K.subtype ≤ Subgroup.centralizer ({a} : Set G) ∨
        ∀ y ∈ (CFSG.pCore q K).map K.subtype, a * y * a⁻¹ = y⁻¹)
    {X : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup p X)
    (haX : a ∈ Subgroup.normalizer (X : Set G)) :
    X ≤ Subgroup.centralizer ({a} : Set G) := by
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard K hK
  intro u hu
  set c := u * a * u⁻¹ * a⁻¹ with hc
  have hcX : c ∈ X := by
    have h1 : a * u⁻¹ * a⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp haX u⁻¹).mp (X.inv_mem hu)
    have : c = u * (a * u⁻¹ * a⁻¹) := by rw [hc]; group
    rw [this]
    exact X.mul_mem hu h1
  have hcK : c ∈ K := hXK hcX
  have hcent : ∀ q : (Nat.card K).primeFactors.attach,
      Subgroup.zpowers (⟨c, hcK⟩ : K) ≤
        Subgroup.centralizer (CFSG.pCore q.1.1 K : Set K) := by
    intro q
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    by_cases hqp : q.1.1 = p
    · have hqp' : CFSG.pCore q.1.1 K = ⊥ := by rw [hqp]; exact hKp
      rw [hqp', Subgroup.coe_bot, Set.mem_singleton_iff] at hw
      rw [hw, one_mul, mul_one]
    · have hU := hq q.1.1 (Nat.prime_of_mem_primeFactors q.1.2) hqp
      have huN : u ∈ Subgroup.normalizer
          (((CFSG.pCore q.1.1 K).map K.subtype : Subgroup G) : Set G) :=
        le_normalizer_map_subtype K (CFSG.pCore q.1.1 K) (hXK hu)
      have h := commutator_mem_centralizer hU huN
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp h (w : G) ⟨w, hw, rfl⟩
  have hcF : (⟨c, hcK⟩ : K) ∈ CFSG.fittingSubgroup K :=
    CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
      (CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores hcent
        (Subgroup.mem_zpowers _))
  have hFp : CFSG.fittingSubgroup K ≤ CFSG.pPrimeCore p K := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    by_cases hqp : q.1.1 = p
    · rw [hqp, hKp]
      exact bot_le
    · have hq' : (q.1.1).Prime := Nat.prime_of_mem_primeFactors q.1.2
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := K) (p := q.1.1)).exists_card_eq
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes (Fact.out) hq').mpr (Ne.symm hqp))
  have hcP := hFp hcF
  have hcop := CFSG.pPrimeCore_coprime_card (p := p) (G := K)
  have hord : orderOf (⟨c, hcK⟩ : K) ∣ Nat.card (CFSG.pPrimeCore p K) := by
    have := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore p K) hcP
    exact this
  obtain ⟨k, hk⟩ := hX ⟨c, hcX⟩
  have hck : c ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hord' : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one hck
  have hordK : orderOf (⟨c, hcK⟩ : K) = orderOf c := Subgroup.orderOf_mk c hcK
  have hc1 : orderOf c = 1 := by
    rw [← hordK] at hord'
    rw [← hordK]
    exact ((hcop.coprime_dvd_right hord).pow_left k).symm.eq_one_of_dvd hord'
  have hc1' : c = 1 := orderOf_eq_one_iff.mp hc1
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hc] at hc1'
  calc u * a = u * a * u⁻¹ * a⁻¹ * (a * u) := by group
    _ = a * u := by rw [hc1', one_mul]

private theorem conj_mul_comm_of_commute {a c y : G} (hc : a * c = c * a) (hy : y * a = a * y) :
    c * y * c⁻¹ * a = a * (c * y * c⁻¹) := by
  have hc' : c⁻¹ * a * c = a := by rw [mul_assoc, hc]; group
  calc c * y * c⁻¹ * a = c * y * (c⁻¹ * a * c) * c⁻¹ := by group
    _ = c * (y * a) * c⁻¹ := by rw [hc']; group
    _ = c * (a * y) * c⁻¹ := by rw [hy]
    _ = (c * a) * y * c⁻¹ := by group
    _ = (a * c) * y * c⁻¹ := by rw [hc]
    _ = a * (c * y * c⁻¹) := by group

private theorem conj_inv_of_commute {a c y : G} (hc : a * c = c * a) (hy : a * y * a⁻¹ = y⁻¹) :
    a * (c * y * c⁻¹) * a⁻¹ = (c * y * c⁻¹)⁻¹ := by
  calc a * (c * y * c⁻¹) * a⁻¹ = (a * c) * y * (a * c)⁻¹ := by group
    _ = (c * a) * y * (c * a)⁻¹ := by rw [hc]
    _ = c * (a * y * a⁻¹) * c⁻¹ := by group
    _ = (c * y * c⁻¹)⁻¹ := by rw [hy]; group

private theorem exists_mem_inf_mul_of_le_sup {L O K : Subgroup G} (hOL : O ≤ L)
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (h : L ≤ K ⊔ O) {l : G} (hl : l ∈ L) :
    ∃ k ∈ K ⊓ L, ∃ a ∈ O, l = k * a := by
  have hl' : l ∈ ((K ⊔ O : Subgroup G) : Set G) := h hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K O hKO] at hl'
  obtain ⟨k, hk, a, ha, rfl⟩ := hl'
  refine ⟨k, ⟨hk, ?_⟩, a, ha, rfl⟩
  have : k = k * a * a⁻¹ := by group
  rw [this]
  exact L.mul_mem hl (L.inv_mem (hOL ha))

end General

section Quotient

variable {G : Type u} [Group G] {N : Subgroup G} {M₀ : Subgroup N} [M₀.Normal]

private theorem mk'_mem_map_iff {X : Subgroup G} (hX : X ≤ N) (n : N) :
    QuotientGroup.mk' M₀ n ∈ (X.subgroupOf N).map (QuotientGroup.mk' M₀) ↔
      (n : G) ∈ X ⊔ M₀.map N.subtype := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    ← Subgroup.mem_map_iff_mem N.subtype_injective, Subgroup.map_sup,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX]
  rfl

private theorem mk'_eq_one_iff (n : N) :
    QuotientGroup.mk' M₀ n = 1 ↔ (n : G) ∈ M₀.map N.subtype := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    ← Subgroup.mem_map_iff_mem N.subtype_injective]
  rfl

private theorem mem_pb_iff (K : Subgroup (N ⧸ M₀)) (n : N) :
    (n : G) ∈ (K.comap (QuotientGroup.mk' M₀)).map N.subtype ↔ QuotientGroup.mk' M₀ n ∈ K := by
  rw [show (n : G) = N.subtype n from rfl, Subgroup.mem_map_iff_mem N.subtype_injective,
    Subgroup.mem_comap]

private theorem pb_le (K : Subgroup (N ⧸ M₀)) :
    (K.comap (QuotientGroup.mk' M₀)).map N.subtype ≤ N :=
  Subgroup.map_subtype_le _

private theorem le_pb (K : Subgroup (N ⧸ M₀)) :
    M₀.map N.subtype ≤ (K.comap (QuotientGroup.mk' M₀)).map N.subtype := by
  apply Subgroup.map_mono
  intro m hm
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).mpr hm]
  exact K.one_mem

private theorem map_pb (K : Subgroup (N ⧸ M₀)) :
    (((K.comap (QuotientGroup.mk' M₀)).map N.subtype).subgroupOf N).map
      (QuotientGroup.mk' M₀) = K := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M₀)]

private theorem map_subgroupOf_sup {X Y : Subgroup G} (hX : X ≤ N) (hY : Y ≤ N) :
    ((X ⊔ Y).subgroupOf N).map (QuotientGroup.mk' M₀) =
      (X.subgroupOf N).map (QuotientGroup.mk' M₀) ⊔ (Y.subgroupOf N).map (QuotientGroup.mk' M₀) :=
  by rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

private theorem map_normal {X : Subgroup G} (hX : X ≤ N)
    (hNX : N ≤ Subgroup.normalizer (X : Set G)) :
    ((X.subgroupOf N).map (QuotientGroup.mk' M₀)).Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hX).mpr hNX).map _
    (QuotientGroup.mk'_surjective M₀)

private theorem le_normalizer_pb {K : Subgroup (N ⧸ M₀)} (hK : K.Normal) :
    N ≤ Subgroup.normalizer
      (((K.comap (QuotientGroup.mk' M₀)).map N.subtype : Subgroup G) : Set G) :=
  have := hK.comap (QuotientGroup.mk' M₀)
  le_normalizer_map_subtype N _

private theorem mk'_mem_normalizer_map {X : Subgroup G} (hX : X ≤ N) {n : N}
    (hn : (n : G) ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' M₀ n ∈
      Subgroup.normalizer (((X.subgroupOf N).map (QuotientGroup.mk' M₀) : Subgroup _) : Set _) := by
  have hnM : (n : G) ∈ Subgroup.normalizer ((M₀.map N.subtype : Subgroup G) : Set G) :=
    le_normalizer_map_subtype N M₀ n.2
  have hnXM : (n : G) ∈ Subgroup.normalizer ((X ⊔ M₀.map N.subtype : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hn, hnM⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective M₀ z
  rw [← map_inv, ← map_mul, ← map_mul, mk'_mem_map_iff hX, mk'_mem_map_iff hX]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp hnXM m

private theorem mem_normalizer_pb {K : Subgroup (N ⧸ M₀)} {n : N}
    (hn : QuotientGroup.mk' M₀ n ∈ Subgroup.normalizer (K : Set (N ⧸ M₀))) :
    (n : G) ∈ Subgroup.normalizer
      (((K.comap (QuotientGroup.mk' M₀)).map N.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨n * m * n⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hm
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp hm
  · rintro ⟨m, hm, hmg⟩
    have hg : g = ((n⁻¹ * m * n : N) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (m : G) = N.subtype m from rfl, hmg]
      group
    rw [hg]
    refine ⟨n⁻¹ * m * n, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hm ⊢
    rw [map_mul, map_mul, map_inv]
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) _).mp hm
    simpa [mul_assoc] using h

private theorem isSylowOf_map_hom [Finite G] {G' : Type*} [Group G'] {r : ℕ} [Fact r.Prime]
    {R K : Subgroup G} (φ : G →* G') (h : IsSylowOf r R K) : IsSylowOf r (R.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem isSylowOf_map_subgroupOf [Finite G] {r : ℕ} [Fact r.Prime] {R K : Subgroup G}
    (hKN : K ≤ N) (h : IsSylowOf r R K) :
    IsSylowOf r ((R.subgroupOf N).map (QuotientGroup.mk' M₀))
      ((K.subgroupOf N).map (QuotientGroup.mk' M₀)) := by
  apply isSylowOf_map_hom
  rw [← isSylowOf_map_subtype_iff, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (h.le.trans hKN), inf_eq_left.mpr hKN]
  exact h

private theorem card_map_subgroupOf_dvd {X : Subgroup G} (hX : X ≤ N) :
    Nat.card ((X.subgroupOf N).map (QuotientGroup.mk' M₀)) ∣ Nat.card X := by
  refine (Subgroup.card_map_dvd (X.subgroupOf N) (QuotientGroup.mk' M₀)).trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

end Quotient

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private abbrev Nb : Type u := σ.N ⧸ CFSG.pCore σ.p σ.N

private abbrev πN : σ.N →* σ.Nb := QuotientGroup.mk' (CFSG.pCore σ.p σ.N)

private abbrev bar (X : Subgroup G) : Subgroup σ.Nb := (X.subgroupOf σ.N).map σ.πN

private abbrev pb (K : Subgroup σ.Nb) : Subgroup G := (K.comap σ.πN).map σ.N.subtype

private abbrev Sb (hσ : σ.IsValid) : Sylow 2 σ.Nb :=
  (σ.S.subtype (σ.S_le_N hσ)).mapSurjective (QuotientGroup.mk'_surjective _)

private theorem coe_Sb (hσ : σ.IsValid) : ((σ.Sb hσ : Sylow 2 σ.Nb) : Subgroup σ.Nb) =
    σ.bar (σ.S : Subgroup G) := rfl

private theorem odd_p' (hσ : σ.IsValid) : Odd σ.p :=
  hσ.p_prime.eq_two_or_odd'.resolve_left hσ.p_ne_two

private theorem odd_card_pCore (hσ : σ.IsValid) : Odd (Nat.card (CFSG.pCore σ.p σ.N)) := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := σ.p) (G := σ.N)).exists_card_eq
  rw [hk]
  exact (σ.odd_p' hσ).pow

private theorem odd_card_pCoreIn (hσ : σ.IsValid) : Odd (Nat.card (pCoreIn σ.p σ.N)) := by
  rw [pCoreIn, Subgroup.card_map_of_injective σ.N.subtype_injective]
  exact σ.odd_card_pCore hσ

private theorem pCoreIn_le_ON (hσ : σ.IsValid) : pCoreIn σ.p σ.N ≤ σ.ON :=
  Subgroup.map_mono (le_oddCore_of_normal CFSG.pCore_normal (σ.odd_card_pCore hσ))

omit [Finite G] in
private theorem pCoreIn_le_N : pCoreIn σ.p σ.N ≤ σ.N := Subgroup.map_subtype_le _

omit [Finite G] in
private theorem pCore_Nb_eq_bot : CFSG.pCore σ.p σ.Nb = ⊥ := pCore_quotient_pCore_eq_bot

omit [Finite G] in
private theorem mk'_mem_bar_iff {X : Subgroup G} (hX : X ≤ σ.N) (n : σ.N) :
    σ.πN n ∈ σ.bar X ↔ (n : G) ∈ X ⊔ pCoreIn σ.p σ.N :=
  mk'_mem_map_iff hX n

omit [Finite G] in
private theorem mk'_mem_bar_iff_of_le {X : Subgroup G} (hX : X ≤ σ.N)
    (hM : pCoreIn σ.p σ.N ≤ X) (n : σ.N) : σ.πN n ∈ σ.bar X ↔ (n : G) ∈ X := by
  rw [σ.mk'_mem_bar_iff hX, sup_eq_left.mpr hM]

omit [Finite G] in
private theorem mk'_mem_bar {X : Subgroup G} {n : σ.N} (hn : (n : G) ∈ X) : σ.πN n ∈ σ.bar X :=
  ⟨n, hn, rfl⟩

omit [Finite G] in
private theorem mk'_eq_one_iff' (n : σ.N) : σ.πN n = 1 ↔ (n : G) ∈ pCoreIn σ.p σ.N :=
  mk'_eq_one_iff n

omit [Finite G] in
private theorem mem_pb_iff' (K : Subgroup σ.Nb) (n : σ.N) : (n : G) ∈ σ.pb K ↔ σ.πN n ∈ K :=
  mem_pb_iff K n

private theorem eq_one_of_mem_S (hσ : σ.IsValid) {s : σ.N} (hs : (s : G) ∈ (σ.S : Subgroup G))
    (h1 : σ.πN s = 1) : s = 1 := by
  rw [σ.mk'_eq_one_iff'] at h1
  obtain ⟨k, hk⟩ := σ.S.isPGroup' ⟨s, hs⟩
  have hk' : (s : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact Subtype.ext (eq_one_of_mem_of_pow_two_pow (σ.odd_card_pCoreIn hσ) h1 hk')

private theorem mem_centerOf_of_mk' (hσ : σ.IsValid) {s : σ.N}
    (hs : (s : G) ∈ (σ.S : Subgroup G)) (h : σ.πN s ∈ centerOf (σ.bar (σ.S : Subgroup G))) :
    (s : G) ∈ centerOf (σ.S : Subgroup G) := by
  refine Subgroup.mem_inf.mpr ⟨hs, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htN : t ∈ σ.N := σ.S_le_N hσ ht
  have h1 : σ.πN ⟨t, htN⟩ * σ.πN s = σ.πN s * σ.πN ⟨t, htN⟩ :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 _ (σ.mk'_mem_bar ht)
  have h2 : σ.πN (⟨t, htN⟩ * s * (s * ⟨t, htN⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, h1, mul_inv_cancel]
  have hmem : ((⟨t, htN⟩ * s * (s * ⟨t, htN⟩)⁻¹ : σ.N) : G) ∈ (σ.S : Subgroup G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (σ.S : Subgroup G).mul_mem ((σ.S : Subgroup G).mul_mem ht hs)
      ((σ.S : Subgroup G).inv_mem ((σ.S : Subgroup G).mul_mem hs ht))
  have h3 := σ.eq_one_of_mem_S hσ hmem h2
  rw [mul_inv_eq_one] at h3
  exact congrArg Subtype.val h3

private theorem centerOf_bar_S (hσ : σ.IsValid) :
    centerOf (σ.bar (σ.S : Subgroup G)) = σ.bar (centerOf (σ.S : Subgroup G)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_inf.mp hz).1
    exact σ.mk'_mem_bar (σ.mem_centerOf_of_mk' hσ hs hz)
  · rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨σ.mk'_mem_bar hs.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs).2 _ ht)

omit [Finite G] in
private theorem bar_sup {X Y : Subgroup G} (hX : X ≤ σ.N) (hY : Y ≤ σ.N) :
    σ.bar (X ⊔ Y) = σ.bar X ⊔ σ.bar Y :=
  map_subgroupOf_sup hX hY

private theorem Z_le_N (hσ : σ.IsValid) : centerOf (σ.S : Subgroup G) ≤ σ.N :=
  inf_le_left.trans (σ.S_le_N hσ)

private theorem bar_solvRad (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    σ.bar (solvRadIn σ.N) = σ.bar σ.ON ⊔ centerOf ((σ.Sb hσ : Sylow 2 σ.Nb) : Subgroup σ.Nb) := by
  rw [σ.coe_Sb hσ, hII.N_solvRad, σ.bar_sup σ.ON_le_N (σ.Z_le_N hσ), σ.centerOf_bar_S hσ]

omit [Finite G] in
private theorem bar_pb (K : Subgroup σ.Nb) : σ.bar (σ.pb K) = K := map_pb K

omit [Finite G] in
private theorem bar_mono {X Y : Subgroup G} (h : X ≤ Y) : σ.bar X ≤ σ.bar Y := by
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, h hn, rfl⟩

private abbrev xb : σ.Nb := σ.πN ⟨σ.x, σ.x_mem_N⟩

private abbrev x₂b (hσ : σ.IsValid) : σ.Nb := σ.πN ⟨σ.x₂, σ.x₂_mem_N hσ⟩

private theorem exists_layerHyp (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = σ.q) {ψ₀ : σ.L₀ →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hψ₀ : Function.Surjective ψ₀) (hker : ψ₀.ker = σ.ON.subgroupOf σ.L₀) :
    ∃ ψ : σ.bar σ.L₀ →* Matrix.SpecialLinearGroup (Fin 2) F,
      LayerHyp ⊤ (σ.bar σ.ON) (σ.bar σ.L₀) (σ.Sb hσ) σ.xb (σ.x₂b hσ) ψ σ.p σ.f := by
  let ρ : σ.L₀ →* σ.bar σ.L₀ :=
    (σ.πN.comp (Subgroup.inclusion hσ.L₀_le_N)).codRestrict (σ.bar σ.L₀) fun l =>
      ⟨Subgroup.inclusion hσ.L₀_le_N l, l.2, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  have hρker : ρ.ker ≤ ψ₀.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : σ.πN (Subgroup.inclusion hσ.L₀_le_N l) = 1 := congrArg Subtype.val hl
    rw [σ.mk'_eq_one_iff'] at h1
    rw [hker, Subgroup.mem_subgroupOf]
    exact σ.pCoreIn_le_ON hσ h1
  let ψ := ρ.liftOfSurjective hρ ⟨ψ₀, hρker⟩
  have hψρ : ∀ l, ψ (ρ l) = ψ₀ l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ l
  have hONn : (σ.bar σ.ON).Normal := map_normal σ.ON_le_N σ.N_le_normalizer_ON
  have hL₀n : (σ.bar σ.L₀).Normal := map_normal hσ.L₀_le_N hσ.N_le_normalizer_L₀
  have hON_S : σ.ON ≤ solvRadIn σ.N := by rw [hII.N_solvRad]; exact le_sup_left
  refine ⟨ψ,
    { surj := ?_
      ker := ?_
      O_le_L := σ.bar_mono hσ.ON_le_L₀
      odd_O := σ.odd_card_ON.of_dvd_nat (card_map_subgroupOf_dvd σ.ON_le_N)
      O_le_N := le_top
      N_le_normalizer_O := (Subgroup.normalizer_eq_top_iff.mpr hONn).ge
      N_le_normalizer_L := (Subgroup.normalizer_eq_top_iff.mpr hL₀n).ge
      S_le_N := le_top
      p_prime := hσ.p_prime
      odd_p := σ.odd_p' hσ
      one_le_f := hσ.one_le_f
      card_F := hF
      five_le := hσ.five_lt_q.le
      x_central := ?_
      x_mem := σ.mk'_mem_bar (σ.x_mem_S hσ)
      x₂_mem := σ.mk'_mem_bar hσ.x₂_mem
      x₂_notMem_center := fun h => hσ.x_ne_x₂
        (hσ.center_involution σ.x₂ (σ.mem_centerOf_of_mk' hσ hσ.x₂_mem h) hσ.x₂_order).symm
      minimalNormal := ?_
      coverTransfer := ?_ }⟩
  · intro z
    obtain ⟨l, hl⟩ := hψ₀ z
    exact ⟨ρ l, by rw [hψρ, hl]⟩
  · ext w
    obtain ⟨l, rfl⟩ := hρ w
    rw [MonoidHom.mem_ker, hψρ, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    change _ ↔ σ.πN (Subgroup.inclusion hσ.L₀_le_N l) ∈ σ.bar σ.ON
    rw [σ.mk'_mem_bar_iff_of_le σ.ON_le_N (σ.pCoreIn_le_ON hσ)]
    rfl
  · intro z _
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((σ.mem_N_iff n).mp n.2)
  · intro K _ hNK hK
    have hKn : K.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hNK)
    have hK'N : σ.pb K ≤ σ.N := pb_le K
    have hK'S : ¬ σ.pb K ≤ solvRadIn σ.N := by
      intro hle
      apply hK
      have h1 := σ.bar_mono hle
      rwa [σ.bar_pb, σ.bar_solvRad hσ hII] at h1
    have h := hII.N_minimalNormal (σ.pb K) hK'N (le_normalizer_pb hKn) hK'S
    have h2 := σ.bar_mono h
    rwa [σ.bar_sup hK'N (solvRadIn_le σ.N), σ.bar_pb, σ.bar_solvRad hσ hII] at h2
  · intro K _ hLK
    have hK'N : σ.pb K ≤ σ.N := pb_le K
    have hL : σ.L₀ ≤ σ.pb K ⊔ solvRadIn σ.N := by
      intro l hl
      have hlN := hσ.L₀_le_N hl
      have h1 : σ.πN ⟨l, hlN⟩ ∈ σ.bar (σ.pb K ⊔ solvRadIn σ.N) := by
        rw [σ.bar_sup hK'N (solvRadIn_le σ.N), σ.bar_pb, σ.bar_solvRad hσ hII]
        exact hLK (σ.mk'_mem_bar hl)
      exact (σ.mk'_mem_bar_iff_of_le (sup_le hK'N (solvRadIn_le σ.N))
        (((σ.pCoreIn_le_ON hσ).trans hON_S).trans le_sup_right) _).mp h1
    have hcov := hII.N_coverTransfer (σ.pb K) hK'N hL
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨k, hk, o, ho, hko⟩ := hcov (show (n : G) ∈ σ.L₀ from hn)
    have hkN : k ∈ σ.N := hK'N hk
    have hoN : o ∈ σ.N := σ.ON_le_N ho
    have hko : k * o = (n : G) := hko
    refine ⟨σ.πN ⟨k, hkN⟩, (σ.mem_pb_iff' K ⟨k, hkN⟩).mp hk, σ.πN ⟨o, hoN⟩, σ.mk'_mem_bar ho, ?_⟩
    change σ.πN ⟨k, hkN⟩ * σ.πN ⟨o, hoN⟩ = σ.πN n
    rw [← map_mul]
    congr 1
    exact Subtype.ext hko

private theorem centralized_or_inverted_of_ne (hσ : σ.IsValid)
    (hV21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p) {r : ℕ} (hr : r.Prime) (hrp : r ≠ σ.p)
    (hdiv : r ∣ Nat.card σ.ON) : σ.Centralized r ∨ σ.Inverted r := by
  by_cases hti : σ.TotallyInverted r
  · exact Or.inr (σ.inverted_of_totallyInverted hσ hr hdiv hti)
  · by_cases hexc : σ.Exceptional r
    · exact absurd (hV21 r ⟨hr, hdiv, not_not.mp hti, hexc⟩) hrp
    · exact (not_not.mp hexc).2

omit [Finite G] in
private theorem barON_normal : (σ.bar σ.ON).Normal := map_normal σ.ON_le_N σ.N_le_normalizer_ON

private theorem odd_card_barON : Odd (Nat.card (σ.bar σ.ON)) :=
  σ.odd_card_ON.of_dvd_nat (card_map_subgroupOf_dvd σ.ON_le_N)

private theorem pCore_barON_eq_bot (hσ : σ.IsValid) : CFSG.pCore σ.p (σ.bar σ.ON) = ⊥ := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have := σ.barON_normal
  have h1 : ((CFSG.pCore σ.p (σ.bar σ.ON)).map (σ.bar σ.ON).subtype).Normal := inferInstance
  have h2 : IsPGroup σ.p ((CFSG.pCore σ.p (σ.bar σ.ON)).map (σ.bar σ.ON).subtype) :=
    CFSG.pCore_isPGroup.map _
  have h3 : (CFSG.pCore σ.p (σ.bar σ.ON)).map (σ.bar σ.ON).subtype ≤ CFSG.pCore σ.p σ.Nb :=
    le_sSup ⟨h1, h2⟩
  rw [σ.pCore_Nb_eq_bot, le_bot_iff] at h3
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h3

private theorem dichotomy_bar_of_dichotomy (hσ : σ.IsValid) {R : Subgroup G}
    (hRx₂ : R ≤ Subgroup.centralizer ({σ.x₂} : Set G) ∨ ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹) :
    σ.bar R ≤ Subgroup.centralizer ({σ.x₂b hσ} : Set σ.Nb) ∨
      ∀ y ∈ σ.bar R, σ.x₂b hσ * y * (σ.x₂b hσ)⁻¹ = y⁻¹ := by
  rcases hRx₂ with hcen | hinv
  · left
    rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hcen hn))
  · right
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simpa using hinv n hn

private theorem pCore_barON_dichotomy (hσ : σ.IsValid)
    (hci : ∀ r : ℕ, r.Prime → r ≠ σ.p → r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ σ.p) :
    (CFSG.pCore q (σ.bar σ.ON)).map (σ.bar σ.ON).subtype ≤
        Subgroup.centralizer ({σ.x₂b hσ} : Set σ.Nb) ∨
      ∀ y ∈ (CFSG.pCore q (σ.bar σ.ON)).map (σ.bar σ.ON).subtype,
        σ.x₂b hσ * y * (σ.x₂b hσ)⁻¹ = y⁻¹ := by
  have : Fact q.Prime := ⟨hq⟩
  have hT2 : IsPGroup 2 σ.T := σ.S.isPGroup'.to_le (σ.T_le_S hσ)
  obtain ⟨R, hR, hTR⟩ := exists_isSylowOf_normalized_of_odd hq hT2
    ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON
  have hRd := σ.sylow_centralized_or_inverted_of_prime hσ hq (hci q hq hqp) hR hTR
  obtain ⟨Q, hQ⟩ := isSylowOf_map_subgroupOf (M₀ := CFSG.pCore σ.p σ.N) σ.ON_le_N hR
  have hle : (CFSG.pCore q (σ.bar σ.ON)).map (σ.bar σ.ON).subtype ≤ σ.bar R := by
    change _ ≤ (R.subgroupOf σ.N).map σ.πN
    rw [← hQ]
    exact Subgroup.map_mono (CFSG.fitting_pCore_le_sylow Q)
  rcases σ.dichotomy_bar_of_dichotomy hσ hRd with hcen | hinv
  · exact Or.inl (hle.trans hcen)
  · exact Or.inr fun y hy => hinv y (hle hy)

private theorem le_centralizer_x₂b (hσ : σ.IsValid)
    (hci : ∀ r : ℕ, r.Prime → r ≠ σ.p → r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r)
    {X : Subgroup σ.Nb} (hX : X ≤ σ.bar σ.ON) (hXp : IsPGroup σ.p X)
    (hx : σ.x₂b hσ ∈ Subgroup.normalizer (X : Set σ.Nb)) :
    X ≤ Subgroup.centralizer ({σ.x₂b hσ} : Set σ.Nb) :=
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  le_centralizer_of_pCore_eq_bot σ.odd_card_barON (σ.pCore_barON_eq_bot hσ)
    (fun _ hq hqp => σ.pCore_barON_dichotomy hσ hci hq hqp) hX hXp hx

private theorem dichotomy_bar (hσ : σ.IsValid)
    (hci : ∀ r : ℕ, r.Prime → r ≠ σ.p → r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r)
    {r : ℕ} (hr : r.Prime) {R : Subgroup σ.Nb} (hR : IsSylowOf r R (σ.bar σ.ON))
    (hSR : ((σ.Sb hσ : Sylow 2 σ.Nb) : Subgroup σ.Nb) ≤ Subgroup.normalizer (R : Set σ.Nb)) :
    R ≤ Subgroup.centralizer ({σ.x₂b hσ} : Set σ.Nb) ∨
      ∀ y ∈ R, σ.x₂b hσ * y * (σ.x₂b hσ)⁻¹ = y⁻¹ := by
  have hx₂S : σ.x₂b hσ ∈ ((σ.Sb hσ : Sylow 2 σ.Nb) : Subgroup σ.Nb) := σ.mk'_mem_bar hσ.x₂_mem
  by_cases hrp : r = σ.p
  · subst hrp
    exact Or.inl (σ.le_centralizer_x₂b hσ hci hR.le hR.isPGroup (hSR hx₂S))
  · have : Fact r.Prime := ⟨hr⟩
    obtain ⟨R₀, hR₀, hSR₀⟩ := exists_isSylowOf_normalized_of_odd hr σ.S.isPGroup'
      ((σ.S_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON
    have hd := σ.sylow_centralized_or_inverted_of_prime hσ hr (hci r hr hrp) hR₀
      ((σ.T_le_S hσ).trans hSR₀)
    have hR₀b : IsSylowOf r (σ.bar R₀) (σ.bar σ.ON) :=
      isSylowOf_map_subgroupOf (M₀ := CFSG.pCore σ.p σ.N) σ.ON_le_N hR₀
    have hSR₀b : ((σ.Sb hσ : Sylow 2 σ.Nb) : Subgroup σ.Nb) ≤
        Subgroup.normalizer ((σ.bar R₀ : Subgroup σ.Nb) : Set σ.Nb) := by
      rw [σ.coe_Sb hσ]
      rintro _ ⟨n, hn, rfl⟩
      exact mk'_mem_normalizer_map (hR₀.le.trans σ.ON_le_N) (hSR₀ hn)
    have hSO : ((σ.Sb hσ : Sylow 2 σ.Nb) : Subgroup σ.Nb) ≤
        Subgroup.normalizer ((σ.bar σ.ON : Subgroup σ.Nb) : Set σ.Nb) :=
      (Subgroup.normalizer_eq_top_iff.mpr σ.barON_normal).ge.trans' le_top
    obtain ⟨c, hc, hcR⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hr (σ.Sb hσ).isPGroup'
      hSO σ.odd_card_barON hR₀b hR hSR₀b hSR
    have hxc : σ.x₂b hσ * c = c * σ.x₂b hσ :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ hx₂S
    rcases σ.dichotomy_bar_of_dichotomy hσ hd with hcen | hinv
    · left
      intro y hy
      rw [← hcR] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact conj_mul_comm_of_commute hxc (Subgroup.mem_centralizer_singleton_iff.mp (hcen hy₀))
    · right
      intro y hy
      rw [← hcR] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact conj_inv_of_commute hxc (hinv y₀ hy₀)

private theorem quaternion_bar (hσ : σ.IsValid) {y : G} (hyS : y ∈ (σ.S : Subgroup G))
    (hy : ∀ X : Subgroup G, X ≤ σ.S → (σ.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
      (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X) :
    ∀ X : Subgroup σ.Nb, X ≤ σ.Sb hσ →
      ((σ.Sb hσ : Sylow 2 σ.Nb) : Subgroup σ.Nb) ≤ Subgroup.normalizer (X : Set σ.Nb) →
      (∃ Q : Subgroup σ.Nb, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) →
        σ.πN ⟨y, σ.S_le_N hσ hyS⟩ ∈ X := by
  intro X hXS hSX ⟨Q, hQX, ⟨e⟩⟩
  have hSN := σ.S_le_N hσ
  set X' : Subgroup G := (σ.S : Subgroup G) ⊓ σ.pb X with hX'
  set Q' : Subgroup G := (σ.S : Subgroup G) ⊓ σ.pb Q with hQ'
  have hSX' : (σ.S : Subgroup G) ≤ Subgroup.normalizer (X' : Set G) := by
    refine (le_inf Subgroup.le_normalizer ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    intro s hs
    exact mem_normalizer_pb (n := ⟨s, hSN hs⟩) (hSX (σ.mk'_mem_bar hs))
  have hQ'X' : Q' ≤ X' := by
    refine inf_le_inf_left _ ?_
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨n, hQX hn, rfl⟩
  have hQ'N : Q' ≤ σ.N := inf_le_left.trans hSN
  let φ : Q' →* Q := (σ.πN.comp (Subgroup.inclusion hQ'N)).codRestrict Q fun q =>
    (σ.mem_pb_iff' Q ⟨q, hQ'N q.2⟩).mp (Subgroup.mem_inf.mp q.2).2
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro q hq
      have h1 : σ.πN ⟨q, hQ'N q.2⟩ = 1 := congrArg Subtype.val hq
      have h2 := σ.eq_one_of_mem_S hσ (Subgroup.mem_inf.mp q.2).1 h1
      exact Subtype.ext (by simpa using congrArg Subtype.val h2)
    · rintro ⟨z, hz⟩
      have hzS : z ∈ σ.bar (σ.S : Subgroup G) := hXS (hQX hz)
      obtain ⟨n, hn, rfl⟩ := hzS
      have hnQ : (n : G) ∈ Q' := ⟨hn, (σ.mem_pb_iff' Q n).mpr hz⟩
      exact ⟨⟨n, hnQ⟩, rfl⟩
  have hyX' := hy X' inf_le_left hSX'
    ⟨Q', hQ'X', ⟨(MulEquiv.ofBijective φ hφ).trans e⟩⟩
  exact (σ.mem_pb_iff' X ⟨y, hSN hyS⟩).mp (Subgroup.mem_inf.mp hyX').2

theorem corollaryV21 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hV21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p)
    (h_II_1_1 : ∃ y ∈ (σ.S : Subgroup G), y ∉ centerOf (σ.S : Subgroup G) ∧
      ∀ X : Subgroup G, X ≤ σ.S → (σ.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X) :
    σ.CorollaryV21 := by
  have hci : ∀ r : ℕ, r.Prime → r ≠ σ.p → r ∣ Nat.card σ.ON → σ.Centralized r ∨ σ.Inverted r :=
    fun r hr hrp hdiv => σ.centralized_or_inverted_of_ne hσ hV21 hr hrp hdiv
  have hMO := σ.pCoreIn_le_ON hσ
  have hx₂N := σ.x₂_mem_N hσ
  refine ⟨?_, ?_⟩
  ·
    intro r hr R hR hTR
    by_cases hrp : r = σ.p
    · subst hrp
      left
      have hRN : R ≤ σ.N := hR.le.trans σ.ON_le_N
      have hRp : IsPGroup σ.p (σ.bar R) := (hR.isPGroup.comap_subtype (K := σ.N)).map _
      have hx₂R : σ.x₂b hσ ∈ Subgroup.normalizer ((σ.bar R : Subgroup σ.Nb) : Set σ.Nb) :=
        mk'_mem_normalizer_map hRN (hTR σ.x₂_mem_T)
      have hc := σ.le_centralizer_x₂b hσ hci (σ.bar_mono hR.le) hRp hx₂R
      intro y hy
      have hyN : y ∈ σ.N := hRN hy
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp
        (hc (σ.mk'_mem_bar (n := ⟨y, hyN⟩) hy))
      have h2 : σ.πN (⟨σ.x₂, hx₂N⟩ * ⟨y, hyN⟩ * (⟨σ.x₂, hx₂N⟩ : σ.N)⁻¹ * (⟨y, hyN⟩ : σ.N)⁻¹) =
          1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      exact (σ.mk'_eq_one_iff' _).mp h2
    · rcases σ.sylow_centralized_or_inverted_of_prime hσ hr (hci r hr hrp) hR hTR with
        hcen | hinv
      · left
        intro y hy
        have h1 : y * σ.x₂ = σ.x₂ * y := Subgroup.mem_centralizer_singleton_iff.mp (hcen hy)
        have : σ.x₂ * y * σ.x₂⁻¹ * y⁻¹ = 1 := by rw [← h1]; group
        rw [this]
        exact Subgroup.one_mem _
      · right
        intro y hy
        rw [hinv y hy, inv_mul_cancel]
        exact Subgroup.one_mem _
  ·
    obtain ⟨F, _, _, hFcard, ψ₀, hψ₀, hker⟩ := hσ.L₀_quotient
    obtain ⟨ψ, hL⟩ := σ.exists_layerHyp hσ hII hFcard hψ₀ hker
    obtain ⟨y, hyS, hyZ, hy⟩ := h_II_1_1
    have hnot := hL.not_le_of_quaternion
      (fun r hr R hR hSR => σ.dichotomy_bar hσ hci hr hR hSR) (σ.mk'_mem_bar hyS)
      (fun h => hyZ (σ.mem_centerOf_of_mk' hσ hyS h)) (σ.quaternion_bar hσ hyS hy)
    obtain ⟨Jb, hJL, hLJ, hJC, hNJ, halt⟩ := hL.layer hnot
    have hJn : Jb.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hNJ)
    have hJO : Jb ⊓ σ.bar σ.ON = ⊥ := by
      rcases halt with ⟨hbot, -⟩ | ⟨h9, h3⟩
      · exact hbot
      · exfalso
        have hp3 : σ.p = 3 := by
          have hdvd : σ.p ∣ 3 ^ 2 := by
            rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
            exact dvd_pow_self _ (by have := hσ.one_le_f; omega)
          exact (Nat.prime_dvd_prime_iff_eq hσ.p_prime Nat.prime_three).mp
            (hσ.p_prime.dvd_of_dvd_pow hdvd)
        have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
        have := hJn
        have := σ.barON_normal
        have hn : (Jb ⊓ σ.bar σ.ON).Normal := inferInstance
        have hpg : IsPGroup σ.p (Jb ⊓ σ.bar σ.ON : Subgroup σ.Nb) :=
          IsPGroup.of_card (n := 1) (by rw [h3, hp3, pow_one])
        have hle : Jb ⊓ σ.bar σ.ON ≤ CFSG.pCore σ.p σ.Nb := le_sSup ⟨hn, hpg⟩
        rw [σ.pCore_Nb_eq_bot, le_bot_iff] at hle
        rw [hle, Subgroup.card_bot] at h3
        omega
    have hJN : σ.pb Jb ≤ σ.N := pb_le Jb
    have hMJ : pCoreIn σ.p σ.N ≤ σ.pb Jb := le_pb Jb
    have hJL₀ : σ.pb Jb ≤ σ.L₀ := by
      rintro _ ⟨n, hn, rfl⟩
      exact (σ.mk'_mem_bar_iff_of_le hσ.L₀_le_N (hMO.trans hσ.ON_le_L₀) n).mp (hJL hn)
    have hL₀eq : σ.L₀ = σ.pb Jb ⊔ σ.ON := by
      refine le_antisymm (fun l hl => ?_) (sup_le hJL₀ hσ.ON_le_L₀)
      have hlN := hσ.L₀_le_N hl
      have h1 : σ.πN ⟨l, hlN⟩ ∈ σ.bar (σ.pb Jb ⊔ σ.ON) := by
        rw [σ.bar_sup hJN σ.ON_le_N, σ.bar_pb, ← hLJ]
        exact σ.mk'_mem_bar hl
      exact (σ.mk'_mem_bar_iff_of_le (sup_le hJN σ.ON_le_N) (hMJ.trans le_sup_left) _).mp h1
    have hJONeq : σ.pb Jb ⊓ σ.ON = pCoreIn σ.p σ.N := by
      refine le_antisymm (fun g hg => ?_) (le_inf hMJ hMO)
      obtain ⟨hgJ, hgO⟩ := Subgroup.mem_inf.mp hg
      have hgN := hJN hgJ
      have h1 : σ.πN ⟨g, hgN⟩ ∈ Jb ⊓ σ.bar σ.ON :=
        Subgroup.mem_inf.mpr ⟨(σ.mem_pb_iff' Jb ⟨g, hgN⟩).mp hgJ, σ.mk'_mem_bar hgO⟩
      rw [hJO, Subgroup.mem_bot] at h1
      exact (σ.mk'_eq_one_iff' _).mp h1
    refine ⟨σ.pb Jb, hJL₀, hMJ, hL₀eq, hJONeq, le_normalizer_pb hJn, ?_, F, inferInstance,
      inferInstance, hFcard, ψ₀.comp (Subgroup.inclusion hJL₀), ?_, ?_⟩
    · rw [Subgroup.commutator_le]
      intro j hj a ha
      have hjN := hJN hj
      have haN := σ.ON_le_N ha
      have hcomm : σ.πN ⟨a, haN⟩ * σ.πN ⟨j, hjN⟩ = σ.πN ⟨j, hjN⟩ * σ.πN ⟨a, haN⟩ :=
        Subgroup.mem_centralizer_iff.mp (hJC ((σ.mem_pb_iff' Jb ⟨j, hjN⟩).mp hj)) _
          (σ.mk'_mem_bar ha)
      have h1 : σ.πN (⟨j, hjN⟩ * ⟨a, haN⟩ * (⟨j, hjN⟩ : σ.N)⁻¹ * (⟨a, haN⟩ : σ.N)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
        group
      have h2 := (σ.mk'_eq_one_iff' _).mp h1
      rw [commutatorElement_def]
      simpa using h2
    · intro γ
      obtain ⟨l, rfl⟩ := hψ₀ γ
      obtain ⟨k, hk, a, ha, hka⟩ := exists_mem_inf_mul_of_le_sup hσ.ON_le_L₀
        (hJN.trans σ.N_le_normalizer_ON) hL₀eq.le l.2
      refine ⟨⟨k, (Subgroup.mem_inf.mp hk).1⟩, ?_⟩
      have hl : l = ⟨k, (Subgroup.mem_inf.mp hk).2⟩ * ⟨a, hσ.ON_le_L₀ ha⟩ := Subtype.ext hka
      have ha1 : ψ₀ ⟨a, hσ.ON_le_L₀ ha⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact ha
      rw [hl, map_mul, ha1, mul_one]
      rfl
    · ext z
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← hJONeq]
      exact ⟨fun h => Subgroup.mem_inf.mpr ⟨z.2, h⟩, fun h => (Subgroup.mem_inf.mp h).2⟩

end Setting

end CFSG.ABGTheoremB
