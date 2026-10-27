module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift2
public import CFSG.LocalAnalysis.GLTheoremA.S8.ONFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)

structure KProfile (Y : Type) [Group Y] [Finite Y] : Prop where
  card3 : (Nat.card Y).factorization 3 = 5
  outer : ¬ 3 ∣ Nat.card (Outer Y)
  nonab : ∃ P : Subgroup Y, Nat.card P = 3 ^ 5 ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a
  e27 : ∃ E U : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
    E ≤ Subgroup.normalizer (U : Set Y)

section Profile

variable {Y : Type} [Group Y] [Finite Y]

theorem KProfile.not_abelian (h : KProfile Y) {A : Subgroup Y} (hA : Nat.card A = 3 ^ 5) :
    ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, a, ha, b, hb, hab⟩ := h.nonab
  have hP' : Nat.card P = 3 ^ (Nat.card Y).factorization 3 := by rw [hP, h.card3]
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 5) hA
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card hP' hAp
  have hAeq : A = P.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hg (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP, hA])
  refine ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, fun hc => hab ?_⟩
  · rw [hAeq]
    exact ⟨a, ha, rfl⟩
  · rw [hAeq]
    exact ⟨b, hb, rfl⟩
  · have := congrArg (fun x => g⁻¹ * x * g) hc
    simpa [mul_assoc] using this

theorem KProfile.card_le (h : KProfile Y) {E : Subgroup Y} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp := isPGroup_of_isElemAbelian hE
  have hle := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_le_of_isPGroup hp
  rw [h.card3] at hle
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  by_contra hlt
  push Not at hlt
  have h1 : 4 < k := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hk ▸ hlt)
  have h2 : k ≤ 5 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hk ▸ hle)
  obtain ⟨a, ha, b, hb, hab⟩ := h.not_abelian (A := E) (by rw [hk, show k = 5 by omega])
  exact hab (isElemAbelian_commute hE ha hb)

theorem exists_nonab_of_normalizing (h5 : (Nat.card Y).factorization 3 = 5) {F : Subgroup Y}
    (hF : IsElemAbelian 3 F) (hF4 : Nat.card F = 3 ^ 4) {σ : Y}
    (hσ : σ ∈ Subgroup.normalizer (F : Set Y)) (hσ3 : ∃ k : ℕ, σ ^ 3 ^ k = 1)
    (hσc : σ ∉ Subgroup.centralizer (F : Set Y)) :
    ∃ P : Subgroup Y, Nat.card P = 3 ^ 5 ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hσ3
  have hz3 : IsPGroup 3 (Subgroup.zpowers σ) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
  have hzN : Subgroup.zpowers σ ≤ Subgroup.normalizer (F : Set Y) := Subgroup.zpowers_le.2 hσ
  have hP3 : IsPGroup 3 ↥(F ⊔ Subgroup.zpowers σ) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_of_isElemAbelian hF) hz3 hzN
  have hle := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_le_of_isPGroup hP3
  rw [h5] at hle
  have hσF : σ ∉ F := fun hmem =>
    hσc (Subgroup.mem_centralizer_iff.2 fun h hh => isElemAbelian_commute hF hh hmem)
  obtain ⟨j, hj⟩ := hP3.exists_card_eq
  have hFP : F ≤ F ⊔ Subgroup.zpowers σ := le_sup_left
  have h4j : 4 ≤ j := by
    have hd : 3 ^ 4 ∣ 3 ^ j := by
      rw [← hF4, ← hj]
      exact Subgroup.card_dvd_of_le hFP
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  have hj5 : j ≤ 5 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hj ▸ hle)
  have hj4 : j ≠ 4 := by
    rintro rfl
    have heq : F = F ⊔ Subgroup.zpowers σ :=
      Subgroup.eq_of_le_of_card_ge hFP (by rw [hj, hF4])
    exact hσF (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
  refine ⟨F ⊔ Subgroup.zpowers σ, by rw [hj, show j = 5 by omega], σ,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers σ), ?_⟩
  by_contra hcon
  push Not at hcon
  apply hσc
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact (hcon f (Subgroup.mem_sup_left hf)).symm

theorem mem_normalizer_of_forall_conj_mem {H : Subgroup Y} {x : Y}
    (h : ∀ y ∈ H, x * y * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem isElemAbelian_range_three {H : Type*} [Group H] {k : ℕ}
    (φ : Multiplicative (Fin k → ZMod 3) →* H) : IsElemAbelian 3 φ.range :=
  CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.isElemAbelian_range φ

theorem card_range_three {H : Type*} [Group H] {k : ℕ}
    (φ : Multiplicative (Fin k → ZMod 3) →* H) (hφ : Function.Injective φ) :
    Nat.card φ.range = 3 ^ k :=
  CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_range_of_injective φ hφ

theorem map_le_normalizer_of_le {J H : Type*} [Group J] [Group H] (ι : J →* H) {W P : Subgroup J}
    (hWP : W ≤ Subgroup.normalizer (P : Set J)) :
    W.map ι ≤ Subgroup.normalizer ((P.map ι : Subgroup H) : Set H) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨w * p * w⁻¹, (Subgroup.mem_normalizer_iff.1 (hWP hw) p).1 hp, by simp⟩
  · rintro ⟨p', hp', hy⟩
    refine ⟨w⁻¹ * p' * w, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (hWP (W.inv_mem hw)) p').1 hp'
      simpa using this
    · have h : ι p' = ι w * y * (ι w)⁻¹ := hy
      calc ι (w⁻¹ * p' * w) = (ι w)⁻¹ * ι p' * ι w := by simp
        _ = y := by rw [h]; group

theorem KProfile.of_mulEquiv {Y' : Type} [Group Y'] [Finite Y'] (e : Y ≃* Y') (h : KProfile Y) :
    KProfile Y' where
  card3 := by rw [← Nat.card_congr e.toEquiv]; exact h.card3
  outer := by rw [← Nat.card_congr (equivalence e).toEquiv]; exact h.outer
  nonab := by
    obtain ⟨P, hP, a, ha, b, hb, hab⟩ := h.nonab
    refine ⟨P.map e.toMonoidHom, ?_, e a, Subgroup.mem_map_of_mem _ ha, e b,
      Subgroup.mem_map_of_mem _ hb, fun hc => hab ?_⟩
    · rw [Subgroup.card_map_of_injective e.injective, hP]
    · apply e.injective
      simpa [map_mul] using hc
  e27 := by
    obtain ⟨E, U, hE, hEc, hU, hU1, hEU⟩ := h.e27
    refine ⟨E.map e.toMonoidHom, U.map e.toMonoidHom, S8.L84.isElemAbelian_map _ hE, ?_, hU.map _,
      fun hb => hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hb),
      map_le_normalizer_of_le _ hEU⟩
    rw [Subgroup.card_map_of_injective e.injective, hEc]

theorem KProfile.of_subgroup {Z : Type} [Group Z] [Finite Z] (A : Subgroup Z)
    (hcard : (Nat.card A).factorization 3 = 5) (hout : ¬ 3 ∣ Nat.card (Outer A))
    {P : Subgroup Z} (hPA : P ≤ A) (hP : Nat.card P = 3 ^ 5) {a b : Z} (ha : a ∈ P) (hb : b ∈ P)
    (hab : a * b ≠ b * a) {E U : Subgroup Z} (hEA : E ≤ A) (hUA : U ≤ A) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hEU : E ≤ Subgroup.normalizer (U : Set Z)) : KProfile ↥A where
  card3 := hcard
  outer := hout
  nonab := ⟨P.subgroupOf A, (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv).trans hP,
    ⟨a, hPA ha⟩, Subgroup.mem_subgroupOf.2 ha, ⟨b, hPA hb⟩, Subgroup.mem_subgroupOf.2 hb,
    fun hc => hab (congrArg Subtype.val hc)⟩
  e27 := by
    refine ⟨E.subgroupOf A, U.subgroupOf A, isElemAbelian_subgroupOf hE,
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv).trans hEc,
      hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUA).symm, ?_, ?_⟩
    · intro hbot
      apply hU1
      rw [eq_bot_iff]
      intro u hu
      have : (⟨u, hUA hu⟩ : ↥A) ∈ U.subgroupOf A := hu
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h := Subgroup.mem_normalizer_iff.1 (hEU (Subgroup.mem_subgroupOf.1 hx)) (y : Z)
      exact h

end Profile

section KLevel

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_primeCore (K : Subgroup G) : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
  have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
  unfold GLAPPrimeCoreOf at h
  rwa [Subgroup.card_map_of_injective K.subtype_injective] at h

abbrev piK (K : Subgroup G) : ↥K →* PQuot 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)

theorem not_dvd_card_ker_piK (K : Subgroup G) : ¬ 3 ∣ Nat.card (piK K).ker := by
  rw [QuotientGroup.ker_mk']
  exact not_dvd_card_primeCore K

theorem piK_injective (K : Subgroup G) {W : Subgroup ↥K} (hW : IsPGroup 3 W) :
    Function.Injective ((piK K).comp W.subtype) :=
  injective_comp_subtype Nat.prime_three (piK K) (not_dvd_card_ker_piK K) hW

theorem not_catalog_ON
    {K : Subgroup G} (hZ : Subgroup.center (PQuot 3 K) = ⊥)
    (h5 : (Nat.card (PQuot 3 K)).factorization 3 = 5) :
    ¬ catalogIs (PSimple 3 K) (S8.sporIs .ONan) := by
  intro hON
  obtain ⟨e⟩ := S8.L84.nonempty_pquot_equiv_ON hON hZ
  have h4 := CFSG.RankThree.Native.factorization_card_ON
  rw [← Nat.card_congr e.toEquiv, h5] at h4
  omega

theorem rank_le_of_profile {K : Subgroup G} (hp : KProfile (PQuot 3 K)) {W : Subgroup G}
    (hWK : W ≤ K) (hW : IsElemAbelian 3 W) : Nat.card W ≤ 3 ^ 4 := by
  set π := piK K
  let W' : Subgroup ↥K := W.subgroupOf K
  have hW' : IsElemAbelian 3 W' := isElemAbelian_subgroupOf hW
  have hinj := piK_injective K (isPGroup_of_isElemAbelian hW')
  have hcard : Nat.card W = Nat.card (W'.map π) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv).symm.trans
      (card_eq_of_injective_comp_subtype π hinj)
  rw [hcard]
  exact hp.card_le (S8.L84.isElemAbelian_map π hW')

theorem sup_primeCore_eq_top {K K₀ : Subgroup G} (hK₀ : K₀ ≤ K)
    (hcov : K₀ ⊔ GLAPPrimeCoreOf 3 K = K) :
    K₀.subgroupOf K ⊔ GLAPPrimeCore 3 ↥K = ⊤ := by
  have hO : GLAPPrimeCoreOf 3 K ≤ K := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have h := Subgroup.subgroupOf_sup (B := K) hK₀ hO
  rw [hcov, Subgroup.subgroupOf_self] at h
  have h2 : (GLAPPrimeCoreOf 3 K).subgroupOf K = GLAPPrimeCore 3 ↥K := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [h2] at h
  exact h.symm

theorem cover_of_profile {K : Subgroup G} (hp : KProfile (PQuot 3 K)) {K₀ : Subgroup G}
    (hK₀ : K₀ ≤ K) (hcov : K₀ ⊔ GLAPPrimeCoreOf 3 K = K) :
    ∃ F T : Subgroup G, F ≤ K₀ ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 3 ∧ T ≤ K ∧ IsPGroup 2 T ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ F ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨E, U, hE, hEc, hU, hU1, hEU⟩ := hp.e27
  set π := piK K with hπ
  set J : Subgroup ↥K := K₀.subgroupOf K with hJ
  set π₀ : ↥J →* PQuot 3 K := π.comp J.subtype with hπ₀
  have hker : ¬ 3 ∣ Nat.card π₀.ker := fun h =>
    not_dvd_card_ker_piK K (h.trans (card_ker_comp_subtype_dvd π J))
  have hrange : π₀.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ J ⊔ GLAPPrimeCore 3 ↥K := by
      rw [sup_primeCore_eq_top hK₀ hcov]
      trivial
    obtain ⟨j, hj, c, hc, hjc⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨j, hj⟩, ?_⟩
    have hπc : π c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    show π j = π x
    rw [← hjc, map_mul, hπc, mul_one]
  obtain ⟨W, P, hW3, hWmap, hWinj, hP2, hPmap, hWP⟩ := exists_lift_normalizing π₀ hker
    (isPGroup_of_isElemAbelian hE) hU (hrange ▸ le_top) (hrange ▸ le_top) hEU
  set ι : ↥J →* G := K.subtype.comp J.subtype with hι
  have hιinj : Function.Injective ι := K.subtype_injective.comp J.subtype_injective
  refine ⟨W.map ι, P.map ι, ?_, ?_, ?_, ?_, hP2.map ι, ?_, map_le_normalizer_of_le ι hWP⟩
  · rintro _ ⟨w, -, rfl⟩
    exact Subgroup.mem_subgroupOf.1 w.2
  · have h1 : IsElemAbelian 3 W := isElemAbelian_of_injective_comp_subtype π₀ hWinj (hWmap ▸ hE)
    exact S8.L84.isElemAbelian_map ι h1
  · rw [Subgroup.card_map_of_injective hιinj, card_eq_of_injective_comp_subtype π₀ hWinj, hWmap,
      hEc]
  · rintro _ ⟨p, -, rfl⟩
    exact (p : ↥K).2
  · intro hT
    apply hU1
    rw [← hPmap, eq_bot_iff]
    rintro _ ⟨p, hp', rfl⟩
    obtain ⟨c, hc, hcp⟩ := hT ⟨p, hp', rfl⟩
    have hcp' : c = (p : ↥K) := Subtype.ext hcp
    show π (p : ↥K) = 1
    rw [← hcp']
    exact (QuotientGroup.eq_one_iff c).2 hc

theorem barAut_eq_localBalance (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    barAut K g hg = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K
      ⟨g⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hg⟩ := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAut_mk, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
  congr 1
  apply Subtype.ext
  simp [conjL_apply]

theorem mem_inner_of_pow {M : Type*} [Group M] (hne : ¬ 3 ∣ Nat.card (Outer M)) (α : MulAut M)
    {k : ℕ} (hα : α ^ 3 ^ k = 1) : α ∈ inner M := by
  have h1 : orderOf (QuotientGroup.mk α : Outer M) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hα]
    rfl
  have h2 := orderOf_dvd_natCard (QuotientGroup.mk α : Outer M)
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer M)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hne)
  have h3 : orderOf (QuotientGroup.mk α : Outer M) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)

theorem inducesInnerMod_of_profile {K : Subgroup G} (hp : KProfile (PQuot 3 K)) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hk : ∃ k : ℕ, g ^ 3 ^ k = 1) :
    InducesInnerMod 3 K g := by
  obtain ⟨k, hk⟩ := hk
  apply inducesInnerMod_of_inner hg
  apply mem_inner_of_pow hp.outer _ (k := k)
  rw [barAut_eq_localBalance, ← map_pow]
  have : (⟨g⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hg⟩ :
      ↥(Subgroup.normalizer (K : Set G))) ^ 3 ^ k = 1 := Subtype.ext (by simp [inv_pow, hk])
  rw [this, map_one]

end KLevel

end CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts
