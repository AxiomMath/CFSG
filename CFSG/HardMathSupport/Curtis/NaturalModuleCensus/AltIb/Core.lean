module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.EvenCentre

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)

section Core

variable {Y : Type*} [Group Y]

theorem mem_of_pow_mem_of_coprime {p : ℕ} (hp : p.Prime) {V : Subgroup Y} {c : Y} {k m : ℕ}
    (hm : orderOf c ∣ m) (hpm : ¬ p ∣ m) (hc : c ^ p ^ k ∈ V) : c ∈ V := by
  have hcop : Nat.Coprime (p ^ k) (orderOf c) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpm (h.trans hm))
  obtain ⟨a, b, hab⟩ : IsCoprime ((p ^ k : ℕ) : ℤ) ((orderOf c : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 hcop
  have h1 : c = (c ^ p ^ k) ^ a := by
    have h2 : (((p ^ k : ℕ) : ℤ)) * a + ((orderOf c : ℕ) : ℤ) * b = 1 := by linarith
    calc c = c ^ ((((p ^ k : ℕ) : ℤ)) * a + ((orderOf c : ℕ) : ℤ) * b) := by rw [h2, zpow_one]
      _ = (c ^ p ^ k) ^ a := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one,
            one_zpow, mul_one]
  rw [h1]
  exact V.zpow_mem hc a


end Core

section Core0

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem exists_perfect_core {L : Subgroup Y} {p : ℕ} (hp : p.Prime)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {x : Y} (hx : x ∈ L) {W : Subgroup Y}
    (hW : ⁅W, W⁆ = W) (hWL : W ≤ L ⊔ Subgroup.centralizer (L : Set Y))
    (hWx : W ≤ Subgroup.centralizer ({x} : Set Y)) {E : Subgroup Y} (hEW : E ≤ W ⊓ L)
    (hE : IsPGroup p E) :
    ∃ V : Subgroup Y, V ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ ⁅V, V⁆ = V ∧ E ≤ V := by
  set A : Subgroup Y := L ⊓ (W ⊔ Subgroup.centralizer (L : Set Y)) with hA
  have hCx : Subgroup.centralizer (L : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hc y hx
  have hAx : A ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) := fun a ha => ⟨ha.1, (sup_le hWx hCx) ha.2⟩
  have hcomm : ∀ j ∈ A, ∀ c ∈ Subgroup.centralizer (L : Set Y), j * c = c * j := fun j hj c hc =>
    Subgroup.mem_centralizer_iff.mp hc j hj.1
  have hWA : W ≤ A ⊔ Subgroup.centralizer (L : Set Y) := by
    intro w hw
    have h1 : w ∈ (L ⊔ Subgroup.centralizer (L : Set Y) : Subgroup Y) := hWL hw
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (ToralCensus.le_normalizer_centralizer L)] at h1
    obtain ⟨l, hl, c, hc, rfl⟩ := h1
    have hlA : l ∈ A := by
      refine ⟨hl, ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.mem_sup_left hw : l * c ∈ W ⊔ Subgroup.centralizer (L : Set Y))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hc : c ∈ W ⊔ Subgroup.centralizer (L : Set Y)))
      simpa using this
    exact Subgroup.mul_mem_sup hlA hc
  have hWV : W ≤ perfectJoin A ⊔ Subgroup.centralizer (L : Set Y) := ToralCensus.perfect_le_perfectJoin_sup hcomm hW hWA
  have hVL : perfectJoin A ≤ L := (perfectJoin_le A).trans (fun a ha => ha.1)
  refine ⟨perfectJoin A, (perfectJoin_le A).trans hAx, perfectJoin_perfect A, ?_⟩
  intro e he
  have heW : e ∈ W := (hEW he).1
  have heL : e ∈ L := (hEW he).2
  have h1 : e ∈ (perfectJoin A ⊔ Subgroup.centralizer (L : Set Y) : Subgroup Y) := hWV heW
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hVL.trans (ToralCensus.le_normalizer_centralizer L))] at h1
  obtain ⟨v, hv, c, hc, rfl⟩ := h1
  have hcL : c ∈ L := by
    have := L.mul_mem (L.inv_mem (hVL hv)) heL
    simpa using this
  have hc' : c ∈ Subgroup.centralizer (L : Set Y) := hc
  have hcomm' : Commute v c := Subgroup.mem_centralizer_iff.mp hc' v (hVL hv)
  obtain ⟨k, hk⟩ := hE ⟨v * c, he⟩
  have hk' : (v * c) ^ p ^ k = 1 := congrArg Subtype.val hk
  rw [hcomm'.mul_pow] at hk'
  have hcN : c ^ p ^ k ∈ perfectJoin A := by
    have h2 : c ^ p ^ k = (v ^ p ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hk'
    rw [h2]
    exact (perfectJoin A).inv_mem ((perfectJoin A).pow_mem hv _)
  have hz : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc' g g.2)
  have hord : orderOf c ∣ Nat.card (Subgroup.center ↥L) := by
    have := orderOf_dvd_natCard (⟨(⟨c, hcL⟩ : ↥L), hz⟩ : ↥(Subgroup.center ↥L))
    simpa [Subgroup.orderOf_mk] using this
  exact (perfectJoin A).mul_mem hv (mem_of_pow_mem_of_coprime hp hord hpZ hcN)

theorem exists_perfect_core_of_comp (hSch : KFactCatalogSchreier) {L : Subgroup Y} {p : ℕ}
    (hp : p.Prime) (hL : IsComponentOf L ⊤)
    (htype : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {x : Y} (hx : x ∈ L) {W : Subgroup Y}
    (hW : ⁅W, W⁆ = W) (hWN : W ≤ Subgroup.normalizer (L : Set Y))
    (hWx : W ≤ Subgroup.centralizer ({x} : Set Y)) {E : Subgroup Y} (hEW : E ≤ W ⊓ L)
    (hE : IsPGroup p E) :
    ∃ V : Subgroup Y, V ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ ⁅V, V⁆ = V ∧ E ≤ V :=
  exists_perfect_core hp hpZ hx hW
    (ToralCensus.perfect_le_sup_centralizer_of_comp hSch hL htype hW hWN) hWx hEW hE

end Core0

section Centre

open TauCeti

theorem not_dvd_card_center_of_rest (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] [Group.IsPerfect A] {P : LieTypeIndex → Prop}
    (hP : P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD ∨ P = IdxG2) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hX : IsLieOf P (A ⧸ Subgroup.center A)) :
    ¬ p ∣ Nat.card (Subgroup.center A) := by
  intro hdvd
  obtain ⟨d, hPd, ⟨e⟩⟩ := hX
  obtain ⟨hd, hA, h2A⟩ := ToralCensus.rest_index hP hPd
  rcases ToralCensus.prime_dvd_torus_of_dvd_card_center hGA d hd e hp (by omega) hdvd with
    ⟨r, q, h, -⟩ | ⟨r, q, h, -⟩
  · exact hA r q h
  · exact h2A r q h

theorem not_dvd_card_center_of_small
    (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type} [Group A] [Finite A]
    [Group.IsPerfect A] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hS : IsSmallTwoOrG2 (A ⧸ Subgroup.center A)) : ¬ p ∣ Nat.card (Subgroup.center A) := by
  intro hpd
  have h6 : p ∣ 6 := hpd.trans (card_center_dvd_six_of_small hGA hS)
  have := Nat.le_of_dvd (by norm_num) h6
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem not_dvd_card_center_of_isRest
    (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type} [Group A] [Finite A]
    [Group.IsPerfect A] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : IsRestTwoOrG2 (A ⧸ Subgroup.center A)) : ¬ p ∣ Nat.card (Subgroup.center A) := by
  rcases hX with h | h | h | h | h
  · exact not_dvd_card_center_of_rest hGA (Or.inl rfl) hp hp5 h
  · exact not_dvd_card_center_of_rest hGA (Or.inr (Or.inl rfl)) hp hp5 h
  · exact not_dvd_card_center_of_rest hGA (Or.inr (Or.inr (Or.inl rfl))) hp hp5 h
  · exact not_dvd_card_center_of_rest hGA (Or.inr (Or.inr (Or.inr rfl))) hp hp5 h
  · exact not_dvd_card_center_of_small hGA hp hp5 h

theorem false_of_small_ib
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hq : CFSG.Open.IsQuasisimple ↥L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hS : IsSmallTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {E : Subgroup Y} (hEL : E ≤ L)
    (hcard : Nat.card E = p ^ 2) : False := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  have hpZ := not_dvd_card_center_of_small hGA hp hp5 hS
  have hEL' : Nat.card E ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hEL
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)] at hEL'
  have hcop : Nat.Coprime (p ^ 2) (Nat.card (Subgroup.center ↥L)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpZ)
  have h2 : p ^ 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    hcop.dvd_of_dvd_mul_right (hcard ▸ hEL')
  exact ToralCensus.not_sq_dvd_smallBound hp hp5
    (h2.trans ((ToralCensus.card_dvd_of_small hS).trans (by norm_num)))

end Centre

section Bar

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem fix_all_bar {L J : Subgroup Y} {p : ℕ} (hp : p.Prime)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {x : Y} (hxL : x ∈ L) (hxp : x ^ p = 1)
    (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) (g : ↥L ⧸ Subgroup.center ↥L)
    (hg : g * QuotientGroup.mk ⟨x, hxL⟩ = QuotientGroup.mk ⟨x, hxL⟩ * g) :
    g ∈ quotImage L J := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  have hz : (l * x')⁻¹ * (x' * l) ∈ Subgroup.center ↥L := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hg
    exact hg
  set z := (l * x')⁻¹ * (x' * l) with hzdef
  have hxl : x' * l = l * x' * z := by rw [hzdef]; group
  have hzc : ∀ g : ↥L, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hpow : ∀ n : ℕ, x' ^ n * l = l * z ^ n * x' ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x' ^ (n + 1) * l = x' ^ n * (x' * l) := by rw [pow_succ, mul_assoc]
        _ = (x' ^ n * l) * x' * z := by rw [hxl]; group
        _ = l * z ^ n * (x' ^ (n + 1) * z) := by rw [ih, pow_succ]; group
        _ = l * z ^ (n + 1) * x' ^ (n + 1) := by rw [hzc (x' ^ (n + 1))]; group
  have hxp' : x' ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hzp : z ^ p = 1 := by
    have := hpow p
    rw [hxp'] at this
    simpa using this
  have hord : orderOf z ∣ Nat.card (Subgroup.center ↥L) := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center ↥L))
    simpa [Subgroup.orderOf_mk] using this
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ Nat.gcd p (Nat.card (Subgroup.center ↥L)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) hord
    rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).2 hpZ)] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  rw [hz1] at hxl
  have hcomm : x * (l : Y) * x⁻¹ = l := by
    have := congrArg Subtype.val hxl
    simp only [Subgroup.coe_mul, mul_one] at this
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
  exact mem_quotImage.2 ⟨l, hfix l l.2 hcomm, rfl⟩

omit [Finite Y] in
theorem exists_quasisimple_lift {L J : Subgroup Y} (hP : IsParabolicTwo L J)
    {Xb : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hXJ : Xb ≤ quotImage L J)
    (hq : CFSG.Open.IsQuasisimple ↥Xb) :
    ∃ X : Subgroup Y, X ≤ J ∧ X ≤ L ∧ CFSG.Open.IsQuasisimple ↥X ∧
      (X.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) = Xb ∧
      ∃ m : ℕ, m ∣ Nat.card (Subgroup.center ↥L) ∧ Nat.card ↥X = Nat.card ↥Xb * m := by
  obtain ⟨hJL, T, hT, hNJ⟩ := hP
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L :=
    (QuotientGroup.ker_mk' _).le
  have hperf : ⁅Xb, Xb⁆ = Xb :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hq.1)
  obtain ⟨W, hWp, hWle, hWmap⟩ := ParabPrime.exists_perfect_map_eq
    (QuotientGroup.mk' (Subgroup.center ↥L)) hker hperf
    (by rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]; exact le_top)
  have hWJ : ∀ w ∈ W, (w : Y) ∈ J := by
    intro w hw
    obtain ⟨l, hlJ, hl⟩ := mem_quotImage.1 (hXJ (hWle hw))
    have hz : l⁻¹ * w ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq]
      exact hl
    have h1 := center_le_of_normalizer_le hT hNJ hz
    have h2 : (w : Y) = (l : Y) * ((l⁻¹ * w : ↥L) : Y) := by simp
    rw [h2]
    exact J.mul_mem hlJ h1
  subst hWmap
  have : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.2 hWp
  have : IsSimpleGroup (↥(W.map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
      Subgroup.center ↥(W.map (QuotientGroup.mk' (Subgroup.center ↥L)))) := hq.2
  let ψ : ↥W →* ↥(W.map (QuotientGroup.mk' (Subgroup.center ↥L))) :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).subgroupMap W
  have hψs : Function.Surjective ψ := MonoidHom.subgroupMap_surjective _ W
  have hψk : ∀ w : ↥W, ψ w = 1 → ((w : ↥L) ∈ Subgroup.center ↥L) := by
    intro w hw
    have h1 : QuotientGroup.mk' (Subgroup.center ↥L) (w : ↥L) = 1 := congrArg Subtype.val hw
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hψc : ψ.ker ≤ Subgroup.center ↥W := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hψk w hw) g)
  have hQW : CFSG.Open.IsQuasisimple ↥W := by
    refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
    exact (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence ψ hψs hψc).isSimpleGroup
  set X : Subgroup Y := W.map L.subtype with hX
  have hXW : ↥X ≃* ↥W := (W.equivMapOfInjective L.subtype L.subtype_injective).symm
  refine ⟨X, ?_, Subgroup.map_subtype_le W, CFSG.ComponentClassification.Components.quasisimple_of_equiv hXW hQW, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hWJ w hw
  · have hXL : X.subgroupOf L = W := Subgroup.comap_map_eq_self_of_injective L.subtype_injective W
    rw [hXL]
  · refine ⟨Nat.card ψ.ker, ?_, ?_⟩
    · let f : ↥ψ.ker →* ↥(Subgroup.center ↥L) :=
        ((W.subtype).comp ψ.ker.subtype).codRestrict (Subgroup.center ↥L) fun w => hψk w w.2
      refine Subgroup.card_dvd_of_injective f fun a b hab => ?_
      exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥(Subgroup.center ↥L) => (t : ↥L)) hab))
    · rw [Nat.card_congr hXW.toEquiv,
        Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv]

omit [Finite Y] in
theorem exists_quasisimple_lift_of_not_dvd {L J : Subgroup Y} (hP : IsParabolicTwo L J) {p : ℕ}
    (hp : p.Prime) (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {Xb : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hXJ : Xb ≤ quotImage L J)
    (hq : CFSG.Open.IsQuasisimple ↥Xb) :
    ∃ X : Subgroup Y, X ≤ J ∧ X ≤ L ∧ CFSG.Open.IsQuasisimple ↥X ∧
      (X.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) = Xb ∧
      ∀ k : ℕ, p ^ k ∣ Nat.card ↥X ↔ p ^ k ∣ Nat.card ↥Xb := by
  obtain ⟨X, hXJ', hXL, hXq, hXmap, m, hm, hcard⟩ := exists_quasisimple_lift hP hXJ hq
  refine ⟨X, hXJ', hXL, hXq, hXmap, fun k => ?_⟩
  have hcop : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpZ (h.trans hm))
  rw [hcard]
  exact hcop.dvd_mul_right

end Bar

section Assembly

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_perfect_core_in_parabolic
    (hSch : KFactCatalogSchreier) (hGA : CFSG.Open.GriessAllModelsStatement)
    {L J : Subgroup Y} (hL : IsComponentOf L ⊤)
    (htype : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hrest : IsRestTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {x : Y} (hx : x ∈ L) (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) {W : Subgroup Y}
    (hW : ⁅W, W⁆ = W) (hWN : W ≤ Subgroup.normalizer (L : Set Y))
    (hWx : W ≤ Subgroup.centralizer ({x} : Set Y)) {E : Subgroup Y} (hEW : E ≤ W ⊓ L)
    (hE : IsPGroup p E) :
    ¬ p ∣ Nat.card (Subgroup.center ↥L) ∧
      ∃ V : Subgroup Y, V ≤ J ⊓ Subgroup.centralizer ({x} : Set Y) ∧ ⁅V, V⁆ = V ∧ E ≤ V := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.2.2.1
  have hpZ := not_dvd_card_center_of_isRest hGA hp hp5 hrest
  refine ⟨hpZ, ?_⟩
  obtain ⟨V, hVle, hV, hEV⟩ :=
    exists_perfect_core_of_comp hSch hp hL htype hpZ hx hW hWN hWx hEW hE
  refine ⟨V, fun v hv => ⟨hfix v (hVle hv).1 ?_, (hVle hv).2⟩, hV, hEV⟩
  have := Subgroup.mem_centralizer_iff.1 (hVle hv).2 x (Set.mem_singleton x)
  rw [this, mul_inv_cancel_right]

end Assembly

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
