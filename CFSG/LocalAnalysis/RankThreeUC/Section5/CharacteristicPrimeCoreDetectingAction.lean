module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryNormalizerRepresentation
public import CFSG.LocalAnalysis.RankThreeUC.Section5.MaxInvariantOdd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CharacteristicPrimeCoreDetectingAction

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped commutatorElement

private theorem openpCore_eq {p : ℕ} {G : Type} [Group G] : CFSG.Open.pCore p G = CFSG.pCore p G :=
  rfl

private theorem comm_le_comm_comm {G : Type*} [Group G] (W R : Subgroup G)
    (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hcop : Nat.Coprime (Nat.card R) (Nat.card W)) :
    ⁅W, R⁆ ≤ ⁅⁅W, R⁆, R⁆ := by
  classical
  have : Subgroup.Normalizes R W := ⟨hRW⟩
  have h2 : CFSG.commutatorAction₂ (A := R) (G := W) = CFSG.commutatorAction (A := R) (G := W) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := W) (A := R) hcop
  have hmap : (CFSG.commutatorAction (A := R) (G := W)).map W.subtype = ⁅W, R⁆ := by
    simpa using CFSG.commutatorAction_subgroup_conj_map_eq_commutator W R hRW
  have hmap2 : (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype ≤ ⁅⁅W, R⁆, R⁆ := by
    let C : Subgroup W := CFSG.commutatorAction (A := R) (G := W)
    let S : Set W := {x : W | ∃ a : R, ∃ h : W, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype =
          (Subgroup.closure S).map W.subtype := rfl
      _ = Subgroup.closure (W.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := W.subtype) S)
      _ ≤ ⁅⁅W, R⁆, R⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅W, R⁆, R⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅W, R⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem W.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅W, R⁆, R⁆ :=
          Subgroup.commutator_mem_commutator ((⁅W, R⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hRW, mul_assoc] using hcomm
  intro x hx
  rw [← hmap, ← h2] at hx
  exact hmap2 hx

private theorem pCoreOf_conj_mem {p : ℕ} {G : Type} [Group G] {H : Subgroup G} {b k : G}
    (hb : b ∈ H) (hk : k ∈ CFSG.Open.pCoreOf p H) : b⁻¹ * k * b ∈ CFSG.Open.pCoreOf p H := by
  unfold CFSG.Open.pCoreOf at *
  obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.mp hk
  rw [openpCore_eq] at *
  haveI := (CFSG.pCore_normal (p := p) (G := ↥H))
  refine Subgroup.mem_map.mpr ⟨(⟨b, hb⟩ : H)⁻¹ * k0 * ⟨b, hb⟩, ?_, rfl⟩
  simpa using (CFSG.pCore_normal (p := p) (G := ↥H)).conj_mem k0 hk0 ((⟨b, hb⟩ : H)⁻¹)

private theorem pCoreOf_isPGroup {p : ℕ} {G : Type} [Group G] (H : Subgroup G) :
    IsPGroup p (CFSG.Open.pCoreOf p H) := by
  unfold CFSG.Open.pCoreOf
  rw [openpCore_eq]
  exact (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

theorem commutator_zpowers_eq_of_coprime_finite {J : Type} [Group J] [Finite J] (X : Subgroup J)
    (hX : IsPGroup 2 X) {d : J} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdq : Nat.card (Subgroup.zpowers d) = q)
    (hdX : ∀ x ∈ X, d⁻¹ * x * d ∈ X) :
    ⁅⁅X, Subgroup.zpowers d⁆, Subgroup.zpowers d⁆ = ⁅X, Subgroup.zpowers d⁆ := by
  classical
  have hord : orderOf d = q := by rw [← Nat.card_zpowers]; exact hdq
  have hpow : d ^ q = 1 := by rw [← hord]; exact pow_orderOf_eq_one d
  have hk : ∀ k : ℕ, ∀ x ∈ X, (d ^ k)⁻¹ * x * d ^ k ∈ X := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      have := hdX _ (ih x hx)
      have e : (d ^ (k + 1))⁻¹ * x * d ^ (k + 1) = d⁻¹ * ((d ^ k)⁻¹ * x * d ^ k) * d := by
        rw [pow_succ, mul_inv_rev]; group
      rw [e]; exact this
  have hdn : Subgroup.zpowers d ≤ Subgroup.normalizer (X : Set J) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hk (q - 1) h hh
      have hinv : d ^ (q - 1) = d⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hq.one_lt.le]; exact hpow)
      rw [hinv, inv_inv] at this
      exact this
    · intro hh
      have := hdX _ hh
      simpa [mul_assoc] using this
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers d)) (Nat.card X) := by
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    rw [hdq, hn]
    exact (Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2))
  have h1 := comm_le_comm_comm X (Subgroup.zpowers d) hdn hcop
  set D := Subgroup.zpowers d with hD
  have hEn : ∀ z ∈ D, ∀ y ∈ ⁅X, D⁆, z * y * z⁻¹ ∈ ⁅X, D⁆ := by
    intro z hz
    have hzN := hdn hz
    have : ⁅X, D⁆ ≤ (⁅X, D⁆).comap (MulAut.conj z).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro x hx w hw
      rw [Subgroup.mem_comap]
      have h1 : (MulAut.conj z).toMonoidHom ⁅x, w⁆ = ⁅z * x * z⁻¹, z * w * z⁻¹⁆ := by
        simp [map_commutatorElement]
      rw [h1]
      refine Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hzN x).mp hx) ?_
      exact D.mul_mem (D.mul_mem hz hw) (D.inv_mem hz)
    intro y hy
    exact this hy
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro y hy z hz
    rw [commutatorElement_def]
    have : y * z * y⁻¹ * z⁻¹ = y * (z * y⁻¹ * z⁻¹) := by group
    rw [this]
    exact (⁅X, D⁆).mul_mem hy (hEn z hz _ ((⁅X, D⁆).inv_mem hy))
  · exact h1

theorem pCoreOf_char {G : Type} [Group G] [Finite G] {B : Subgroup G} (q : ℕ) :
    ∀ φ : ↥B ≃* ↥B, Subgroup.map φ.toMonoidHom ((CFSG.Open.pCoreOf q B).subgroupOf B) =
      (CFSG.Open.pCoreOf q B).subgroupOf B := by
  intro φ
  have : (CFSG.Open.pCoreOf q B).subgroupOf B = CFSG.pCore q B := by
    unfold CFSG.Open.pCoreOf
    rw [openpCore_eq, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective B.subtype_injective]
  rw [this]
  exact CFSG.pCore_map_iso q φ

theorem exists_noncommuting_pair {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G]
    {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) {q : ℕ} (hq : q ∈ piOf B)
    (hAne : CFSG.Open.pCoreOf q B ≠ ⊥) :
    ∃ k ∈ CFSG.Open.pCoreOf 2 (B ⊔ T), ∃ a ∈ CFSG.Open.pCoreOf q B, ∃ x ∈ P,
      ⁅k, a⁆ * x * ⁅k, a⁆⁻¹ ≠ x := by
  have hAB : CFSG.Open.pCoreOf q B ≤ B := Subgroup.map_subtype_le _
  have h3 := (characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants h51 h53 (CFSG.Open.pCoreOf q B) hAB (pCoreOf_char q)).2.2 hAne
  by_contra hcon
  push Not at hcon
  apply h3
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx s hs
  have hs' : s ∈ Subgroup.centralizer (P : Set G) := by
    have : ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), CFSG.Open.pCoreOf q B⁆ ≤ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.commutator_le]
      intro k hk a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hcon k hk a ha y hy
      calc y * ⁅k, a⁆ = (⁅k, a⁆ * y * ⁅k, a⁆⁻¹) * ⁅k, a⁆ := by rw [this]
        _ = ⁅k, a⁆ * y := by group
    exact this hs
  rw [Subgroup.mem_centralizer_iff] at hs'
  rw [Subgroup.mem_bot, commutatorElement_def]
  have := hs' x hx
  calc x * s * x⁻¹ * s⁻¹ = (x * s) * (s * x)⁻¹ := by group
    _ = 1 := by rw [← this]; simp

theorem pCoreOf_ne_bot {G : Type} [Group G] [Finite G] {B : Subgroup G} (hB : IsMulCommutative B)
    {q : ℕ} (hq : q ∈ piOf B) : CFSG.Open.pCoreOf q B ≠ ⊥ := by
  haveI : Fact q.Prime := ⟨hq.1⟩
  classical
  haveI : Fintype B := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card (G := ↥B) q (by rw [← Nat.card_eq_fintype_card]; exact hq.2)
  have hbne : b ≠ 1 := by
    intro h; rw [h, orderOf_one] at hb; exact hq.1.one_lt.ne hb
  have hN : (Subgroup.zpowers b).Normal := by
    haveI : IsMulCommutative B := hB
    exact Subgroup.normal_of_comm _
  have hp : IsPGroup q (Subgroup.zpowers b) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb, pow_one]
  have hle : Subgroup.zpowers b ≤ CFSG.Open.pCore q B :=
    le_sSup ⟨hN, hp⟩
  intro h
  unfold CFSG.Open.pCoreOf at h
  have h2 : CFSG.Open.pCore q B = ⊥ := by
    have := (Subgroup.map_eq_bot_iff_of_injective (CFSG.Open.pCore q B) B.subtype_injective).mp h
    exact this
  rw [h2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact hbne hle

theorem exists_detecting_action {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G]
    {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hEA : CFSG.Open.IsElemAbelian p P) {q : ℕ} (hq : q ∈ piOf B) (hq3 : 3 < q) :
    ∃ (J : Type) (_ : Group J) (_ : Finite J) (W : Type) (_ : AddCommGroup W)
      (_ : Module (AlgebraicClosure (ZMod p)) W) (_ : Module.Finite (AlgebraicClosure (ZMod p)) W)
      (τ : Representation (AlgebraicClosure (ZMod p)) J W)
      (f : Subgroup.normalizer (P : Set G) →* J) (ι : Additive P →+ W),
      Function.Injective τ ∧ Function.Surjective f ∧
      Module.finrank (AlgebraicClosure (ZMod p)) W = CFSG.Open.pRank p P ∧
      Function.Injective ι ∧
      Submodule.span (AlgebraicClosure (ZMod p)) (Set.range ι) = ⊤ ∧
      (∀ (g : Subgroup.normalizer (P : Set G)) (x : P),
        ι (Additive.ofMul (P.normalizerMonoidHom g x)) = τ (f g) (ι (Additive.ofMul x))) ∧
      (∀ g : Subgroup.normalizer (P : Set G), f g = 1 ↔ ∀ x ∈ P, (g : G) * x * (g : G)⁻¹ = x) ∧
      ∃ E D : Subgroup J, E ≠ ⊥ ∧ IsPGroup 2 E ∧ Nat.card D = q ∧ ⁅E, D⁆ = E ∧
        E ≤ ((CFSG.Open.pCoreOf 2 (B ⊔ T)).subgroupOf (Subgroup.normalizer (P : Set G))).map f ∧
        D ≤ (B.subgroupOf (Subgroup.normalizer (P : Set G))).map f := by
  obtain ⟨J, hJg, hJf, W, hW, hWm, hWf, τ, f, ι, h1, h2, h3, h4, h5, h6, h7⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryNormalizerRepresentation.exists_faithful_image h51 h53 hEA
  refine ⟨J, hJg, hJf, W, hW, hWm, hWf, τ, f, ι, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  classical
  haveI : Fact q.Prime := ⟨hq.1⟩
  have hBT : B ⊔ T ≤ (Subgroup.normalizer (P : Set G)) := sup_le h51.setting.normB h51.setting.normT
  have hAne : CFSG.Open.pCoreOf q B ≠ ⊥ := pCoreOf_ne_bot h51.setting.abelian hq
  have hAB : CFSG.Open.pCoreOf q B ≤ B := Subgroup.map_subtype_le _
  have hKBT : CFSG.Open.pCoreOf 2 (B ⊔ T) ≤ B ⊔ T := Subgroup.map_subtype_le _
  have hKN : CFSG.Open.pCoreOf 2 (B ⊔ T) ≤ (Subgroup.normalizer (P : Set G)) := hKBT.trans hBT
  obtain ⟨k, hk, a, ha, x, hx, hne⟩ := exists_noncommuting_pair h51 h53 hq hAne
  let k' : (Subgroup.normalizer (P : Set G)) := ⟨k, hKN hk⟩
  let a' : (Subgroup.normalizer (P : Set G)) := ⟨a, h51.setting.normB (hAB ha)⟩
  have hexpA : Monoid.exponent (CFSG.Open.pCoreOf q B) = q := h51.exponent_Or q hq
  have ha_pow : a ^ q = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : CFSG.Open.pCoreOf q B)
    rw [hexpA] at this
    have h2 := congrArg (fun y : CFSG.Open.pCoreOf q B => (y : G)) this
    simpa using h2
  have ha'_pow : a' ^ q = 1 := by
    apply Subtype.ext
    simpa [a'] using ha_pow
  have hcomm : ⁅f k', f a'⁆ ≠ 1 := by
    intro h
    apply hne
    have h1 : f ⁅k', a'⁆ = 1 := by rw [map_commutatorElement]; exact h
    have h2 := (h7 ⁅k', a'⁆).1 h1 x hx
    exact h2
  have hfa_ne : f a' ≠ 1 := by
    intro h
    apply hcomm
    rw [h, commutatorElement_one_right]
  have hfa_pow : (f a') ^ q = 1 := by
    rw [← map_pow, ha'_pow, map_one]
  set D : Subgroup J := Subgroup.zpowers (f a') with hD
  have hDcard : Nat.card D = q := by
    rw [hD, Nat.card_zpowers]
    exact orderOf_eq_prime hfa_pow hfa_ne
  set E0 : Subgroup J := ((CFSG.Open.pCoreOf 2 (B ⊔ T)).subgroupOf (Subgroup.normalizer (P : Set G))).map f with hE0
  have hconj : ∀ n : (Subgroup.normalizer (P : Set G)), (n : G) ∈ B → ∀ y ∈ E0, (f n)⁻¹ * y * f n ∈ E0 := by
    intro n hn y hy
    rw [hE0, Subgroup.mem_map] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    have hgK : (g : G) ∈ CFSG.Open.pCoreOf 2 (B ⊔ T) := Subgroup.mem_subgroupOf.mp hg
    have hmem : ((n⁻¹ * g * n : (Subgroup.normalizer (P : Set G))) : G) ∈ CFSG.Open.pCoreOf 2 (B ⊔ T) := by
      have := pCoreOf_conj_mem (p := 2) (H := B ⊔ T) (b := (n : G)) (k := (g : G))
        (le_sup_left (a := B) (b := T) hn) hgK
      simpa using this
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem f (by
      rw [Subgroup.mem_subgroupOf]; exact hmem)
  have hE0p : IsPGroup 2 E0 := by
    have hK2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (B ⊔ T)).subgroupOf (Subgroup.normalizer (P : Set G))) :=
      (pCoreOf_isPGroup (p := 2) (B ⊔ T)).of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm
    exact hK2.map f
  have hdX : ∀ y ∈ E0, (f a')⁻¹ * y * f a' ∈ E0 := hconj a' (hAB ha)
  have hDnorm : D ≤ Subgroup.normalizer (E0 : Set J) := by
    rw [hD, Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hconj a'⁻¹ (Subgroup.inv_mem _ (hAB ha)) _ hh
      simpa [map_inv, mul_assoc] using this
    · intro hh
      have := hdX _ hh
      simpa [mul_assoc] using this
  have hle : ⁅E0, D⁆ ≤ E0 := by
    rw [Subgroup.commutator_le]
    intro y hy z hz
    have hzN : z ∈ Subgroup.normalizer (E0 : Set J) := hDnorm hz
    have hzy : z * y⁻¹ * z⁻¹ ∈ E0 := (Subgroup.mem_normalizer_iff.mp hzN y⁻¹).mp (E0.inv_mem hy)
    rw [commutatorElement_def]
    have : y * z * y⁻¹ * z⁻¹ = y * (z * y⁻¹ * z⁻¹) := by group
    rw [this]
    exact E0.mul_mem hy hzy
  refine ⟨⁅E0, D⁆, D, ?_, ?_, hDcard, ?_, hle, ?_⟩
  · intro h
    have hm : ⁅f k', f a'⁆ ∈ ⁅E0, D⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hk))
        (Subgroup.mem_zpowers _)
    rw [h] at hm
    exact hcomm (Subgroup.mem_bot.mp hm)
  · exact hE0p.to_le hle
  · exact commutator_zpowers_eq_of_coprime_finite E0 hE0p hq.1 (by omega) hDcard hdX
  · rw [hD]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr (hAB ha)))

end CFSG.LocalAnalysis.RankThreeUC.Section5.CharacteristicPrimeCoreDetectingAction
