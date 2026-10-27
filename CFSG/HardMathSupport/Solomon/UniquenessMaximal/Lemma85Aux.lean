module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Vocab
public import CFSG.LocalAnalysis.GLTheoremB.BaseCase

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

namespace Lemma85Aux

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf' {A N : Subgroup G} (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem twoMod_iff [Finite G] {Y W : Subgroup G} (hYW : Y ≤ W)
    (hW : W ≤ Subgroup.normalizer (Y : Set G)) :
    (∃ n : ℕ, Nat.card W = Nat.card Y * 2 ^ n) ↔ ∀ w ∈ W, ∃ n : ℕ, w ^ 2 ^ n ∈ Y := by
  have hN : (Y.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYW).2 hW
  have hcardY : Nat.card (Y.subgroupOf W) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYW).toEquiv
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf W)
  rw [hcardY] at hcard
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨n, hn⟩ w hw
    have hq : Nat.card (↥W ⧸ Y.subgroupOf W) = 2 ^ n := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [← hcard, hn, mul_comm]
    refine ⟨n, ?_⟩
    have h1 := pow_card_eq_one' (G := ↥W ⧸ Y.subgroupOf W)
      (x := ((⟨w, hw⟩ : W) : ↥W ⧸ Y.subgroupOf W))
    rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro h
    have hp : IsPGroup 2 (↥W ⧸ Y.subgroupOf W) := by
      intro x
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn⟩ := h w.1 w.2
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hn
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    exact ⟨n, by rw [hcard, hn, mul_comm]⟩


section OTwoPrimeTwo

variable (X : Subgroup G)

theorem glaPPrimeCoreOf_le_self (p : ℕ) : GLAPPrimeCoreOf p X ≤ X :=
  Subgroup.map_subtype_le _

theorem oTwoPrimeTwo_le : oTwoPrimeTwo X ≤ X := Subgroup.map_subtype_le _

theorem glaPPrimeCoreOf_le_oTwoPrimeTwo : GLAPPrimeCoreOf 2 X ≤ oTwoPrimeTwo X := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore 2 ↥X) y ∈ CFSG.pCore 2 (↥X ⧸ GLAPPrimeCore 2 ↥X)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 2 ↥X) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  rw [h1]
  exact one_mem _

variable {X}

theorem mem_oTwoPrimeTwo {x : G} : x ∈ oTwoPrimeTwo X ↔
    ∃ h : X, (h : G) = x ∧ QuotientGroup.mk' (GLAPPrimeCore 2 ↥X) h ∈
      CFSG.pCore 2 (↥X ⧸ GLAPPrimeCore 2 ↥X) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, rfl, hh⟩
  · rintro ⟨h, rfl, hh⟩
    exact ⟨h, hh, rfl⟩

theorem exists_pow_mem_of_mem_oTwoPrimeTwo {r : G} (hr : r ∈ oTwoPrimeTwo X) :
    ∃ n : ℕ, r ^ 2 ^ n ∈ GLAPPrimeCoreOf 2 X := by
  obtain ⟨h, rfl, hh⟩ := mem_oTwoPrimeTwo.1 hr
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X ⧸ GLAPPrimeCore 2 ↥X)) ⟨_, hh⟩
  refine ⟨n, ⟨h ^ 2 ^ n, ?_, rfl⟩⟩
  have := congrArg Subtype.val hn
  simp only [OneMemClass.coe_one] at this
  show h ^ 2 ^ n ∈ GLAPPrimeCore 2 ↥X
  rw [← QuotientGroup.eq_one_iff]
  simpa using this

theorem le_oTwoPrimeTwo_of_pow {W : Subgroup G} (hWX : W ≤ X)
    (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (h : ∀ w ∈ W, ∃ n : ℕ, w ^ 2 ^ n ∈ GLAPPrimeCoreOf 2 X) : W ≤ oTwoPrimeTwo X := by
  have hN : (W.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).2 hXW
  let π := QuotientGroup.mk' (GLAPPrimeCore 2 ↥X)
  have hWb : ((W.subgroupOf X).map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 2 ((W.subgroupOf X).map π) := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    obtain ⟨n, hn⟩ := h w.1 (Subgroup.mem_subgroupOf.1 hw)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    show π w ^ 2 ^ n = 1
    rw [← map_pow]
    obtain ⟨y, hy, hyeq⟩ := hn
    have : y = w ^ 2 ^ n := Subtype.ext (by simpa using hyeq)
    rw [QuotientGroup.coe_mk', QuotientGroup.eq_one_iff]
    rw [← this]
    exact hy
  have hle : (W.subgroupOf X).map π ≤ CFSG.pCore 2 (↥X ⧸ GLAPPrimeCore 2 ↥X) :=
    le_sSup ⟨hWb, hp⟩
  intro w hw
  exact mem_oTwoPrimeTwo.2 ⟨⟨w, hWX hw⟩, rfl, hle ⟨_, Subgroup.mem_subgroupOf.2 hw, rfl⟩⟩

theorem le_normalizer_oTwoPrimeTwo [Finite G] : X ≤ Subgroup.normalizer (oTwoPrimeTwo X : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  obtain ⟨h, rfl, hh⟩ := mem_oTwoPrimeTwo.1 hr
  refine mem_oTwoPrimeTwo.2 ⟨⟨x, hx⟩ * h * ⟨x, hx⟩⁻¹, by simp, ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact (CFSG.pCore_normal (p := 2) (G := ↥X ⧸ GLAPPrimeCore 2 ↥X)).conj_mem _ hh _

theorem normalizer_le_glaPPrimeCoreOf [Finite G] {M : Subgroup G} (p : ℕ)
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) :
    M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := by
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨y', hy', rfl⟩ := hy
  let φ : MulAut ↥X := X.normalizerMonoidHom ⟨m, hMX hm⟩
  have hφ : (GLAPPrimeCore p ↥X).map φ.toMonoidHom = GLAPPrimeCore p ↥X :=
    CFSG.pPrimeCore_map_iso p φ
  refine ⟨φ y', ?_, ?_⟩
  · rw [← hφ]
    exact ⟨y', hy', rfl⟩
  · simp [φ]

theorem normalizer_le_oTwoPrimeTwo [Finite G] {M : Subgroup G}
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) :
    M ≤ Subgroup.normalizer (oTwoPrimeTwo X : Set G) := by
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  have hmX := hMX hm
  have hmX' := hMX (inv_mem hm)
  have hYm := normalizer_le_glaPPrimeCoreOf (X := X) 2 hMX hm
  let W : Subgroup G := (oTwoPrimeTwo X).map (MulAut.conj m).toMonoidHom
  have hmem : m * r * m⁻¹ ∈ W := ⟨r, hr, rfl⟩
  refine le_oTwoPrimeTwo_of_pow (W := W) ?_ ?_ ?_ hmem
  · rintro _ ⟨r', hr', rfl⟩
    have h1 : r' ∈ X := oTwoPrimeTwo_le X hr'
    have := (Subgroup.mem_normalizer_iff.1 hmX r').1 h1
    simpa using this
  · intro x hx
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨r', hr', rfl⟩ := hw
    have hx' : m⁻¹ * x * m ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 hmX' x).1 hx
      simpa [mul_assoc] using this
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oTwoPrimeTwo (X := X) hx') r').1 hr'
    refine ⟨_, this, ?_⟩
    simp [mul_assoc]
  · rintro _ ⟨r', hr', rfl⟩
    obtain ⟨n, hn⟩ := exists_pow_mem_of_mem_oTwoPrimeTwo hr'
    refine ⟨n, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 hYm _).1 hn
    show (m * r' * m⁻¹) ^ 2 ^ n ∈ _
    rw [conj_pow]
    simpa [mul_assoc] using this

theorem le_glaPPrimeCoreOf_of_normalizes {p : ℕ} (hp : p.Prime) {M W : Subgroup G}
    (hWM : W ≤ M) (hW : M ≤ Subgroup.normalizer (W : Set G)) (hcop : ¬ p ∣ Nat.card W) :
    W ≤ GLAPPrimeCoreOf p M := by
  have hN : (W.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWM).2 hW
  have hc : Nat.card (W.subgroupOf M) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv
  have hle : W.subgroupOf M ≤ GLAPPrimeCore p ↥M :=
    le_sSup ⟨hN, by rw [hc]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hcop⟩
  calc W = (W.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hWM).symm
    _ ≤ GLAPPrimeCoreOf p M := Subgroup.map_mono hle

theorem exists_card_oTwoPrimeTwo [Finite G] :
    ∃ a : ℕ, Nat.card (oTwoPrimeTwo X) = Nat.card (GLAPPrimeCoreOf 2 X) * 2 ^ a := by
  have hYR := glaPPrimeCoreOf_le_oTwoPrimeTwo X
  refine (twoMod_iff hYR ?_).2 fun r hr => exists_pow_mem_of_mem_oTwoPrimeTwo hr
  exact (oTwoPrimeTwo_le X).trans (le_normalizer_glaPPrimeCoreOf 2 X)

end OTwoPrimeTwo

section Sylow

variable [Finite G]

omit [Finite G] in
theorem exists_sylow_of_max {R Q : Subgroup G} (hQR : Q ≤ R) (hQ2 : IsPGroup 2 Q)
    (hmax : ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ R → IsPGroup 2 Q' → Q' = Q) :
    ∃ S : Sylow 2 ↥R, (S : Subgroup ↥R) = Q.subgroupOf R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQR2 : IsPGroup 2 (Q.subgroupOf R) :=
    IsPGroup.of_equiv hQ2 (Subgroup.subgroupOfEquivOfLe hQR).symm
  obtain ⟨S, hS⟩ := hQR2.exists_le_sylow
  refine ⟨S, ?_⟩
  have h1 : Q ≤ (S : Subgroup ↥R).map R.subtype := by
    intro x hx
    exact ⟨⟨x, hQR hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have h2 : (S : Subgroup ↥R).map R.subtype = Q :=
    hmax _ h1 (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
  rw [← h2]
  exact (Subgroup.comap_map_eq_self_of_injective R.subtype_injective _).symm

theorem exists_mem_mul_normalizer_of_sylow {R Q : Subgroup G} (hQR : Q ≤ R) (hQ2 : IsPGroup 2 Q)
    (hmax : ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ R → IsPGroup 2 Q' → Q' = Q) {m : G}
    (hm : m ∈ Subgroup.normalizer (R : Set G)) :
    ∃ g ∈ R, g⁻¹ * m ∈ Subgroup.normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmR : ∀ x ∈ R, m * x * m⁻¹ ∈ R := fun x hx => (Subgroup.mem_normalizer_iff.1 hm x).1 hx
  have hmR' : ∀ x ∈ R, m⁻¹ * x * m ∈ R := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hm) x).1 hx
    simpa using this
  let Q' : Subgroup G := Q.map (MulAut.conj m).toMonoidHom
  have hQ'R : Q' ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmR x (hQR hx)
  have hQ'2 : IsPGroup 2 Q' := hQ2.map _
  have hmax' : ∀ Q'' : Subgroup G, Q' ≤ Q'' → Q'' ≤ R → IsPGroup 2 Q'' → Q'' = Q' := by
    intro Q'' h1 h2 h3
    let Q3 : Subgroup G := Q''.map (MulAut.conj m⁻¹).toMonoidHom
    have hQ3 : Q = Q3 := by
      refine (hmax Q3 ?_ ?_ (h3.map _)).symm
      · intro x hx
        refine ⟨m * x * m⁻¹, h1 ⟨x, hx, rfl⟩, ?_⟩
        simp [mul_assoc]
      · rintro _ ⟨x, hx, rfl⟩
        simpa using hmR' x (h2 hx)
    refine le_antisymm (fun x hx => ?_) h1
    have : m⁻¹ * x * m ∈ Q3 := ⟨x, hx, by simp⟩
    rw [← hQ3] at this
    exact ⟨_, this, by simp [mul_assoc]⟩
  obtain ⟨P1, hP1⟩ := exists_sylow_of_max hQR hQ2 hmax
  obtain ⟨P2, hP2⟩ := exists_sylow_of_max hQ'R hQ'2 hmax'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥R) P1 P2
  refine ⟨g.1, g.2, ?_⟩
  rw [← inv_mem_iff, mul_inv_rev, inv_inv]
  refine Subgroup.mem_normalizer_fintype fun q hq => ?_
  have h1 : (⟨q, hQR hq⟩ : ↥R) ∈ (P1 : Subgroup ↥R) := by
    rw [hP1]; exact hq
  have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) (P1 : Subgroup ↥R) h1
  rw [← Sylow.coe_subgroup_smul, hg, hP2] at h2
  have h3 : g.1 * q * g.1⁻¹ ∈ Q' := by
    have := Subgroup.mem_subgroupOf.1 h2
    simpa using this
  obtain ⟨q0, hq0, hq0e⟩ := h3
  have : m⁻¹ * g.1 * q * (m⁻¹ * g.1)⁻¹ = q0 := by
    have e : m * q0 * m⁻¹ = g.1 * q * g.1⁻¹ := hq0e
    calc m⁻¹ * g.1 * q * (m⁻¹ * g.1)⁻¹ = m⁻¹ * (g.1 * q * g.1⁻¹) * m := by group
      _ = m⁻¹ * (m * q0 * m⁻¹) * m := by rw [e]
      _ = q0 := by group
  rw [this]; exact hq0

theorem oTwoPrimeTwo_eq_sup {X Q : Subgroup G} (hQR : Q ≤ oTwoPrimeTwo X) (hQ2 : IsPGroup 2 Q)
    (hmax : ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ oTwoPrimeTwo X → IsPGroup 2 Q' → Q' = Q) :
    oTwoPrimeTwo X = GLAPPrimeCoreOf 2 X ⊔ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_card_oTwoPrimeTwo (X := X)
  obtain ⟨S, hS⟩ := exists_sylow_of_max hQR hQ2 hmax
  have hYodd : ¬ 2 ∣ Nat.card (GLAPPrimeCoreOf 2 X) := not_dvd_card_glaPPrimeCoreOf Nat.prime_two X
  have hYpos : 0 < Nat.card (GLAPPrimeCoreOf 2 X) := Nat.card_pos
  have hQcard : Nat.card Q = 2 ^ a := by
    have h1 : Nat.card Q = Nat.card (Q.subgroupOf (oTwoPrimeTwo X)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv).symm
    have h2 := S.card_eq_multiplicity
    rw [hS] at h2
    rw [h1, h2, ha]
    congr 1
    rw [Nat.factorization_mul hYpos.ne' (by positivity)]
    simp [Nat.factorization_eq_zero_of_not_dvd hYodd, Nat.Prime.factorization_self Nat.prime_two]
  have hYN : oTwoPrimeTwo X ≤ Subgroup.normalizer (GLAPPrimeCoreOf 2 X : Set G) :=
    (oTwoPrimeTwo_le X).trans (le_normalizer_glaPPrimeCoreOf 2 X)
  have hprod := card_sup_mul_card_inf' (A := Q) (N := GLAPPrimeCoreOf 2 X) (hQR.trans hYN)
  have hinf : Q ⊓ GLAPPrimeCoreOf 2 X = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (Q ⊓ GLAPPrimeCoreOf 2 X : Subgroup G) ∣ 2 ^ a :=
      hQcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (Q ⊓ GLAPPrimeCoreOf 2 X : Subgroup G) ∣ Nat.card (GLAPPrimeCoreOf 2 X) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (2 ^ a) (Nat.card (GLAPPrimeCoreOf 2 X)) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hYodd).pow_left a
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [hinf, Subgroup.card_bot, mul_one, hQcard] at hprod
  symm
  rw [sup_comm]
  refine Subgroup.eq_of_le_of_card_ge (sup_le hQR (glaPPrimeCoreOf_le_oTwoPrimeTwo X)) ?_
  rw [hprod, ha, mul_comm]

theorem le_normalizer_sup_of_frattini {M₀ R Q A Z : Subgroup G} (hRM : R ≤ M₀)
    (hMR : M₀ ≤ Subgroup.normalizer (R : Set G)) (hQR : Q ≤ R) (hQ2 : IsPGroup 2 Q)
    (hmax : ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ R → IsPGroup 2 Q' → Q' = Q)
    (hRA : R ≤ A) (hMA : M₀ ≤ Subgroup.normalizer (A : Set G))
    (hZ : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Z : Set G)) :
    M₀ ≤ Subgroup.normalizer ((A ⊔ Z : Subgroup G) : Set G) := by
  intro m hm
  obtain ⟨g, hg, hk⟩ := exists_mem_mul_normalizer_of_sylow hQR hQ2 hmax (hMR hm)
  have hkM : g⁻¹ * m ∈ M₀ := M₀.mul_mem (M₀.inv_mem (hRM hg)) hm
  have hk' : g⁻¹ * m ∈ Subgroup.normalizer (A ⊔ Z : Subgroup G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A Z ⟨hMA hkM, hZ hk⟩
  have hg' : g ∈ Subgroup.normalizer (A ⊔ Z : Subgroup G) :=
    Subgroup.le_normalizer ((le_sup_left : A ≤ A ⊔ Z) (hRA hg))
  have := Subgroup.mul_mem _ hg' hk'
  simpa using this

theorem le_oTwoPrimeTwo_of_frattini {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M₀ Q Z : Subgroup G}
    (hQR : Q ≤ oTwoPrimeTwo (GLAPPrimeCoreOf p M₀)) (hQ2 : IsPGroup 2 Q)
    (hmax : ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ oTwoPrimeTwo (GLAPPrimeCoreOf p M₀) →
      IsPGroup 2 Q' → Q' = Q)
    (hZ2 : IsPGroup 2 Z) (hZM : Z ≤ M₀)
    (hZN : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Z : Set G)) :
    Z ≤ oTwoPrimeTwo (GLAPPrimeCoreOf p M₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := GLAPPrimeCoreOf p M₀ with hXdef
  have hXM : X ≤ M₀ := glaPPrimeCoreOf_le_self M₀ p
  have hMX : M₀ ≤ Subgroup.normalizer (X : Set G) := le_normalizer_glaPPrimeCoreOf p M₀
  have hMR : M₀ ≤ Subgroup.normalizer (oTwoPrimeTwo X : Set G) :=
    normalizer_le_oTwoPrimeTwo hMX
  have hRX : oTwoPrimeTwo X ≤ X := oTwoPrimeTwo_le X
  have hRM : oTwoPrimeTwo X ≤ M₀ := hRX.trans hXM
  obtain ⟨c, hc⟩ := hZ2.exists_card_eq
  have hZX : Z ≤ X := by
    have hN := le_normalizer_sup_of_frattini hRM hMR hQR hQ2 hmax hRX hMX hZN
    have hcard := card_sup_mul_card_inf' (A := Z) (N := X) (hZM.trans hMX)
    have hnd : ¬ p ∣ Nat.card (X ⊔ Z : Subgroup G) := by
      intro hd
      rw [sup_comm] at hd
      have h1 : p ∣ Nat.card Z * Nat.card X :=
        hcard ▸ Dvd.dvd.mul_right hd _
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
      · rw [hc] at h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact not_dvd_card_glaPPrimeCoreOf hp M₀ h
    exact le_sup_right.trans
      (le_glaPPrimeCoreOf_of_normalizes hp (sup_le hXM hZM) hN hnd)
  have hN2 := le_normalizer_sup_of_frattini hRM hMR hQR hQ2 hmax le_rfl hMR hZN
  have hW : (oTwoPrimeTwo X ⊔ Z) ≤ oTwoPrimeTwo X := by
    have hWX : oTwoPrimeTwo X ⊔ Z ≤ X := sup_le hRX hZX
    have hXW : X ≤ Subgroup.normalizer ((oTwoPrimeTwo X ⊔ Z : Subgroup G) : Set G) :=
      hXM.trans hN2
    have hYW : GLAPPrimeCoreOf 2 X ≤ oTwoPrimeTwo X ⊔ Z :=
      (glaPPrimeCoreOf_le_oTwoPrimeTwo X).trans le_sup_left
    have hWY : oTwoPrimeTwo X ⊔ Z ≤ Subgroup.normalizer (GLAPPrimeCoreOf 2 X : Set G) :=
      hWX.trans (le_normalizer_glaPPrimeCoreOf 2 X)
    refine le_oTwoPrimeTwo_of_pow hWX hXW ((twoMod_iff hYW hWY).1 ?_)
    obtain ⟨a, ha⟩ := exists_card_oTwoPrimeTwo (X := X)
    have hcard := card_sup_mul_card_inf' (A := Z) (N := oTwoPrimeTwo X) (hZM.trans hMR)
    rw [sup_comm, hc, ha] at hcard
    have hd : Nat.card (Z ⊓ oTwoPrimeTwo X : Subgroup G) ∣ 2 ^ c :=
      hc ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨e, he, hee⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    rw [hee] at hcard
    refine ⟨c + a - e, ?_⟩
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ e)
    have : c + a - e + e = c + a := Nat.sub_add_cancel (by omega)
    rw [hcard, mul_assoc, ← pow_add, this]
    ring
  exact le_sup_right.trans hW

end Sylow

section FourGroup

theorem inv_mul_conj_mem_zpowers {U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hcard : Nat.card U = 4) {z c : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U) (hcz : c * z * c⁻¹ = z) {u : G} (hu : u ∈ U) :
    u⁻¹ * (c * u * c⁻¹) ∈ Subgroup.zpowers z := by
  have hz2 : z ^ 2 = 1 := hU.2 z hzU
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hCcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hCU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).2 hzU
  have hcardCU : Nat.card ((Subgroup.zpowers z).subgroupOf U) = 2 := by
    rw [← hCcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
  have hidx : ((Subgroup.zpowers z).subgroupOf U).index = 2 := by
    have := Subgroup.card_mul_index ((Subgroup.zpowers z).subgroupOf U)
    rw [hcardCU, hcard] at this
    omega
  have hfix : ∀ x ∈ Subgroup.zpowers z, c * x * c⁻¹ = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← conj_zpow, hcz]
  have hiff : u ∈ Subgroup.zpowers z ↔ c * u * c⁻¹ ∈ Subgroup.zpowers z := by
    constructor
    · intro h
      rw [hfix u h]; exact h
    · intro h
      have h1 := hfix _ h
      have h2 : MulAut.conj c (MulAut.conj c u) = MulAut.conj c u := by
        simpa [MulAut.conj_apply] using h1
      have h3 := (MulAut.conj c).injective h2
      rw [← h3]; exact h
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨u⁻¹, U.inv_mem hu⟩)
    (b := ⟨c * u * c⁻¹, hcU u hu⟩)).2 (by
      show u⁻¹ ∈ Subgroup.zpowers z ↔ c * u * c⁻¹ ∈ Subgroup.zpowers z
      rw [inv_mem_iff]; exact hiff)
  exact h

theorem exists_mem_inf_centerOf [Finite G] {P U : Subgroup G} (hP : IsPGroup 2 P) (hUP : U ≤ P)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ z ∈ U, z ≠ 1 ∧ z ∈ centerOf P := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hN : (U.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).2 hPU
  have hne : U.subgroupOf P ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUP, h, Subgroup.map_bot]
  have := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 this
  refine ⟨(a.1 : G), Subgroup.mem_subgroupOf.1 a.2.1, ?_, ⟨a.1, a.2.2, rfl⟩⟩
  intro h
  apply ha
  apply Subtype.ext
  apply Subtype.ext
  exact h

end FourGroup

end Lemma85Aux

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
