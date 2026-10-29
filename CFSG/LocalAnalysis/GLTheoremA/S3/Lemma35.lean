module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma34
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.HardMathSupport.Solomon.Proving.LBBalanceUp
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux2
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S3

section Helpers

private theorem mem_glaPPrimeCoreOf' {p : ℕ} {X : Subgroup G} {y : G} :
    y ∈ GLAPPrimeCoreOf p X ↔ ∃ h : y ∈ X, (⟨y, h⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

private theorem mem_oPPrimeP' {p : ℕ} {X : Subgroup G} {y : G} :
    y ∈ oPPrimeP p X ↔ ∃ h : y ∈ X, QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, h⟩ ∈
      CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  unfold oPPrimeP
  simp [Subgroup.mem_map]

private theorem oPPrimeP_le' (p : ℕ) (X : Subgroup G) : oPPrimeP p X ≤ X :=
  Subgroup.map_subtype_le _

private theorem glaPPrimeCoreOf_le' (p : ℕ) (X : Subgroup G) : GLAPPrimeCoreOf p X ≤ X :=
  Subgroup.map_subtype_le _

private theorem glaPPrimeCoreOf_le_oPPrimeP' (p : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf p X ≤ oPPrimeP p X := by
  intro y hy
  obtain ⟨h, hN⟩ := mem_glaPPrimeCoreOf'.1 hy
  refine mem_oPPrimeP'.2 ⟨h, ?_⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, h⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 hN
  rw [h1]
  exact Subgroup.one_mem _

private theorem conj_mem_glaPPrimeCoreOf' {p : ℕ} {X : Subgroup G} {g y : G} (hg : g ∈ X)
    (hy : y ∈ GLAPPrimeCoreOf p X) : g * y * g⁻¹ ∈ GLAPPrimeCoreOf p X := by
  obtain ⟨hyX, hy'⟩ := mem_glaPPrimeCoreOf'.1 hy
  refine mem_glaPPrimeCoreOf'.2 ⟨X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg), ?_⟩
  have e : (⟨g * y * g⁻¹, X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg)⟩ : ↥X) =
      ⟨g, hg⟩ * ⟨y, hyX⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [e]
  exact (GLAPPrimeCore.normal p ↥X).conj_mem _ hy' _

private theorem le_normalizer_glaPPrimeCoreOf' (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_glaPPrimeCoreOf' hg hx
  · intro hx
    have h := conj_mem_glaPPrimeCoreOf' (X.inv_mem hg) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h

private theorem le_normalizer_oPPrimeP' (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oPPrimeP p X : Set G) := by
  have key : ∀ g ∈ X, ∀ y ∈ oPPrimeP p X, g * y * g⁻¹ ∈ oPPrimeP p X := by
    intro g hg y hy
    obtain ⟨hyX, hy'⟩ := mem_oPPrimeP'.1 hy
    refine mem_oPPrimeP'.2 ⟨X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg), ?_⟩
    have e : (⟨g * y * g⁻¹, X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg)⟩ : ↥X) =
        ⟨g, hg⟩ * ⟨y, hyX⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (CFSG.pCore_normal (G := ↥X ⧸ GLAPPrimeCore p ↥X) (p := p)).conj_mem _ hy' _
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨key g hg y, fun h => by simpa [mul_assoc] using key g⁻¹ (X.inv_mem hg) _ h⟩

private theorem eq_one_of_pow_mem' {p : ℕ} {Y : Subgroup G} {x : G} {N : ℕ} (hx : x ∈ Y)
    (hcop : Nat.Coprime p (Nat.card Y)) (hpow : x ^ (p ^ N) = 1) : x = 1 := by
  have h1 : orderOf x ∣ p ^ N := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf x ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hx
  have h3 : Nat.Coprime (orderOf x) (Nat.card Y) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left N hcop)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2)

private theorem disjoint_of_coprime' {p : ℕ} {Y P : Subgroup G} (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card Y)) : Disjoint Y P := by
  rw [Subgroup.disjoint_def]
  intro x hxY hxP
  obtain ⟨n, hn⟩ := hP ⟨x, hxP⟩
  exact eq_one_of_pow_mem' hxY hcop (by simpa using congrArg Subtype.val hn)

private theorem exists_pow_mem' {p : ℕ} (hp : p.Prime) (K : Subgroup G) {x : G}
    (hx : x ∈ oPPrimeP p K) : ∃ n : ℕ, x ^ (p ^ n) ∈ GLAPPrimeCoreOf p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hxK, hxQ⟩ := mem_oPPrimeP'.1 hx
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥K ⧸ GLAPPrimeCore p ↥K)) ⟨_, hxQ⟩
  refine ⟨n, mem_glaPPrimeCoreOf'.2 ⟨K.pow_mem hxK _, ?_⟩⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨x, hxK⟩ ^ (p ^ n)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  exact (QuotientGroup.eq_one_iff _).1 h1

private theorem card_oPPrimeP_eq' {p : ℕ} (hp : p.Prime) (K : Subgroup G) :
    ∃ a : ℕ, Nat.card (oPPrimeP p K) = Nat.card (GLAPPrimeCoreOf p K) * p ^ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hYN : GLAPPrimeCoreOf p K ≤ oPPrimeP p K := glaPPrimeCoreOf_le_oPPrimeP' p K
  haveI hYnorm : ((GLAPPrimeCoreOf p K).subgroupOf (oPPrimeP p K)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact conj_mem_glaPPrimeCoreOf' (oPPrimeP_le' p K g.2) hn⟩
  have hqp : IsPGroup p (↥(oPPrimeP p K) ⧸ (GLAPPrimeCoreOf p K).subgroupOf (oPPrimeP p K)) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨n, hn⟩ := exists_pow_mem' hp K x.2
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hn
  obtain ⟨a, ha⟩ := hqp.exists_card_eq
  refine ⟨a, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((GLAPPrimeCoreOf p K).subgroupOf (oPPrimeP p K))
  have h2 : Nat.card ↥((GLAPPrimeCoreOf p K).subgroupOf (oPPrimeP p K)) =
      Nat.card ↥(GLAPPrimeCoreOf p K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv
  rw [ha, h2] at h1
  rw [h1, mul_comm]

private theorem pCore_self_centralizing' {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (hlayer : GLAPLayer p K = ⊥) (w : ↥K ⧸ GLAPPrimeCore p ↥K)
    (hw : ∀ z ∈ CFSG.pCore p (↥K ⧸ GLAPPrimeCore p ↥K), w * z = z * w) :
    w ∈ CFSG.pCore p (↥K ⧸ GLAPPrimeCore p ↥K) := by
  have htop : GLAPLayer p (⊤ : Subgroup ↥K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := CFSG.HardMathSupport.Solomon.Proving.lbUp_layer_top_le_comap hp K hx
    rw [hlayer, Subgroup.mem_comap, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  have hc := GL83.hasPrimeConstraint_of_glaPLayer_eq_bot (X := ↥K) hp htop
  unfold CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint at hc
  obtain ⟨N, hNn, hNp, hcent⟩ := hc
  have hNle : N ≤ CFSG.pCore p (↥K ⧸ GLAPPrimeCore p ↥K) := le_sSup ⟨hNn, hNp⟩
  have hwC : w ∈ Subgroup.centralizer
      (N : Set (↥K ⧸ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore p)) :=
    Subgroup.mem_centralizer_iff.2 fun z hz => (hw z (hNle hz)).symm
  exact hNle (hcent hwC)

private theorem le_normalizer_of_commutator_eq' {Q V : Subgroup G} (h : ⁅Q, V⁆ = Q) :
    V ≤ Subgroup.normalizer (Q : Set G) := by
  have key : ∀ v ∈ V, ∀ k ∈ Q, v * k⁻¹ * v⁻¹ ∈ Q := by
    intro v hv k hk
    have hc : ⁅k, v⁆ ∈ Q := by
      have := Subgroup.commutator_mem_commutator hk hv
      rwa [h] at this
    have e : k⁻¹ * ⁅k, v⁆ = v * k⁻¹ * v⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [← e]
    exact Q.mul_mem (Q.inv_mem hk) hc
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := key v hv x⁻¹ (Q.inv_mem hx)
    rwa [inv_inv] at h1
  · intro hx
    have h1 := key v⁻¹ (V.inv_mem hv) _ hx
    have e2 : v⁻¹ * (v * x * v⁻¹)⁻¹ * v⁻¹⁻¹ = x⁻¹ := by group
    rw [e2] at h1
    simpa using Q.inv_mem h1

private theorem le_normalizer_of_centralizes' {E Q : Subgroup G}
    (h : ∀ q ∈ Q, ∀ e ∈ E, e * q = q * e) : Q ≤ Subgroup.normalizer (E : Set G) := by
  have hconj : ∀ q ∈ Q, ∀ e ∈ E, q * e * q⁻¹ = e := fun q hq e he => by
    rw [← h q hq e he]
    group
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hconj q hq x hx]
    exact hx
  · intro hx
    have h1 := hconj q⁻¹ (Q.inv_mem hq) _ hx
    have e2 : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
    rw [e2] at h1
    rw [h1]
    exact hx

end Helpers

theorem exists_faithful_invariant_sylow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E V : Subgroup G}
    (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥) (hV : IsPGroup 2 V)
    (hVK : V ≤ Subgroup.centralizer (E : Set G))
    (hlayer : GLAPLayer p (Subgroup.centralizer (E : Set G)) = ⊥)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (E : Set G))))) :
    ∃ P : Subgroup G, IsPGroup p P ∧ E ≤ P ∧ P ≤ Subgroup.centralizer (E : Set G) ∧
      V ≤ Subgroup.normalizer (P : Set G) ∧ ∀ v ∈ V, (∀ y ∈ P, v * y = y * v) → v = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = Subgroup.centralizer (E : Set G) := ⟨_, rfl⟩
  rw [← hK] at hVK hlayer hodd
  rw [← hK]
  have hcentral : ∀ k ∈ K, ∀ e ∈ E, e * k = k * e := fun k hk e he => by
    rw [hK] at hk
    exact Subgroup.mem_centralizer_iff.1 hk e he
  have hEK : E ≤ K := fun e he => by
    rw [hK]
    exact Subgroup.mem_centralizer_iff.2 fun h hh => isElemAbelian_commute hE hh he
  have hEnorm : (E.subgroupOf K).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have e : (g : G) * (x : G) * (g : G)⁻¹ = (x : G) := by
        rw [← hcentral (g : G) g.2 (x : G) hx]
        group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      exact hx⟩
  have hE' : IsPGroup p (E.subgroupOf K) := by
    intro g
    obtain ⟨n, hn⟩ := isPGroup_of_isElemAbelian hE ⟨(g : G), Subgroup.mem_subgroupOf.1 g.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hEN₀ : E ≤ oPPrimeP p K := by
    intro e he
    have heK : e ∈ K := hEK he
    refine mem_oPPrimeP'.2 ⟨heK, ?_⟩
    have hWn : ((E.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K))).Normal :=
      Subgroup.Normal.map hEnorm _ (QuotientGroup.mk'_surjective _)
    have hWp : IsPGroup p ↥((E.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K))) :=
      IsPGroup.map hE' _
    have hWle : (E.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) ≤
        CFSG.pCore p (↥K ⧸ GLAPPrimeCore p ↥K) := le_sSup ⟨hWn, hWp⟩
    exact hWle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 he))
  obtain ⟨a, ha⟩ := card_oPPrimeP_eq' hp K
  have hYcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p K)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp K
  have hNodd : Odd (Nat.card (oPPrimeP p K)) := by
    rw [ha]
    exact hodd.mul (hp.odd_of_ne_two hp2).pow
  have hcop2 : Nat.Coprime 2 (Nat.card (oPPrimeP p K)) := Nat.coprime_two_left.2 hNodd
  have hpdvd : p ∣ Nat.card (oPPrimeP p K) := by
    obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
    have h1 : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot E).2 hE1
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [hj, pow_zero] at h1
      exact lt_irrefl 1 h1
    have hpE : p ∣ Nat.card E := by
      rw [hj]
      exact dvd_pow_self p hj0
    exact hpE.trans (Subgroup.card_dvd_of_le hEN₀)
  have hVN₀ : V ≤ Subgroup.normalizer (oPPrimeP p K : Set G) :=
    hVK.trans (le_normalizer_oPPrimeP' p K)
  obtain ⟨P, hPN₀, hPp, -, hVP, hPcard⟩ :=
    S3.exists_invariant_sylow Nat.prime_two hp hV hVN₀ hcop2 hpdvd
  have hPK : P ≤ K := hPN₀.trans (oPPrimeP_le' p K)
  have hPY : P ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    hPK.trans (le_normalizer_glaPPrimeCoreOf' p K)
  have hYdisj : Disjoint (GLAPPrimeCoreOf p K) P := disjoint_of_coprime' hPp hYcop
  have hcardP : Nat.card P = p ^ a := by
    rw [hPcard, ha]
    congr 1
    have hY0 : Nat.card (GLAPPrimeCoreOf p K) ≠ 0 := Nat.card_pos.ne'
    have hpa : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
    rw [Nat.factorization_mul hY0 hpa, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization_self hp,
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hYcop),
      smul_eq_mul, mul_one, zero_add]
  have hcardYP := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (GLAPPrimeCoreOf p K) P hPY hYdisj
  have hYP : GLAPPrimeCoreOf p K ⊔ P = oPPrimeP p K :=
    Subgroup.eq_of_le_of_card_ge (sup_le (glaPPrimeCoreOf_le_oPPrimeP' p K) hPN₀)
      (le_of_eq (by rw [hcardYP, hcardP, ha]))
  have hPYN : P ⊔ GLAPPrimeCoreOf p K = oPPrimeP p K := by
    rw [sup_comm]
    exact hYP
  have hdecomp : ∀ x ∈ oPPrimeP p K, ∃ a' ∈ P, ∃ m ∈ GLAPPrimeCoreOf p K, x = a' * m := by
    intro x hx
    have hxm : x ∈ ((P ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G) := by
      rw [hPYN]
      exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P _ hPY] at hxm
    obtain ⟨a', ha', m, hm, hxam⟩ := Set.mem_mul.1 hxm
    exact ⟨a', ha', m, hm, hxam.symm⟩
  have hEP : E ≤ P := by
    intro e he
    obtain ⟨a', ha', m, hm, hem⟩ := hdecomp e (hEN₀ he)
    have hca : Commute a' e := (hcentral a' (hPK ha') e he).symm
    have hcaI : Commute a'⁻¹ e := hca.inv_left
    obtain ⟨n₁, hn₁⟩ := hPp ⟨a', ha'⟩
    obtain ⟨n₂, hn₂⟩ := isPGroup_of_isElemAbelian hE ⟨e, he⟩
    have hn₁' : a' ^ (p ^ n₁) = 1 := by simpa using congrArg Subtype.val hn₁
    have hn₂' : e ^ (p ^ n₂) = 1 := by simpa using congrArg Subtype.val hn₂
    have ha1 : a' ^ (p ^ (n₁ + n₂)) = 1 := by
      rw [pow_add, pow_mul, hn₁', one_pow]
    have he1 : e ^ (p ^ (n₁ + n₂)) = 1 := by
      rw [add_comm, pow_add, pow_mul, hn₂', one_pow]
    have hm' : m = a'⁻¹ * e := by
      rw [hem]
      group
    have hmpow : m ^ (p ^ (n₁ + n₂)) = 1 := by
      rw [hm', hcaI.mul_pow, inv_pow, ha1, he1]
      simp
    have hm1 : m = 1 := eq_one_of_pow_mem' hm hYcop hmpow
    rw [hem, hm1, mul_one]
    exact ha'
  refine ⟨P, hPp, hEP, hPK, hVP, ?_⟩
  intro v hv hvP
  have hvK : v ∈ K := hVK hv
  have hw : ∀ z ∈ CFSG.pCore p (↥K ⧸ GLAPPrimeCore p ↥K),
      QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨v, hvK⟩ : ↥K) * z =
        z * QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨v, hvK⟩ : ↥K) := by
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥K) z
    have hxN : (x : G) ∈ oPPrimeP p K := mem_oPPrimeP'.2 ⟨x.2, by simpa using hz⟩
    obtain ⟨a', ha', m, hm, hxam⟩ := hdecomp x hxN
    have ha'K : a' ∈ K := hPK ha'
    have hmK : m ∈ K := glaPPrimeCoreOf_le' p K hm
    have hmone : QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨m, hmK⟩ : ↥K) = 1 := by
      obtain ⟨_, hm'⟩ := mem_glaPPrimeCoreOf'.1 hm
      exact (QuotientGroup.eq_one_iff _).2 hm'
    have hxeq : QuotientGroup.mk' (GLAPPrimeCore p ↥K) x =
        QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨a', ha'K⟩ : ↥K) := by
      have hx' : x = (⟨a', ha'K⟩ : ↥K) * ⟨m, hmK⟩ := Subtype.ext hxam
      rw [hx', map_mul, hmone, mul_one]
    rw [hxeq, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvP a' ha')
  have hwQ := pCore_self_centralizing' hp hlayer _ hw
  have hvN : v ∈ oPPrimeP p K := mem_oPPrimeP'.2 ⟨hvK, hwQ⟩
  obtain ⟨n, hn⟩ := hV ⟨v, hv⟩
  exact eq_one_of_pow_mem' hvN hcop2 (by simpa using congrArg Subtype.val hn)

theorem dihedral_contra (hDih : DihedralUsed) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B E V P : Subgroup G} (hB : GLAIsBmax p B) (hEB : E ≤ B) {k : ℕ}
    (hk : Nat.card E * p ^ k = Nat.card B) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 2 ^ (k + 2))
    (hVK : V ≤ Subgroup.centralizer (E : Set G)) (hP : IsPGroup p P) (hEP : E ≤ P)
    (hPK : P ≤ Subgroup.centralizer (E : Set G)) (hVP : V ≤ Subgroup.normalizer (P : Set G))
    (hfaith : ∀ v ∈ V, (∀ y ∈ P, v * y = y * v) → v = 1) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfaithD : ∀ u ∈ V, P ≤ Subgroup.centralizer ({u} : Set G) → u = 1 := fun u hu hPu =>
    hfaith u hu fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (hPu hy)).symm
  obtain ⟨u, huV, hu1, Q₁, hQ₁P, hQ₁el, hQ₁card, hQ₁C, hQ₁comm⟩ :=
    hDih G p hp hp2 P V (k + 1) hP hV (by rw [hVcard]) hVP hfaithD
  have hEel : IsElemAbelian p E := isElemAbelian_mono hB.1 hEB
  have hVE : ∀ v ∈ V, ∀ e ∈ E, e * v = v * e := fun v hv e he =>
    Subgroup.mem_centralizer_iff.1 (hVK hv) e he
  have hQE : ∀ q ∈ Q₁, ∀ e ∈ E, e * q = q * e := fun q hq e he =>
    Subgroup.mem_centralizer_iff.1 (hPK (hQ₁P hq)) e he
  haveI : IsMulCommutative Q₁ := hQ₁el.1
  have hcop2 : Nat.Coprime 2 (Nat.card Q₁) := by
    rw [hQ₁card]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hfit := CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35.commutator_inf_centralizer_eq_bot
    Nat.prime_two (isPGroup_of_isElemAbelian hV) (le_normalizer_of_commutator_eq' hQ₁comm) hcop2
  rw [hQ₁comm] at hfit
  have hEQ : E ⊓ Q₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun v hv => (hVE v hv x hx.1).symm
    have hx' : x ∈ Q₁ ⊓ Subgroup.centralizer (V : Set G) := ⟨hx.2, hxC⟩
    rw [hfit] at hx'
    exact hx'
  have hQN : Q₁ ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_centralizes' hQE
  have hcardEQ : Nat.card (E ⊔ Q₁ : Subgroup G) = Nat.card E * Nat.card Q₁ :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E Q₁ hQN
      (disjoint_iff.2 hEQ)
  have hEQel : IsElemAbelian p (E ⊔ Q₁ : Subgroup G) :=
    isElemAbelian_sup_of_commute hEel hQ₁el
      (fun e he => Subgroup.mem_centralizer_iff.2 fun q hq => (hQE q hq e he).symm)
  have hEQC : E ⊔ Q₁ ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.2 ?_) hQ₁C
    exact hVE u huV e he
  have hcz : ∀ x : G, x * u = u * x → x ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    intro x hx
    have hcomm : Commute x u := hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
      have hc : x * u ^ n = u ^ n * x := (hcomm.zpow_right n).eq
      rw [hc]
      group
    · intro hh
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hh
      refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
      have hc2 : x⁻¹ * u ^ n = u ^ n * x⁻¹ := (hcomm.zpow_right n).inv_left.eq
      have hh' : h = x⁻¹ * (x * h * x⁻¹) * x := by group
      rw [← hn] at hh'
      rw [hh', hc2]
      group
  have hEQN : E ⊔ Q₁ ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
    fun x hx => hcz x (Subgroup.mem_centralizer_singleton_iff.1 (hEQC hx))
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono hV (Subgroup.zpowers_le.2 huV))
  have huz : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
  have hbound := card_le_pow_glaTwoLocalRank hp hEQel huz hu2 hEQN
  rw [hcardEQ, hQ₁card] at hbound
  have h1 : Nat.card E * p ^ (k + 1) = Nat.card B * p := by
    rw [pow_succ, ← mul_assoc, hk]
  rw [h1, hB.2.1] at hbound
  have hpm : 0 < p ^ GLATwoLocalRank p G := pow_pos hp.pos _
  nlinarith [hp.two_le]

theorem km22 (hDih : DihedralUsed) {p : ℕ} (hc : S3Ctx G p) {B : Subgroup G}
    (hS : Star3 G p B)
    (hcons : ∀ E : Subgroup G, E ≤ B → Nat.card B ≤ Nat.card E * p ^ 2 →
      GLAPLayer p (Subgroup.centralizer (E : Set G)) = ⊥)
    {E : Subgroup G} (hEB : E ≤ B) {k : ℕ} (hk : k ≤ 2) (hcard : Nat.card E * p ^ k = Nat.card B) :
    ∀ V : Subgroup G, V ≤ Subgroup.centralizer (E : Set G) → IsElemAbelian 2 V →
      Nat.card V ≤ 2 ^ (k + 1) := by
  intro V hVK hVel
  by_contra hlt
  push Not at hlt
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_two hVel
  have hdvd : 2 ^ (k + 2) ∣ Nat.card V := by
    rw [ha] at hlt ⊢
    have : k + 1 < a := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨V', hV'V, hV'card⟩ := S3.exists_card_pow_le Nat.prime_two hVel hdvd
  have hV'el : IsElemAbelian 2 V' := isElemAbelian_mono hVel hV'V
  have hB4 : p ^ 4 ≤ Nat.card B := by
    rw [hS.bmax.2.1]
    exact Nat.pow_le_pow_right hp.pos hc.rank_ge
  have hEne : E ≠ ⊥ := by
    rintro rfl
    have h1 : p ^ k = Nat.card B := by simpa using hcard
    have h2 : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos hk
    have h3 : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hlayer := hcons E hEB (by
    rw [← hcard]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos hk))
  have hodd := lemma34_ii hc hS hEB hEne
  obtain ⟨P, hP, hEP, hPK, hVP, hfaith⟩ :=
    S3.exists_faithful_invariant_sylow hp hp2 (isElemAbelian_mono hS.bmax.1 hEB) hEne
      (isPGroup_of_isElemAbelian hV'el) (hV'V.trans hVK) hlayer hodd
  exact S3.dihedral_contra hDih hp hp2 hS.bmax hEB hcard hV'el hV'card (hV'V.trans hVK) hP hEP
    hPK hVP hfaith

end S3

theorem lemma35 {p : ℕ} (hKM : KMUsedAt) (hDih : DihedralUsed) (hc : S3Ctx G p)
    {B : Subgroup G} (hS : Star3 G p B) :
    ∃ E : Subgroup G, E ≤ B ∧ Nat.card B ≤ Nat.card E * p ^ 2 ∧ NotPConstr p E := by
  by_contra hnot
  have hp := hc.prime
  have hp2 := hc.odd
  have hcons : ∀ E : Subgroup G, E ≤ B → Nat.card B ≤ Nat.card E * p ^ 2 →
      GLAPLayer p (Subgroup.centralizer (E : Set G)) = ⊥ := fun E hEB hcard => by
    by_contra h
    exact hnot ⟨E, hEB, hcard, h⟩
  obtain ⟨N, hN, hBN⟩ := GLAIsBmax.exists_maxTwoLocal hS.bmax
  have hT2 : IsPGroup 2 ↥(pCoreOf 2 N) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hBT : B ≤ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) :=
    hBN.trans (le_normalizer_pCoreOf 2 N)
  have hCB : ∀ a ∈ B, (∀ t ∈ pCoreOf 2 N, a * t = t * a) → a = 1 := by
    intro a ha hat
    have h := GL83.inf_centralizer_eq_bot_of_pCoreOf hp hp2 hc.charTwo hN.1 hBN hS.bmax.1
    have : a ∈ B ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) :=
      ⟨ha, Subgroup.mem_centralizer_iff.2 fun t ht => (hat t ht).symm⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have h3 : p ^ 3 ≤ Nat.card B := by
    rw [hS.bmax.2.1]
    exact Nat.pow_le_pow_right hp.pos (by have := hc.rank_ge; omega)
  have hH1 : ∀ E : Subgroup G, E ≤ B → ∀ k : ℕ, k ≤ 2 → Nat.card E * p ^ k = Nat.card B →
      ∀ V : Subgroup G, V ≤ pCoreOf 2 N ⊓ Subgroup.centralizer (E : Set G) → IsElemAbelian 2 V →
        Nat.card V ≤ 2 ^ (k + 1) := fun E hEB k hk hcard V hV hVel =>
    S3.km22 hDih hc hS hcons hEB hk hcard V (hV.trans inf_le_right) hVel
  obtain ⟨hsymp, hp3⟩ := hKM G p hp hp2 B (pCoreOf 2 N) hS.bmax.1 hT2 hBT hCB h3 hH1
  exact hc.noGF2 hp3 ⟨N, hN, hsymp, B, hp3 ▸ hS.bmax, hBN⟩

end CFSG.LocalAnalysis.GLTheoremA
