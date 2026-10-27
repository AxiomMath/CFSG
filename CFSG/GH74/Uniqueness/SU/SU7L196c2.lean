module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Adapters.Involutions
public import CFSG.GH74.Uniqueness.SU.SU7L194
public import CFSG.GH74.Uniqueness.SU.SU9CM

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG
  CFSG.GH74.Uniqueness.SU.SU9

namespace L196c

section Generic

theorem exists_mem_normalizer_sub {X : Type*} [Group X] [Finite X] {A' P : Subgroup X}
    (hP : IsPGroup 2 P) (hAP : A' ≤ P) (hne : A' ≠ P) :
    ∃ n ∈ P, n ∈ normalizer (A' : Set X) ∧ n ∉ A' := by
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  have hlt : A'.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm hAP
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ A'.subgroupOf P := by rw [h]; trivial
    exact this
  have h1 := hnc _ hlt
  obtain ⟨n, hnN, hnS⟩ := IsConcreteLE.exists_of_lt h1
  refine ⟨(n : X), n.2, ?_, fun h => hnS (by rw [Subgroup.mem_subgroupOf]; exact h)⟩
  rw [mem_normalizer_iff] at hnN ⊢
  intro y
  by_cases hy : y ∈ P
  · have := hnN ⟨y, hy⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · have hy' : (n : X) * y * (n : X)⁻¹ ∉ P := fun hmem => hy (by
      have := mul_mem (mul_mem (inv_mem n.2) hmem) n.2
      simpa [mul_assoc] using this)
    constructor
    · intro hyA
      exact absurd (hAP hyA) hy
    · intro hA
      exact absurd (hAP hA) hy'

theorem exists_sylow_eq_of_normalizer {X : Type*} [Group X] [Finite X] {A' : Subgroup X}
    (hA' : IsPGroup 2 A')
    (hN : ∀ n ∈ normalizer (A' : Set X), (∃ k : ℕ, n ^ (2 ^ k) = 1) → n ∈ A') :
    ∃ P : Sylow 2 X, (P : Subgroup X) = A' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hAP⟩ := hA'.exists_le_sylow
  refine ⟨P, ?_⟩
  by_contra hne
  obtain ⟨n, hnP, hnN, hnA⟩ := exists_mem_normalizer_sub P.isPGroup' hAP (fun h => hne h.symm)
  apply hnA
  apply hN n hnN
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨n, hnP⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_of_cube_mem_of_two_pow {G : Type*} [Group G] {A : Subgroup G} {n : G}
    (h3 : n ^ 3 ∈ A) {k : ℕ} (hk : n ^ (2 ^ k) = 1) : n ∈ A := by
  have hcop : IsCoprime (3 : ℤ) ((2 : ℤ) ^ k) := by
    have : Nat.Coprime 3 (2 ^ k) := (Nat.Coprime.pow_right k (by norm_num))
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  obtain ⟨s, t, hst⟩ := hcop
  have h1 : n = (n ^ 3) ^ s * (n ^ (2 ^ k)) ^ t := by
    rw [hk, one_zpow, mul_one, ← zpow_natCast, ← zpow_mul]
    have : n ^ ((3 : ℕ) * s : ℤ) = n := by
      have e : (3 : ℤ) * s = 1 - t * 2 ^ k := by linarith
      rw [Nat.cast_ofNat, e, zpow_sub, zpow_one]
      have : n ^ (t * 2 ^ k : ℤ) = 1 := by
        rw [mul_comm, zpow_mul]
        have : n ^ (2 ^ k : ℤ) = 1 := by exact_mod_cast hk
        rw [this, one_zpow]
      rw [this]; simp
    exact this.symm
  rw [h1]
  exact A.mul_mem (A.zpow_mem h3 s) (by rw [hk, one_zpow]; exact A.one_mem)

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem normalizer_le_M_of_le_A (hc : Ctx19 S U M V x z A B R) {E : Subgroup G} {n : ℕ}
    (hEA : E ≤ A) (hE : IsE n E) (hn : 2 ≤ n) : normalizer (E : Set G) ≤ M := by
  refine Claim.normalizer_le_M_of_isE hc.hyp (E := E) (F := A) (n := n) (m := 4)
    (hEA.trans (Cfg.A_le_S hc)) hE hn ?_ (Cfg.isE_A hc) (by norm_num)
  intro y hy
  refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 (fun e he => ?_), Cfg.A_le_S hc hy⟩
  exact Cfg.A_comm hc e (hEA he) y hy

theorem exists_w (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) (hMcard : Nat.card M = 1152)
    {a : G} (ha : a ∈ A) (haU : a ∉ U) :
    ∃ w : G, w ∈ M ∧ w * a = a * w ∧ orderOf w = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h48 := CM.card_cent hc h194M hTM' hMcard ha haU
  obtain ⟨c, hc3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer ({a} : Set G) ⊓ M)) 3
    (by rw [h48]; norm_num)
  refine ⟨(c : G), c.2.2, ?_, ?_⟩
  · exact mem_centralizer_singleton_iff.1 c.2.1
  · rw [Subgroup.orderOf_coe]; exact hc3

theorem two_elt_mem_A (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) (hMcard : Nat.card M = 1152)
    {a : G} (ha : a ∈ A) (haU : a ∉ U) {n : G} (hnM : n ∈ M) (hna : n * a = a * n) {k : ℕ}
    (hk : n ^ (2 ^ k) = 1) : n ∈ A := by
  classical
  set Cc : Subgroup G := centralizer ({a} : Set G) ⊓ M with hCc
  have hAC : A ≤ Cc := fun y hy =>
    Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (Cfg.A_comm hc y hy a ha),
      Cfg.S_le_M hc (Cfg.A_le_S hc hy)⟩
  have hnC : n ∈ Cc := Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hna, hnM⟩
  have hnorm : (A.subgroupOf Cc).Normal := ⟨fun y hy g => by
    have hgN : (g : G) ∈ normalizer (A : Set G) := Cfg.mem_normalizer_of_conjSub_eq
      (CM.conjSub_A_of_cent hc hTM' ha haU g.2.2 (mem_centralizer_singleton_iff.1 g.2.1))
    exact (mem_normalizer_iff.1 hgN y).1 hy⟩
  have hcard : Nat.card ↥(A.subgroupOf Cc) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv]; exact Cfg.card_A hc
  have hCcard : Nat.card ↥Cc = 48 := CM.card_cent hc h194M hTM' hMcard ha haU
  have hindex : (A.subgroupOf Cc).index = 3 := by
    have h := (A.subgroupOf Cc).card_mul_index
    rw [hcard, hCcard] at h
    omega
  have h3 := Subgroup.pow_index_mem (A.subgroupOf Cc) (⟨n, hnC⟩ : ↥Cc)
  rw [hindex] at h3
  exact mem_of_cube_mem_of_two_pow h3 hk

theorem exists_sylow_A (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) (hMcard : Nat.card M = 1152)
    {a : G} (ha : a ∈ A) (haU : a ∉ U) :
    ∃ P : Sylow 2 ↥(centralizer ({a} : Set G)),
      (P : Subgroup ↥(centralizer ({a} : Set G))) = A.subgroupOf (centralizer ({a} : Set G)) := by
  classical
  have hAp : IsPGroup 2 ↥A := S.isPGroup'.to_le (Cfg.A_le_S hc)
  refine exists_sylow_eq_of_normalizer (Bar.isPGroup_subgroupOf hAp _) ?_
  rintro n hn ⟨k, hk⟩
  have hnN : (n : G) ∈ normalizer (A : Set G) := by
    apply Gen.mem_normalizer_of_conj_le
    intro y hy
    have hyK : y ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.2 (Cfg.A_comm hc y hy a ha)
    have := (mem_normalizer_iff.1 hn ⟨y, hyK⟩).1 hy
    exact this
  have hnM : (n : G) ∈ M := normalizer_le_M_of_le_A hc le_rfl (Cfg.isE_A hc) (by norm_num) hnN
  have hna : (n : G) * a = a * n := mem_centralizer_singleton_iff.1 n.2
  have hk' : (n : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact two_elt_mem_A hc h194M hTM' hMcard ha haU hnM hna hk'

theorem A1_central (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U)
    (hMcard : Nat.card M = 1152) {a w : G} (ha : a ∈ A) (haU : a ∉ U) (hwM : w ∈ M)
    (hwa : w * a = a * w) (hw : orderOf w = 3) :
    ∀ e ∈ A ⊓ centralizer ({w} : Set G), ∀ n ∈ centralizer ({a} : Set G) ⊓ M, e * n = n * e := by
  intro e he n hn
  have hle : (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U) ≤ centralizer ({e} : Set G) := by
    refine sup_le ?_ ?_
    · intro y hy
      exact mem_centralizer_singleton_iff.2 (Cfg.A_comm hc y hy.1 e he.1)
    · intro ω hω
      exact mem_centralizer_singleton_iff.2 (CM.A1_comm_W hc e he ω hω).symm
  have hn' : n ∈ (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U) := by
    rw [← CM.cent_eq hc h194M hTM' hCT hMcard ha haU hwM hwa hw]; exact hn
  exact (mem_centralizer_singleton_iff.1 (hle hn')).symm

theorem cent_comm_A1 (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R)
    (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U)
    (hMcard : Nat.card M = 1152) {a w : G} (ha : a ∈ A) (haU : a ∉ U) (hwM : w ∈ M)
    (hwa : w * a = a * w) (hw : orderOf w = 3) :
    ∀ e ∈ A ⊓ centralizer ({w} : Set G), ∀ g ∈ centralizer ({a} : Set G), e * g = g * e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro e he g hg
  set K : Subgroup G := centralizer ({a} : Set G) with hK
  have hAK : A ≤ K := fun y hy => mem_centralizer_singleton_iff.2 (Cfg.A_comm hc y hy a ha)
  by_cases he1 : e = 1
  · rw [he1]; simp
  obtain ⟨P, hP⟩ := exists_sylow_A hc h194M hTM' hMcard ha haU
  have he2 : e * e = 1 := Cfg.A_sq hc e he.1
  let x₀ : ↥K := ⟨e, hAK he.1⟩
  have hx₀P : x₀ ∈ (P : Subgroup ↥K) := by rw [hP]; exact he.1
  have hPab : ∀ q ∈ (P : Subgroup ↥K), ∀ q' ∈ (P : Subgroup ↥K), q * q' = q' * q := by
    intro q hq q' hq'
    rw [hP] at hq hq'
    exact Subtype.ext (Cfg.A_comm hc q hq q' hq')
  have hW : CFSG.Quasithin.IsWeaklyClosedIn (P : Subgroup ↥K) (P : Subgroup ↥K) := by
    intro g' hle
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have : Nat.card (CFSG.Quasithin.conjSubgroup (P : Subgroup ↥K) g') =
        Nat.card (P : Subgroup ↥K) := Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective
    exact le_of_eq this.symm
  have hwc : ∀ g' : ↥K, g'⁻¹ * x₀ * g' ∈ (P : Subgroup ↥K) → g'⁻¹ * x₀ * g' = x₀ := by
    intro g' hg'
    have hx : x₀ ∈ Subgroup.centralizer ((P : Subgroup ↥K) : Set ↥K) :=
      mem_centralizer_iff.2 (fun q hq => hPab q hq x₀ hx₀P)
    have hy : g'⁻¹ * x₀ * g' ∈ Subgroup.centralizer ((P : Subgroup ↥K) : Set ↥K) :=
      mem_centralizer_iff.2 (fun q hq => hPab q hq _ hg')
    obtain ⟨n, hn, hnxy⟩ := CFSG.Quasithin.burnside_fusion_lemma_centralizer P le_rfl hW hx hy
      (g := g') rfl
    have hnN : (n : G) ∈ normalizer (A : Set G) := by
      apply Gen.mem_normalizer_of_conj_le
      intro y hy'
      have hyK : y ∈ K := hAK hy'
      have hyP : (⟨y, hyK⟩ : ↥K) ∈ (P : Subgroup ↥K) := by rw [hP]; exact hy'
      have := (mem_normalizer_iff.1 hn ⟨y, hyK⟩).1 hyP
      rw [hP] at this
      exact this
    have hnM : (n : G) ∈ M := normalizer_le_M_of_le_A hc le_rfl (Cfg.isE_A hc) (by norm_num) hnN
    have hnC : (n : G) ∈ centralizer ({a} : Set G) ⊓ M := Subgroup.mem_inf.2 ⟨n.2, hnM⟩
    have hen : e * (n : G) = n * e := A1_central hc h194M hTM' hCT hMcard ha haU hwM hwa hw e he n hnC
    rw [← hnxy]
    apply Subtype.ext
    show (n : G)⁻¹ * e * n = e
    calc (n : G)⁻¹ * e * n = (n : G)⁻¹ * (e * n) := by group
      _ = (n : G)⁻¹ * (n * e) := by rw [hen]
      _ = e := by group
  let z' : ↥(P : Subgroup ↥K) := ⟨x₀, hx₀P⟩
  have hzZ : z' ∈ Subgroup.center ↥(P : Subgroup ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (hPab q.1 q.2 x₀ hx₀P)
  have hz2 : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf x₀ = 2
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact he2) he1
  obtain ⟨-, hmk⟩ := CFSG.Adapters.glauberman_zStar P z' hzZ hz2 (fun g' hg' => hwc g' hg')
  have ha1 : a ≠ 1 := fun h => haU (h ▸ U.one_mem)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact Cfg.A_sq hc a ha) ha1
  have h194a : pPrimeCore 2 ↥K = ⊥ :=
    (L194.lemma194_of_ctx hKI3 hKI4 hc).2 a (Cfg.A_le_S hc ha) ha2
  have hodd : oddCore ↥K = ⊥ := by
    have hle : oddCore ↥K ≤ pPrimeCore 2 ↥K := by
      apply sSup_le
      rintro N ⟨hNn, hNodd⟩
      exact le_sSup ⟨hNn, Nat.coprime_two_left.2 hNodd⟩
    rw [h194a] at hle
    exact le_bot_iff.1 hle
  have hcentral : (⟨g, hg⟩ : ↥K) * x₀ = x₀ * ⟨g, hg⟩ := by
    have h1 := Subgroup.mem_center_iff.1 hmk (QuotientGroup.mk (⟨g, hg⟩ : ↥K))
    have h2 : (QuotientGroup.mk ((⟨g, hg⟩ : ↥K) * x₀ * (⟨g, hg⟩ : ↥K)⁻¹ * x₀⁻¹) :
        ↥K ⧸ oddCore ↥K) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h1' : (QuotientGroup.mk (⟨g, hg⟩ : ↥K) : ↥K ⧸ oddCore ↥K) * QuotientGroup.mk x₀ =
          QuotientGroup.mk x₀ * QuotientGroup.mk (⟨g, hg⟩ : ↥K) := h1
      rw [h1']
      group
    have h3 : (⟨g, hg⟩ : ↥K) * x₀ * (⟨g, hg⟩ : ↥K)⁻¹ * x₀⁻¹ ∈ oddCore ↥K :=
      (QuotientGroup.eq_one_iff _).1 h2
    rw [hodd, Subgroup.mem_bot] at h3
    calc (⟨g, hg⟩ : ↥K) * x₀ = ((⟨g, hg⟩ : ↥K) * x₀ * (⟨g, hg⟩ : ↥K)⁻¹ * x₀⁻¹) * x₀ *
        (⟨g, hg⟩ : ↥K) := by group
      _ = x₀ * ⟨g, hg⟩ := by rw [h3]; group
  exact (congrArg Subtype.val hcentral).symm

theorem cent_le_M (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R)
    (h194M : pPrimeCore 2 ↥M = ⊥)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    (hCT : ∀ m ∈ M, (∀ t ∈ Tsub S U, m * t = t * m) → m ∈ Tsub S U)
    (hMcard : Nat.card M = 1152) {a w : G} (ha : a ∈ A) (haU : a ∉ U) (hwM : w ∈ M)
    (hwa : w * a = a * w) (hw : orderOf w = 3) :
    centralizer ({a} : Set G) ≤ M := by
  intro g hg
  have hgN : g ∈ normalizer ((A ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) := by
    apply Gen.mem_normalizer_of_conj_le
    intro y hy
    have h1 := cent_comm_A1 hKI3 hKI4 hc h194M hTM' hCT hMcard ha haU hwM hwa hw y hy g hg
    have : g * y * g⁻¹ = y := by
      calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [← h1]
        _ = y := by group
    rw [this]; exact hy
  have hA1 : IsE 2 (A ⊓ centralizer ({w} : Set G)) := by
    refine ⟨isElemAbelian_iff.2 ⟨fun a₁ h₁ b₁ h₂ => Cfg.A_comm hc a₁ h₁.1 b₁ h₂.1,
      fun a₁ h₁ => ?_⟩, ?_⟩
    · rw [pow_two]; exact Cfg.A_sq hc a₁ h₁.1
    · rw [CM.card_A1 hc hTM' hCT ha haU hwM hwa hw]; norm_num
  exact normalizer_le_M_of_le_A hc inf_le_left hA1 le_rfl hgN

end Config

end L196c

end CFSG.GH74.Uniqueness.SU.SU7
