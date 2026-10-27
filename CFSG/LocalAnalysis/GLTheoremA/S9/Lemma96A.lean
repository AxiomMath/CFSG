module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Contra
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs96
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9.L96

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem map_commutator_top {p : ℕ} (L : Subgroup G) :
    (⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆).map L.subtype =
      (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) := by
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rfl

theorem card_commutator_top {p : ℕ} (L : Subgroup G) :
    Nat.card ↥(⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆) =
      Nat.card (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) := by
  rw [← map_commutator_top (p := p) L]
  exact (Subgroup.card_map_of_injective L.subtype_injective).symm

theorem coreOf_le {p : ℕ} {L : Subgroup G} : GLAPPrimeCoreOf p L ≤ L :=
  Subgroup.map_subtype_le _

theorem pRank_ltilde_le {p : ℕ} {L : Subgroup G}
    (hodd : Odd (Nat.card (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G))) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (LTilde p L)) ≤ CFSG.Open.pRank 2 L := by
  have hN : ¬ 2 ∣ Nat.card ↥(⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆) := by
    rw [card_commutator_top]
    exact Nat.odd_iff.1 hodd |> fun h => by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CFSG.SectionRank.pRank_quotient_eq (G := ↥L) _ hN).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup L).symm).le

theorem card_le_two_pow_center {p : ℕ} {L E : Subgroup G}
    (hodd : Odd (Nat.card (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G))) (hE : IsElemAbelian 2 E)
    (hEO : E ≤ GLAPPrimeCoreOf p L) :
    Nat.card E ≤ 2 ^ CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) := by
  have hEL : E ≤ L := hEO.trans coreOf_le
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_two hE
  set N : Subgroup ↥L := ⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆ with hNdef
  set φ : ↥E →* LTilde p L := (QuotientGroup.mk' N).comp (Subgroup.inclusion hEL) with hφ
  have hdisj : Disjoint E (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) :=
    Subgroup.disjoint_of_coprime_natCard
      (by rw [hk]; exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at he
    have hmem : (e : G) ∈ (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) := by
      rw [← map_commutator_top]
      exact Subgroup.mem_map_of_mem _ he
    have h1 : (e : G) ∈ E ⊓ (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) := ⟨e.2, hmem⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have hcentral : φ.range ≤ Subgroup.center (LTilde p L) := by
    rintro _ ⟨e, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H l =>
      have heO : Subgroup.inclusion hEL e ∈ GLAPPrimeCore p ↥L := by
        obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.1 (hEO e.2)
        have : o = Subgroup.inclusion hEL e := Subtype.ext hoe
        rwa [← this]
      have hc : ⁅l⁻¹, (Subgroup.inclusion hEL e)⁻¹⁆ ∈ N :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
          ((GLAPPrimeCore p ↥L).inv_mem heO)
      rw [hφ, MonoidHom.comp_apply]
      change (QuotientGroup.mk' N) l * (QuotientGroup.mk' N) (Subgroup.inclusion hEL e) =
        (QuotientGroup.mk' N) (Subgroup.inclusion hEL e) * (QuotientGroup.mk' N) l
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      have : (l * Subgroup.inclusion hEL e)⁻¹ * (Subgroup.inclusion hEL e * l) =
          (⁅l⁻¹, (Subgroup.inclusion hEL e)⁻¹⁆)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]; exact N.inv_mem hc
  have h2 := CFSG.SectionRank.le_pRank_of_injective Nat.prime_two.one_lt
    (fun a b => Subtype.ext (isElemAbelian_commute hE a.2 b.2))
    (fun a => Subtype.ext (by simpa using hE.2 a a.2)) hk φ hinj hcentral
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) h2

theorem two_part_le_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L Q₁ S : Subgroup G}
    (hcent : L ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ oPPrimeP p L) (hSL : S ≤ L)
    (hS : IsPGroup 2 S) :
    S ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ GLAPPrimeCoreOf p L := by
  intro s hs
  have hsL : s ∈ L ⊓ Subgroup.centralizer (Q₁ : Set G) := ⟨hSL hs.1, hs.2⟩
  obtain ⟨g', hg', hgs⟩ := Subgroup.mem_map.1 (hcent hsL)
  have hy : (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) g' ∈
      CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L) := Subgroup.mem_comap.1 hg'
  obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥L ⧸ GLAPPrimeCore p ↥L) ⟨_, hy⟩
  obtain ⟨n, hn⟩ := hS ⟨s, hs.1⟩
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) g' ^ (p ^ m) = 1 := congrArg Subtype.val hm
  have hg2 : g' ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    have hg's : (g' : G) = s := hgs
    rw [hg's]
    exact this
  have h2 : (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) g' ^ (2 ^ n) = 1 := by
    rw [← map_pow, hg2, map_one]
  have hcop : Nat.Coprime (p ^ m) (2 ^ n) :=
    Nat.Coprime.pow m n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hord : orderOf ((QuotientGroup.mk' (GLAPPrimeCore p ↥L)) g') = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have h3 : (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) g' = 1 := orderOf_eq_one_iff.1 hord
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  rw [← hgs]
  exact Subgroup.mem_map_of_mem _ h3

theorem le_normalizer_of_le_elemAbelian {p : ℕ} {S A B : Subgroup G} (hS : IsElemAbelian p S)
    (hA : A ≤ S) (hB : B ≤ S) : B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have := isElemAbelian_commute hS (hB hb) (hA ha)
    rw [this]; simpa using ha
  · intro hba
    have haS : a ∈ S := by
      have h1 : b * a * b⁻¹ ∈ S := hA hba
      have h2 : b⁻¹ * (b * a * b⁻¹) * b ∈ S :=
        S.mul_mem (S.mul_mem (S.inv_mem (hB hb)) h1) (hB hb)
      simpa [mul_assoc] using h2
    have := isElemAbelian_commute hS (hB hb) haS
    rw [this] at hba
    simpa using hba

theorem card_sup_mul_card_inf_of_le_elemAbelian {p : ℕ} {S A B : Subgroup G}
    (hS : IsElemAbelian p S) (hA : A ≤ S) (hB : B ≤ S) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B :=
  card_sup_mul_card_inf_of_le_normalizer (le_normalizer_of_le_elemAbelian hS hA hB)


theorem exists_complement {p : ℕ} (hp : p.Prime) {S S₀ : Subgroup G} (hS : IsElemAbelian p S)
    (h : S₀ ≤ S) :
    ∃ S₁ : Subgroup G, S₁ ≤ S ∧ S₀ ⊓ S₁ = ⊥ ∧ Nat.card S₀ * Nat.card S₁ = Nat.card S := by
  classical
  let P : Subgroup G → Prop := fun T => T ≤ S ∧ S₀ ⊓ T = ⊥
  obtain ⟨S₁, hS₁, hmax⟩ : ∃ S₁, P S₁ ∧ ∀ T, P T → Nat.card T ≤ Nat.card S₁ := by
    obtain ⟨S₁, hmem, hmax⟩ := Set.exists_max_image {T | P T} (fun T => Nat.card T)
      (Set.toFinite _) ⟨⊥, bot_le, inf_bot_eq _⟩
    exact ⟨S₁, hmem, fun T hT => hmax T hT⟩
  have hM : S₀ ⊔ S₁ = S := by
    by_contra hne
    have hlt : S₀ ⊔ S₁ < S := lt_of_le_of_ne (sup_le h hS₁.1) hne
    obtain ⟨x, hxS, hxM⟩ := SetLike.exists_of_lt hlt
    set M := S₀ ⊔ S₁ with hMdef
    set Z := Subgroup.zpowers x with hZdef
    have hx1 : x ≠ 1 := fun h1 => hxM (h1 ▸ M.one_mem)
    haveI : Fact p.Prime := ⟨hp⟩
    have hZcard : Nat.card Z = p := by
      rw [hZdef, Nat.card_zpowers]
      exact orderOf_eq_prime (hS.2 x hxS) hx1
    have hZS : Z ≤ S := (Subgroup.zpowers_le.2 hxS)
    have hMS : M ≤ S := sup_le h hS₁.1
    have hMZ : M ⊓ Z = ⊥ := by
      have hd : Nat.card ↥(M ⊓ Z) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime hp).1 hd with h1 | h1
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have : M ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hZcard])
        exact hxM (by
          have : x ∈ M ⊓ Z := by rw [this]; exact Subgroup.mem_zpowers x
          exact this.1)
    have hS₁Z : S₁ ⊓ Z = ⊥ := by
      rw [eq_bot_iff, ← hMZ]
      exact inf_le_inf_right _ le_sup_right
    set T := S₁ ⊔ Z with hTdef
    have hTS : T ≤ S := sup_le hS₁.1 hZS
    have hTcard : Nat.card T = Nat.card S₁ * p := by
      have := card_sup_mul_card_inf_of_le_elemAbelian hS hS₁.1 hZS
      rw [hS₁Z, Subgroup.card_bot, mul_one, hZcard] at this
      exact this
    have hMcard : Nat.card M = Nat.card S₀ * Nat.card S₁ := by
      have := card_sup_mul_card_inf_of_le_elemAbelian hS h hS₁.1
      rw [hS₁.2, Subgroup.card_bot, mul_one] at this
      exact this
    have hMZcard : Nat.card ↥(M ⊔ Z) = Nat.card M * p := by
      have := card_sup_mul_card_inf_of_le_elemAbelian hS hMS hZS
      rw [hMZ, Subgroup.card_bot, mul_one, hZcard] at this
      exact this
    have hsup : S₀ ⊔ T = M ⊔ Z := by
      rw [hTdef, hMdef, sup_assoc]
    have hS₀T : S₀ ⊓ T = ⊥ := by
      have h1 := card_sup_mul_card_inf_of_le_elemAbelian hS h hTS
      rw [hsup, hMZcard, hMcard, hTcard] at h1
      have hpos : 0 < Nat.card S₀ * Nat.card S₁ * p :=
        Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) hp.pos
      have h2 : Nat.card ↥(S₀ ⊓ T) = 1 := by
        have : Nat.card S₀ * Nat.card S₁ * p * Nat.card ↥(S₀ ⊓ T) =
            Nat.card S₀ * Nat.card S₁ * p * 1 := by
          rw [mul_one]; rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      exact Subgroup.eq_bot_of_card_eq _ h2
    have hle := hmax T ⟨hTS, hS₀T⟩
    rw [hTcard] at hle
    have : 0 < Nat.card S₁ := Nat.card_pos
    nlinarith [hp.two_le]
  refine ⟨S₁, hS₁.1, hS₁.2, ?_⟩
  have := card_sup_mul_card_inf_of_le_elemAbelian hS h hS₁.1
  rw [hM, hS₁.2, Subgroup.card_bot, mul_one] at this
  exact this.symm

theorem card_le_two_pow_of_faithful (hD : DihedralUsed) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {S₁ Q₁ : Subgroup G} (hS : IsElemAbelian 2 S₁) (hexp : ∀ g ∈ Q₁, g ^ q = 1)
    (hN : S₁ ≤ Subgroup.normalizer (Q₁ : Set G))
    (hf : S₁ ⊓ Subgroup.centralizer (Q₁ : Set G) = ⊥) :
    Nat.card S₁ ≤ 2 ^ (GLATwoLocalRank q G + 1) := by
  obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_two hS
  by_cases hj0 : j = 0
  · rw [hj, hj0]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hP : IsPGroup q Q₁ := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  obtain ⟨u, huU, hu1, Q', hQ'le, hQ'e, hQ'card, hQ'u, -⟩ :=
    hD G q hq hq2 Q₁ S₁ k hP hS hj hN (fun u hu hQ => by
      have : u ∈ S₁ ⊓ Subgroup.centralizer (Q₁ : Set G) :=
        ⟨hu, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
      · rw [hf] at this; exact this
      · have := Subgroup.mem_centralizer_iff.1 (hQ hh) u (Set.mem_singleton u)
        exact this.symm)
  have hu2 : u ^ 2 = 1 := by simpa using hS.2 u huU
  have hne : Subgroup.zpowers u ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]; exact hu1
  have hES : Q' ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [← S3.centralizer_zpowers] at hQ'u
    exact hQ'u.trans (Subgroup.centralizer_le_normalizer _)
  have hz2 : IsPGroup 2 (Subgroup.zpowers u) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]
  have h1 := card_le_pow_glaTwoLocalRank hq hQ'e hne hz2 hES
  rw [hQ'card] at h1
  have h2 : k ≤ GLATwoLocalRank q G := (Nat.pow_le_pow_iff_right hq.one_lt).1 h1
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

variable {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G}

theorem exists_S0 (hc : S9Ctx G p) (hC : Contra92 p B x L q Q₁)
    (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank p G) :
    ∃ S₀ : Subgroup G, S₀ ≤ GLAPPrimeCoreOf p L ∧ IsElemAbelian 2 S₀ ∧
      2 ^ CFSG.Open.pRank 2 L ≤ Nat.card S₀ * 2 ^ (GLATwoLocalRank p G + 1) := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hq := hC.setup.prime
  obtain ⟨S, hSL, hS, hScard⟩ := CFSG.SectionRank.exists_pRank (G := G) (p := 2) (by norm_num) L
  have hS2 : IsPGroup 2 S := isPGroup_of_isElemAbelian hS
  have hS₀O : S ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ GLAPPrimeCoreOf p L :=
    two_part_le_core hp hp2 hC.setup.cent hSL hS2
  obtain ⟨S₁, hS₁S, hdisj, hprod⟩ :=
    exists_complement Nat.prime_two hS (inf_le_left : S ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ S)
  have hS₁ : IsElemAbelian 2 S₁ := isElemAbelian_mono hS hS₁S
  have hfaith : S₁ ⊓ Subgroup.centralizer (Q₁ : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : g ∈ (S ⊓ Subgroup.centralizer (Q₁ : Set G)) ⊓ S₁ := ⟨⟨hS₁S hg.1, hg.2⟩, hg.1⟩
    rw [hdisj] at h1
    exact h1
  have hN : S₁ ≤ Subgroup.normalizer (Q₁ : Set G) :=
    (hS₁S.trans hSL).trans (Subgroup.le_normalizer.trans hC.setup.char)
  have hcard := card_le_two_pow_of_faithful P55.dihedralUsed hq hC.setup.ne_two hS₁ hC.setup.exp hN hfaith
  refine ⟨S ⊓ Subgroup.centralizer (Q₁ : Set G), hS₀O, isElemAbelian_mono hS inf_le_left, ?_⟩
  rw [← hScard, ← hprod]
  exact Nat.mul_le_mul_left _ (hcard.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem rank_ineq_ltilde (hc : S9Ctx G p) (hC : Contra92 p B x L q Q₁)
    (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank p G) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (LTilde p L)) ≤
      CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) + GLATwoLocalRank p G + 1 := by
  obtain ⟨S₀, hS₀O, hS₀, hS⟩ := exists_S0 hc hC h95
  have h1 := card_le_two_pow_center hC.odd hS₀ hS₀O
  have h2 : 2 ^ CFSG.Open.pRank 2 L ≤
      2 ^ (CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) + GLATwoLocalRank p G + 1) := by
    calc 2 ^ CFSG.Open.pRank 2 L ≤ Nat.card S₀ * 2 ^ (GLATwoLocalRank p G + 1) := hS
      _ ≤ 2 ^ CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) * 2 ^ (GLATwoLocalRank p G + 1) :=
        Nat.mul_le_mul_right _ h1
      _ = 2 ^ (CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) + GLATwoLocalRank p G + 1) := by
        rw [← pow_add]; ring_nf
  have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  exact (pRank_ltilde_le hC.odd).trans h3

theorem pRank_L_le_of_odd (hc : S9Ctx G p) (hC : Contra92 p B x L q Q₁)
    (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank p G)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p L))) :
    CFSG.Open.pRank 2 L ≤ GLATwoLocalRank p G + 1 := by
  obtain ⟨S₀, hS₀O, hS₀, hS⟩ := exists_S0 hc hC h95
  have hdisj : Disjoint S₀ (GLAPPrimeCoreOf p L) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_two hS₀
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hbot : S₀ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : g ∈ S₀ ⊓ GLAPPrimeCoreOf p L := ⟨hg, hS₀O hg⟩
    rw [hdisj.eq_bot] at h1
    exact h1
  rw [hbot, Subgroup.card_bot, one_mul] at hS
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hS

end CFSG.LocalAnalysis.GLTheoremA.S9.L96
