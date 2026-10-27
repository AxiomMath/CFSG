module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourTail3
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA67
public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Mod
public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Lift

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open scoped commutatorElement Pointwise MatrixGroups

@[expose] def U3FrameConcl (s : ℕ) (Λ : Type) [Group Λ] (T : Subgroup Λ) (g : Λ) : Prop :=
  ∃ k₁ k₃ d y y₃ : Λ,
    y ∈ CFSG.CGT.Timmesfeld75.conjSubgroup k₁ (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T) ∧
    y₃ ∈ CFSG.CGT.Timmesfeld75.conjSubgroup k₃ (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T) ∧
    y ≠ 1 ∧ y₃ ≠ 1 ∧ y ^ (2 ^ s + 1) = 1 ∧ y₃ ^ (2 ^ s + 1) = 1 ∧
    (∀ x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup k₃
      (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T), d * x = x * d) ∧
    (∀ x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup k₁
      (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T), d * y⁻¹ * x = x * (d * y⁻¹)) ∧
    (∀ x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup k₃
      (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T), y * y₃⁻¹ * x = x * (y * y₃⁻¹))

@[expose] def U3Frame : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ (Λ : Type) [Group Λ] [Finite Λ], StatedClassicalModel Λ StatedLieTag.PSU 3 2 s →
    ∀ (T : Subgroup Λ), (∃ S : Sylow 2 Λ,
        T = (Subgroup.center (S : Subgroup Λ)).map (S : Subgroup Λ).subtype) →
      CFSG.CGT.Timmesfeld75.ConjTwoTransitive Λ T →
      ∀ g : Λ, CFSG.CGT.Timmesfeld75.conjSubgroup g T ≠ T →
        Nat.card ↥(T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T) = 2 ^ s * ((2 ^ s) ^ 2 - 1) →
        U3FrameConcl s Λ T g

theorem coprime_two_pow_sub_one_add_one {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime (2 ^ n - 1) (2 ^ n + 1) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ n := ⟨_, rfl⟩
  rw [← hq]
  have hev : 2 ∣ q := by rw [hq]; exact dvd_pow_self 2 hn
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_two_pow
  have hg : Nat.gcd (q - 1) (q + 1) ∣ 2 := by
    have h1 := Nat.gcd_dvd_left (q - 1) (q + 1)
    have h2 := Nat.gcd_dvd_right (q - 1) (q + 1)
    have := Nat.dvd_sub h2 h1
    have e : q + 1 - (q - 1) = 2 := by omega
    rwa [e] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hg with h | h
  · exact h
  · exfalso
    have h1 := Nat.gcd_dvd_left (q - 1) (q + 1)
    rw [h] at h1
    omega

section Core

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} {T : Sylow 2 G}

theorem slTailU3_core [R.Normal] (h : EightCtx Y T R) {n s : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ s)
    (hnat : IsNaturalSLTwoModule ↥Y n) (hFrame : U3Frame)
    {K : Subgroup (G ⧸ R)} (hJbK : jBar R T ≤ K)
    (hstd : CFSG.CGT.Timmesfeld75.StdPair (↥K ⧸ Subgroup.center ↥K)
      (((jBar R T).subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))))
    (hcardTh : Nat.card (((jBar R T).subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) =
      2 ^ n)
    (ρ : ↥Y →* ↥K) (ι' : (↥Y ⧸ pCore 2 ↥Y) →* ↥K ⧸ Subgroup.center ↥K)
    (hρval : ∀ z : ↥Y, ((ρ z : ↥K) : G ⧸ R) = QuotientGroup.mk' R z)
    (hι'mk : ∀ y : ↥Y, ι' (QuotientGroup.mk y) =
      QuotientGroup.mk' (Subgroup.center ↥K) (ρ y))
    (hι'inj : Function.Injective ι')
    (hmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) StatedLieTag.PSU 3 2 s) : False := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTcard, ⟨S, hSdef⟩, hBor⟩ := hstd.of_psu3 hs hmodel
  have hns : n = s := Nat.pow_right_injective (le_refl 2) (hcardTh.symm.trans hTcard)
  subst hns
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  have hOY : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  have hρker : ∀ y : ↥Y, ρ y = 1 ↔ y ∈ pCore 2 ↥Y := by
    intro y
    constructor
    · intro hy
      have h1 : ι' (QuotientGroup.mk y) = 1 := by rw [hι'mk, hy, map_one]
      have h2 : (QuotientGroup.mk y : ↥Y ⧸ pCore 2 ↥Y) = 1 := hι'inj (by rw [h1, map_one])
      exact (QuotientGroup.eq_one_iff y).mp h2
    · intro hy
      have hyR : (y : G) ∈ R := hOY ⟨y, hy, rfl⟩
      have h3 : QuotientGroup.mk' R (y : G) = 1 := (QuotientGroup.eq_one_iff _).mpr hyR
      apply Subtype.ext
      rw [hρval]
      exact h3
  have hNat := natQ_of_eight h hn hnat hJbK ρ hρval hρker
  have hq := (h.quasisimple_of_SL hn1 hnat).1
  have hperf := commutator_range_eq ρ (pCore 2 ↥Y) hρker (Group.isPerfect_def.mp hq)
  have hinj : ∀ y ∈ ρ.range, π y = 1 → y = 1 := by
    rintro _ ⟨y, rfl⟩ h1
    have : y ∈ pCore 2 ↥Y := by
      have h2 : ι' (QuotientGroup.mk y) = 1 := by rw [hι'mk]; exact h1
      have h3 : (QuotientGroup.mk y : ↥Y ⧸ pCore 2 ↥Y) = 1 := hι'inj (by rw [h2, map_one])
      exact (QuotientGroup.eq_one_iff y).mp h3
    exact (hρker y).mpr this
  obtain ⟨hJbcard, hJbYb⟩ := eight_jBar_card_le h hn1 hnat hJbK ρ hρval
  obtain ⟨φ, -⟩ := id hnat
  obtain ⟨eYb⟩ := range_mulEquiv ρ (pCore 2 ↥Y) hρker φ
  obtain ⟨g, hg, hgen⟩ := l2_gen_facts hn hJbYb hJbcard eYb
  set Jb : Subgroup ↥K := (jBar R T).subgroupOf K with hJb
  set That : Subgroup (↥K ⧸ Subgroup.center ↥K) := Jb.map π with hThat
  have hL : That ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (π g) That = ρ.range.map π := by
    rw [← hgen, Subgroup.map_sup]
    congr 1
    exact (map_map_conj_eq π Jb g).symm
  have hrangeπ : ρ.range.map π = ι'.range := by
    rw [← MonoidHom.range_comp]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨QuotientGroup.mk y, by rw [hι'mk]; rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨y, by rw [hι'mk]; rfl⟩
  have hLcard : Nat.card ↥(ρ.range.map π) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [hrangeπ, ← Nat.card_congr (MonoidHom.ofInjective hι'inj).toEquiv]
    exact card_sl2_two_pow hn0 φ
  have hne : CFSG.CGT.Timmesfeld75.conjSubgroup (π g) That ≠ That := by
    intro heq
    rw [heq, sup_idem] at hL
    have hc1 : Nat.card ↥That = 2 ^ n := hTcard
    rw [hL, hLcard] at hc1
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hpos : 0 < 2 ^ n := by positivity
    have := Nat.eq_of_mul_eq_mul_left hpos (hc1.trans (mul_one _).symm)
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  obtain ⟨k₁, k₃, d, y, y₃, hy, hy₃, hy1, hy₃1, hyr, hy₃r, hdc₃, hdc₁, hyc₃⟩ :=
    hFrame n hs _ hmodel That ⟨S, hSdef⟩ hBor.1 (π g) hne (by rw [hL]; exact hLcard)
  rw [hL] at hy hy₃ hdc₃ hdc₁ hyc₃
  have hθ : Function.Injective (h.vAct.comp K.subtype) :=
    h.vAct_injective.comp (Subgroup.subtype_injective K)
  exact frame_false_K (omegaOneCenterIn_comm R) hθ (coprime_two_pow_sub_one_add_one hn0)
    (Even.add_one (Nat.even_pow.mpr ⟨even_two, hn0⟩)) hNat hperf hinj
    hy hy₃ hy1 hy₃1 hyr hy₃r hdc₃ hdc₁ hyc₃

end Core

theorem slTailU3_of (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hFrame : U3Frame) : SLTailU3 := by
  intro G _ _ _ _ Y T R _ hctx n hn hnat s hs hmodel
  obtain ⟨hn2, -, -, hstd, hcardTh, -, ρ, ι', hρval, hι'mk, hι'inj, -⟩ :=
    eight_sl_ident hctx hn hnat hS h215 hL
  exact slTailU3_core hctx hn2 hs hnat hFrame Subgroup.le_normalClosure hstd hcardTh ρ ι' hρval
    hι'mk hι'inj hmodel

end CFSG.CGT.PushingUpLit.CGT6
