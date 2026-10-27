module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinTools
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

namespace Unc25G2

namespace BenderBorel

section Solvable

open Subgroup

theorem isSolvable_normalizer_of_sup_cyclic {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q D : Subgroup G} (hQ : IsPGroup p Q) (hD : IsCyclic D)
    (hsup : Q ⊔ D = normalizer (Q : Set G)) : Group.IsSolvable (normalizer (Q : Set G)) := by
  set N := normalizer (Q : Set G)
  have hQN : Q ≤ N := le_normalizer
  have hDN : D ≤ N := hsup ▸ le_sup_right
  set Q' := Q.subgroupOf N
  have : Q'.Normal := (normal_subgroupOf_iff_le_normalizer hQN).mpr le_rfl
  have : IsPGroup p Q' := hQ.of_equiv (subgroupOfEquivOfLe hQN).symm
  have : Group.IsNilpotent Q' := this.isNilpotent
  have : Group.IsSolvable Q' := inferInstance
  have htop : D.subgroupOf N ⊔ Q' = ⊤ := by
    rw [← (subgroupOf_sup hDN hQN), sup_comm, hsup, subgroupOf_self]
  have hdec : ∀ x : N, ∃ d ∈ D.subgroupOf N, ∃ q ∈ Q', d * q = x := fun x => by
    have hx : x ∈ ((D.subgroupOf N ⊔ Q' : Subgroup N) : Set N) := by rw [htop]; trivial
    rw [mul_normal] at hx
    obtain ⟨d, hd, q, hq, rfl⟩ := hx
    exact ⟨d, hd, q, hq, rfl⟩
  have : IsMulCommutative D := hD.isMulCommutative
  have hcomm : ∀ a b : N ⧸ Q', a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    obtain ⟨d, hd, q, hq, rfl⟩ := hdec x
    obtain ⟨d', hd', q', hq', rfl⟩ := hdec y
    have hqq : ((q : N) : N ⧸ Q') = 1 := (QuotientGroup.eq_one_iff _).mpr hq
    have hqq' : ((q' : N) : N ⧸ Q') = 1 := (QuotientGroup.eq_one_iff _).mpr hq'
    have hdd : d * d' = d' * d := by
      have h1 := isMulCommutative_iff.mp this (⟨(d : G), hd⟩ : D) ⟨(d' : G), hd'⟩
      exact Subtype.ext (congrArg (fun z : D => (z : G)) h1)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hqq, hqq', mul_one, mul_one,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hdd]
  have : Group.IsSolvable (N ⧸ Q') := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_ker_le_range Q'.subtype (QuotientGroup.mk' Q')
    (by rw [QuotientGroup.ker_mk', range_subtype])

end Solvable

section Regular

open MulAction

theorem two_power_of_centralizer {X : Type*} [Group X] [Finite X] (B Q : Subgroup X)
    (hQ2 : IsPGroup 2 Q)
    (hfaith : ∀ x : X, (∀ ω : X ⧸ B, x • ω = ω) → x = 1)
    (hreg : ∀ α β : X ⧸ B, α ≠ QuotientGroup.mk 1 → β ≠ QuotientGroup.mk 1 →
      ∃ r ∈ Q, r • α = β)
    (hbase : ∃ b : X ⧸ B, b ≠ QuotientGroup.mk 1)
    {x : X} (hxB : x ∈ B) (hxc : ∀ q ∈ Q, x * q = q * x) : ∃ j : ℕ, x ^ 2 ^ j = 1 := by
  obtain ⟨b₀, hb₀⟩ := hbase
  have hfix : ∀ y ∈ B, y • (QuotientGroup.mk 1 : X ⧸ B) = QuotientGroup.mk 1 := by
    intro y hy
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using B.inv_mem hy)
  have hne : x • b₀ ≠ QuotientGroup.mk 1 := by
    intro h
    apply hb₀
    have : x • b₀ = x • (QuotientGroup.mk 1 : X ⧸ B) := by rw [h, hfix x hxB]
    exact (MulAction.injective x) this
  obtain ⟨r, hr, hrb⟩ := hreg b₀ (x • b₀) hb₀ hne
  have hpow : ∀ n : ℕ, x ^ n • b₀ = r ^ n • b₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ, mul_smul, ih, mul_smul]
      have hrn : r ^ n ∈ Q := Q.pow_mem hr n
      have hc : x * r ^ n = r ^ n * x := hxc _ hrn
      rw [← mul_smul, hc, mul_smul, ← hrb]
  obtain ⟨j, hj⟩ := hQ2 ⟨r, hr⟩
  have hrj : r ^ 2 ^ j = 1 := congrArg Subtype.val hj
  refine ⟨j, hfaith _ (fun ω => ?_)⟩
  by_cases hω : ω = QuotientGroup.mk 1
  · rw [hω]; exact hfix _ (B.pow_mem hxB _)
  · obtain ⟨s, hs, hsb⟩ := hreg b₀ ω hb₀ hω
    have hcs : x ^ 2 ^ j * s = s * x ^ 2 ^ j := by
      have : Commute x s := hxc s hs
      exact (this.pow_left _).eq
    rw [← hsb, ← mul_smul, hcs, mul_smul, hpow, hrj, one_smul]

theorem mem_of_two_power {X : Type*} [Group X] [Finite X] {B Q : Subgroup X}
    (hn : (Q.subgroupOf B).Normal) (hodd : ¬ 2 ∣ (Q.subgroupOf B).index) {y : X} (hy : y ∈ B)
    {j : ℕ} (hyj : y ^ 2 ^ j = 1) : y ∈ Q := by
  set Q' := Q.subgroupOf B
  have h1 : ((⟨y, hy⟩ : B) : B ⧸ Q') ^ 2 ^ j = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨y, hy⟩ : B) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hyj)
    rw [this, QuotientGroup.mk_one]
  have h2 : orderOf ((⟨y, hy⟩ : B) : B ⧸ Q') ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf ((⟨y, hy⟩ : B) : B ⧸ Q') ∣ Q'.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hi0 : i = 0 := by
    by_contra hne
    apply hodd
    rw [hio] at h3
    exact (dvd_pow_self 2 hne).trans h3
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hio
  have : (⟨y, hy⟩ : B) ∈ Q' := (QuotientGroup.eq_one_iff _).mp hio
  exact Subgroup.mem_subgroupOf.mp this

end Regular

section Bridge

open CFSG.BenderSuzuki

theorem isSimpleBenderGroup_of_fusion {X : Type*} [Group X] [Finite X]
    (h : fusionIsBenderGroup X) : IsSimpleBenderGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact IsSimpleBenderGroup.isPSL2 ⟨f, hf, ⟨e⟩⟩
  · let k := GaloisField 2 f
    let K := FiniteField.Extension k 2 2
    let J := binaryQuadraticHermitian f (by omega)
    have : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
    have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
      rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
    have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
      quadraticBinaryFrobenius_fixed_card f (by omega)
    have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
    let eU := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
    have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    exact IsSimpleBenderGroup.isPSU3 ⟨f, hf, K, inferInstance, inferInstance, J, hJ, hKcard, hfixed,
      ⟨(e.trans (MulEquiv.subgroupCongr hmodel.symm)).trans eU.symm⟩⟩
  · have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
    exact IsSimpleBenderGroup.isSuzuki ⟨a, ha, ⟨e.trans (MulEquiv.subgroupCongr
      (hmodel.symm.trans (szModel_eq_suzukiMatrixGroup a)))⟩⟩

theorem exists_borel_of_bender {X : Type*} [Group X] [Finite X] (h : fusionIsBenderGroup X) :
    ∃ q k : ℕ, 4 ≤ q ∧ fusionBenderBorel X q k := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf,
      (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf,
      (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
    exact ⟨_, _, by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega),
      (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩

end Bridge

section Assembly

open CFSG.BenderSuzuki MulAction

theorem twoRank_of_borel {X : Type*} [Group X] [Finite X] (Q : Sylow 2 X) {q : ℕ} (hq : 4 ≤ q)
    (hZpow : ∀ z ∈ Subgroup.center (Q : Subgroup X), z ^ 2 = 1)
    (hZcard : Nat.card (Subgroup.center (Q : Subgroup X)) = q) :
    PFchapter1section1.TwoRankAtLeastTwo X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZp : IsPGroup 2 (Subgroup.center (Q : Subgroup X)) := fun z =>
    ⟨1, by apply Subtype.ext; simpa using hZpow z.1 z.2⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
  have h4 : 2 ^ 2 ∣ Nat.card (Subgroup.center (Q : Subgroup X)) := by
    rw [hn]
    have h : 2 ^ 2 ≤ 2 ^ n := by rw [← hn, hZcard]; simpa using hq
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp h)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  refine ⟨(K.map (Subgroup.center (Q : Subgroup X)).subtype).map (Q : Subgroup X).subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Q : Subgroup X).subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.center _).subtype_injective, hK]
    norm_num
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
    simpa using congrArg Subtype.val (hZpow z.1 z.2)

theorem regular_of_borel {X : Type*} [Group X] [Finite X] (hmodel : IsSimpleBenderGroup X)
    (Q : Sylow 2 X) (hsolv : Group.IsSolvable (Subgroup.normalizer ((Q : Subgroup X) : Set X))) :
    IsRegularOn (Q : Subgroup X)
      {ω : X ⧸ Subgroup.normalizer ((Q : Subgroup X) : Set X) | ω ≠ QuotientGroup.mk 1} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsBorelSubgroup (Subgroup.normalizer ((Q : Subgroup X) : Set X)) := ⟨hsolv, Q, rfl⟩
  obtain ⟨P₁, hP₁n, hreg⟩ := simpleBender_borel_normalSylow_regular hB hmodel
  have hle : (Q : Subgroup X) ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) :=
    Subgroup.le_normalizer
  let QB : Sylow 2 (Subgroup.normalizer ((Q : Subgroup X) : Set X)) := Q.subtype hle
  have heq : P₁ = QB := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Subgroup.normalizer ((Q : Subgroup X) : Set X))
      QB P₁
    have hP₁n' : (P₁ : Subgroup (Subgroup.normalizer ((Q : Subgroup X) : Set X))).Normal := hP₁n
    have h1 : g⁻¹ • P₁ = P₁ := Sylow.smul_eq_of_normal
    calc P₁ = g⁻¹ • P₁ := h1.symm
      _ = g⁻¹ • (g • QB) := by rw [hg]
      _ = QB := by rw [smul_smul, inv_mul_cancel, one_smul]
  subst heq
  have hmapPB : (QB : Subgroup (Subgroup.normalizer ((Q : Subgroup X) : Set X))).map
      (Subgroup.normalizer ((Q : Subgroup X) : Set X)).subtype = (Q : Subgroup X) := by
    rw [Sylow.coe_subtype]
    simpa [Subgroup.subgroupOf_map_subtype]
  rw [hmapPB] at hreg
  exact hreg

theorem centralizer_le_of_borel {X : Type*} [Group X] [Finite X] [hs : IsSimpleGroup X]
    (hmodel : IsSimpleBenderGroup X) (Q : Sylow 2 X)
    (hsolv : Group.IsSolvable (Subgroup.normalizer ((Q : Subgroup X) : Set X)))
    (hBtop : Subgroup.normalizer ((Q : Subgroup X) : Set X) ≠ ⊤) {x : X}
    (hx : x ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X))
    (hc : ∀ q ∈ (Q : Subgroup X), x * q = q * x) : x ∈ (Q : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := Subgroup.normalizer ((Q : Subgroup X) : Set X) with hB
  have hreg := regular_of_borel hmodel Q hsolv
  have hbase : ∃ b : X ⧸ B, b ≠ QuotientGroup.mk 1 := by
    obtain ⟨g, hg⟩ : ∃ g : X, g ∉ B := by
      by_contra h
      push Not at h
      exact hBtop (eq_top_iff.mpr fun g _ => h g)
    refine ⟨QuotientGroup.mk g, fun h => hg ?_⟩
    have := QuotientGroup.eq.mp h
    simpa using B.inv_mem this
  have hfaith : ∀ y : X, (∀ ω : X ⧸ B, y • ω = ω) → y = 1 := by
    intro y hy
    have hker : (MulAction.toPermHom X (X ⧸ B)).ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom X (X ⧸ B)).ker with h | h
      · exact h
      · exfalso
        obtain ⟨b, hb⟩ := hbase
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
        have hg : g ∈ (MulAction.toPermHom X (X ⧸ B)).ker := by rw [h]; trivial
        have := congrArg (fun p : Equiv.Perm (X ⧸ B) => p (QuotientGroup.mk 1)) hg
        apply hb
        have h2 : g • (QuotientGroup.mk 1 : X ⧸ B) = QuotientGroup.mk 1 := this
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h2
        exact h2
    have : y ∈ (MulAction.toPermHom X (X ⧸ B)).ker := by
      rw [MonoidHom.mem_ker]
      exact Equiv.ext fun ω => hy ω
    rw [hker, Subgroup.mem_bot] at this
    exact this
  have hle : (Q : Subgroup X) ≤ B := Subgroup.le_normalizer
  have hj := two_power_of_centralizer B (Q : Subgroup X) Q.isPGroup' hfaith
    (fun α β hα hβ => by
      obtain ⟨⟨r, hr⟩, hrβ, -⟩ := hreg hα hβ
      exact ⟨r, hr, hrβ⟩) hbase hx hc
  obtain ⟨j, hj⟩ := hj
  let QB : Sylow 2 B := Q.subtype hle
  have hn : ((Q : Subgroup X).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr le_rfl
  have hodd : ¬ 2 ∣ ((Q : Subgroup X).subgroupOf B).index := by
    have h := Sylow.not_dvd_index QB
    rwa [show (QB : Subgroup B) = (Q : Subgroup X).subgroupOf B from Sylow.coe_subtype Q hle] at h
  exact mem_of_two_power hn hodd hx hj

theorem map_normalizer_subgroupOf {G : Type*} [Group G] {L P : Subgroup G} (hPL : P ≤ L) :
    (Subgroup.normalizer ((P.subgroupOf L : Subgroup L) : Set L)).map L.subtype =
      L ⊓ Subgroup.normalizer (P : Set G) := by
  refine Subgroup.ext (fun y => ?_)
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hb ⊢
    intro h
    constructor
    · intro hh
      exact Subgroup.mem_subgroupOf.mp ((hb ⟨h, hPL hh⟩).mp (Subgroup.mem_subgroupOf.mpr hh))
    · intro hh
      have hhL : h ∈ L := by
        have h1 : (b : G)⁻¹ * ((b : G) * h * (b : G)⁻¹) * (b : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem b.2) (hPL hh)) b.2
        simpa [mul_assoc] using h1
      exact Subgroup.mem_subgroupOf.mp ((hb ⟨h, hhL⟩).mpr (Subgroup.mem_subgroupOf.mpr hh))
  · rintro ⟨hyL, hyn⟩
    refine ⟨⟨y, hyL⟩, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.mp hyn (h : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact this

theorem isPGroup_subgroupOf' {G : Type*} [Group G] {P : Subgroup G} (L : Subgroup G)
    (hP : IsPGroup 2 P) : IsPGroup 2 (P.subgroupOf L) := by
  intro g
  obtain ⟨k, hk⟩ := hP ⟨((g.1 : ↥L) : G), Subgroup.mem_subgroupOf.mp g.2⟩
  have hk' : ((g.1 : ↥L) : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ⟨k, Subtype.ext (Subtype.ext hk')⟩

end Assembly

end BenderBorel

end Unc25G2

open Unc25G2 Unc25G2.BenderBorel in
theorem benderBorelFacts : BenderBorelFacts := by
  intro G _ _ L P hq hB hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup ↥L := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hP'2 : IsPGroup 2 (P.subgroupOf L) := isPGroup_subgroupOf' L hP.2.1
  let Q : Sylow 2 ↥L := hP'2.toSylow hP.2.2
  have hQ : (Q : Subgroup ↥L) = P.subgroupOf L := rfl
  obtain ⟨q, k, hq4, hBor⟩ := exists_borel_of_bender hB
  obtain ⟨hSE, ⟨D, hDcyc, hDodd, hQD, hsup⟩, hZpow, hZcard, hQcard⟩ := hBor Q
  have hrank := twoRank_of_borel Q hq4 hZpow hZcard
  have hcoatom : IsCoatom (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)) :=
    CFSG.ShultStronglyClosedTI.rank_two_strongEmbedding_isCoatom hrank _ hSE
  have hNeq : (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.normalizer (P : Set G) := by
    rw [hQ]; exact map_normalizer_subgroupOf hP.1
  have hsolv : Group.IsSolvable (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)) :=
    isSolvable_normalizer_of_sup_cyclic Q.isPGroup' hDcyc hsup
  refine ⟨?_, ?_⟩
  · apply charTwo_of_normal_pGroup (E := P)
    · exact fun x hx => ⟨hP.1 hx, Subgroup.le_normalizer hx⟩
    · exact fun x hx => hx.2
    · exact hP.2.1
    · rintro x ⟨⟨hxL, hxn⟩, hxc⟩
      have hxB : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
        have : x ∈ (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)).map L.subtype := by
          rw [hNeq]; exact ⟨hxL, hxn⟩
        obtain ⟨b, hb, hbx⟩ := this
        have : b = ⟨x, hxL⟩ := Subtype.ext hbx
        rwa [← this]
      have hmem := centralizer_le_of_borel (isSimpleBenderGroup_of_fusion hB) Q hsolv hcoatom.1 hxB
        (fun q hq => by
          have h1 := Subgroup.mem_centralizer_iff.mp hxc (q : G)
            (Subgroup.mem_subgroupOf.mp (show q ∈ P.subgroupOf L from hq))
          exact Subtype.ext h1.symm)
      exact Subgroup.mem_subgroupOf.mp (show (⟨x, hxL⟩ : ↥L) ∈ P.subgroupOf L from hmem)
  · intro X' hNX hXL
    have hX'' : Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) ≤ X'.subgroupOf L := fun b hb =>
      Subgroup.mem_subgroupOf.mpr (hNX (by rw [← hNeq]; exact ⟨b, hb, rfl⟩))
    rcases eq_or_lt_of_le hX'' with h | h
    · left
      rw [← hNeq, h, Subgroup.map_subgroupOf_eq_of_le hXL]
    · right
      have htop := hcoatom.2 _ h
      have hLX : L ≤ X' := Subgroup.subgroupOf_eq_top.mp htop
      exact le_antisymm hXL hLX

end CFSG.QuasithinUnique
