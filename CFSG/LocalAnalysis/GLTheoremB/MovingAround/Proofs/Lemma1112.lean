module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BSL34Sylow
public import CFSG.Models.PGLSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn card_of_isLThreeFour)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Lemma1112

variable {G : Type} [Group G]

theorem isElemAbelian_of_le {p : ℕ} {E H : Subgroup G} (hE : IsElemAbelian p E) (hHE : H ≤ E) :
    IsElemAbelian p H := by
  have hcomm : ∀ x y : G, x ∈ E → y ∈ E → x * y = y * x := fun x y hx hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 b.1 (hHE a.2) (hHE b.2))⟩⟩, fun x hx => hE.2 x (hHE hx)⟩

theorem card_eq_pow_pRank {p : ℕ} [Fact p.Prime] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian p E) : Nat.card E = p ^ CFSG.Open.pRank p E := by
  have hpg : IsPGroup p E := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨g, hg⟩
    have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 g hg)
    rw [Subgroup.orderOf_mk]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  unfold CFSG.Open.pRank
  have hgr : IsGreatest {k | ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧ Nat.card F = p ^ k} n := by
    refine ⟨⟨E, le_rfl, hE, hn⟩, ?_⟩
    rintro k ⟨F, hFE, -, hFk⟩
    have hle : p ^ k ≤ p ^ n := by
      rw [← hFk, ← hn]
      exact Subgroup.card_le_of_le hFE
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle
  rw [hgr.csSup_eq, hn]

theorem center_eq_bot_of_isLThreeFour {X : Type} [Group X] (hX : IsLThreeFour X) :
    Subgroup.center X = ⊥ := by
  have h20 : Nat.card X = 20160 := card_of_isLThreeFour hX
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hX
  haveI : IsSimpleGroup (StatedProj (StatedSL 3 F)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 3) F (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  haveI : IsSimpleGroup X := e.isSimpleGroup
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : X, x * y = y * x := fun x y => by
      have hx : x ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.1 hx y).symm
    letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
    have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
    rw [h20] at hp
    norm_num at hp

theorem not_le_K [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) (hA : IsElemAbelian 3 A) (hL : IsLThreeFour (barOf 3 K)) :
    ¬ A ≤ K := by
  intro hAK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨haA, ha1⟩ := h.ha
  have haK : a ∈ K := hAK haA
  have hord : orderOf (⟨a, haK⟩ : K) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA.2 a haA) ha1
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) := h.hK.1
  have hcomm : ∀ k ∈ K, a * k = k * a := fun k hk =>
    Subgroup.mem_centralizer_iff.1 (hKC hk) a (Set.mem_singleton a)
  have hz : (QuotientGroup.mk (⟨a, haK⟩ : K) : barOf 3 K) ∈ Subgroup.center (barOf 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (hcomm k.1 k.2).symm
  have hz1 : (QuotientGroup.mk (⟨a, haK⟩ : K) : barOf 3 K) = 1 := by
    rw [center_eq_bot_of_isLThreeFour hL] at hz
    exact Subgroup.mem_bot.1 hz
  have hmem : (⟨a, haK⟩ : K) ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 hz1
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  have h3 : orderOf (⟨⟨a, haK⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥K)) = 3 :=
    (Subgroup.orderOf_mk _ hmem).trans hord
  have hdvd := orderOf_dvd_natCard (⟨⟨a, haK⟩, hmem⟩ : ↥(GLAPPrimeCore 3 ↥K))
  rw [h3] at hdvd
  have := hcop.eq_one_of_dvd hdvd
  norm_num at this

end Lemma1112

@[expose] def Lemma1112.P1Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K),
    IsSylowIn 3 (centBar 3 (Cg a) K) (Subgroup.zpowers a) ∧ CFSG.Open.pRank 3 (Cg a) = 3

@[expose] def Lemma1112.P2Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K), IsSCp 3 ⊤ A → CFSG.Open.pRank 3 (Cg a) = 3 →
    ∀ U : Subgroup G, IsEkIn 3 1 A U → ¬ U ≤ A ⊓ K → GConj (Subgroup.zpowers a) U

@[expose] def Lemma1112.P3Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K), ∀ U : Subgroup G, IsEkIn 3 1 (E ⊓ A) U →
      ¬ GConj (Subgroup.zpowers a) U

theorem lemma1112_of_inputs (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h104ii : Lemma104_iiStatement) (hP1 : Lemma1112.P1Claim) (hP2 : Lemma1112.P2Claim)
    (hP3 : Lemma1112.P3Claim) : Lemma1112Statement := by
  intro G _ _ m p B M E A a K h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨rfl, hA3, hL⟩ := h1111 h
  have hrkA0 : CFSG.Open.pRank 3 (E ⊓ A) = 2 := (h119 h).1
  have hsc : IsSCp 3 ⊤ A :=
    (h104ii h.toCex117Base.toSec11.toSec10Fails h.pair).2
  have hel : IsElemAbelian 3 A := hsc.2.1
  obtain ⟨hsyl, hrkC⟩ := hP1 h
  have hnot : ¬ A ≤ K := Lemma1112.not_le_K h hel hL
  have hA0el : IsElemAbelian 3 (E ⊓ A) := Lemma1112.isElemAbelian_of_le hel inf_le_right
  have hcardA : Nat.card A = 27 := by
    rw [Lemma1112.card_eq_pow_pRank hel, hA3]
    norm_num
  have hcardA0 : Nat.card ↥(E ⊓ A) = 9 := by
    rw [Lemma1112.card_eq_pow_pRank hA0el, hrkA0]
    norm_num
  have hAK9 : Nat.card ↥(A ⊓ K) ≤ 9 := by
    have hne : A ⊓ K ≠ A := by
      intro heq
      apply hnot
      intro x hx
      have hx' : x ∈ A ⊓ K := by rw [heq]; exact hx
      exact (Subgroup.mem_inf.1 hx').2
    have hdvd : Nat.card ↥(A ⊓ K) ∣ 3 ^ 3 := by
      have hd := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ K ≤ A)
      rw [hcardA] at hd
      exact hd
    obtain ⟨k, hk, hkd⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    interval_cases k
    · rw [hkd]; norm_num
    · rw [hkd]; norm_num
    · rw [hkd]; norm_num
    · exfalso
      apply hne
      exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardA, hkd]; norm_num)
  have hA0K : E ⊓ A = A ⊓ K := by
    have hle : E ⊓ A ≤ A ⊓ K := by
      intro e he
      by_contra heK
      have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
      have he1 : e ≠ 1 := by
        rintro rfl
        exact heK (Subgroup.one_mem _)
      have hord : orderOf e = 3 := orderOf_eq_prime (hel.2 e heA) he1
      have hU : IsEkIn 3 1 A (Subgroup.zpowers e) :=
        ⟨Subgroup.zpowers_le.2 heA, Lemma1112.isElemAbelian_of_le hel (Subgroup.zpowers_le.2 heA),
          by rw [Nat.card_zpowers, hord, pow_one]⟩
      have hnU : ¬ Subgroup.zpowers e ≤ A ⊓ K := fun hz => heK (hz (Subgroup.mem_zpowers e))
      have hU0 : IsEkIn 3 1 (E ⊓ A) (Subgroup.zpowers e) :=
        ⟨Subgroup.zpowers_le.2 he, Lemma1112.isElemAbelian_of_le hA0el (Subgroup.zpowers_le.2 he),
          by rw [Nat.card_zpowers, hord, pow_one]⟩
      exact hP3 h _ hU0 (hP2 h hsc hrkC _ hU hnU)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA0]; exact hAK9)
  refine ⟨⟨hsyl, hrkC⟩, hA0K, fun U hU => ⟨fun hn => ?_, fun hg hle => ?_⟩⟩
  · rw [hA0K] at hn
    exact hP2 h hsc hrkC U hU hn
  · exact hP3 h U ⟨hle, hU.2.1, hU.2.2⟩ hg

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
