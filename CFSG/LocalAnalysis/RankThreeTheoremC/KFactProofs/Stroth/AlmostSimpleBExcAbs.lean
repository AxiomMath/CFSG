module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerReduce
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LieType.SeitzGeneration
open scoped Pointwise

section Abstract

@[expose] def NoSylowNormalizesTwo (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ R E : Subgroup X, R ≠ ⊥ → IsPGroup 2 R → E ≤ Subgroup.normalizer (R : Set X) →
    ¬ p ^ (Nat.card X).factorization p ∣ Nat.card E

variable {X : Type*} [Group X] [Finite X]

theorem odd_card_of_normal_of_noSylowNormalizes {p : ℕ} (hp : p.Prime)
    (h : NoSylowNormalizesTwo p X) (C : Subgroup X)
    (hC : (Nat.card X).factorization p ≤ (Nat.card C).factorization p)
    (N : Subgroup C) [N.Normal] (hcop : Nat.Coprime p (Nat.card N)) : Odd (Nat.card N) := by
  classical
  by_contra hodd
  have h2 : 2 ∣ Nat.card N := (Nat.not_odd_iff_even.1 hodd).two_dvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow p C) := inferInstance
  obtain ⟨S, hS⟩ := exists_sylow_normalized_of_isPGroup (ℓ := 2) N (P : Subgroup C)
    P.isPGroup' hcop
  have hSne : (S : Subgroup N) ≠ ⊥ := by
    intro h0
    have h1 : Nat.card (S : Subgroup N) = 1 := by rw [h0]; simp
    rw [Sylow.card_eq_multiplicity] at h1
    have hf : 1 ≤ (Nat.card N).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have := Nat.one_lt_pow (by omega : (Nat.card N).factorization 2 ≠ 0) (by norm_num : 1 < 2)
    omega
  set A : Subgroup C := (S : Subgroup N).map N.subtype with hA
  set R : Subgroup X := A.map C.subtype with hR
  have hR2 : IsPGroup 2 R := by
    intro x
    obtain ⟨_, ⟨s, hs, rfl⟩, hx⟩ := x.2
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hx, ← map_pow, ← map_pow, hk', map_one, map_one]
  have hRne : R ≠ ⊥ := by
    intro h0
    apply hSne
    have h1 : A = ⊥ := (Subgroup.map_eq_bot_iff_of_injective A C.subtype_injective).1 h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 h1
  have hMR : (P : Subgroup C).map C.subtype ≤ Subgroup.normalizer (R : Set X) :=
    (Subgroup.map_mono hS).trans (Subgroup.le_normalizer_map C.subtype)
  refine h R _ hRne hR2 hMR ?_
  rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
  exact pow_dvd_pow p hC

theorem centralizer_pPart_of_sylowTorus {p m : ℕ} (hp : p.Prime) (hT : SylowTorus X p m)
    {d : X} (hdp : d ^ p = 1) :
    (Nat.card X).factorization p ≤
      (Nat.card (Subgroup.centralizer ({d} : Set X))).factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, E, hTc, hconj, -, -, -, -⟩ := hT.exists_torus
  have hdP : IsPGroup p (Subgroup.zpowers d) := by
    intro g
    obtain ⟨n, hn⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
  obtain ⟨Q, hdQ⟩ := hdP.exists_le_sylow
  obtain ⟨g, hg⟩ := hconj (Q : Subgroup X) Q.isPGroup'
  have hcomm : ∀ a ∈ (Q : Subgroup X), ∀ b ∈ (Q : Subgroup X), a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, hs, hsa⟩ := hg ha
    obtain ⟨t, ht, htb⟩ := hg hb
    rw [← hsa, ← htb]
    show (MulAut.conj g).toMonoidHom s * (MulAut.conj g).toMonoidHom t =
      (MulAut.conj g).toMonoidHom t * (MulAut.conj g).toMonoidHom s
    rw [← map_mul, ← map_mul, setLike_mul_comm hs ht]
  have hQc : (Q : Subgroup X) ≤ Subgroup.centralizer ({d} : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm x hx d (hdQ (Subgroup.mem_zpowers d))
  have hdvd : Nat.card (Q : Subgroup X) ∣ Nat.card (Subgroup.centralizer ({d} : Set X)) :=
    Subgroup.card_dvd_of_le hQc
  rw [Sylow.card_eq_multiplicity] at hdvd
  exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd

theorem pClosureOdd_of_sylowTorus {p m : ℕ} (hp : p.Prime) (hT : SylowTorus X p m)
    (h : NoSylowNormalizesTwo p X) : PClosureOdd p X := by
  intro d _ hdp
  refine OddPCoreInClosure.of_odd_core fun N hN hcop => ?_
  haveI := hN
  exact odd_card_of_normal_of_noSylowNormalizes hp h (Subgroup.centralizer ({d} : Set X))
    (centralizer_pPart_of_sylowTorus hp hT hdp) N hcop

end Abstract

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
