module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

private lemma pCore_two_le_pPrimeCore_aux {H : Type*} [Group H] [Finite H] {q : ℕ}
    [Fact q.Prime] (hq2 : q ≠ 2) : CFSG.pCore 2 H ≤ CFSG.pPrimeCore q H := by
  have hcop : Nat.Coprime q (Nat.card (CFSG.pCore 2 H)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := H) (p := 2))
    rw [hn]
    exact ((Nat.coprime_primes Fact.out Nat.prime_two).2 hq2).pow_right n
  exact le_sSup ⟨inferInstance, hcop⟩

theorem pCore_two_quot_eq_bot : CFSG.pCore 2 (Y ⧸ CFSG.pCore 2 Y) = ⊥ := by
  set N : Subgroup Y := CFSG.pCore 2 Y
  set K : Subgroup Y := (CFSG.pCore 2 (Y ⧸ N)).comap (QuotientGroup.mk' N)
  have hKn : K.Normal := (CFSG.pCore_normal (p := 2) (G := Y ⧸ N)).comap _
  have hKp : IsPGroup 2 K := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := Y ⧸ N) ⟨_, hx⟩
    have hxa : x ^ (2 ^ a) ∈ N := by
      have h1 := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one, QuotientGroup.mk'_apply] at h1
      rw [← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := 2) (G := Y) ⟨_, hxa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
    rw [pow_add, pow_mul, h2]
  have hle : K ≤ N := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ K := hy
  exact (QuotientGroup.eq_one_iff x).mpr (hle hx)

theorem pPrimeCore_quot_pCore_two (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pPrimeCore p (Y ⧸ CFSG.pCore 2 Y) =
      (CFSG.pPrimeCore p Y).map (QuotientGroup.mk' (CFSG.pCore 2 Y)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup Y := CFSG.pCore 2 Y
  set X : Subgroup Y := CFSG.pPrimeCore p Y
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  refine le_antisymm ?_ (CFSG.map_pPrimeCore_le π hπ)
  set K : Subgroup Y := (CFSG.pPrimeCore p (Y ⧸ N)).comap π
  have hKN : K.Normal := (CFSG.pPrimeCore_normal (p := p) (G := Y ⧸ N)).comap π
  have hmapK : K.map π = CFSG.pPrimeCore p (Y ⧸ N) :=
    Subgroup.map_comap_eq_self_of_surjective hπ _
  have hNK : N ≤ K := by
    rw [← QuotientGroup.ker_mk' N]
    exact MonoidHom.ker_le_comap π _
  let g : ↥K →* (Y ⧸ N) := π.comp K.subtype
  have hgker : g.ker = N.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact (QuotientGroup.eq_one_iff (x : Y))
  have hgrange : g.range = K.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card K = Nat.card N * Nat.card (K.map π) := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hgker, hgrange] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv] at h
    exact h.symm
  have hcopN : Nat.Coprime p (Nat.card N) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := Y) (p := 2))
    rw [hn]
    exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right n
  have hcopK : Nat.Coprime p (Nat.card K) := by
    rw [hcard]
    exact hcopN.mul_right (by rw [hmapK]; exact CFSG.pPrimeCore_coprime_card)
  have hKX : K ≤ X := le_sSup ⟨hKN, hcopK⟩
  rw [← hmapK]
  exact Subgroup.map_mono hKX

theorem pRank_pPrimeCore_quot_le (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (CFSG.pPrimeCore p (Y ⧸ CFSG.pCore 2 Y)) ≤
      CFSG.Open.pRank r (CFSG.pPrimeCore p Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  rw [pPrimeCore_quot_pCore_two hp hp2]
  set X : Subgroup Y := CFSG.pPrimeCore p Y
  set N : Subgroup Y := CFSG.pCore 2 Y
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  set M : Subgroup ↥X := N.subgroupOf X
  haveI hMnormal : M.Normal := (CFSG.pCore_normal (p := 2) (G := Y)).subgroupOf X
  have hMp : IsPGroup 2 M := (CFSG.pCore_isPGroup (G := Y) (p := 2)).comap_subtype
  have hcopM : ¬ r ∣ Nat.card M := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hMp
    rw [hk]
    intro hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))
  let φ : ↥X →* ↥(X.map π) :=
    ((π.comp X.subtype).codRestrict (X.map π) fun x =>
      Subgroup.mem_map.mpr ⟨(x : Y), x.2, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφker : φ.ker = M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : Y)).mp (Subtype.ext_iff.mp hx)
    · intro hx
      exact Subtype.ext_iff.mpr ((QuotientGroup.eq_one_iff (x : Y)).mpr hx)
  have hiso : (↥X ⧸ M) ≃* ↥(X.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  have heq : CFSG.Open.pRank r (X.map π) = CFSG.Open.pRank r X := by
    calc CFSG.Open.pRank r (X.map π)
        = CFSG.Open.pRank r (⊤ : Subgroup ↥(X.map π)) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
      _ = CFSG.Open.pRank r (⊤ : Subgroup (↥X ⧸ M)) := by
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt hiso.symm]
      _ = CFSG.Open.pRank r (⊤ : Subgroup ↥X) :=
          CFSG.SectionRank.pRank_quotient_eq M hcopM
      _ = CFSG.Open.pRank r X :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup X).symm
  exact heq.le

theorem nonempty_quot_pPrimeCore_quot_mulEquiv (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (((Y ⧸ CFSG.pCore 2 Y) ⧸ CFSG.pPrimeCore p (Y ⧸ CFSG.pCore 2 Y)) ≃*
      (Y ⧸ CFSG.pPrimeCore p Y)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (pPrimeCore_quot_pCore_two hp hp2)).trans ?_⟩
  exact QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 Y) (CFSG.pPrimeCore p Y)
    (pCore_two_le_pPrimeCore_aux hp2)

theorem isSolvable_pPrimeCore_of_quot (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Group.IsSolvable ↥(CFSG.pPrimeCore p (Y ⧸ CFSG.pCore 2 Y))) :
    Group.IsSolvable ↥(CFSG.pPrimeCore p Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [pPrimeCore_quot_pCore_two hp hp2] at h
  haveI : Group.IsSolvable ↥((CFSG.pPrimeCore p Y).map
      (QuotientGroup.mk' (CFSG.pCore 2 Y))) := h
  let X : Subgroup Y := CFSG.pPrimeCore p Y
  let N : Subgroup Y := CFSG.pCore 2 Y
  let M : Subgroup ↥X := N.subgroupOf X
  have hMp : IsPGroup 2 M := (CFSG.pCore_isPGroup (G := Y) (p := 2)).comap_subtype
  haveI hMnil : Group.IsNilpotent ↥M := IsPGroup.isNilpotent hMp
  haveI : Group.IsSolvable ↥M := inferInstance
  let φ : ↥X →* ↥(X.map (QuotientGroup.mk' N)) :=
    (((QuotientGroup.mk' N).comp X.subtype).codRestrict (X.map (QuotientGroup.mk' N))
      fun x => Subgroup.mem_map.mpr ⟨(x : Y), x.2, rfl⟩)
  have hφker : φ.ker = M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : Y)).mp (Subtype.ext_iff.mp hx)
    · intro hx
      exact Subtype.ext_iff.mpr ((QuotientGroup.eq_one_iff (x : Y)).mpr hx)
  refine Group.isSolvable_of_ker_le_range M.subtype φ ?_
  intro x hx
  rw [hφker] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem closure_pElem_quot_eq_top (hp : p.Prime) (N : Subgroup Y) [N.Normal]
    (h : closure {y : Y | ∃ k : ℕ, orderOf y = p ^ k} = ⊤) :
    closure {y : Y ⧸ N | ∃ k : ℕ, orderOf y = p ^ k} = ⊤ := by
  let S : Set Y := {y : Y | ∃ k : ℕ, orderOf y = p ^ k}
  let T : Set (Y ⧸ N) := {y : Y ⧸ N | ∃ k : ℕ, orderOf y = p ^ k}
  have hS : closure S = ⊤ := h
  have himage : (QuotientGroup.mk' N) '' S ⊆ T := by
    rintro z ⟨y, ⟨k, hk⟩, rfl⟩
    have hdvd : orderOf ((QuotientGroup.mk' N) y) ∣ p ^ k := by
      rw [← hk]
      exact orderOf_map_dvd (QuotientGroup.mk' N) y
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨i, hi⟩
  have hchain : (⊤ : Subgroup (Y ⧸ N)) = closure ((QuotientGroup.mk' N) '' S) := by
    calc ⊤ = (⊤ : Subgroup Y).map (QuotientGroup.mk' N) :=
          (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)).symm
      _ = (closure S).map (QuotientGroup.mk' N) :=
          congrArg (fun U : Subgroup Y => U.map (QuotientGroup.mk' N)) hS.symm
      _ = closure ((QuotientGroup.mk' N) '' S) := MonoidHom.map_closure _ _
  have hmain : (⊤ : Subgroup (Y ⧸ N)) ≤ closure T :=
    hchain.le.trans (Subgroup.closure_mono himage)
  exact top_le_iff.mp hmain

theorem nonempty_center_quot_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty ((A ⧸ center A) ≃* (B ⧸ center B)) :=
  ⟨QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
