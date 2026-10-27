module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017LyFive
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Table
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso
public import CFSG.RankThree.PartTwo.Census.Sporadic.J3
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.McL
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.SignalizerFunctor.Helpers

theorem glaTwoLocalRank_le_of_not_dvd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (k : ℕ)
    (h : ∀ t : X, orderOf t = 2 → ¬ p ^ k ∣ Nat.card (Subgroup.centralizer ({t} : Set X))) :
    GLATwoLocalRank p X ≤ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine glaTwoLocalRank_le_of_card_le hp fun R E hR hR2 hEN hE =>
    card_le_of_involution_data_pk hp hp2 k (fun t ht F hF hFe => ?_)
      (fun t ht F hF _ hcard => absurd (hcard ▸ Subgroup.card_dvd_of_le hF) (h t ht)) R E hR hR2
      hEN hE
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian hFe)
  rw [hm]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hlt
  push Not at hlt
  exact h t ht ((Nat.pow_dvd_pow p hlt.le).trans (hm ▸ Subgroup.card_dvd_of_le hF))

theorem twoRankLe_of_model {s : TauCeti.SporadicName} {p k : ℕ} (hp : p.Prime) {X : Type}
    [Group X] (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* X) → GLATwoLocalRank p K ≤ k) :
    TwoRankLe p s k := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := hX
  exact h K ⟨e.trans b.symm⟩

section J3

open CFSG.Sporadic.Schreier

theorem twoRankLe_three_j3 :
    TwoRankLe 3 .J3 2 := by
  refine twoRankLe_of_model (X := j3P) Nat.prime_three
    (CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv.map fun b => j3PermEquiv.symm.trans b)
    fun K _ _ ⟨φ⟩ => ?_
  rw [← CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr (by norm_num) φ]
  refine glaTwoLocalRank_le_of_not_dvd Nat.prime_three (by norm_num) 2 fun t ht h9 => ?_
  rw [CFSG.RankThree.PartTwo.Census.card_centralizer_j3P ht] at h9
  exact absurd h9 (by norm_num)

end J3

section Alt

open Equiv Equiv.Perm

theorem not_dvd_card_centralizer_of_even_involution_eight {σ : Perm (Fin 8)} (h2 : orderOf σ = 2)
    (hs : Perm.sign σ = 1) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) := by
  rw [Perm.nat_card_centralizer]
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [h2]; exact Nat.prime_two)
  rw [h2] at hn
  have hsum := Perm.sum_cycleType_le σ
  have hsign := Perm.sign_of_cycleType σ
  rw [hn] at hsum hsign ⊢
  rw [hs] at hsign
  simp only [Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hn4 : n ≤ 4 := by omega
  interval_cases n <;> first | exact absurd hsign (by decide) | decide

variable {K : Type} [Group K] [Finite K]

theorem injective_of_center_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C : Type} [Group C]
    [Finite C] (hZ : Nat.card (Subgroup.center C) = 2) {P : Type} [Group P] (φ : C →* P)
    (hker : φ.ker ≤ Subgroup.center C) {F : Subgroup C} (hF : IsElemAbelian p F) :
    Function.Injective (φ.comp F.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
  have hxZ : (x : C) ∈ Subgroup.center C := hker hx
  have h2 : (x : C) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center C) (x := ⟨x, hxZ⟩)
    rw [hZ] at this
    simpa using congrArg Subtype.val this
  have hpx : (x : C) ^ p = 1 := hF.2 x x.2
  have hg := pow_gcd_eq_one.2 ⟨h2, hpx⟩
  rw [(Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2), pow_one] at hg
  rw [Subgroup.mem_bot]
  exact Subtype.ext hg

theorem isElemAbelian_range_p {p : ℕ} {A P : Type} [Group A] [Group P] (ψ : A →* P)
    (hA : ∀ a b : A, a * b = b * a) (h3 : ∀ a : A, a ^ p = 1) : IsElemAbelian p ψ.range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨a, x, rfl⟩ := a
    obtain ⟨b, y, rfl⟩ := b
    show ψ x * ψ y = ψ y * ψ x
    rw [← map_mul, ← map_mul, hA]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, h3, map_one]

theorem involution_data_of_doubleCover {p n k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnk : n / p ≤ k)
    (halt : ∀ σ : Perm (Fin n), orderOf σ = 2 → Perm.sign σ = 1 →
      ¬ p ^ k ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))))
    {t : K} (ht : orderOf t = 2)
    (hD : CFSG.GH74.GLS.IsDoubleCoverOfAlt ↥(Subgroup.centralizer ({t} : Set K)) n) :
    (∀ F : Subgroup K, F ≤ Subgroup.centralizer ({t} : Set K) → IsElemAbelian p F →
      Nat.card F ≤ p ^ k) ∧
    (∀ F : Subgroup K, F ≤ Subgroup.centralizer ({t} : Set K) → IsElemAbelian p F →
      Nat.card F = p ^ k → ∀ u : K, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set K) →
        u * t = t * u → u = t) := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hD
  set C := Subgroup.centralizer ({t} : Set K) with hCdef
  let φ : ↥C →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥C)))
  have hker : φ.ker ≤ Subgroup.center ↥C := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : e (QuotientGroup.mk x) = 1 := Subtype.ext hx
    have h2 : (QuotientGroup.mk x : ↥C ⧸ Subgroup.center ↥C) = 1 := by
      rw [← map_one e.symm, ← h1, MulEquiv.symm_apply_apply]
    exact (QuotientGroup.eq_one_iff x).1 h2
  have hdata : ∀ F : Subgroup K, F ≤ C → IsElemAbelian p F →
      IsElemAbelian p ((φ.comp (F.subgroupOf C).subtype).range) ∧
        Nat.card ((φ.comp (F.subgroupOf C).subtype).range) = Nat.card F := by
    intro F hFC hF
    have hF' : IsElemAbelian p (F.subgroupOf C) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · exact comm_of_elemAbelian hF a.2 b.2
      · exact hF.2 _ hx
    have hinj := injective_of_center_two_p hp hp2 hZ φ hker hF'
    refine ⟨isElemAbelian_range_p _ (fun a b => Subtype.ext (Subtype.ext
      (comm_of_elemAbelian hF a.2 b.2))) (fun a => Subtype.ext (Subtype.ext (hF.2 _ a.2))), ?_⟩
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv
  refine ⟨fun F hFC hF => ?_, fun F hFC hF hFk u hu hufF hut => ?_⟩
  · obtain ⟨hE, hc⟩ := hdata F hFC hF
    rw [← hc]
    haveI : Fact p.Prime := ⟨hp⟩
    refine (CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltInputs.card_le_pow_div hE).trans ?_
    rw [Fintype.card_fin]
    exact Nat.pow_le_pow_right hp.pos hnk
  · by_contra hne
    have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hut
    have htZ : (⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : ↥C) ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
    set ū : Equiv.Perm (Fin n) := φ ⟨u, huC⟩ with hū
    have hū1 : ū ≠ 1 := by
      intro h1
      have huZ : (⟨u, huC⟩ : ↥C) ∈ Subgroup.center ↥C := hker h1
      classical
      haveI : Fintype ↥(Subgroup.center ↥C) := Fintype.ofFinite _
      have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; norm_num at ht
      have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; norm_num at hu
      let zt : ↥(Subgroup.center ↥C) := ⟨_, htZ⟩
      let zu : ↥(Subgroup.center ↥C) := ⟨_, huZ⟩
      have hcard := Finset.card_le_univ ({1, zt, zu} : Finset ↥(Subgroup.center ↥C))
      rw [← Nat.card_eq_fintype_card, hZ] at hcard
      rw [Finset.card_insert_of_notMem, Finset.card_pair] at hcard
      · omega
      · intro h
        exact hne (congrArg (fun z : ↥(Subgroup.center ↥C) => ((z : ↥C) : K)) h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => ht1 (congrArg (fun z : ↥(Subgroup.center ↥C) => ((z : ↥C) : K)) h).symm,
          fun h => hu1 (congrArg (fun z : ↥(Subgroup.center ↥C) => ((z : ↥C) : K)) h).symm⟩
    have hū2 : orderOf ū = 2 := by
      refine orderOf_eq_prime ?_ hū1
      rw [hū, ← map_pow]
      have : (⟨u, huC⟩ : ↥C) ^ 2 = 1 := Subtype.ext (by
        have := pow_orderOf_eq_one u
        rwa [hu] at this)
      rw [this, map_one]
    have hūs : Equiv.Perm.sign ū = 1 :=
      Equiv.Perm.mem_alternatingGroup.1 (e (QuotientGroup.mk ⟨u, huC⟩)).2
    obtain ⟨-, hc⟩ := hdata F hFC hF
    have hle : (φ.comp (F.subgroupOf C).subtype).range ≤
        Subgroup.centralizer ({ū} : Set (Equiv.Perm (Fin n))) := by
      rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hū, MonoidHom.comp_apply, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show ((x : ↥C) : K) * u = u * ((x : ↥C) : K)
      exact (Subgroup.mem_centralizer_iff.1 hufF) _ (Subgroup.mem_subgroupOf.1 x.2)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hc, hFk] at hdvd
    exact halt ū hū2 hūs hdvd

end Alt

section McL

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 10000 in
theorem twoRankLe_three_mcl :
    TwoRankLe 3 .McL 2 := by
  have hbr : Nonempty (NativeSporadic.Carrier .McL ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) :=
    CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  refine twoRankLe_of_model Nat.prime_three hbr ?_
  intro K _ _ hK
  have hK' : IsSporadic K .McL := hK
  have hdata := fun (t : K) (ht : orderOf t = 2) =>
    involution_data_of_doubleCover (K := K) (p := 3) (n := 8) (k := 2) Nat.prime_three
      (by norm_num) (by norm_num)
      (fun σ h2 hs => not_dvd_card_centralizer_of_even_involution_eight h2 hs) ht
      (CFSG.EvenSporadicStandard.McLStd.isDoubleCoverOfAlt_mcl hK' ht)
  exact glaTwoLocalRank_le_of_card_le Nat.prime_three fun R E hR hR2 hEN hE =>
    card_le_of_involution_data_pk Nat.prime_three (by norm_num) 2
      (fun t ht => (hdata t ht).1) (fun t ht => (hdata t ht).2) R E hR hR2 hEN hE

end McL

end CFSG.LocalAnalysis.GLTheoremA.H1017
