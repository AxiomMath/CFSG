module

import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.PreuniquenessRankFour.FrattiniEmbedding
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSymplectic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers

private theorem gl83Solv_isSolvable_of_card_dvd_two_three {H : Type*} [Group H] [Finite H]
    {a b : ℕ} (h : Nat.card H ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

private theorem gl83Solv_eq_one_of_dvd {n : ℕ} (h : n ∣ 2 ^ 5 * 3) (hmod : n ≡ 1 [MOD 13]) :
    n = 1 := by
  have hle : n ≤ 96 := Nat.le_of_dvd (by norm_num) h
  unfold Nat.ModEq at hmod
  interval_cases n <;> omega

private theorem gl83Solv_isSolvable_of_card_dvd {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 2 ^ 5 * 3 * 13) : Group.IsSolvable H := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 13 H) := inferInstance
  have hindex : (P : Subgroup H).index ∣ 2 ^ 5 * 3 := by
    have h1 : (P : Subgroup H).index ∣ 2 ^ 5 * 3 * 13 := (Subgroup.index_dvd_card _).trans h
    have h2 : Nat.Coprime (P : Subgroup H).index 13 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 P.not_dvd_index)
    exact h2.dvd_of_dvd_mul_right h1
  have hn : Nat.card (Sylow 13 H) = 1 :=
    gl83Solv_eq_one_of_dvd (P.card_dvd_index.trans hindex) (card_sylow_modEq_one 13 H)
  have : Subsingleton (Sylow 13 H) := Finite.card_le_one_iff_subsingleton.mp hn.le
  have : (P : Subgroup H).Normal := Sylow.normal_of_subsingleton P
  have : Group.IsSolvable P := by
    have := P.isPGroup'.isNilpotent
    infer_instance
  have : Group.IsSolvable (H ⧸ (P : Subgroup H)) := by
    apply gl83Solv_isSolvable_of_card_dvd_two_three (a := 5) (b := 1)
    rw [← Subgroup.index_eq_card]
    simpa using hindex
  exact Group.isSolvable_of_subgroup_quotient (P : Subgroup H)

private theorem gl83Solv_dvd_of_not_nine_dvd {c : ℕ} (h : c ∣ 2 ^ 5 * 13 * 3 ^ 3)
    (h9 : ¬ 9 ∣ c) : c ∣ 2 ^ 5 * 3 * 13 := by
  obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.1 h
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h₂
  have hj : j ≤ 1 := by
    by_contra hj
    exact h9 (Dvd.dvd.mul_left
      (Nat.dvd_trans (by norm_num : 9 ∣ 3 ^ 2) (pow_dvd_pow 3 (by omega))) c₁)
  calc c₁ * 3 ^ j ∣ 2 ^ 5 * 13 * 3 ^ 1 := Nat.mul_dvd_mul h₁ (pow_dvd_pow 3 hj)
    _ = 2 ^ 5 * 3 * 13 := by norm_num

private theorem gl83Solv_card_quotient_dvd_GL {Q : Type*} [Group Q] [Finite Q]
    (hcentralizer : Subgroup.centralizer (CFSG.Open.pCore 3 Q : Set Q) ≤ CFSG.Open.pCore 3 Q) :
    ∃ d : ℕ, Nat.card (CFSG.Open.pCore 3 Q ⧸ frattini (CFSG.Open.pCore 3 Q)) = 3 ^ d ∧
      Nat.card (Q ⧸ CFSG.Open.pCore 3 Q) ∣ ∏ i : Fin d, (3 ^ d - 3 ^ (i : ℕ)) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R := CFSG.Open.pCore 3 Q
  let : R.Normal := CFSG.PreuniquenessRankFour.Helpers.pCore_normal 3
  have hR : IsPGroup 3 R := CFSG.PreuniquenessRankFour.Helpers.pCore_isPGroup 3
  let : IsMulCommutative (R ⧸ frattini R) :=
    CFSG.PreuniquenessRankFour.Helpers.pGroup_frattini_quotient_isMulCommutative 3 hR
  let : CommGroup (R ⧸ frattini R) := IsMulCommutative.instCommGroup
  let : Module (ZMod 3) (Additive (R ⧸ frattini R)) :=
    AddCommGroup.zmodModule (n := 3) fun member => by
      change Additive.ofMul (member.toMul ^ 3) = 0
      rw [CFSG.PreuniquenessRankFour.Helpers.pGroup_frattini_quotient_pow_eq_one 3 hR]
      rfl
  let : MulDistribMulAction Q R := MulDistribMulAction.compHom R (MulAut.conjNormal (H := R))
  let := CFSG.PreuniquenessRankFour.Helpers.characteristic_quotient_mulDistribMulAction
    (acting := Q) (frattini R)
  let hom := CFSG.PreuniquenessRankFour.Helpers.multiplicative_action_zmod_linear_aut
    (acting := Q) (source := R ⧸ frattini R) 3
  have hkernel : hom.ker = R := by
    rw [CFSG.PreuniquenessRankFour.Helpers.multiplicative_action_zmod_linear_aut_kernel]
    exact CFSG.PreuniquenessRankFour.Helpers.selfcentralizing_pCore_frattini_conjugation_kernel_eq
      3 hcentralizer
  obtain ⟨embedding, hinjective, _⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.quotient_hom_injective_of_kernel_eq R hom hkernel
  have hcard : Nat.card (Q ⧸ R) = Nat.card embedding.range :=
    Nat.card_congr (MonoidHom.ofInjective hinjective).toEquiv
  have hdivides := embedding.range.card_subgroup_dvd_card
  rw [← hcard] at hdivides
  let space := Additive (R ⧸ frattini R)
  let basis := Module.finBasis (ZMod 3) space
  let equivalence := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) space).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv basis).toMulEquiv)
  rw [Nat.card_congr equivalence.toEquiv, Matrix.card_GL_field, ZMod.card] at hdivides
  refine ⟨Module.finrank (ZMod 3) space, ?_, hdivides⟩
  have hspace := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := space)
  rw [Nat.card_zmod] at hspace
  exact hspace

private theorem gl83Solv_isSolvable_of_selfCentralizing {Q : Type*} [Group Q] [Finite Q]
    (hcentralizer : Subgroup.centralizer (CFSG.Open.pCore 3 Q : Set Q) ≤ CFSG.Open.pCore 3 Q)
    (P : Sylow 3 Q) (hP : Nat.card P = 81)
    (hPnc : ∃ a ∈ (P : Subgroup Q), ∃ b ∈ (P : Subgroup Q), a * b ≠ b * a) :
    Group.IsSolvable Q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (CFSG.Open.pCore 3 Q).Normal := CFSG.PreuniquenessRankFour.Helpers.pCore_normal 3
  have hRp : IsPGroup 3 (CFSG.Open.pCore 3 Q) :=
    CFSG.PreuniquenessRankFour.Helpers.pCore_isPGroup 3
  have hRP : CFSG.Open.pCore 3 Q ≤ P := hRp.le_sylow_of_normal P
  obtain ⟨d, hV, hdvd⟩ := gl83Solv_card_quotient_dvd_GL hcentralizer
  set R := CFSG.Open.pCore 3 Q with hR
  have hRcard : Nat.card R ∣ 3 ^ 4 := by
    have := Subgroup.card_dvd_of_le hRP
    rw [hP] at this
    exact this
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hRcard
  have hRV : Nat.card R = Nat.card (R ⧸ frattini R) * Nat.card (frattini R) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hdk : d ≤ k := by
    have h1 : 3 ^ d ∣ 3 ^ k := by
      rw [← hV, ← hk, hRV]
      exact Dvd.intro _ rfl
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have hd3 : d ≤ 3 := by
    by_contra hd
    have hd4 : d = 4 := by omega
    have hk4' : k = 4 := by omega
    have hΦ : Nat.card (frattini R) = 1 := by
      rw [hk, hV, hd4, hk4'] at hRV
      omega
    have hinj : Function.Injective (QuotientGroup.mk' (frattini R)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact Subgroup.card_eq_one.mp hΦ
    have hcomm :=
      CFSG.PreuniquenessRankFour.Helpers.pGroup_frattini_quotient_isMulCommutative 3 hRp
    have hReq : R = P := Subgroup.eq_of_le_of_card_ge hRP (by rw [hP, hk, hk4']; norm_num)
    obtain ⟨a, ha, b, hb, hab⟩ := hPnc
    rw [← hReq] at ha hb
    apply hab
    have hab' := hinj (a₁ := ⟨a, ha⟩ * ⟨b, hb⟩) (a₂ := ⟨b, hb⟩ * ⟨a, ha⟩)
      (by rw [map_mul, map_mul]; exact hcomm.is_comm.comm _ _)
    exact congrArg Subtype.val hab'
  have hQ : Nat.card Q = Nat.card (Q ⧸ R) * Nat.card R :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup R
  have hQP : Nat.card Q = Nat.card P * (P : Subgroup Q).index := (Subgroup.card_mul_index _).symm
  have hm : ¬ 3 ∣ (P : Subgroup Q).index := P.not_dvd_index
  have hsolv : Group.IsSolvable (Q ⧸ R) := by
    interval_cases d
    · exact gl83Solv_isSolvable_of_card_dvd_two_three (a := 0) (b := 0) (by simpa using hdvd)
    · exact gl83Solv_isSolvable_of_card_dvd_two_three (a := 1) (b := 0)
        (by simpa [Fin.prod_univ_succ] using hdvd)
    · exact gl83Solv_isSolvable_of_card_dvd_two_three (a := 4) (b := 1)
        (by simpa [Fin.prod_univ_succ] using hdvd)
    · apply gl83Solv_isSolvable_of_card_dvd
      have h1 : Nat.card (Q ⧸ R) ∣ 2 ^ 5 * 13 * 3 ^ 3 := by
        simpa [Fin.prod_univ_succ] using hdvd
      have h9 : ¬ 9 ∣ Nat.card (Q ⧸ R) := by
        intro h9
        rw [hQ, hP, hk] at hQP
        interval_cases k <;> norm_num at hQP <;> omega
      exact gl83Solv_dvd_of_not_nine_dvd h1 h9
  have : Group.IsSolvable R := by
    have := hRp.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient R

private theorem gl83Solv_wreath_not_comm :
    ∃ a b : Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3), a * b ≠ b * a := by
  refine ⟨⟨fun _ => 1, Multiplicative.ofAdd 1⟩,
    ⟨fun x => if x = 1 then Multiplicative.ofAdd 1 else 1, 1⟩, fun h => ?_⟩
  have := congrArg (fun w : Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) => w.left 1) h
  revert this
  decide

theorem isSolvable_quotient_of_hasPrimeConstraint_wreath {X : Type*} [Group X] [Finite X]
    (hX : HasPrimeConstraint (G := X) 3) (S : Sylow 3 X)
    (e : (S : Subgroup X) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :
    Group.IsSolvable (X ⧸ primeComplementCore (G := X) 3) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := primeComplementCore (G := X) 3 with hO
  obtain ⟨N, hNn, hNp, hNc⟩ := hX
  have hNR : N ≤ CFSG.Open.pCore 3 (X ⧸ O) :=
    le_sSup ⟨hNn, hNp⟩
  have hcentralizer : Subgroup.centralizer (CFSG.Open.pCore 3 (X ⧸ O) : Set (X ⧸ O)) ≤
      CFSG.Open.pCore 3 (X ⧸ O) :=
    (Subgroup.centralizer_le hNR).trans (hNc.trans hNR)
  have hS : Nat.card (S : Subgroup X) = 81 := by
    rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
    simp
  have hdisj : Disjoint (S : Subgroup X) O := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hS, show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.Coprime.pow_left 4 (primeComplementCore_coprime 3)
  let f := (QuotientGroup.mk' O).comp (S : Subgroup X).subtype
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxO : (x : X) ∈ O := (QuotientGroup.eq_one_iff (x : X)).mp hx
    have hx1 : (x : X) = 1 := by
      have := hdisj.le_bot ⟨x.2, hxO⟩
      simpa using this
    exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPrange : (P : Subgroup (X ⧸ O)) = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hP : Nat.card P = 81 := by
    rw [hPrange, ← hS]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  obtain ⟨a, b, hab⟩ := gl83Solv_wreath_not_comm
  refine gl83Solv_isSolvable_of_selfCentralizing hcentralizer P hP
    ⟨f (e.symm a), ?_, f (e.symm b), ?_, fun h => hab ?_⟩
  · rw [hPrange]
    exact ⟨_, rfl⟩
  · rw [hPrange]
    exact ⟨_, rfl⟩
  · have h2 : e.symm a * e.symm b = e.symm b * e.symm a := hinj (by simpa only [map_mul] using h)
    rw [← map_mul, ← map_mul] at h2
    exact e.symm.injective h2

end CFSG.LocalAnalysis.RankThreeTheoremC
