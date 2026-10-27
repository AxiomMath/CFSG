module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.AutThreeGroupSmall
import CFSG.LocalAnalysis.AGLEmbedding.SUThreeTwoQData
import CFSG.GroupTheory.AutomorphismRestrictionKernel
import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitLines
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniAutomorphismKernel
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem card_GL_fin_le_two_at_two (d : ℕ) (hd : d ≤ 2) :
    Nat.card (GL (Fin d) (ZMod 2)) = 1 ∨ Nat.card (GL (Fin d) (ZMod 2)) = 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  interval_cases d
  · left
    rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
    simp
  · left
    rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
    simp [Fin.prod_univ_one]
  · right
    rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
    norm_num [Fin.prod_univ_two]

private theorem prime_dvd_card_GL_fin_le_two_at_two {r d : ℕ} (hr : r.Prime) (hd : d ≤ 2)
    (hdvd : r ∣ Nat.card (GL (Fin d) (ZMod 2))) : r = 2 ∨ r = 3 := by
  rcases card_GL_fin_le_two_at_two d hd with h | h
  · rw [h] at hdvd
    exact absurd (Nat.dvd_one.mp hdvd) hr.ne_one
  · have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h, h6] at hdvd
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)

theorem prime_dvd_card_mulAut_of_isPGroup_two {W : Type*} [Group W] [Finite W]
    (hW : IsPGroup 2 W) (hsmall : Nat.card (W ⧸ frattini W) ≤ 4) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card (MulAut W)) : r = 2 ∨ r = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcomm, hpow, -, hdata⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hW
  obtain ⟨d, hcard, -⟩ := hdata
  have hdle : d ≤ 2 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [hcard, h4] at hsmall
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hsmall
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => hcomm.is_comm.comm a b) hpow hcard
  let φ : MulAut W →* MulAut (W ⧸ frattini W) :=
    CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction (frattini W)
  have hker : IsPGroup 2 φ.ker :=
    CFSG.RankThreeEvenClassification.Helpers.frattini_automorphism_kernel_isPGroup
      2 Nat.prime_two hW
  have hkerCard : Nat.card φ.ker * Nat.card φ.range = Nat.card (MulAut W) :=
    Subgroup.card_ker_mul_card_range φ
  have hrangeDvd : Nat.card φ.range ∣ Nat.card (MulAut (W ⧸ frattini W)) :=
    Subgroup.card_subgroup_dvd_card φ.range
  have hGLcard : Nat.card (MulAut (W ⧸ frattini W)) =
      Nat.card (GL (Fin d) (ZMod 2)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e
  rw [← hkerCard] at hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with hkerDvd | hrangeDvd'
  · left
    obtain ⟨m, hm⟩ := hker.exists_card_eq
    rw [hm] at hkerDvd
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hkerDvd)
  · exact prime_dvd_card_GL_fin_le_two_at_two hr hdle (by
      rw [← hGLcard]
      exact hrangeDvd'.trans hrangeDvd)

private theorem card_frattiniQuotient_le_four {W : Type*} [Group W] [Finite W]
    (hW : IsPGroup 2 W) (hcard : Nat.card W = 8) {x : W} (hx : orderOf x = 4) :
    Nat.card (W ⧸ frattini W) ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hpow, -, ⟨d, hquot, -⟩⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hW
  have hdle : d ≤ 3 := by
    have hdvd : 2 ^ d ∣ 2 ^ 3 := by
      have h := hquot ▸ Subgroup.card_quotient_dvd_card (frattini W)
      rwa [hcard, show (8 : ℕ) = 2 ^ 3 by norm_num] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      (Nat.le_of_dvd (by norm_num) hdvd)
  have hdne : d ≠ 3 := by
    intro hd3
    have h8 : Nat.card (W ⧸ frattini W) = Nat.card W := by
      rw [hquot, hd3, hcard]
      norm_num
    have hphi : Nat.card (frattini W) = 1 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini W)
      rw [h8, hcard] at h
      omega
    have hbot : frattini W = ⊥ := Subgroup.card_eq_one.mp hphi
    have hx2 : x ^ 2 = 1 := by
      have hq : (QuotientGroup.mk' (frattini W)) (x ^ 2) = 1 := by
        rw [map_pow]
        simpa using hpow (QuotientGroup.mk' (frattini W) x)
      have hmem : x ^ 2 ∈ frattini W := by
        rw [← QuotientGroup.eq_one_iff]
        simpa [QuotientGroup.mk'_apply] using hq
      rw [hbot] at hmem
      simpa using hmem
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at hdvd2
    exact absurd hdvd2 (by norm_num)
  rw [hquot]
  calc 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 := by norm_num

private theorem card_frattiniQuotient_le_nine_of_three_group {R : Type*} [Group R] [Finite R]
    (hR3 : IsPGroup 3 R) (hRcard : Nat.card R = 27)
    (hnonab : ∃ a b : R, a * b ≠ b * a) : Nat.card (R ⧸ frattini R) ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, d, hquot, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hR3
  have hdle : d ≤ 3 := by
    have hdvd : 3 ^ d ∣ 3 ^ 3 := by
      have h := hquot ▸ Subgroup.card_quotient_dvd_card (frattini R)
      rwa [hRcard, show (27 : ℕ) = 3 ^ 3 by norm_num] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
      (Nat.le_of_dvd (by norm_num) hdvd)
  have hdne : d ≠ 3 := by
    intro hd3
    have h27 : Nat.card (R ⧸ frattini R) = Nat.card R := by
      rw [hquot, hd3, hRcard]
      norm_num
    have hphi : Nat.card (frattini R) = 1 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini R)
      rw [h27, hRcard] at h
      omega
    have hbot : frattini R = ⊥ := Subgroup.card_eq_one.mp hphi
    obtain ⟨a, b, hab⟩ := hnonab
    have hcomm : a * b = b * a := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← Subgroup.mem_bot, ← hbot]
      exact CFSG.SectionRank.Ccomm.commutator_mem_frattini hR3 a b
    exact hab hcomm
  rw [hquot]
  calc 3 ^ d ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 9 := by norm_num

private theorem prime_dvd_card_mulAut_of_characteristic_three_of_quotient {Q : Type*} [Group Q]
    [Finite Q] (R : Subgroup Q) [R.Characteristic] (hR3 : IsPGroup 3 R)
    (hRsmall : Nat.card (R ⧸ frattini R) ≤ 9) (hW2 : IsPGroup 2 (Q ⧸ R))
    (hWsmall : Nat.card ((Q ⧸ R) ⧸ frattini (Q ⧸ R)) ≤ 4)
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card (MulAut Q)) : r = 2 ∨ r = 3 := by
  let φ : MulAut Q →* MulAut ↥R × MulAut (Q ⧸ R) :=
    CFSG.characteristicRestrictionQuotient R
  have hker : IsPGroup 3 φ.ker := by
    rw [CFSG.characteristicRestrictionQuotient_ker]
    exact CFSG.characteristic_joint_kernel_isPGroup 3 Nat.prime_three R hR3
  have hcard : Nat.card φ.ker * Nat.card φ.range = Nat.card (MulAut Q) :=
    Subgroup.card_ker_mul_card_range φ
  have hrangeDvd : Nat.card φ.range ∣ Nat.card (MulAut ↥R × MulAut (Q ⧸ R)) :=
    Subgroup.card_subgroup_dvd_card φ.range
  rw [← hcard] at hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with hkerDvd | hrangeDvd'
  · right
    obtain ⟨m, hm⟩ := hker.exists_card_eq
    rw [hm] at hkerDvd
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow hkerDvd)
  · have hdvd' : r ∣ Nat.card (MulAut ↥R) * Nat.card (MulAut (Q ⧸ R)) := by
      have h := hrangeDvd'.trans hrangeDvd
      rwa [Nat.card_prod] at h
    rcases (Nat.Prime.dvd_mul hr).mp hdvd' with hR | hW
    · exact prime_dvd_card_mulAut_eq_two_or_three hR3 hRsmall hr hR
    · exact prime_dvd_card_mulAut_of_isPGroup_two hW2 hWsmall hr hW

private theorem card_alternatingGroup_fin_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

private theorem characteristic_alternatingGroup_fin_three :
    (alternatingGroup (Fin 3)).Characteristic := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR3 : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by simpa using card_alternatingGroup_fin_three)
  have hidx : ¬ 3 ∣ (alternatingGroup (Fin 3)).index := by
    rw [alternatingGroup.index_eq_two]
    norm_num
  let S : Sylow 3 (Equiv.Perm (Fin 3)) := hR3.toSylow hidx
  have hS : (S : Subgroup (Equiv.Perm (Fin 3))) = alternatingGroup (Fin 3) := by
    ext x
    show x ∈ hR3.toSylow hidx ↔ x ∈ alternatingGroup (Fin 3)
    rw [IsPGroup.mem_toSylow]
  have hN : (S : Subgroup (Equiv.Perm (Fin 3))).Normal := by
    rw [hS]
    infer_instance
  have hchar := Sylow.characteristic_of_normal S hN
  rwa [hS] at hchar

private theorem prime_dvd_card_mulAut_perm_three {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card (MulAut (Equiv.Perm (Fin 3)))) : r = 2 ∨ r = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hRcard := card_alternatingGroup_fin_three
  have hR3 : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by simpa using hRcard)
  letI : (alternatingGroup (Fin 3)).Characteristic :=
    characteristic_alternatingGroup_fin_three
  have hRsmall : Nat.card (alternatingGroup (Fin 3) ⧸
      frattini (alternatingGroup (Fin 3))) ≤ 9 := by
    have hdvd := Subgroup.card_quotient_dvd_card (frattini (alternatingGroup (Fin 3)))
    rw [hRcard] at hdvd
    have hle : Nat.card (alternatingGroup (Fin 3) ⧸
        frattini (alternatingGroup (Fin 3))) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hWcard : Nat.card (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (alternatingGroup (Fin 3))
    rw [hQcard, hRcard] at h
    omega
  have hW2 : IsPGroup 2 (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) := by
    refine IsPGroup.of_card (n := 1) ?_
    simpa using hWcard
  have hWsmall : Nat.card ((Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) ⧸
      frattini (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3))) ≤ 4 := by
    have hdvd := Subgroup.card_quotient_dvd_card
      (frattini (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)))
    have hle : Nat.card ((Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) ⧸
        frattini (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3))) ≤
        Nat.card (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :=
      Nat.le_of_dvd Nat.card_pos hdvd
    omega
  exact prime_dvd_card_mulAut_of_characteristic_three_of_quotient
    (alternatingGroup (Fin 3)) hR3 hRsmall hW2 hWsmall hr hdvd

private theorem sq_not_mem_of_isPGroup_three {Q : Type*} [Group Q] {R : Subgroup Q}
    (hR3 : IsPGroup 3 R) {f : Q} (hf2 : f ^ 2 ≠ 1) (hf4 : f ^ 4 = 1) : f ^ 2 ∉ R := by
  intro hmem
  obtain ⟨m, hm⟩ := hR3 ⟨f ^ 2, hmem⟩
  have h1 : (f ^ 2) ^ (3 ^ m) = 1 := congrArg Subtype.val hm
  have h2 : orderOf (f ^ 2) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (f ^ 2) = 2 := by
    refine orderOf_eq_prime ?_ hf2
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, hf4]
  rw [h3] at h2
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)

private theorem exists_three_core_statedSU {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    ∃ R : Subgroup ↥(CFSG.Open.StatedSU 3 2 K),
      R.Characteristic ∧ IsPGroup 3 R ∧ Nat.card (R ⧸ frattini R) ≤ 9 ∧
        Nat.card ↥(CFSG.Open.StatedSU 3 2 K) = 216 ∧ Nat.card R = 27 ∧
          ∃ f : ↥(CFSG.Open.StatedSU 3 2 K), f ^ 4 = 1 ∧ f ^ 2 ∉ R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q := ↥(CFSG.Open.StatedSU 3 2 K)
  let R : Subgroup Q := CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup Q)
  obtain ⟨s, d, z, f, g, -, -, -, hf4, -, -, -, hHeis, -, -, -, -, hf2, -, -, hTcard⟩ :=
    CFSG.AGLEmbedding.SUQ.exists_qdata_of_su (Y := Q) (T := ⊤)
      ⟨K, inferInstance, inferInstance, hK, ⟨Subgroup.topEquiv⟩⟩
  have hQcard : Nat.card Q = 216 := by
    rw [Subgroup.card_top] at hTcard
    exact hTcard
  have hRcard : Nat.card R = 27 := hHeis.card
  have hR3 : IsPGroup 3 R := fun ⟨a, ha⟩ =>
    ⟨1, Subtype.ext (by simpa using hHeis.cube a ha)⟩
  have hnonabR : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hHeis.nonabelian
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hRsmall := card_frattiniQuotient_le_nine_of_three_group hR3 hRcard hnonabR
  have hRchar : R.Characteristic := by
    refine Subgroup.characteristic_iff_map_eq.mpr fun α => ?_
    have h := CFSG.AGLEmbedding.SUPair.map_oUpperTwo (α : Q →* Q) (⊤ : Subgroup Q)
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr α.surjective] at h
    exact h
  exact ⟨R, hRchar, hR3, hRsmall, hQcard, hRcard, f, hf4,
    sq_not_mem_of_isPGroup_three hR3 hf2 hf4⟩

private theorem prime_dvd_card_mulAut_statedSU {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card (MulAut ↥(CFSG.Open.StatedSU 3 2 K))) : r = 2 ∨ r = 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := ↥(CFSG.Open.StatedSU 3 2 K)
  obtain ⟨R, hRchar, hR3, hRsmall, hQcard, hRcard, f, hf4, hf2R⟩ :=
    exists_three_core_statedSU hK
  letI : R.Characteristic := hRchar
  have hWcard : Nat.card (Q ⧸ R) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [hQcard, hRcard] at h
    change Nat.card (↥(CFSG.Open.StatedSU 3 2 K) ⧸ R) = 8
    omega
  have hW2 : IsPGroup 2 (Q ⧸ R) :=
    IsPGroup.of_card (n := 3) (by rw [hWcard]; norm_num)
  let x : Q ⧸ R := QuotientGroup.mk' R f
  have hx4 : x ^ 4 = 1 := by
    rw [show x = QuotientGroup.mk' R f from rfl, ← map_pow, hf4, map_one]
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    apply hf2R
    have h' : (QuotientGroup.mk' R (f ^ 2) : Q ⧸ R) = 1 := by
      rw [map_pow]
      exact h
    rw [← QuotientGroup.eq_one_iff]
    simpa [QuotientGroup.mk'_apply] using h'
  have hxord : orderOf x = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using hx2)
      (by simpa using hx4)
    simpa using h
  have hWsmall : Nat.card ((Q ⧸ R) ⧸ frattini (Q ⧸ R)) ≤ 4 :=
    card_frattiniQuotient_le_four hW2 hWcard hxord
  exact prime_dvd_card_mulAut_of_characteristic_three_of_quotient R hR3 hRsmall hW2 hWsmall
    hr hdvd

theorem prime_dvd_card_mulAut_of_isSymThreeOrSUThreeTwo {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.AGLEmbedding.IsSymThreeOrSUThreeTwo Q) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card (MulAut Q)) : r = 2 ∨ r = 3 := by
  rcases hQ with ⟨⟨e⟩⟩ | ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩
  · rw [Nat.card_congr (MulAut.congr e).toEquiv] at hdvd
    exact prime_dvd_card_mulAut_perm_three hr hdvd
  · have hdvd' : r ∣ Nat.card (MulAut ↥(CFSG.Open.StatedSU 3 2 K)) := by
      rwa [Nat.card_congr (MulAut.congr e).toEquiv] at hdvd
    exact @prime_dvd_card_mulAut_statedSU K hKfield hKfinite hKcard r hr hdvd'

private theorem characteristicQuotientAction_eq_one_of_isSymThreeOrSUThreeTwo {I : Subgroup G}
    (hI : CFSG.AGLEmbedding.IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) {d k : ℕ}
    (hd : d.Prime) (h5 : 5 ≤ d) (σ : MulAut ↥I) (hσ : σ ^ d ^ k = 1) :
    CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction
      (CFSG.pCore 2 ↥I) σ = 1 := by
  classical
  let ψ : MulAut (↥I ⧸ CFSG.pCore 2 ↥I) :=
    CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction
      (CFSG.pCore 2 ↥I) σ
  change ψ = 1
  by_contra hne
  have hψ : ψ ^ d ^ k = 1 := by
    rw [show ψ = CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction
      (CFSG.pCore 2 ↥I) σ from rfl, ← map_pow, hσ, map_one]
  have hord : orderOf ψ ∣ d ^ k := orderOf_dvd_of_pow_eq_one hψ
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hd).mp hord
  have hj : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hjeq
    exact hne (orderOf_eq_one_iff.mp hjeq)
  have hdvdord : d ∣ orderOf ψ := hjeq ▸ dvd_pow_self d hj
  have hdvdAut : d ∣ Nat.card (MulAut (↥I ⧸ CFSG.pCore 2 ↥I)) :=
    hdvdord.trans (orderOf_dvd_natCard ψ)
  rcases prime_dvd_card_mulAut_of_isSymThreeOrSUThreeTwo hI hd hdvdAut with h | h <;> omega

theorem commutator_mem_pCoreOf_of_isSymThreeOrSUThreeTwo {I : Subgroup G}
    (hI : CFSG.AGLEmbedding.IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) {d : ℕ}
    (hd : d.Prime) (h5 : 5 ≤ d) {b : G} (hb : b ∈ Subgroup.normalizer (I : Set G)) {k : ℕ}
    (hbk : b ^ d ^ k = 1) : ∀ x ∈ I, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 I := by
  classical
  let N : Subgroup ↥I := CFSG.pCore 2 ↥I
  let σ : MulAut ↥I := CFSG.AGLEmbedding.CZeroOrbit.conjRestrict I ⟨b, hb⟩
  have hb' : (⟨b, hb⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ d ^ k = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hbk, Subgroup.coe_one]
  have hσ : σ ^ d ^ k = 1 := by
    rw [show σ = CFSG.AGLEmbedding.CZeroOrbit.conjRestrict I ⟨b, hb⟩ from rfl, ← map_pow,
      hb', map_one]
  have hψ1 : CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction N σ = 1 :=
    characteristicQuotientAction_eq_one_of_isSymThreeOrSUThreeTwo hI hd h5 σ hσ
  intro x hx
  have hbx : b * x * b⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp hb x).mp hx
  have hconj : CFSG.AGLEmbedding.CZeroOrbit.conjRestrict I ⟨b, hb⟩ ⟨x, hx⟩ =
      ⟨b * x * b⁻¹, hbx⟩ := by
    apply Subtype.ext
    rw [CFSG.AGLEmbedding.CZeroOrbit.conjRestrict_apply]
  have hq : QuotientGroup.mk' N (⟨b * x * b⁻¹, hbx⟩ : ↥I) =
      QuotientGroup.mk' N ⟨x, hx⟩ := by
    have h := congrArg (fun f : MulAut (↥I ⧸ N) =>
      f (QuotientGroup.mk' N ⟨x, hx⟩)) hψ1
    simp only [N, MulAut.one_apply,
      CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction_apply] at h
    rwa [hconj] at h
  have hmem : (⟨b * x * b⁻¹, hbx⟩ : ↥I) / ⟨x, hx⟩ ∈ N := by
    have hq' : (QuotientGroup.mk (⟨b * x * b⁻¹, hbx⟩ : ↥I) : ↥I ⧸ N) =
        QuotientGroup.mk ⟨x, hx⟩ := by
      simpa [QuotientGroup.mk'_apply] using hq
    exact (QuotientGroup.eq_iff_div_mem (N := N)).mp hq'
  exact Subgroup.mem_map.mpr ⟨(⟨b * x * b⁻¹, hbx⟩ : ↥I) / ⟨x, hx⟩, hmem, by
    simp [Subgroup.coe_div, div_eq_mul_inv]⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
