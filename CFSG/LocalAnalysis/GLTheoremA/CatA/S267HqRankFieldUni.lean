module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankCrit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankLift
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.ClassicalInvolution.Asc77.AscSCH19
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

private theorem exists_not_comm_of_commutator_eq_top {G : Type} [Group G] [Nontrivial G]
    (h : commutator G = ⊤) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hbot : commutator G = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top, eq_top_iff]
    intro x _
    rw [mem_center_iff]
    intro y
    exact hcon y x
  rw [hbot] at h
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hxb : x ∈ (⊥ : Subgroup G) := h.symm ▸ mem_top x
  exact hx (mem_bot.1 hxb)

private theorem lt_of_primitive {p ℓ m : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hprim : ∀ k : ℕ, 0 < k → k < m → ¬ ℓ ∣ p ^ k - 1) : m < ℓ := by
  by_contra hle
  push Not at hle
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have ha : (p : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h)
  apply hprim (ℓ - 1) (by have := hℓ.two_le; omega) (by have := hℓ.two_le; omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow,
    ZMod.pow_card_sub_one_eq_one ha, Nat.cast_one, sub_self]

private theorem ne_of_primitive {p ℓ m : ℕ} (hℓ : ℓ.Prime) (hm : 0 < m) (hd : ℓ ∣ p ^ m - 1) :
    ℓ ≠ p := by
  rintro rfl
  have h1 : ℓ ∣ ℓ ^ m := dvd_pow_self ℓ (by omega)
  have h2 := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)

section Field

variable {K : Type} [Field K] [Finite K]

theorem two_mul_le_pRank_PSU4 {p f : ℕ} (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    2 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := CFSG.RankThree.PartTwo.Census.two_ne_zero_of_unitaryFieldData h hp2
  obtain ⟨P, hP⟩ := CFSG.RankThree.Classical.exists_fourFrame h h2
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hη0 : c - h.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hη : h.bar (c - h.bar c) = -(c - h.bar c) := by rw [map_sub, h.bar_bar, neg_sub]
  obtain ⟨hU, hUcard⟩ := CFSG.RankThree.Classical.unitary_four_paired_root h P hP hη0 hη
  set e := CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (n := 4) (by norm_num)
  refine CFSG.SectionRank.le_pRank h.prime.one_lt le_top
    (CFSG.SectionRank.isElemAbelian_map hU e.toMonoidHom) ?_
  rw [Subgroup.card_map_of_injective e.injective, hUcard]

private theorem exists_zsigmondy_PSU_four {p f : ℕ} (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ ℓ ∣ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) ∧
      ∀ i : ℕ, 0 < i → i < 4 * f → ¬ ℓ ∣ p ^ i - 1 := by
  have hp := h.prime
  have hf := h.one_le
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨ℓ, hℓ, hℓd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 (show 3 ≤ 4 * f by omega)
  have hℓp := ne_of_primitive hℓ (by omega) hℓd
  have hlt := lt_of_primitive hp hℓ hℓp hprim
  refine ⟨ℓ, hℓ, hℓp, ?_, hprim⟩
  have h4 : (p ^ f) ^ 4 - 1 = p ^ (4 * f) - 1 := by rw [← pow_mul, mul_comm]
  have hSU : ℓ ∣ Nat.card (StatedSU 4 (p ^ f) K) := by
    rw [CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four h, h4]
    exact Dvd.dvd.mul_left hℓd _
  have hsplit := card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K))
  have hZ : Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K)) ≤ 4 := by
    rw [← CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h (by norm_num),
      CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars h (by norm_num)]
    exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  rw [hsplit] at hSU
  rcases (Nat.Prime.dvd_mul hℓ).1 hSU with h' | h'
  · exact h'
  · have := Nat.le_of_dvd Nat.card_pos h'
    omega

theorem six_le_pRank_of_surj_PSU4
    {p f : ℕ} (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hf : 3 ≤ f) {X : Type} [Group X] [Finite X] (φ : X →* StatedProj (StatedSU 4 (p ^ f) K))
    (hφ : Function.Surjective φ) : 6 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hp := h.prime
  have hK : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
  haveI : IsSimpleGroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 4 (by norm_num)
      (fun h' => by simp only [Prod.mk.injEq] at h'; omega)
  have hq4 : 4 ≤ p ^ f := by
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 3
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  obtain ⟨hperf, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier hK (by decide : Even 4) le_rfl
      hq4
  have hnc := exists_not_comm_of_commutator_eq_top hperf
  have hM : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedSU 4 (p ^ f) K))) := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro hd
    have h1 : p ∣ p ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ p ^ f := dvd_pow_self p (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h1))
  have hcen := pRank_cover_of_multiplier hnc hp hM
    ((show 6 ≤ 2 * f by omega).trans (two_mul_le_pRank_PSU4 h hp2))
  obtain ⟨ℓ, hℓ, hℓp, hℓF, hprim⟩ := exists_zsigmondy_PSU_four h hp2
  have hinv := not_dvd_card_GL_of_prime (F := StatedProj (StatedSU 4 (p ^ f) K)) (k := 6 ^ 2 / 4)
    hp hℓ hℓp hℓF (fun i hi1 hi2 => hprim i (by omega) (by norm_num at hi2; omega))
  exact le_pRank_of_surj_crit hnc hp hp2 hcen hinv φ hφ

theorem six_le_twoLocalRank_of_PSU_field
    {p f N : ℕ}
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hf : 3 ≤ f) (hN : 5 ≤ N) {X : Type} [Group X]
    [Finite X] (φ : X →* StatedProj (StatedSU N (p ^ f) K)) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank p X := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp := h.prime
  have h2 := CFSG.RankThree.PartTwo.Census.two_ne_zero_of_unitaryFieldData h hp2
  have hne : (-1 : K) ≠ 1 := fun h' => h2 (by linear_combination -h')
  have hk : 0 + 4 ≤ N := by omega
  set ψ := (CFSG.ComponentClassification.Burgoyne.Proj.projH (StatedSU N (p ^ f) K)).comp
    (CFSG.OddStandard.GH71.S55.C5U.blkSU h 0 hk) with hψ
  have hinj : Function.Injective ψ :=
    CFSG.OddStandard.GH71.S55.C5U.proj_blkSU_injective h hk (by omega)
  have hnorm : h.norm ((-1 : Kˣ) : K) = 1 := by
    simp [UnitaryFieldData.norm]
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) ∈ StatedSU 4 (p ^ f) K :=
    CFSG.ClassicalGroups.UnitaryFlag.scalar_mem_unitarySU h (by norm_num) hnorm (by norm_num)
  set m1 : StatedSU 4 (p ^ f) K := ⟨_, hmem⟩ with hm1
  have hcen : Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) ∈ center (GL (Fin 4) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hcomm : ∀ A : StatedSU 4 (p ^ f) K, m1 * A = A * m1 := fun A =>
    Subtype.ext ((mem_center_iff.1 hcen (A : GL (Fin 4) K)).symm)
  have hm1sq : m1 * m1 = 1 := by
    rw [hm1]
    refine Subtype.ext ?_
    change Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) *
      Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) = 1
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  have hm1ne : m1 ≠ 1 := by
    intro h'
    have h'' := congrArg
      (fun A : StatedSU 4 (p ^ f) K => ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h'
    change Matrix.scalar (Fin 4) ((-1 : Kˣ) : K) 0 0 = (1 : Matrix (Fin 4) (Fin 4) K) 0 0 at h''
    rw [Matrix.scalar_apply, diagonal_apply_eq, one_apply_eq, Units.val_neg, Units.val_one] at h''
    exact hne h''
  set z := ψ m1 with hz
  have hz2 : z ^ 2 = 1 := by rw [pow_two, hz, ← map_mul, hm1sq, map_one]
  have hz1 : z ≠ 1 := fun h' => hm1ne (hinj (h'.trans (map_one ψ).symm))
  refine le_twoLocalRank_of_section hp (J := ψ.range) (U₀ := zpowers z) ?_
    (zpowers_ne_bot.2 hz1) ?_ ?_ φ hφ
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one])
  · refine le_trans ?_ (centralizer_le_normalizer _)
    rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    have hc : Commute z (ψ A) := by
      show z * ψ A = ψ A * z
      rw [hz, ← map_mul, ← map_mul, hcomm A]
    exact (hc.zpow_left k).eq
  · intro X' _ _ φ' hφ'
    let e := MonoidHom.ofInjective hinj
    exact six_le_pRank_of_surj_PSU4 h hp2 hf
      ((CFSG.ComponentClassification.Burgoyne.Proj.projH (StatedSU 4 (p ^ f) K)).comp
        (e.symm.toMonoidHom.comp φ'))
      ((QuotientGroup.mk'_surjective _).comp (e.symm.surjective.comp hφ'))

end Field

theorem six_le_twoLocalRank_twistedA_field
    {n : ℕ} (hn : 4 ≤ n)
    (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid) (hq2 : Q.p ≠ 2)
    (hr : 3 ≤ Q.exponent) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie ⟨.twistedA n Q, hv⟩).Group) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank Q.p X := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩ = Q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA n Q
  have hfe : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩ = Q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA n Q
  have hcp : (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩).Prime := by
    rw [hc]
    exact Q.prime_p
  haveI : Fact (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩).Prime := ⟨hcp⟩
  have hf1 : 1 ≤ TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩ := by omega
  have h : UnitaryFieldData (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩)
      (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩)
      (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩)
        (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩)) :=
    ⟨hcp, hf1, GaloisField.card _ _ (by omega)⟩
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj n Q hv
  have := six_le_twoLocalRank_of_PSU_field h (by rw [hc]; exact hq2) (by omega) (by omega)
    (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
  rwa [hc] at this

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
