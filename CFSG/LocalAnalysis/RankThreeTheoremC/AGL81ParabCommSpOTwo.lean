module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.Quasithin.SteinbergBKCentralCoreRootKillsKernel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp

open Matrix CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab
  (normal_eq_top_or_le_center not_isSolvable_of_isQuasisimple)

section GeneralLinear

variable {K : Type} [Field K]

theorem conj_mem_range_toGL {m : ℕ} (x : GL (Fin m) K) {s : GL (Fin m) K}
    (hs : s ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) :
    x * s * x⁻¹ ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range := by
  rw [SpecialLinearGroup.range_toGL_eq_ker_det] at hs ⊢
  exact (MonoidHom.normal_ker _).conj_mem s hs x

theorem mem_center_of_commute_with_range_toGL {m : ℕ} {x : GL (Fin m) K}
    (hx : ∀ s ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range,
      x * s = s * x) : x ∈ Subgroup.center (GL (Fin m) K) := by
  refine Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    (Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_)
  have h := congrArg (fun y : GL (Fin m) K => (y : Matrix (Fin m) (Fin m) K))
    (hx (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection t.hij t.c)) ⟨_, rfl⟩)
  rw [Units.val_mul, Units.val_mul] at h
  exact h.symm

theorem eq_one_of_mem_center_of_pow_two_pow [CharP K 2] {m k : ℕ} {t : GL (Fin m) K}
    (ht : t ∈ Subgroup.center (GL (Fin m) K)) (hk : t ^ 2 ^ k = 1) : t = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp ht
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Units.ext (Matrix.ext fun i => i.elim0)
  · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have h1 : Matrix.scalar (Fin m) (c ^ 2 ^ k) = Matrix.scalar (Fin m) (1 : K) := by
      rw [map_pow, hc, ← Units.val_pow_eq_pow_val, hk, Units.val_one, map_one]
    have h2 : c ^ 2 ^ k = 1 := Matrix.scalar_inj.mp h1
    have h3 : (c - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h2, one_pow, sub_self]
    have h4 : c = 1 :=
      sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h3)
    exact Units.ext (by rw [← hc, h4, map_one, Units.val_one])

theorem pCore_specialLinear_eq_bot [Finite K] [CharP K 2] (m : ℕ) :
    CFSG.pCore 2 (SpecialLinearGroup (Fin m) K) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge m 2 with hm | hm
  · haveI := subsingleton_specialLinear_of_lt_two (K := K) hm
    exact Subsingleton.elim _ _
  rcases hm.eq_or_lt with rfl | hm3
  · classical
    haveI := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact CFSG.Quasithin.SteinbergBK.pCore_two_specialLinearGroup_eq_bot n.pos
      (by rw [Nat.card_eq_fintype_card]; exact hn)
  · have hSL : CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin m) K) := by
      classical
      exact ⟨(CFSG.LinearGroups.special_linear_isPerfect hm (Or.inl hm3)).commutator_eq_top,
        (CFSG.LinearGroups.linear_projective_simple hm (Or.inl hm3)).2.1⟩
    rcases normal_eq_top_or_le_center hSL CFSG.pCore_normal with htop | hc
    · exfalso
      have hP : IsPGroup 2 (SpecialLinearGroup (Fin m) K) := by
        have h := CFSG.pCore_isPGroup (p := 2) (G := SpecialLinearGroup (Fin m) K)
        rw [htop] at h
        exact h.of_equiv Subgroup.topEquiv
      haveI := hP.isNilpotent
      exact not_isSolvable_of_isQuasisimple hSL inferInstance
    · rw [eq_bot_iff]
      intro s hs
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := SpecialLinearGroup (Fin m) K) ⟨s, hs⟩
      have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hcomm : ∀ x ∈ (SpecialLinearGroup.toGL :
          SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range,
          SpecialLinearGroup.toGL s * x = x * SpecialLinearGroup.toGL s := by
        rintro _ ⟨g, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg _ (Subgroup.mem_center_iff.mp (hc hs) g).symm
      have h1 : SpecialLinearGroup.toGL s = 1 :=
        eq_one_of_mem_center_of_pow_two_pow (mem_center_of_commute_with_range_toGL hcomm)
          (by rw [← map_pow, hsk, map_one])
      exact SpecialLinearGroup.toGL_injective (by rw [h1, map_one])

theorem eq_bot_of_isPGroup_normal_gl [Finite K] [CharP K 2] {m : ℕ}
    {T : Subgroup (GL (Fin m) K)} [hTn : T.Normal] (hT : IsPGroup 2 T) : T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : SpecialLinearGroup (Fin m) K →* GL (Fin m) K := SpecialLinearGroup.toGL
  have hnorm : (T.comap ρ).Normal := hTn.comap ρ
  have hle : T.comap ρ ≤ CFSG.pCore 2 (SpecialLinearGroup (Fin m) K) :=
    le_sSup ⟨hnorm, hT.comap_of_injective ρ SpecialLinearGroup.toGL_injective⟩
  rw [pCore_specialLinear_eq_bot] at hle
  rw [eq_bot_iff]
  intro t ht
  have hcomm : ∀ s ∈ ρ.range, t * s = s * t := by
    rintro _ ⟨g, rfl⟩
    have h1 : ρ g * t * (ρ g)⁻¹ ∈ T := hTn.conj_mem t ht _
    have h2 : ρ g * t * (ρ g)⁻¹ * t⁻¹ ∈ T := T.mul_mem h1 (T.inv_mem ht)
    obtain ⟨g', hg'⟩ : ρ g * t * (ρ g)⁻¹ * t⁻¹ ∈ ρ.range := by
      have h3 : t * (ρ g)⁻¹ * t⁻¹ ∈ ρ.range :=
        conj_mem_range_toGL t (ρ.range.inv_mem ⟨g, rfl⟩)
      simpa only [mul_assoc] using ρ.range.mul_mem (⟨g, rfl⟩ : ρ g ∈ ρ.range) h3
    have hg'1 : g' = 1 := Subgroup.mem_bot.mp (hle (by rw [Subgroup.mem_comap, hg']; exact h2))
    rw [hg'1, map_one] at hg'
    exact ((mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hg'.symm))).symm
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  exact eq_one_of_mem_center_of_pow_two_pow (mem_center_of_commute_with_range_toGL hcomm)
    (congrArg Subtype.val hk)

end GeneralLinear

section LeviNormal

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {I : Set ℕ}
  (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I)

theorem spFlagCutHom_surjective {b : ℕ} (hb : b ∈ I) :
    Function.Surjective (spFlagCutHom (K := K) hI (spFlagPrev_mem I b) hb) := fun A =>
  ⟨⟨spFlagCutEmb (spFlagPrev I b) b (hI b hb) A,
    spFlagCutEmb_mem hI _ (fun _ hc => le_spFlagPrev_or_le hc) A⟩, cutHom_cutEmb hI hb A⟩

include htI in
theorem spFlagResHom_surjective (hmax : ∀ c ∈ I, c ≤ t) :
    Function.Surjective (spFlagResHom (K := K) hI htI) := fun c =>
  ⟨⟨spFlagResEmb t c, spFlagResEmb_mem hI hmax c⟩, resHom_resEmb hI htI hmax c⟩

include hI htI in
theorem le_ker_spFlagLeviHom_of_normal_isPGroup (hI1 : ∀ i ∈ I, 1 ≤ i)
    (hmax : ∀ c ∈ I, c ≤ t) (R : Subgroup ↥(flagStabilizer r K I)) [hR : R.Normal]
    (hRp : IsPGroup 2 R) : R ≤ (spFlagLeviHom hI htI).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine leviHom_eq_one_of_blocks hI htI (fun b hb => ?_) ?_
  · have hβ := spFlagCutHom_surjective (K := K) hI hb
    haveI : (R.map (spFlagCutHom (K := K) hI (spFlagPrev_mem I b) hb)).Normal := hR.map _ hβ
    have hbot := eq_bot_of_isPGroup_normal_gl (hRp.map (spFlagCutHom (K := K) hI
      (spFlagPrev_mem I b) hb))
    have hmem : spFlagCutHom (K := K) hI (spFlagPrev_mem I b) hb x ∈
        R.map (spFlagCutHom (K := K) hI (spFlagPrev_mem I b) hb) := ⟨x, hx, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · have hβ := spFlagResHom_surjective (K := K) hI htI hmax
    haveI : (R.map (spFlagResHom (K := K) hI htI)).Normal := hR.map _ hβ
    have hbot := eq_bot_of_isPGroup_normal_statedSp (r - t)
      (hRp.map (spFlagResHom (K := K) hI htI))
    have hmem : spFlagResHom (K := K) hI htI x ∈ R.map (spFlagResHom (K := K) hI htI) :=
      ⟨x, hx, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem

end LeviNormal

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
