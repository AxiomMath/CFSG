module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabLin
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.Quasithin.SteinbergBKCentralCoreRootKillsKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab

section Block

variable {K : Type} [Field K]

theorem eq_one_of_mem_center_of_pow_two_pow [CharP K 2] {m k : ℕ} {t : GL (Fin m) K}
    (ht : t ∈ Subgroup.center (GL (Fin m) K)) (hk : t ^ 2 ^ k = 1) : t = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp ht
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

theorem pCore_two_specialLinearGroup_eq_bot_of_charTwo [Finite K] [CharP K 2] (m : ℕ) :
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

theorem eq_bot_of_isPGroup_of_normalized_range_toGL [Finite K] [CharP K 2] {m : ℕ}
    {T : Subgroup (GL (Fin m) K)} (hT : IsPGroup 2 T)
    (hSN : ∀ s ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range,
      ∀ t ∈ T, s * t * s⁻¹ ∈ T) : T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : SpecialLinearGroup (Fin m) K →* GL (Fin m) K := SpecialLinearGroup.toGL
  have hnorm : (T.comap ρ).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have := hSN (ρ g) ⟨g, rfl⟩ (ρ x) hx
    simpa [Subgroup.mem_comap] using this
  have hle : T.comap ρ ≤ CFSG.pCore 2 (SpecialLinearGroup (Fin m) K) :=
    le_sSup ⟨hnorm, hT.comap_of_injective ρ SpecialLinearGroup.toGL_injective⟩
  rw [pCore_two_specialLinearGroup_eq_bot_of_charTwo] at hle
  rw [eq_bot_iff]
  intro t ht
  have hcomm : ∀ s ∈ ρ.range, t * s = s * t := by
    rintro _ ⟨g, rfl⟩
    have h1 : ρ g * t * (ρ g)⁻¹ ∈ T := hSN _ ⟨g, rfl⟩ t ht
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

end Block

theorem le_ker_linBlockHom_of_normal_isPGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {I : Set ℕ} (R : Subgroup ↥(flagStabilizer n K I)) [R.Normal] (hR : IsPGroup 2 R)
    (a : Fin n) : R ≤ (linBlockHom K n I a).ker := by
  have hT : R.map (linBlockHom K n I a) = ⊥ := by
    refine eq_bot_of_isPGroup_of_normalized_range_toGL (hR.map _) ?_
    rintro s hs _ ⟨r, hr, rfl⟩
    have hmem : (Pi.mulSingle a s : ∀ b, GL (Fin (linBlockLen n I b)) K) ∈
        (linLeviHom K n I).range := by
      refine pi_le_range_linLeviHom ((Subgroup.mem_pi _).mpr fun b _ => ?_)
      by_cases hb : b = a
      · subst hb
        simpa using hs
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    obtain ⟨x, hx⟩ := hmem
    have hxa : linBlockHom K n I a x = s := by
      have h := congrFun hx a
      rw [Pi.mulSingle_eq_same] at h
      exact h
    refine ⟨x * r * x⁻¹, Subgroup.Normal.conj_mem inferInstance r hr x, ?_⟩
    rw [map_mul, map_mul, map_inv, hxa]
  intro r hr
  have h : linBlockHom K n I a r ∈ R.map (linBlockHom K n I a) := ⟨r, hr, rfl⟩
  rw [hT] at h
  exact h

theorem le_ker_linLeviHom_of_normal_isPGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {I : Set ℕ} (R : Subgroup ↥(LinearFlag.flagStabilizer n K I)) [R.Normal]
    (hR : IsPGroup 2 R) : R ≤ (CFSG.AGLEmbedding.LeviBlock.linLeviHom K n I).ker := by
  intro r hr
  rw [MonoidHom.mem_ker]
  funext a
  exact le_ker_linBlockHom_of_normal_isPGroup R hR a hr

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
