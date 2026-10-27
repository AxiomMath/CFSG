module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCover
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearFlag
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab

open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial Matrix

section Block

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
  refine GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    (Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_)
  have h := congrArg (fun y : GL (Fin m) K => (y : Matrix (Fin m) (Fin m) K))
    (hx (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection t.hij t.c)) ⟨_, rfl⟩)
  rw [Units.val_mul, Units.val_mul] at h
  exact h.symm

theorem commute_of_solvable_normalized_range_toGL [Finite K] (hK : 4 ≤ Nat.card K) {m : ℕ}
    {N : Subgroup (GL (Fin m) K)} (hN : Group.IsSolvable ↥N)
    (hSN : ∀ s ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range,
      ∀ x ∈ N, s * x * s⁻¹ ∈ N) :
    ∀ x ∈ N, ∀ s ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range, x * s = s * x := by
  intro x hx s hs
  by_cases hm : 2 ≤ m
  · have hSL : CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin m) K) := by
      classical
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
      exact ⟨(CFSG.LinearGroups.special_linear_isPerfect hm (Or.inr ⟨t, ht⟩)).commutator_eq_top,
        (CFSG.LinearGroups.linear_projective_simple hm (Or.inr ⟨t, ht⟩)).2.1⟩
    exact commute_of_solvable_of_isQuasisimple
      (CFSG.Open.IsQuasisimple.of_mulEquiv (LeviBlock.slEquivToGLRange m).symm hSL) hN hSN
      (fun y _ t ht => conj_mem_range_toGL y ht) x hx s hs
  · have := LeviBlock.subsingleton_specialLinear_of_lt_two (K := K) (by omega : m < 2)
    obtain ⟨t, rfl⟩ := hs
    rw [Subsingleton.elim t 1, map_one, mul_one, one_mul]

theorem le_center_of_solvable_normalized_range_toGL [Finite K] (hK : 4 ≤ Nat.card K) {m : ℕ}
    {N : Subgroup (GL (Fin m) K)} (hN : Group.IsSolvable ↥N)
    (hSN : ∀ s ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range,
      ∀ x ∈ N, s * x * s⁻¹ ∈ N) : N ≤ Subgroup.center (GL (Fin m) K) :=
  fun _ hx => mem_center_of_commute_with_range_toGL fun s hs =>
    commute_of_solvable_normalized_range_toGL hK hN hSN _ hx s hs

end Block

theorem solvNormalCentral_range_linLeviHom {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    (n : ℕ) (I : Set ℕ) : SolvNormalCentral ↥(LeviBlock.linLeviHom K n I).range := by
  classical
  intro N hN hNs ν hν
  rw [Subgroup.mem_center_iff]
  intro l
  apply Subtype.ext
  funext a
  let ev : ↥(LeviBlock.linLeviHom K n I).range →* GL (Fin (LeviBlock.linBlockLen n I a)) K :=
    (Pi.evalMonoidHom (fun a => GL (Fin (LeviBlock.linBlockLen n I a)) K) a).comp
      (LeviBlock.linLeviHom K n I).range.subtype
  have hsolv : Group.IsSolvable ↥(N.map ev) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective ev N)
  have hcent : N.map ev ≤ Subgroup.center (GL (Fin (LeviBlock.linBlockLen n I a)) K) := by
    refine le_center_of_solvable_normalized_range_toGL hK hsolv ?_
    rintro s hs _ ⟨ν', hν', rfl⟩
    have hmem : (Pi.mulSingle a s : ∀ b, GL (Fin (LeviBlock.linBlockLen n I b)) K) ∈
        (LeviBlock.linLeviHom K n I).range := by
      refine LeviBlock.pi_le_range_linLeviHom ((Subgroup.mem_pi _).mpr fun b _ => ?_)
      by_cases hb : b = a
      · subst hb
        simpa using hs
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    refine ⟨⟨_, hmem⟩ * ν' * ⟨_, hmem⟩⁻¹, hN.conj_mem ν' hν' _, ?_⟩
    simp [ev]
  exact (Subgroup.mem_center_iff.mp (hcent ⟨ν, hν, rfl⟩) (l.1 a))

theorem solvNormalCentral_parabolic_linear
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {L J : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (h3 : 3 ∣ Nat.card ↥(Subgroup.center ↥L))
    {f : ℕ} (hf : 1 ≤ f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 3 (GaloisField 2 f))
    (hJ : IsParabolicTwo L J) : SolvNormalCentral (↥J ⧸ CFSG.pCore 2 ↥J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : 4 ≤ Nat.card (GaloisField 2 f) := by
    have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    have hdvd := oddCenterLinear_of_griess hGA G L hL hodd 3 (GaloisField 2 f) ⟨e⟩
    rw [← Nat.card_eq_fintype_card, hcard] at hdvd
    have h3' : 3 ∣ 2 ^ f - 1 := (h3.trans hdvd).trans (Nat.gcd_dvd_right _ _)
    rcases Nat.lt_or_ge f 2 with h | h
    · obtain rfl : f = 1 := by omega
      norm_num at h3'
    · rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨ρ, hρs, -, hρ⟩ :=
    kFactCoverLinear_of_griess hGA G L hL hodd 3 (GaloisField 2 f) le_rfl e
  obtain ⟨σ, e', I, hσs, hσ, -, hcomap, -, -⟩ :=
    exists_comap_eq_flagStabilizer hodd (by norm_num) e hρs hρ hJ
  obtain ⟨-, hσk⟩ := ToralCensus.surjective_and_ker_le_of_compat hL.2.2.1 e' σ hσ
  have hQJ : ∀ q : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f),
      q ∈ LinearFlag.flagStabilizer 3 (GaloisField 2 f) I → ((σ q : ↥L) : G) ∈ J := by
    intro q hq
    rw [← hcomap] at hq
    exact hq
  let φ : ↥(LinearFlag.flagStabilizer 3 (GaloisField 2 f) I) →* ↥J :=
    ((L.subtype.comp σ).comp (LinearFlag.flagStabilizer 3 (GaloisField 2 f) I).subtype).codRestrict
      J fun q => hQJ q.1 q.2
  have hφapply : ∀ q, ((φ q : ↥J) : G) = ((σ q.1 : ↥L) : G) := fun q => rfl
  have hφs : Function.Surjective φ := by
    rintro ⟨j, hj⟩
    obtain ⟨g, hg⟩ := hσs ⟨j, hJ.1 hj⟩
    have hgQ : g ∈ LinearFlag.flagStabilizer 3 (GaloisField 2 f) I := by
      rw [← hcomap]
      show ((σ g : ↥L) : G) ∈ J
      rw [hg]
      exact hj
    exact ⟨⟨g, hgQ⟩, Subtype.ext (by rw [hφapply]; exact congrArg Subtype.val hg)⟩
  have hφk : Group.IsSolvable ↥φ.ker := by
    have hcentral : ∀ a : ↥φ.ker, a.1.1 ∈ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f)) := fun a =>
      hσk (MonoidHom.mem_ker.mpr (Subtype.ext (by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
        rwa [hφapply] at h)))
    refine Group.isSolvable_of_comm fun a b => ?_
    exact Subtype.ext (Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral b) a.1.1)))
  have hβs : Function.Surjective (LeviBlock.linLeviHom (GaloisField 2 f) 3 I).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hβk : IsPGroup 2 ↥(LeviBlock.linLeviHom (GaloisField 2 f) 3 I).rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact LeviBlock.isPGroup_ker_linLeviHom (by norm_num)
  exact solvNormalCentral_quotPCore φ hφs hφk _ hβs hβk
    (solvNormalCentral_range_linLeviHom hK 3 I)

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab
