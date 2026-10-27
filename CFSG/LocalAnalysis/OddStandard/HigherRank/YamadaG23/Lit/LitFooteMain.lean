module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YOutside
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionNormalQuaternion
import CFSG.ClassicalInvolution.Asc77.AscIHSL2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

@[expose] def FooteMainL6 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Sylow 2 H),
    (∃ (p f : ℕ) (L : Type) (_ : Group L), p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧
      CFSG.Blueprint.LieModel L .PSL 6 p f ∧ ∃ P : Sylow 2 L, Nonempty (↥S ≃* ↥P)) →
    ∃ z : H, (center ↥(S : Subgroup H)).map (S : Subgroup H).subtype = zpowers z ∧
      CFSG.ClassicalInvolution.NormalQuaternionAt z

theorem orderOf_eq_two_of_center_eq_zpowers {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    {z : H} (hZ : (center ↥(S : Subgroup H)).map (S : Subgroup H).subtype = zpowers z)
    (hQ : CFSG.ClassicalInvolution.NormalQuaternionAt z) : orderOf z = 2 := by
  obtain ⟨K, hKC, -, hzK, Q, r, hr, ⟨eQ⟩⟩ := hQ
  have hzS : z ∈ (S : Subgroup H) := by
    have hz : z ∈ (center ↥(S : Subgroup H)).map (S : Subgroup H).subtype := hZ ▸ mem_zpowers z
    obtain ⟨y, -, rfl⟩ := hz
    exact y.2
  have hr2 : 2 ≤ 2 ^ (r - 2) := by
    simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ r - 2 by omega)
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    have hdvdQ : 2 ∣ Nat.card (Q : Subgroup K) := by
      have h := Nat.card_congr eQ.toEquiv
      rw [Nat.card_eq_fintype_card (α := QuaternionGroup _), QuaternionGroup.card] at h
      change 2 ∣ Nat.card ↥Q
      rw [h]
      exact Dvd.dvd.mul_right (by norm_num) _
    have hdvd : 2 ∣ Nat.card H :=
      hdvdQ.trans ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card K))
    have hne : (S : Subgroup H) ≠ ⊥ := S.ne_bot_of_dvd_card hdvd
    haveI : Nontrivial ↥(S : Subgroup H) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hcS := S.isPGroup'.center_nontrivial
    rw [zpowers_one_eq_bot,
      Subgroup.map_eq_bot_iff_of_injective _ (S : Subgroup H).subtype_injective] at hZ
    exact ((Subgroup.nontrivial_iff_ne_bot _).1 hcS) hZ
  set zK : K := ⟨z, hzK⟩ with hzK_def
  have hcomm : ∀ x : K, x * zK = zK * x := fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (hKC x.2))
  have hcen : zpowers zK ≤ center K := zpowers_le.2 (mem_center_iff.2 hcomm)
  haveI : (zpowers zK).Normal := normal_of_le_center hcen
  have hp : IsPGroup 2 (zpowers zK) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 S.isPGroup' ⟨z, hzS⟩
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe zK, ← hk, ← Subgroup.orderOf_coe]
  have hzQ : zK ∈ (Q : Subgroup K) := hp.le_sylow_of_normal Q (mem_zpowers zK)
  set zQ : ↥(Q : Subgroup K) := ⟨zK, hzQ⟩ with hzQ_def
  have hcenQ : eQ zQ ∈ center (QuaternionGroup (2 ^ (r - 2))) := by
    refine mem_center_iff.2 fun g => ?_
    obtain ⟨y, rfl⟩ := eQ.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg eQ (Subtype.ext (hcomm y))
  have hsq := CFSG.ClassicalInvolution.Asc77.sq_eq_one_of_mem_center_quaternion hr2 hcenQ
  have hzQ2 : zQ ^ 2 = 1 := eQ.injective (by rw [map_pow, hsq, map_one])
  have hz2 : z ^ 2 = 1 := by
    have h := congrArg (fun x : ↥(Q : Subgroup K) => ((x : K) : H)) hzQ2
    simpa [hzQ_def, hzK_def] using h
  exact orderOf_eq_prime hz2 hz1

theorem inCatalog_of_hasPSL6Sylow
    (hFM : FooteMainL6)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (h : HasPSL6Sylow S) :
    CFSG.Assembly.InCatalog S := by
  haveI := hs
  obtain ⟨p, f, L, instL, hp, hf, hq, hL, P, P', hPP'⟩ := h
  obtain ⟨z, hZ, hQ⟩ := hFM S P ⟨p, f, L, instL, hp, hf, hq, hL, P', hPP'⟩
  by_cases hab : ∀ a b : S, a * b = b * a
  · exact CFSG.Assembly.abelian_simple S hab
  push Not at hab
  exact CFSG.ComponentClassification.StandardRecognition.inCatalog_of_normalQuaternionAt hCIT hab
    (orderOf_eq_two_of_center_eq_zpowers P hZ hQ) hQ

end CFSG.OddStandard.HigherRank.YamadaG23
