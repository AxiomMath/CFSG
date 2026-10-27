module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.Open Matrix
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.PerfectCover (hopfMultiplier)

section Scalars

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem scalar_mem_statedSU_iff (hK : Nat.card K = (r ^ f) ^ 2) (hn : 1 ≤ n) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (r ^ f) K ↔
      c ^ n = 1 ∧ c ^ (r ^ f + 1) = 1 := by
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n,
    CFSG.LieType.Universal.Unitary.mem_SUid]
  have hscal : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun _ => (c : K)) := by
    rw [GeneralLinearGroup.coe_scalar, scalar_apply]
  have hdet : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 ↔ c ^ n = 1 := by
    rw [hscal, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Units.val_pow_eq_pow_val, ← Units.val_one (α := K), Units.val_inj]
  have key : ∀ a : Kˣ, (diagonal (fun _ : Fin n => (a : K)) : Matrix (Fin n) (Fin n) K) = 1 ↔
      a = 1 := by
    intro a
    constructor
    · intro h
      have h1 := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
      rw [diagonal_apply_eq, one_apply_eq] at h1
      exact Units.ext h1
    · rintro rfl
      simp
  have hm : CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution K r f)
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun _ => ((c ^ (r ^ f + 1) : Kˣ) : K)) := by
    rw [hscal, CFSG.LieType.Universal.Unitary.conjTr, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [unitaryInvolution_apply, Units.val_pow_eq_pow_val, pow_succ]
  have hconj : CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution K r f)
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 ↔
      c ^ (r ^ f + 1) = 1 := by
    rw [hm]
    exact key _
  rw [hdet, hconj]

theorem scalar_injective_of_pos (hn : 1 ≤ n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ → GL (Fin n) K) := by
  intro c c' h
  have h1 := congrArg (fun g : GL (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply] at h1
  rw [diagonal_apply_eq, diagonal_apply_eq] at h1
  exact Units.ext h1

theorem nonempty_mulEquiv_scalars_statedSU (hK : Nat.card K = (r ^ f) ^ 2) (hn : 1 ≤ n) :
    Nonempty (rootsOfUnity (Nat.gcd n (r ^ f + 1)) K ≃*
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)) := by
  set d := Nat.gcd n (r ^ f + 1) with hd
  have hmem : ∀ c : rootsOfUnity d K,
      GeneralLinearGroup.scalar (Fin n) (c : Kˣ) ∈ StatedSU n (r ^ f) K := by
    intro c
    rw [scalar_mem_statedSU_iff hK hn]
    have hc : (c : Kˣ) ^ d = 1 := (mem_rootsOfUnity d _).1 c.2
    exact ⟨orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_pow_eq_one hc).trans (Nat.gcd_dvd_left _ _)),
      orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_pow_eq_one hc).trans (Nat.gcd_dvd_right _ _))⟩
  let ι : rootsOfUnity d K →* (StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K) :=
    { toFun := fun c => ⟨⟨GeneralLinearGroup.scalar (Fin n) (c : Kˣ), hmem c⟩,
        Subgroup.mem_subgroupOf.2 ⟨(c : Kˣ), rfl⟩⟩
      map_one' := Subtype.ext (Subtype.ext (map_one _))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul _ _ _)) }
  have hinj : Function.Injective ι := by
    intro c c' h
    have h1 := congrArg (fun x : (StatedScalars (Fin n) K).subgroupOf
      (StatedSU n (r ^ f) K) => ((x : StatedSU n (r ^ f) K) : GL (Fin n) K)) h
    exact Subtype.ext (scalar_injective_of_pos hn h1)
  have hsurj : Function.Surjective ι := by
    rintro ⟨⟨x, hxS⟩, hxZ⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hxZ
    have hc' : GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (r ^ f) K := by
      change _ = x at hc
      rw [hc]
      exact hxS
    obtain ⟨h1, h2⟩ := (scalar_mem_statedSU_iff hK hn c).1 hc'
    have hcd : c ^ d = 1 := (pow_gcd_eq_one (a := c)).2 ⟨h1, h2⟩
    exact ⟨⟨c, (mem_rootsOfUnity d c).2 hcd⟩, Subtype.ext (Subtype.ext hc)⟩
  exact ⟨MulEquiv.ofBijective ι ⟨hinj, hsurj⟩⟩

theorem isCyclic_scalars_statedSU (hK : Nat.card K = (r ^ f) ^ 2) (hn : 1 ≤ n) :
    IsCyclic ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_scalars_statedSU hK hn
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem card_scalars_statedSU (hK : Nat.card K = (r ^ f) ^ 2) (hn : 1 ≤ n) :
    Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)) =
      Nat.gcd n (r ^ f + 1) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_scalars_statedSU hK hn
  rw [← Nat.card_congr e.toEquiv]
  have h : rootsOfUnity (Nat.gcd n (r ^ f + 1)) K =
      (powMonoidHom (Nat.gcd n (r ^ f + 1)) : Kˣ →* Kˣ).ker := by
    ext x
    rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [h, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hK]
  refine Nat.gcd_eq_right ?_
  have hq : 1 ≤ r ^ f := Nat.one_le_pow _ _ (Fact.out : r.Prime).pos
  have h2 : (r ^ f) ^ 2 - 1 = (r ^ f + 1) * (r ^ f - 1) := by
    have := Nat.sq_sub_sq (r ^ f) 1
    rwa [one_pow] at this
  rw [h2]
  exact (Nat.gcd_dvd_right _ _).trans (Dvd.intro _ rfl)

end Scalars

theorem exists_cover_unitary {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (hZp : IsPGroup p (center L)) {n r f : ℕ} [Fact r.Prime]
    (hn : 5 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K r] (hK : Nat.card K = (r ^ f) ^ 2)
    (e : L ⧸ center L ≃* StatedProj (StatedSU n (r ^ f) K)) :
    ∃ φ : StatedSU n (r ^ f) K →* L, Function.Surjective φ ∧
      ∀ s, e (QuotientGroup.mk (φ s)) = QuotientGroup.mk s := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0] at h1
      norm_num at h1
    · exact h0
  have hr : r.Prime := Fact.out
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU n r f := by
    refine ⟨hr, hf, by omega, ?_⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hlm : CFSG.Models.LieModel (StatedProj (StatedSU n (r ^ f) K)) .PSU n r f :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩⟩
  obtain ⟨m, hpm, hmcard⟩ := exists_card_hopfMultiplier_eq hGA hp hp5 hlm
  have hperf : Group.IsPerfect (StatedSU n (r ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  refine exists_cover_of_card hp hL hZp hperf
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)))
    (QuotientGroup.mk'_surjective _) ?_ e ⟨m, hpm, ?_⟩
  · rw [QuotientGroup.ker_mk']
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  · rw [hmcard, QuotientGroup.ker_mk', card_scalars_statedSU hK (by omega)]
    rfl

end CFSG.LocalAnalysis.RankFourTheoremC
