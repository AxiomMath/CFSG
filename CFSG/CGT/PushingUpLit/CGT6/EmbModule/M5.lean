module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5SplitX
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5CoverX

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.G23 CFSG.Open CFSG.RankThree.PerfectCover
  CFSG.CGT.PushingUpLit.CGT6.EmbModule

theorem g23NoSmallFaithful_holds :
    G23NoSmallFaithful := by
  intro L _ _ hq hmodel V _ _ hV ρ hρ
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hmodel
  let _ := hKf
  have _ := hKfin
  have hK : Nat.card K = 3 := by simpa using hKcard
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_three hK
  let eX : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  let eLX : L ⧸ Subgroup.center L ≃* adjointGroup .G2 K := e.trans eX
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  have hXs : IsSimpleGroup (adjointGroup .G2 K) := eLX.symm.isSimpleGroup
  have hLperf : Group.IsPerfect L := ⟨hq.1⟩
  let p : L →* adjointGroup .G2 K := eLX.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hp : Function.Surjective p := eLX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hpker : ∀ x, p x = 1 ↔ x ∈ Subgroup.center L := by
    intro x
    change eLX (QuotientGroup.mk' (Subgroup.center L) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hpc : p.ker ≤ Subgroup.center L := fun x hx => (hpker x).1 hx
  have hw : ∀ i, FreeGroup.mk (commWords (pairs i)) ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  have hP := isPresentation σ hK
  have hwg := lift_gens_commWords σ
  let φ : Cov →* L := (hopfLift p hp hpc).comp (presentedCoverEquiv hP hw hwg).toMonoidHom
  have hφp : ∀ x, p (φ x) = coverMap hP hwg x := by
    intro x
    change p (hopfLift p hp hpc (presentedCoverEquiv hP hw hwg x)) = _
    rw [← MonoidHom.comp_apply, comp_hopfLift]
    exact hopfCoverMap_presentedCoverEquiv hP hw hwg x
  have hφs : Function.Surjective φ :=
    (hopfLift_surjective p hp hpc).comp (presentedCoverEquiv hP hw hwg).surjective
  by_cases hφi : Function.Injective φ
  · have := cover_bound_cov σ hK hXs hV (ρ.comp φ) (hρ.comp hφi)
    calc 2 ^ 14 ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ Nat.card V := this
  ·
    have hker3 : Nat.card (coverMap hP hwg).ker = 3 := card_ker_coverMap σ hK
    have hfin : Finite (coverMap hP hwg).ker :=
      Nat.finite_of_card_ne_zero (by rw [hker3]; omega)
    have hle : φ.ker ≤ (coverMap hP hwg).ker := fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [← hφp, hx, map_one]
    have hdvd : Nat.card φ.ker ∣ 3 := hker3 ▸ Subgroup.card_dvd_of_le hle
    have heq : φ.ker = (coverMap hP hwg).ker := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact absurd ((MonoidHom.ker_eq_bot_iff φ).1 (Subgroup.card_eq_one.1 h1)) hφi
      · exact Subgroup.eq_of_le_of_card_ge hle (hker3.trans h3.symm).le
    have hpinj : Function.Injective p := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨y, rfl⟩ := hφs x
      have hy : y ∈ (coverMap hP hwg).ker := by
        rw [MonoidHom.mem_ker, ← hφp]
        exact hx
      rw [← heq, MonoidHom.mem_ker] at hy
      rw [Subgroup.mem_bot]
      exact hy
    let eL : L ≃* adjointGroup .G2 K := MulEquiv.ofBijective p ⟨hpinj, hp⟩
    exact split_bound_adjoint σ hV (ρ.comp eL.symm.toMonoidHom)
      (hρ.comp eL.symm.injective)

end CFSG.CGT.PushingUpLit.CGT6
