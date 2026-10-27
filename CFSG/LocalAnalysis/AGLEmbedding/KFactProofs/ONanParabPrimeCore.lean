module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Y : Type*} [Group Y]

theorem eq_map_borel_sup_of_le
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {π : K →* Y} (hπ : Function.Surjective π) {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) :
    J = (borel D H).map π ⊔ ⨆ i ∈ negIndices D (J.comap π), (rankOne D.rootGroup i).map π := by
  have hBA : borel D H ≤ J.comap π := fun b hb => hBJ ⟨b, hb, rfl⟩
  have h := congrArg (Subgroup.map π) (eq_borel_sup_rankOne hct hext hBA)
  rw [Subgroup.map_comap_eq_self_of_surjective hπ, Subgroup.map_sup, Subgroup.map_iSup] at h
  refine h.trans ?_
  congr 1
  exact iSup_congr fun i => Subgroup.map_iSup _ _

theorem dvd_of_dvd_card_map_borel [Finite Y]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (π : K →* Y) {m : ℕ} (hH : ∀ h ∈ ⨆ i, H i, h ^ m = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpB : p ∣ Nat.card ((borel D H).map π)) : p ∣ m := by
  set T : Subgroup K := ⨆ i, H i with hT
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos hext hX
  have hBeq : (borel D H).map π = T.map π ⊔ (posUnipotent D).map π := by
    rw [CFSG.LieType.Steinberg.borel, Subgroup.map_sup]
  have hTN : T.map π ≤ Subgroup.normalizer ((posUnipotent D).map π : Set Y) :=
    (Subgroup.map_mono (iSup_le_borel.trans (borel_le_normalizer_posUnipotent hct))).trans
      (Subgroup.le_normalizer_map π)
  have hdvd := card_sup_dvd_mul (T.map π) ((posUnipotent D).map π) hTN
  rw [← hBeq] at hdvd
  have hdvd' := hpB.trans hdvd
  rcases hp.dvd_mul.1 hdvd' with h | h
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p h
    obtain ⟨t₀, ht₀, ht₀e⟩ := t.2
    have hpow : ((t : Y)) ^ m = 1 := by
      rw [← ht₀e, ← map_pow, hH t₀ ht₀, map_one]
    have := orderOf_dvd_of_pow_eq_one hpow
    rwa [Subgroup.orderOf_coe, ht] at this
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (hU2.map π).exists_card_eq
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem exists_perfect_dvd_of_borel_lt [Finite Y]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    {π : K →* Y} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {q : ℕ} (hq4 : 4 ≤ q) (hrank : ∀ i, RankOneNode D i q)
    (hH : ∀ h ∈ ⨆ i, H i, h ^ (q ^ 2 - 1) = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {J : Subgroup Y} (hBJ : (borel D H).map π ≤ J) (hne : J ≠ (borel D H).map π) :
    (p ∣ q ^ 2 - 1 → ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V) ∧
      (p ∣ Nat.card J → ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V) := by
  have hBA : borel D H ≤ J.comap π := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hAne : J.comap π ≠ borel D H := by
    intro h
    apply hne
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ J, h]
  obtain ⟨i₀, hi₀⟩ := negIndices_nonempty_of_ne hct hext hBA hAne
  have hJeq := eq_map_borel_sup_of_le hct hext hπ hBJ
  have hperfi : ∀ i ∈ negIndices D (J.comap π),
      ⁅(rankOne D.rootGroup i).map π, (rankOne D.rootGroup i).map π⁆ =
        (rankOne D.rootGroup i).map π ∧ (rankOne D.rootGroup i).map π ≤ J := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.map_commutator, (hrank i).perfect hq4]
    · rintro _ ⟨x, hx, rfl⟩
      exact (show rankOne D.rootGroup i ≤ J.comap π from
        rankOne_le_of_mem_negIndices hBA hi) hx
  have hgen : J ≤ (borel D H).map π ⊔ perfectJoin J :=
    hJeq.le.trans (sup_le_sup_left (iSup₂_le fun i hi =>
      le_perfectJoin (hperfi i hi).2 (hperfi i hi).1) _)
  have hfirst : p ∣ q ^ 2 - 1 → ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V := by
    intro hpq
    obtain ⟨x, hx, hxp, hxc⟩ := (hrank i₀).prime p hp hp5 hpq
    refine ⟨(rankOne D.rootGroup i₀).map π, (hperfi i₀ hi₀).2, (hperfi i₀ hi₀).1, ?_⟩
    have hπx : π x ≠ 1 := fun h => hxc (hker h)
    have hord : orderOf (π x) = p := by
      have hdvd : orderOf (π x) ∣ p :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, ← hxp, pow_orderOf_eq_one, map_one])
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hπx
      · exact h
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ ⟨x, hx, rfl⟩
  refine ⟨hfirst, fun hpJ => ?_⟩
  rcases dvd_card_of_generated hp hBJ hgen hpJ with h | h
  · exact hfirst (dvd_of_dvd_card_map_borel hct hext hX π hH hp (by omega) h)
  · exact ⟨perfectJoin J, perfectJoin_le J, perfectJoin_perfect J, h⟩

end CFSG.AGLEmbedding.ParabPrime
