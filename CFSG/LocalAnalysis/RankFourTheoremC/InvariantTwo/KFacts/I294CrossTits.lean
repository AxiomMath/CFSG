module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

theorem isMulCommutative_sylow_of_card_eq_tits {L : Type} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hcard : Nat.card L = 17971200) (P : Sylow p L) :
    IsMulCommutative (P : Subgroup L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk : (Nat.card L).factorization p ≤ 2 := by
    by_contra hk
    have hk3 : 3 ≤ (Nat.card L).factorization p := by omega
    have h3 : p ^ 3 ∣ Nat.card L :=
      (pow_dvd_pow p hk3).trans (Nat.ordProj_dvd _ _)
    rw [hcard] at h3
    have hpd : p ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 :=
      (dvd_pow_self p (by norm_num)).trans h3
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
          omega
      · have h5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1
          (hp.dvd_of_dvd_pow h)
        subst h5
        norm_num at h3
    · have h13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h
      subst h13
      norm_num at h3
  have hPcard : Nat.card (P : Subgroup L) = p ^ (Nat.card L).factorization p :=
    Sylow.card_eq_multiplicity P
  generalize (Nat.card L).factorization p = k at hPcard hk
  interval_cases k
  · have h1 : Nat.card (P : Subgroup L) = 1 := by simpa using hPcard
    haveI : Subsingleton (P : Subgroup L) := (Nat.card_eq_one_iff_unique.1 h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have h1 : Nat.card (P : Subgroup L) = p := by simpa using hPcard
    haveI : IsCyclic (P : Subgroup L) := isCyclic_of_prime_card h1
    exact ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard

section Tits


theorem crossSylowAbelianAt_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    CrossSylowAbelianAt ⟨.tits, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ P
  have hR : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv (MulEquiv.refl _)
  obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hR
  have hcard : Nat.card L = 17971200 := by
    rw [Nat.card_congr (e.trans e').toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exact isMulCommutative_sylow_of_card_eq_tits hp hp5 hcard P

theorem crossFamTits : CrossFamTits := fun hv =>
  crossAt_of_sylowAbelian (crossSylowAbelianAt_tits hv)

end Tits

end CFSG.LocalAnalysis.RankFourTheoremC
