module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.OddPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.OddSylow315
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma gamma_oddA8_elem2_mul_self (u : Elem2 2) : u * u = 1 := by
  apply Multiplicative.ext
  rw [toAdd_mul]
  funext i
  change u.toAdd i + u.toAdd i = (0 : ZMod 2)
  have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc u.toAdd i + u.toAdd i = (2 : ZMod 2) * u.toAdd i := by ring
    _ = 0 := by rw [h2, zero_mul]

private lemma gamma_oddA8_pair_sq_one {x : Elem2 2 × alternatingGroup (Fin 8)}
    (hx : x.2 = 1) : x * x = 1 := by
  have hxe : x = (x.1, (1 : alternatingGroup (Fin 8))) := by
    ext <;> simp [hx]
  rw [hxe]
  ext <;> simp [gamma_oddA8_elem2_mul_self]

private lemma gamma_oddA8_centralizer_dvd {K : Type} [Group K] [Finite K]
    (f : K →* Equiv.Perm (Fin 8)) (hf : Function.Injective f) (hodd : Odd (Nat.card K)) :
    (∀ g : K, orderOf g = 7 →
        Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 7) ∧
      (∀ g : K, orderOf g = 5 →
        Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 15) := by
  constructor
  · intro g hg
    have hfg : orderOf (f g) = 7 := by rw [orderOf_injective f hf g, hg]
    have hle : (Subgroup.centralizer ({g} : Set K)).map f ≤
        Subgroup.centralizer ({f g} : Set (Equiv.Perm (Fin 8))) := by
      simpa using Subgroup.map_centralizer_le_centralizer_image ({g} : Set K) f
    calc Nat.card ↥(Subgroup.centralizer ({g} : Set K))
        = Nat.card ↥((Subgroup.centralizer ({g} : Set K)).map f) :=
          (Subgroup.card_map_of_injective (f := f) hf).symm
      _ ∣ Nat.card ↥(Subgroup.centralizer
            ({f g} : Set (Equiv.Perm (Fin 8)))) := Subgroup.card_dvd_of_le hle
      _ = 7 := gamma_perm_card_centralizer_seven (f g) hfg
  · intro g hg
    have hfg : orderOf (f g) = 5 := by rw [orderOf_injective f hf g, hg]
    have hle : (Subgroup.centralizer ({g} : Set K)).map f ≤
        Subgroup.centralizer ({f g} : Set (Equiv.Perm (Fin 8))) := by
      simpa using Subgroup.map_centralizer_le_centralizer_image ({g} : Set K) f
    have hdvd30 : Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 30 := by
      calc Nat.card ↥(Subgroup.centralizer ({g} : Set K))
          = Nat.card ↥((Subgroup.centralizer ({g} : Set K)).map f) :=
            (Subgroup.card_map_of_injective (f := f) hf).symm
        _ ∣ Nat.card ↥(Subgroup.centralizer
              ({f g} : Set (Equiv.Perm (Fin 8)))) := Subgroup.card_dvd_of_le hle
        _ = 30 := gamma_perm_card_centralizer_five (f g) hfg
    have hoddC : Odd (Nat.card ↥(Subgroup.centralizer ({g} : Set K))) :=
      Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card _)
    have hcop : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({g} : Set K))) 2 :=
      hoddC.coprime_two_right
    have h : Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 2 * 15 := by
      simpa using hdvd30
    exact hcop.dvd_of_dvd_mul_left h

theorem gamma_odd_card_le_of_injective {K : Type} [Group K] [Finite K]
    (f : K →* Equiv.Perm (Fin 8)) (hf : Function.Injective f) (hodd : Odd (Nat.card K)) :
    Nat.card K ≤ 57 := by
  have hdvd40320 : Nat.card K ∣ 40320 := by
    have h := Subgroup.card_dvd_of_injective f hf
    rw [Nat.card_perm, Nat.card_fin, Nat.factorial] at h
    norm_num at h
    exact h
  have hdvd315 : Nat.card K ∣ 315 := by
    have h40320 : (40320 : ℕ) = 2 ^ 7 * 315 := by norm_num
    have h' : Nat.card K ∣ 2 ^ 7 * 315 := h40320 ▸ hdvd40320
    have hcop : Nat.Coprime (Nat.card K) (2 ^ 7) := by
      rw [Nat.coprime_pow_right_iff (by norm_num : 0 < 7)]
      exact hodd.coprime_two_right
    exact hcop.dvd_of_dvd_mul_left h'
  obtain ⟨h7, h5⟩ := gamma_oddA8_centralizer_dvd f hf hodd
  by_contra hle
  push Not at hle
  obtain ⟨k, hk⟩ := hdvd315
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | h
    · rw [hk0, mul_zero] at hk
      omega
    · exact h
  have hk5 : k ≤ 5 := by
    by_contra h
    push Not at h
    have h6 : 6 ≤ k := by omega
    have hc : 58 ≤ Nat.card K := by omega
    have hge : 58 * 6 ≤ Nat.card K * k := Nat.mul_le_mul hc h6
    rw [← hk] at hge
    norm_num at hge
  interval_cases k
  · have hK : Nat.card K = 315 := by omega
    exact gamma_odd_false_315 hK h7 h5
  · omega
  · have hK : Nat.card K = 105 := by omega
    exact gamma_odd_false_105 hK h7
  · omega
  · have hK : Nat.card K = 63 := by omega
    exact gamma_odd_false_63 hK h7

theorem gamma_odd_card_le {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hM : IsShapeTwoTwoTimesA8 ↥M) (hLM : L ≤ M) (hodd : Odd (Nat.card L)) :
    Nat.card L ≤ 57 := by
  obtain ⟨e⟩ := hM
  let f : ↥L →* Equiv.Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp
      ((MonoidHom.snd (Elem2 2) (alternatingGroup (Fin 8))).comp
        (e.toMonoidHom.comp (Subgroup.inclusion hLM)))
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr ?_
    intro l hl
    have h2 : (e (Subgroup.inclusion hLM l)).2 = 1 := by
      apply Subtype.ext
      simpa [f] using hl
    have hx2 : e (Subgroup.inclusion hLM l) * e (Subgroup.inclusion hLM l) = 1 :=
      gamma_oddA8_pair_sq_one h2
    have hsq : (Subgroup.inclusion hLM l) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, pow_two, hx2, map_one]
    have hdvd2 : orderOf l ∣ 2 := by
      have hdvd2' : orderOf (Subgroup.inclusion hLM l) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hsq
      have hord : orderOf (Subgroup.inclusion hLM l) = orderOf l :=
        orderOf_injective (Subgroup.inclusion hLM) (Subgroup.inclusion_injective hLM) l
      rwa [hord] at hdvd2'
    have hdvdL : orderOf l ∣ Nat.card ↥L := orderOf_dvd_natCard l
    have hoddl : Odd (orderOf l) := Odd.of_dvd_nat hodd hdvdL
    have hcop : Nat.Coprime (orderOf l) 2 := hoddl.coprime_two_right
    have hone : orderOf l = 1 := by
      have h : orderOf l ∣ 2 * 1 := by simpa using hdvd2
      exact Nat.dvd_one.mp (hcop.dvd_of_dvd_mul_left h)
    exact orderOf_eq_one_iff.mp hone
  exact gamma_odd_card_le_of_injective f hf hodd

end CFSG.EvenSporadicStandard.HNRecog.Section3
