module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bU33
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoUThree
public import CFSG.LieType.ChevTwo.OppCl.SmallGlue
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


private def u33Pp3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

private theorem u33Pp3_card : u33Pp3.card = 3 := by
  rw [TauCeti.PrimePower.card_def]
  rfl

private theorem u33Valid_tw23 : (TauCeti.LieTypeIndex.twistedA 2 u33Pp3).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [u33Pp3]

theorem catalogIs_of_psu_three_three {S : Type} [Group S]
    (h : StatedClassicalModel S .PSU 3 3 1) : catalogIs S fU33 := by
  have hT : StatedClassicalModel (TauCeti.ValidLieTypeIndex.Group
      ⟨.twistedA 2 u33Pp3, u33Valid_tw23⟩) .PSU 3 3 1 :=
    CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two
      u33Pp3 u33Valid_tw23 u33Pp3_card (MulEquiv.refl _)
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique
    (by norm_num : (3 : ℕ) ≠ 2) h hT
  exact ⟨.lie ⟨.twistedA 2 u33Pp3, u33Valid_tw23⟩,
    by simp [fU33, onLie, u33Pp3], ⟨e⟩⟩

section Certs


theorem seitzSimpleStmt_of_psu_three_three {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSU 3 3 1) : SeitzSimpleStmt S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : catalogIs S fU33 := catalogIs_of_psu_three_three h
  have hScard : Nat.card S = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h
  have hSsimple : IsSimpleGroup S :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h
  have hOut : Nat.card (Outer S) = 2 :=
    CFSG.AGLEmbedding.card_outer_eq_two_of_model_psu_three_three h
  have hOutdvd : Nat.card (Outer S) ∣ 2 := by rw [hOut]
  have hZ : Subgroup.center S = ⊥ :=
    center_eq_bot_of_simple_nonprime hScard (by norm_num)
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hZ
  refine seitzSimpleStmt_of_vacuous hSsimple ?_ ?_
  · rw [hScard]
    norm_num
  · intro q hq hq2 E hE hbig U hU2 hUinv
    haveI : Fact q.Prime := ⟨hq⟩
    have hEin : E ≤ (MulAut.conj : S →* MulAut S).range := by
      intro α hα
      have hαodd : Odd (orderOf α) := by
        have hdvd : orderOf α ∣ q := orderOf_dvd_of_pow_eq_one (hE.2 α hα)
        rcases (Nat.dvd_prime hq).1 hdvd with h1 | hq'
        · rw [h1]
          exact odd_one
        · rw [hq']
          exact hq.odd_of_ne_two hq2
      exact CFSG.LieType.ChevTwo.OppCl.mem_inner_of_odd_orderOf_of_card_outer_dvd_two
        hOutdvd hαodd
    set P : Subgroup S := E.comap (MulAut.conj : S →* MulAut S) with hP
    have hPcard : Nat.card P = Nat.card E := by
      rw [hP, ← Subgroup.card_map_of_injective (K := P) hinj,
        Subgroup.map_comap_eq_self hEin]
    obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra h
      have hnle : n ≤ 1 := by omega
      have hle : q ^ n ≤ q := by
        simpa using Nat.pow_le_pow_right hq.pos hnle
      have : q ^ 2 ≤ q := le_trans hbig (hn ▸ hle)
      nlinarith [hq.one_lt]
    have hPdvd : q ^ n ∣ 6048 := by
      rw [← hn, ← hPcard]
      simpa [hScard] using Subgroup.card_subgroup_dvd_card P
    have hq3 : q = 3 := by
      have hq_dvd : q ∣ 6048 := dvd_trans (dvd_pow_self q (by omega)) hPdvd
      have h6048 : (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 := by norm_num
      rw [h6048] at hq_dvd
      rcases (Nat.Prime.dvd_mul hq).1 hq_dvd with h | h7
      · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
            (hq.dvd_of_dvd_pow h2)) hq2
        · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h3)
      · exfalso
        have hq7 : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h7
        have h49 : 7 ^ 2 ∣ q ^ n := by
          rw [hq7]
          exact pow_dvd_pow 7 hn2
        have : 49 ∣ 6048 := h49.trans hPdvd
        norm_num at this
    have hP3 : IsElemAbelian 3 P := by
      have := CFSG.Open.IsElemAbelian.comap hE hinj
      rwa [hq3] at this
    have hP9 : 9 ≤ Nat.card P := by
      rw [hPcard, hn, hq3]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hPN : P ≤ Subgroup.normalizer (U : Set S) := by
      intro p hp
      have hpE : MulAut.conj p ∈ E := by
        rw [hP, Subgroup.mem_comap] at hp
        exact hp
      have hpinvE : (MulAut.conj p)⁻¹ ∈ E := E.inv_mem hpE
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        exact hUinv (MulAut.conj p) hpE u hu
      · intro hu
        have h := hUinv (MulAut.conj p)⁻¹ hpinvE (MulAut.conj p u) hu
        have heq : (MulAut.conj p)⁻¹ (MulAut.conj p u) = u := by
          simp only [← map_inv, MulAut.conj_apply]
          group
        rwa [heq] at h
    by_cases hU : U = ⊥
    · exact hU
    · exfalso
      have hrank := rankBound_u33_three hc P U hP3 hU2 hU hPN
      omega

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
