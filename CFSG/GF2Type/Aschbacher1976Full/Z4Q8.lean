module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Main
public import CFSG.GF2Type.Aschbacher1976Common.NotWeaklyClosed
public import CFSG.Milestones.LR_wreathed_simple_recognition

public section

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG CFSG.Blueprint

theorem valuation_three_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : padicValNat p 96 = f) : p = 3 ∧ f = 1 := by
  have hdvd : p ∣ 96 := dvd_of_one_le_padicValNat (by omega)
  have key : ∀ q ∈ Nat.divisors 96, q.Prime → q = 2 ∨ q = 3 := by decide
  have hp3 : p = 3 := (key p (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hp).resolve_left hp2
  subst hp3
  refine ⟨rfl, ?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have h3 : padicValNat 3 96 = 1 := by
    have e : (96 : ℕ) = 3 * 32 := by norm_num
    rw [e, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  omega

section Certified


theorem leafZ4Q8_holds : Asc76LeafZ4Q8 := by
  intro G _ _ z hsetting hZ4
  obtain ⟨hsimp, hnab, hz, -⟩ := hsetting
  haveI := hsimp
  have hdih : ∀ x : G, orderOf x = 4 →
      CFSG.EvenSporadicStandard.Finkelstein77.WeaklyClosedInNormalizer (Subgroup.zpowers x) →
      CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo G ∨
        CFSG.ComponentClassification.AschbacherKnownGroup.HasSemidihedralSylowTwo G :=
    fun x hx hwc => CFSG.GF2Type.Aschbacher1976Common.dihedral_or_semidihedral_of_weaklyClosed
      hnab hx hwc
  obtain ⟨hH96, T, hTp, hTmax, -, hwr⟩ :=
    CFSG.GF2Type.Aschbacher1976Full.Z4Q8.sylow_structure hdih hZ4 hz
  have hwr' : ∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n) :=
    ⟨{ toSubgroup := T, isPGroup' := hTp, is_maximal' := fun {Q} hQ hle => hTmax Q hQ hle },
      2, le_rfl, hwr⟩
  rcases CFSG.Milestones.lr_wreathed_simple_recognition_1 G hnab hwr' with
    ⟨p, f, hp, hp2, hf, hmod, hmodel⟩ | ⟨p, f, hp, hp2, hf, hmod, hmodel⟩
  · exfalso
    have hval := (CFSG.Semidihedral.Principal.degree_three_model_characteristic_valuation_regularity
      .PSL (Or.inl rfl) p f hp (hp.odd_of_ne_two hp2) hf hmodel).2.2.1 z hz
    rw [hH96] at hval
    obtain ⟨rfl, rfl⟩ := valuation_three_one hp hp2 hf hval
    norm_num at hmod
  · have hval := (CFSG.Semidihedral.Principal.degree_three_model_characteristic_valuation_regularity
      .PSU (Or.inr rfl) p f hp (hp.odd_of_ne_two hp2) hf hmodel).2.2.1 z hz
    rw [hH96] at hval
    obtain ⟨rfl, rfl⟩ := valuation_three_one hp hp2 hf hval
    exact Or.inl ⟨by decide, hmodel⟩

end Certified

end CFSG.GF2Type.Aschbacher1976Full
