module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutSemilinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutGalois

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section PCard

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem card_pGroup_dvd (hp2 : p ≠ 2) (hq : 2 < p ^ f)
    (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hS : IsPGroup p S)
    (hSR : ∀ α ∈ S, ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ) :
    Nat.card S ∣ p ^ (3 * f) * f := by
  have hp : p.Prime := Fact.out
  have hcharP : CharP K p := charP_of_card hp hK
  obtain ⟨φ, c, -, hker⟩ := exists_semilinear_hom J hJ hK hfix hq S hS hSR
  rw [← Subgroup.card_ker_mul_card_range φ]
  refine mul_dvd_mul ?_ ?_
  ·
    obtain ⟨b, hb⟩ := (hS.to_subgroup φ.ker).exists_card_eq
    have h1 := card_ker_le_card_comap J hJ S φ hker
    have h2 := Subgroup.card_le_card_group (S.comap
      ((MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).comp
        (rootGroup J hJ).subtype))
    rw [card_rootGroup_eq J hJ hK hfix] at h2
    rw [hb] at h1 ⊢
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 (h1.trans h2))
  ·
    have : Finite (K ≃+* K) := finite_ringEquiv K
    have hrange : IsPGroup p φ.range := hS.of_surjective φ.rangeRestrict
      φ.rangeRestrict_surjective
    obtain ⟨a, ha⟩ := hrange.exists_card_eq
    have hK2 : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    have h1 : Nat.card φ.range ∣ 2 * f := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [card_ringEquiv K p (2 * f) hK2] at this
    have hcop : Nat.Coprime (Nat.card φ.range) 2 := by
      rw [ha]
      exact Nat.Coprime.pow_left a ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    exact hcop.dvd_of_dvd_mul_left h1

end PCard

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitaryAutPCard : KFactUnitaryAutPCard := by
  intro L _ _ p _ d hp2 hd h S hS
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_stable_rootGroup J hJ hK hfix hf e S hS
  have hS' : IsPGroup p (S.map (MulAut.congr e').toMonoidHom) := by
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    obtain ⟨k, hk⟩ := hS ⟨a, ha⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : a ^ p ^ k = 1 := congrArg Subtype.val hk
    show (MulAut.congr e').toMonoidHom a ^ p ^ k = 1
    rw [← map_pow, h1, map_one]
  have hcard : Nat.card (S.map (MulAut.congr e').toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (f := (MulAut.congr e').toMonoidHom) (MulAut.congr e').injective
  rw [← hcard]
  exact UnitaryModel.card_pGroup_dvd J hJ hK hfix hp2 hq _ hS' he'

end CFSG.AGLEmbedding
