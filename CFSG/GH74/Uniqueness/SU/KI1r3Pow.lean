module

public import CFSG.GH74.Uniqueness.SU.KI1r3PowB
public import CFSG.RankThree.GroupTheory.SteinbergCDRankOneAutPrimes
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU.K.R3.Pow

theorem Pow.mem_normalizer_of_forall_mem {G : Type*} [Group G] (R : Subgroup G) [Finite R] {g : G}
    (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R) : g ∈ normalizer (R : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hg h hh, fun hh => ?_⟩
  let c : R → R := fun r => ⟨g * r * g⁻¹, hg r r.2⟩
  have hinj : Function.Injective c := by
    intro a b hab
    have h1 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hinj ⟨g * h * g⁻¹, hh⟩
  have h2 : g * (r : G) * g⁻¹ = g * h * g⁻¹ := congrArg Subtype.val hr
  have h3 : (r : G) = h := by simpa using h2
  exact h3 ▸ r.2

theorem r3pow {G : Type} [Group G] [Finite G] (R : Subgroup G) (hR : IsPGroup 2 R) (y z : G)
    (hz : z * z = 1) (hzR : ∀ r ∈ R, z * r * z⁻¹ ∈ R) (hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R)
    (hy : IsPGroup 3 (zpowers y)) (hzy : z * y * z⁻¹ = y⁻¹)
    (hC : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1)
    (hrk : Open.pRank 2 (centralizer ({z} : Set G) ⊓ R) ≤ 1) :
    ∀ r ∈ R, y ^ 3 * r * (y ^ 3)⁻¹ = r := by
  have hyN := Pow.mem_normalizer_of_forall_mem R hyR
  have hzN := Pow.mem_normalizer_of_forall_mem R hzR
  let σ : MulAut R := R.normalizerMonoidHom ⟨y, hyN⟩
  let τ : MulAut R := R.normalizerMonoidHom ⟨z, hzN⟩
  have hσapp : ∀ r : R, ((σ r : R) : G) = y * r * y⁻¹ := fun r => rfl
  have hτapp : ∀ r : R, ((τ r : R) : G) = z * r * z⁻¹ := fun r => rfl
  obtain ⟨k, hk⟩ := hy ⟨y, mem_zpowers y⟩
  have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hDih : DihAct σ τ k := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (⟨y, hyN⟩ : normalizer (R : Set G)) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hyk)
      change R.normalizerMonoidHom ⟨y, hyN⟩ ^ 3 ^ k = 1
      rw [← map_pow, this, map_one]
    · have : (⟨z, hzN⟩ : normalizer (R : Set G)) ^ 2 = 1 :=
        Subtype.ext (by simpa [pow_two] using hz)
      change R.normalizerMonoidHom ⟨z, hzN⟩ ^ 2 = 1
      rw [← map_pow, this, map_one]
    · have : (⟨z, hzN⟩ : normalizer (R : Set G)) * ⟨y, hyN⟩ *
          (⟨z, hzN⟩ : normalizer (R : Set G))⁻¹ = (⟨y, hyN⟩ : normalizer (R : Set G))⁻¹ :=
        Subtype.ext (by simpa using hzy)
      have h2 := congrArg R.normalizerMonoidHom this
      simpa only [map_mul, map_inv] using h2
    · intro r hr
      exact Subtype.ext (hC r r.2 (by rw [← hσapp r, hr]))
  let C : Subgroup G := centralizer ({z} : Set G) ⊓ R
  have hCR : C ≤ R := inf_le_right
  have hP : IsPGroup 2 C := hR.to_le hCR
  have hrank : CFSG.pRank 2 C ≤ 1 := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two]; exact hrk
  have hP4 := CFSG.RankThree.GroupTheory.card_frattini_quotient_le_four_of_pRank_le_one hP hrank
  have hσ3 := pow_three_eq_one_aut hR hDih hP hP4 (Subgroup.inclusion hCR) (by
    intro r hr
    have hr' : z * (r : G) * z⁻¹ = r := by rw [← hτapp r, hr]
    have hc : (r : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h5 : z * (r : G) = r * z := calc
        z * (r : G) = z * (r : G) * z⁻¹ * z := by group
        _ = r * z := by rw [hr']
      exact h5.symm
    exact ⟨⟨r, hc, r.2⟩, rfl⟩)
  intro r hr
  have hmap : σ ^ 3 = R.normalizerMonoidHom ((⟨y, hyN⟩ : normalizer (R : Set G)) ^ 3) :=
    (map_pow R.normalizerMonoidHom _ 3).symm
  rw [hmap] at hσ3
  have h3 := congrArg (fun a : MulAut R => ((a ⟨r, hr⟩ : R) : G)) hσ3
  simpa using h3

end CFSG.GH74.Uniqueness.SU.K.R3
