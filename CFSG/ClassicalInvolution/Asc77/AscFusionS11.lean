module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR9
public import CFSG.ClassicalInvolution.Asc77.AscFusionS2

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups Pointwise

section Pure

variable {G : Type} [Group G]

theorem swap_element {z t j k : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z)
    (hjt : j * t = t * j) (hjz : j⁻¹ * z * j = z * t) (hkz : k * z = z * k)
    (hkt : k⁻¹ * t * k = t * z) :
    (j * k * j)⁻¹ * z * (j * k * j) = t ∧ (j * k * j)⁻¹ * t * (j * k * j) = z := by
  have hjt' : j⁻¹ * t * j = t := by
    calc j⁻¹ * t * j = j⁻¹ * (t * j) := by group
      _ = j⁻¹ * (j * t) := by rw [hjt]
      _ = t := by group
  have hkz' : k⁻¹ * z * k = z := by
    calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
      _ = k⁻¹ * (k * z) := by rw [hkz]
      _ = z := by group
  have hztz : z * t * z = t := by
    calc z * t * z = t * z * z := by rw [hzt]
      _ = t * (z * z) := by group
      _ = t := by rw [hz2, mul_one]
  have htzt : t * z * t = z := by
    calc t * z * t = z * t * t := by rw [← hzt]
      _ = z * (t * t) := by group
      _ = z := by rw [ht2, mul_one]
  constructor
  · calc (j * k * j)⁻¹ * z * (j * k * j) = j⁻¹ * (k⁻¹ * (j⁻¹ * z * j) * k) * j := by group
      _ = j⁻¹ * (k⁻¹ * (z * t) * k) * j := by rw [hjz]
      _ = j⁻¹ * ((k⁻¹ * z * k) * (k⁻¹ * t * k)) * j := by group
      _ = j⁻¹ * (z * (t * z)) * j := by rw [hkz', hkt]
      _ = j⁻¹ * (z * t * z) * j := by group
      _ = j⁻¹ * t * j := by rw [hztz]
      _ = t := hjt'
  · calc (j * k * j)⁻¹ * t * (j * k * j) = j⁻¹ * (k⁻¹ * (j⁻¹ * t * j) * k) * j := by group
      _ = j⁻¹ * (k⁻¹ * t * k) * j := by rw [hjt']
      _ = j⁻¹ * (t * z) * j := by rw [hkt]
      _ = (j⁻¹ * t * j) * (j⁻¹ * z * j) := by group
      _ = t * (z * t) := by rw [hjt', hjz]
      _ = t * z * t := by group
      _ = z := htzt

theorem kappa_delta_facts {z v κ : G} (hz2 : z * z = 1) (hvz : v * z = z * v) (hκ2 : κ * κ = z)
    (hκn : (v * v)⁻¹ * κ * (v * v) = κ⁻¹)
    (hcomm : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ) :
    (κ * (v⁻¹ * κ * v)) * (κ * (v⁻¹ * κ * v)) = 1 ∧
      (v * v) * (κ * (v⁻¹ * κ * v)) = (κ * (v⁻¹ * κ * v)) * (v * v) ∧
      (κ * (v⁻¹ * κ * v)) * v * (κ * (v⁻¹ * κ * v))⁻¹ = v * z := by
  set κ' : G := v⁻¹ * κ * v with hκ'
  set δ : G := κ * κ' with hδ
  set n : G := v * v with hn
  have hzv : v⁻¹ * z * v = z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * z) := by rw [hvz]
      _ = z := by group
  have e1 : κ * v = v * κ' := by rw [hκ']; group
  have e2 : κ' * v = v * κ⁻¹ := by
    calc κ' * v = v⁻¹ * κ * (v * v) := by rw [hκ']; group
      _ = v * ((v * v)⁻¹ * κ * (v * v)) := by group
      _ = v * κ⁻¹ := by rw [hκn]
  have e3 : κ' * κ' = z := by
    calc κ' * κ' = v⁻¹ * (κ * κ) * v := by rw [hκ']; group
      _ = z := by rw [hκ2, hzv]
  have hδ2 : δ * δ = 1 := by
    calc δ * δ = κ * (κ' * κ) * κ' := by rw [hδ]; group
      _ = κ * (κ * κ') * κ' := by rw [← hcomm]
      _ = (κ * κ) * (κ' * κ') := by group
      _ = 1 := by rw [hκ2, e3, hz2]
  have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  have hκ'n : n⁻¹ * κ' * n = κ'⁻¹ := by
    calc n⁻¹ * κ' * n = v⁻¹ * ((v * v)⁻¹ * κ * (v * v)) * v := by rw [hκ', hn]; group
      _ = κ'⁻¹ := by rw [hκn, hκ']; group
  have hnδ : n⁻¹ * δ * n = δ := by
    calc n⁻¹ * δ * n = (n⁻¹ * κ * n) * (n⁻¹ * κ' * n) := by rw [hδ]; group
      _ = κ⁻¹ * κ'⁻¹ := by rw [hκn, hκ'n]
      _ = (κ' * κ)⁻¹ := by group
      _ = δ⁻¹ := by rw [← hcomm]
      _ = δ := hδi
  have hnδ' : n * δ = δ * n := by
    have := congrArg (fun x => n * x) hnδ
    simpa [mul_assoc] using this.symm
  refine ⟨hδ2, hnδ', ?_⟩
  rw [hδi]
  calc δ * v * δ = κ * (κ' * v) * κ * κ' := by rw [hδ]; group
    _ = κ * (v * κ⁻¹) * κ * κ' := by rw [e2]
    _ = (κ * v) * κ' := by group
    _ = v * (κ' * κ') := by rw [e1]; group
    _ = v * z := by rw [e3]


end Pure

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_fixed_order_four_of_inner (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRK : IsSylow2In (R ⊓ K) K) {t : G} (htR : t ∈ R) (ht2 : t * t = 1)
    (htN : t ∈ Subgroup.normalizer (K : Set G)) {u : G} (huK : u ∈ K)
    (hact : ∀ y ∈ K, t * y * t⁻¹ * (u * y * u⁻¹)⁻¹ ∈ oddCoreOf K)
    (hg2 : ∀ y ∈ K, ⁅u * u, y⁆ ∈ oddCoreOf K) (hnc : ¬ ∀ y ∈ K, ⁅u, y⁆ ∈ oddCoreOf K) :
    ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
  classical
  obtain ⟨e⟩ := hK.nonempty_equiv
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  have hF2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hodd
  set φ : ↥K →* SL(2, GaloisField p f) := chartMap e with hφ
  have hφs : Function.Surjective φ := chartMap_surjective e
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzK : z ∈ K := hKz.mem
  set h : SL(2, GaloisField p f) := φ ⟨u, huK⟩ with hh
  have hu2c : h * h ∈ Subgroup.center SL(2, GaloisField p f) := by
    have := (comm_mem_oddCoreOf_iff_central e (K.mul_mem huK huK)).mp hg2
    have e1 : chartMap e ⟨u * u, K.mul_mem huK huK⟩ = h * h := by
      rw [hh, hφ, ← map_mul]
      rfl
    rwa [e1] at this
  have hhnc : h ∉ Subgroup.center SL(2, GaloisField p f) := fun hc =>
    hnc ((comm_mem_oddCoreOf_iff_central e huK).mpr hc)
  have hcc : (-1 : SL(2, GaloisField p f)) * (-1) = 1 := by
    apply Subtype.ext
    simp
  have hh2 : h * h = -1 := by
    rw [mem_center_sl2_iff] at hu2c
    rcases hu2c with h1 | h1
    · exfalso
      have hinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right h1
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self _ hF2 _ hinv with
        h2 | h2
      · exact hhnc (by rw [h2]; exact Subgroup.one_mem _)
      · exact hhnc (by rw [h2]; exact (mem_center_sl2_iff _).mpr (Or.inr rfl))
    · exact h1
  have hφz : φ ⟨z, hzK⟩ = -1 := by
    have hz1 : φ ⟨z, hzK⟩ ≠ 1 := by
      intro h1
      have hmem : z ∈ oddCoreOf K := (mem_oddCoreOf_iff_chart e).mpr ⟨hzK, h1⟩
      exact hKz.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
        (isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one))
    have hinv : (φ ⟨z, hzK⟩)⁻¹ = φ ⟨z, hzK⟩ := by
      rw [← map_inv]
      congr 1
      exact inv_eq_of_mul_eq_one_right (Subtype.ext hKz.sq)
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self _ hF2 _ hinv with
      h1 | h1
    · exact absurd h1 hz1
    · exact h1
  have hconj : ∀ y : ↥K, φ ⟨t * (y : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN y).mp y.2⟩ =
      h * φ y * h⁻¹ := by
    intro y
    have := chart_conj_eq e htN huK y.2 (hact y y.2)
    rw [hh]
    exact this
  let P₀ : Sylow 2 ↥K := AscL62.sylowOfIsSylow2In'' hRK
  let P : Sylow 2 SL(2, GaloisField p f) := Sylow.mapSurjective (f := φ) hφs P₀
  have hPcoe : (P : Subgroup SL(2, GaloisField p f)) = (P₀ : Subgroup ↥K).map φ :=
    Sylow.coe_mapSurjective (f := φ) hφs P₀
  have hP₀ : ∀ y : ↥K, y ∈ (P₀ : Subgroup ↥K) ↔ (y : G) ∈ R := by
    intro y
    constructor
    · intro hy
      have : (y : G) ∈ R ⊓ K := hy
      exact this.1
    · intro hy
      have : (y : G) ∈ R ⊓ K := ⟨hy, y.2⟩
      exact this
  have hmemP : ∀ y : ↥K, (y : G) ∈ R → φ y ∈ (P : Subgroup SL(2, GaloisField p f)) := by
    intro y hyR
    rw [hPcoe]
    exact ⟨y, (hP₀ y).mpr hyR, rfl⟩
  have hnormP : h ∈ Subgroup.normalizer ((P : Subgroup SL(2, GaloisField p f)) : Set _) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have hs' : s ∈ (P : Subgroup SL(2, GaloisField p f)) := hs
    rw [hPcoe] at hs'
    obtain ⟨y, hy, rfl⟩ := hs'
    have hyR : (y : G) ∈ R := (hP₀ y).mp hy
    have e1 := hconj y
    have hty : t * (y : G) * t⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem htR hyR) (R.inv_mem htR)
    have := hmemP ⟨t * (y : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN y).mp y.2⟩ hty
    rw [e1] at this
    exact this
  have hhP : h ∈ (P : Subgroup SL(2, GaloisField p f)) := by
    have h2 : IsPGroup 2 (Subgroup.zpowers h) := isPGroup_zpowers_of_sq_sq (by rw [hh2, hcc])
    have hsup := IsPGroup.to_sup_of_normal_right' h2 P.isPGroup' (Subgroup.zpowers_le.mpr hnormP)
    have := P.is_maximal' hsup le_sup_right
    rw [← this]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  rw [hPcoe] at hhP
  obtain ⟨a', ha', hφa'⟩ := hhP
  have haR : (a' : G) ∈ R := (hP₀ a').mp ha'
  have haK : (a' : G) ∈ K := a'.2
  have ha4 : (a' : G) ^ 4 = 1 := by
    have h1 : φ (a' ^ 4) = 1 := by
      rw [map_pow, hφa']
      calc h ^ 4 = (h * h) * (h * h) := by simp [pow_succ, mul_assoc]
        _ = 1 := by rw [hh2, hcc]
    have hmem : ((a' ^ 4 : ↥K) : G) ∈ oddCoreOf K :=
      (mem_oddCoreOf_iff_chart e).mpr ⟨(a' ^ 4).2, h1⟩
    have hR4 : ((a' ^ 4 : ↥K) : G) ∈ R := by
      have : ((a' ^ 4 : ↥K) : G) = (a' : G) ^ 4 := rfl
      rw [this]
      exact R.pow_mem haR 4
    have h2 : IsPGroup 2 (Subgroup.zpowers ((a' ^ 4 : ↥K) : G)) :=
      hR2.to_le (Subgroup.zpowers_le.mpr hR4)
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem h2
  have haa : (a' : G) * (a' : G) = z := by
    have h1 : ((a' : G) * (a' : G)) * ((a' : G) * (a' : G)) = 1 := by
      calc ((a' : G) * (a' : G)) * ((a' : G) * (a' : G)) = (a' : G) ^ 4 := by
            simp [pow_succ, mul_assoc]
        _ = 1 := ha4
    rcases hKz.unique _ (K.mul_mem haK haK) h1 with h2 | h2
    · exfalso
      have h3 : φ (a' * a') = 1 := by
        have : (a' * a' : ↥K) = 1 := Subtype.ext h2
        rw [this, map_one]
      rw [map_mul, hφa', hh2] at h3
      exact sl2_neg_one_ne_one hodd h3
    · exact h2
  refine ⟨(a' : G), ⟨haR, haK⟩, haa, ?_⟩
  have hta : φ ⟨t * (a' : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN a').mp a'.2⟩ = φ a' := by
    rw [hconj a', hφa']
    group
  have hw : (t * (a' : G) * t⁻¹) * (a' : G)⁻¹ ∈ oddCoreOf K := by
    have h1 : φ (⟨t * (a' : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN a').mp a'.2⟩ * a'⁻¹) =
        1 := by
      rw [map_mul, map_inv, hta, mul_inv_cancel]
    exact (mem_oddCoreOf_iff_chart e).mpr ⟨(K.mul_mem ((Subgroup.mem_normalizer_iff.mp htN a').mp
      a'.2) (K.inv_mem a'.2)), h1⟩
  have hwR : (t * (a' : G) * t⁻¹) * (a' : G)⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem htR haR) (R.inv_mem htR)) (R.inv_mem haR)
  have hw1 : (t * (a' : G) * t⁻¹) * (a' : G)⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hw
      (hR2.to_le (Subgroup.zpowers_le.mpr hwR))
  have : t * (a' : G) * t⁻¹ = (a' : G) := mul_inv_eq_one.mp hw1
  calc t * (a' : G) = (t * (a' : G) * t⁻¹) * t := by group
    _ = (a' : G) * t := by rw [this]


end Members

end CFSG.ClassicalInvolution.Asc77.AscFusion
