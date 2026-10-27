module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisAction
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup

variable {G : Type*} [Group G] {Q : Subgroup G}

namespace HeisCoordData

theorem ker_actHom_eq_subgroupOf {p : ℕ} (D : HeisCoordData p Q)
    (hker : ∀ n : normalizer (Q : Set G), D.actMat n = 1 → (n : G) ∈ Q) :
    D.actHom.ker = Q.subgroupOf (normalizer (Q : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h1 : D.actHom n = 1 ↔ D.actMat n = 1 := by
    rw [← Units.val_inj, D.coe_actHom]; simp
  rw [h1]
  refine ⟨hker n, fun hn => ?_⟩
  have := D.actMat_of_mem (p := p) ⟨(n : G), hn⟩
  exact this

end HeisCoordData

theorem card_normalizer_eq {p : ℕ} [Finite G] (D : HeisCoordData p Q)
    (hker : ∀ n : normalizer (Q : Set G), D.actMat n = 1 → (n : G) ∈ Q) :
    Nat.card (normalizer (Q : Set G)) = Nat.card Q * Nat.card D.actHom.range := by
  have h := Subgroup.card_ker_mul_card_range D.actHom
  rw [D.ker_actHom_eq_subgroupOf hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := Q))).toEquiv] at h
  exact h.symm

theorem card_range_actHom_dvd (D : HeisCoordData 11 Q) :
    Nat.card D.actHom.range ∣ 13200 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h := Subgroup.card_subgroup_dvd_card D.actHom.range
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) = 13200 := by
    rw [Matrix.card_GL_field (n := 2) (𝔽 := ZMod 11)]
    simp [Fin.prod_univ_two, ZMod.card]
  rwa [hc] at h

theorem isSolvable_normalizer_of_heis [Finite G] {Q : Subgroup G}
    (D : HeisCoordData 11 Q) (hQc : Nat.card Q = 11 ^ 3)
    (hker : ∀ n : normalizer (Q : Set G), D.actMat n = 1 → (n : G) ∈ Q)
    {M : ℕ} (hG : Nat.card G = 11 ^ 3 * M) (hM : Nat.gcd M 13200 ∣ 240)
    (t : normalizer (Q : Set G))
    (hdet : orderOf (Matrix.GeneralLinearGroup.det (D.actHom t)) = 10) :
    Group.IsSolvable (normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set R := D.actHom.range with hR
  have hRM : Nat.card R ∣ M := by
    have h1 := Subgroup.card_subgroup_dvd_card (normalizer (Q : Set G))
    rw [card_normalizer_eq D hker, hQc, hG] at h1
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 h1
  have hR240 : Nat.card R ∣ 240 :=
    (Nat.dvd_gcd hRM (card_range_actHom_dvd D)).trans hM
  let det' : R →* (ZMod 11)ˣ := Matrix.GeneralLinearGroup.det.comp R.subtype
  have hrange : Nat.card det'.range = 10 := by
    have hd : Nat.card det'.range ∣ Nat.card (ZMod 11)ˣ :=
      Subgroup.card_subgroup_dvd_card _
    have hu : Nat.card (ZMod 11)ˣ = 10 := by
      rw [Nat.card_units]; simp
    rw [hu] at hd
    have hmem : Matrix.GeneralLinearGroup.det (D.actHom t) ∈ det'.range :=
      ⟨⟨D.actHom t, t, rfl⟩, rfl⟩
    have h10 : 10 ∣ Nat.card det'.range := by
      rw [← hdet, ← Subgroup.orderOf_mk _ hmem]
      exact orderOf_dvd_natCard _
    exact Nat.dvd_antisymm hd h10
  have hker24 : Nat.card det'.ker ∣ 24 := by
    have h := Subgroup.card_ker_mul_card_range det'
    rw [hrange] at h
    rw [← h] at hR240
    have : Nat.card det'.ker * 10 ∣ 24 * 10 := by simpa using hR240
    exact (Nat.mul_dvd_mul_iff_right (by norm_num)).1 this
  have hkerSolv : Group.IsSolvable det'.ker := by
    apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    have h1 : (Nat.card det'.ker).primeFactors ⊆ (24 : ℕ).primeFactors :=
      Nat.primeFactors_mono hker24 (by norm_num)
    have h2 : (24 : ℕ).primeFactors = {2, 3} := by
      have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [this, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
      rfl
    calc (Nat.card det'.ker).primeFactors.card ≤ (24 : ℕ).primeFactors.card :=
          Finset.card_le_card h1
      _ = 2 := by rw [h2]; rfl
  have hRSolv : Group.IsSolvable R :=
    Group.isSolvable_of_ker_le_range det'.ker.subtype det' (by simp)
  have hQSolv : Group.IsSolvable D.actHom.ker := by
    rw [D.ker_actHom_eq_subgroupOf hker]
    have hp : IsPGroup 11 (Q.subgroupOf (normalizer (Q : Set G))) := by
      apply IsPGroup.of_card (n := 3)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.le_normalizer (H := Q))).toEquiv, hQc]
    have := hp.isNilpotent
    infer_instance
  have : Group.IsSolvable R := hRSolv
  have : Group.IsSolvable D.actHom.ker := hQSolv
  exact Group.isSolvable_of_ker_le_range D.actHom.ker.subtype D.actHom.rangeRestrict
    (by simp [MonoidHom.ker_rangeRestrict])

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

