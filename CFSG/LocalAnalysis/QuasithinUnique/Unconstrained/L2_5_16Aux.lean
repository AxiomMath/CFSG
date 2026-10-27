module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin DihedralGroup
open scoped MatrixGroups

theorem center_dihedral_four : ∀ a : DihedralGroup 4, (∀ b : DihedralGroup 4, a * b = b * a) →
    a = 1 ∨ a = r 2 := by decide

theorem r2_central : ∀ a : DihedralGroup 4, a * r 2 = r 2 * a := by decide

theorem r2_sq : (r 2 : DihedralGroup 4) * r 2 = 1 := by decide

theorem r2_ne_one : (r 2 : DihedralGroup 4) ≠ 1 := by decide

theorem normalizer_le_of_dihedral_eight {K : Type*} [Group K] [Finite K] (P : Subgroup K)
    (e : ↥P ≃* DihedralGroup 4)
    (hC : ∀ u : K, u * u = 1 → u ≠ 1 → Nat.card (Subgroup.centralizer ({u} : Set K)) = 8) :
    Subgroup.normalizer (P : Set K) ≤ P := by
  let uP : P := e.symm (r 2)
  have huP : (uP : K) ∈ P := uP.2
  have hu2 : (uP : K) * (uP : K) = 1 := by
    have : uP * uP = 1 := by
      show e.symm (r 2) * e.symm (r 2) = 1
      rw [← map_mul, r2_sq, map_one]
    simpa using congrArg Subtype.val this
  have hu1 : (uP : K) ≠ 1 := by
    intro h
    have h1 : uP = 1 := Subtype.ext h
    have h2 : e uP = e 1 := congrArg e h1
    have h3 : e uP = r 2 := by simp [uP]
    rw [h3, map_one] at h2
    exact r2_ne_one h2
  have huz : ∀ y ∈ P, y * (uP : K) = (uP : K) * y := by
    intro y hy
    have h : e ⟨y, hy⟩ * r 2 = r 2 * e ⟨y, hy⟩ := r2_central _
    have h' : (⟨y, hy⟩ : P) * uP = uP * ⟨y, hy⟩ := by
      apply e.injective
      simp only [map_mul]
      simpa [uP] using h
    simpa using congrArg Subtype.val h'
  have hPle : P ≤ Subgroup.centralizer ({(uP : K)} : Set K) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact huz y hy
  have hcard : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hPeq : P = Subgroup.centralizer ({(uP : K)} : Set K) :=
    Subgroup.eq_of_le_of_card_ge hPle (by rw [hC _ hu2 hu1, hcard])
  intro n hn
  have hn' := Subgroup.mem_normalizer_iff.mp hn
  have hnuP : n * (uP : K) * n⁻¹ ∈ P := (hn' _).mp huP
  have hconj : ∀ y ∈ P, n⁻¹ * y * n ∈ P := fun y hy =>
    (hn' (n⁻¹ * y * n)).mpr (by simpa [mul_assoc] using hy)
  have hcen : ∀ y : P, y * (⟨n * (uP : K) * n⁻¹, hnuP⟩ : P) =
      (⟨n * (uP : K) * n⁻¹, hnuP⟩ : P) * y := by
    intro y
    apply Subtype.ext
    show (y : K) * (n * (uP : K) * n⁻¹) = (n * (uP : K) * n⁻¹) * y
    have h1 := huz _ (hconj _ y.2)
    calc (y : K) * (n * (uP : K) * n⁻¹) = n * ((n⁻¹ * (y : K) * n) * (uP : K)) * n⁻¹ := by group
      _ = n * ((uP : K) * (n⁻¹ * (y : K) * n)) * n⁻¹ := by rw [h1]
      _ = (n * (uP : K) * n⁻¹) * y := by group
  have hcenD : ∀ b : DihedralGroup 4, e ⟨n * (uP : K) * n⁻¹, hnuP⟩ * b =
      b * e ⟨n * (uP : K) * n⁻¹, hnuP⟩ := by
    intro b
    have := hcen (e.symm b)
    have h2 := congrArg e this
    simpa using h2.symm
  rcases center_dihedral_four _ hcenD with h | h
  · exfalso
    have : (⟨n * (uP : K) * n⁻¹, hnuP⟩ : P) = 1 := e.injective (by simpa using h)
    have h2 := congrArg Subtype.val this
    simp only [OneMemClass.coe_one] at h2
    apply hu1
    calc (uP : K) = n⁻¹ * (n * (uP : K) * n⁻¹) * n := by group
      _ = 1 := by rw [h2]; group
  · have : (⟨n * (uP : K) * n⁻¹, hnuP⟩ : P) = uP := by
      apply e.injective
      rw [h]
      simp [uP]
    have h2 := congrArg Subtype.val this
    have hc : n * (uP : K) = (uP : K) * n := by
      have : n * (uP : K) * n⁻¹ = (uP : K) := h2
      calc n * (uP : K) = n * (uP : K) * n⁻¹ * n := by group
        _ = (uP : K) * n := by rw [this]
    have : n ∈ Subgroup.centralizer ({(uP : K)} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc
    rw [← hPeq] at this
    exact this

theorem card_centralizer_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine Nat.card_congr
    { toFun := fun x => ⟨c * x * c⁻¹, ?_⟩
      invFun := fun y => ⟨c⁻¹ * y * c, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * (x : G) * c⁻¹ * (c * a * c⁻¹) = c * ((x : G) * a) * c⁻¹ := by group
      _ = c * (a * (x : G)) * c⁻¹ := by rw [hx]
      _ = c * a * c⁻¹ * (c * (x : G) * c⁻¹) := by group
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hb : a = c⁻¹ * b * c := by rw [← hc]; group
    rw [hb]
    calc c⁻¹ * (y : G) * c * (c⁻¹ * b * c) = c⁻¹ * ((y : G) * b) * c := by group
      _ = c⁻¹ * (b * (y : G)) * c := by rw [hy]
      _ = c⁻¹ * b * c * (c⁻¹ * (y : G) * c) := by group
  · intro x; apply Subtype.ext; group
  · intro y; apply Subtype.ext; group

theorem card_centralizer_congr {K L : Type*} [Group K] [Group L] (e : K ≃* L) (u : K) :
    Nat.card (Subgroup.centralizer ({u} : Set K)) =
      Nat.card (Subgroup.centralizer ({e u} : Set L)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e x, ?_⟩
      invFun := fun y => ⟨e.symm y, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
  · intro x; simp
  · intro y; simp

theorem card_centralizer_psl2_eight {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hq : Fintype.card F = 7 ∨ Fintype.card F = 9) :
    ∀ u : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, u * u = 1 → u ≠ 1 →
      Nat.card (Subgroup.centralizer ({u} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)))
        = 8 := by
  obtain ⟨T₀, w, -, -, -, -, hconj, hcent, hcard⟩ :=
    CFSG.QuasithinUnique.K1.psl2_torus_data hF (by omega)
  intro u hu2 hu1
  obtain ⟨x, hxT, hxu⟩ := hconj u hu2 hu1
  obtain ⟨c, hc⟩ := isConj_iff.mp hxu
  have hx2 : x * x = 1 := by
    rw [← hc]
    calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hx1 : x ≠ 1 := by
    intro h
    apply hu1
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = 1 := by rw [hc, h]; group
  rw [card_centralizer_eq_of_isConj hxu, hcent x hxT hx1 hx2]
  rcases hq with h | h
  · rw [h] at hcard; norm_num at hcard; omega
  · rw [h] at hcard; norm_num at hcard; omega

theorem factorization_two_pow_mul {k b : ℕ} (hb : ¬ 2 ∣ b) :
    (2 ^ k * b).factorization 2 = k := by
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hb0]
  simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hb]

theorem twoPart_eq_eight {G : Type*} [Group G] {X : Subgroup G} {b : ℕ} (hb : ¬ 2 ∣ b)
    (hX : Nat.card X = 8 * b) : twoPart X = 8 := by
  unfold twoPart
  have h8 : 8 * b = 2 ^ 3 * b := by norm_num
  rw [hX, h8, factorization_two_pow_mul hb]
  norm_num

theorem card_centralizer_eight_of_L32 {K : Type} [Group K]
    (h : StatedClassicalModel K .PSL 3 2 1) :
    Nat.card K = 168 ∧ ∀ u : K, u * u = 1 → u ≠ 1 →
      Nat.card (Subgroup.centralizer ({u} : Set K)) = 8 := by
  have hL : CFSG.Blueprint.LieModel K .PSL 3 2 1 :=
    Or.inl ⟨by decide, h⟩
  have h7 := CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism K hL
  rcases h7 with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨F, _, _, _, e, hqF, hF, hq5⟩ :=
      CFSG.QuasithinUnique.K1.psl2_model_data (X := K) (p := 7) (f := 1) (by norm_num) hc
    have hq7 : Fintype.card F = 7 := by simpa using hqF
    refine ⟨?_, fun u hu2 hu1 => ?_⟩
    · rw [Nat.card_congr e.toEquiv]
      have := CFSG.QuasithinUnique.K1.psl2_card_mul_two hF hq5
      rw [hq7] at this
      omega
    · have hu2' : e u * e u = 1 := by rw [← map_mul, hu2, map_one]
      have hu1' : e u ≠ 1 := fun h => hu1 (e.injective (by rw [h, map_one]))
      rw [card_centralizer_congr e u]
      exact card_centralizer_psl2_eight hF (Or.inl hq7) (e u) hu2' hu1'
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_centralizer_eight_of_A6 {K : Type} [Group K]
    (e : K ≃* alternatingGroup (Fin 6)) :
    Nat.card K = 360 ∧ ∀ u : K, u * u = 1 → u ≠ 1 →
      Nat.card (Subgroup.centralizer ({u} : Set K)) = 8 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F := GaloisField 3 2
  have : Fintype F := Fintype.ofFinite F
  have hF9 : Fintype.card F = 9 := by
    have := GaloisField.card 3 2 (by norm_num)
    rw [← Nat.card_eq_fintype_card]
    simpa using this
  have hF : ringChar F ≠ 2 := by
    have : ringChar F = 3 := ringChar.eq F 3
    omega
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
    F hF9
  let e' : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := e.trans φ.symm
  refine ⟨?_, fun u hu2 hu1 => ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact card_alt_six
  · have hu2' : e' u * e' u = 1 := by rw [← map_mul, hu2, map_one]
    have hu1' : e' u ≠ 1 := fun h => hu1 (e'.injective (by rw [h, map_one]))
    rw [card_centralizer_congr e' u]
    exact card_centralizer_psl2_eight hF (Or.inr hF9) (e' u) hu2' hu1'

end CFSG.QuasithinUnique.Unc25K1
