module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YFCount

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YF

open scoped Matrix
open CFSG.StandardType CFSG.StandardType.D4Rank CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.D4YB

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_singular_coordinate_mod (hQ3 : Nat.card K % 3 = 2) :
    Nat.card {v : Fin (2 * 4) → K // coordinateQuadPlus 4 K v = 0} % 3 = 1 := by
  have h := card_singular_coordinate_gen (K := K)
  have h3 : Nat.card K ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hQ3]
  have h4 : Nat.card K ^ 4 % 3 = 1 := by rw [Nat.pow_mod, hQ3]
  have h7 : Nat.card K ^ 7 % 3 = 2 := by rw [Nat.pow_mod, hQ3]
  omega

theorem core_odd (hQ3 : Nat.card K % 3 = 2) {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hns : ∀ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g ≠ α)
    {E : Subgroup (Om8 K)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hfix : ∀ e ∈ E, α e = e) (hcard : 9 ≤ Nat.card E) {R : Subgroup (Om8 K)}
    (hR2 : IsPGroup 2 R) (hR : R ≠ ⊥) (hER : E ≤ Subgroup.normalizer (R : Set (Om8 K))) :
    False := by
  have hd := fixDim_two_or_four ggD4TrialityClassInput_holds α hα3 hns E hE hfix
  obtain ⟨Z, hZne, hZs, hZE⟩ := exists_totallySingular R hR2 hR
  haveI : IsMulCommutative E := hE.1
  have hnd : ∀ v : Fin (2 * 4) → K, (∀ w, QuadraticMap.polar (coordinateQuadPlus 4 K) v w = 0) →
      v = 0 := fun v hv =>
    (regular_coordinateQuadPlus 4 K (by norm_num)).1.1 v fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w
  refine hZne (key_lemma (coordinateQuadPlus 4 K) hQ3 (by simp) hnd (card_singular_coordinate_mod hQ3)
    (E := E) ((omLin (K := K)).comp E.subtype) (fun x v => ?_) (fun x => Subtype.ext (hE.2 x x.2))
    hcard (fun x hx => hd x x.2 fun h => hx (Subtype.ext h)) Z (fun x v hv => hZE x (hER x.2) v hv)
    hZs)
  exact omRep_Q (K := K) x v


end Core

section CommCalc

variable {G : Type*} [Group G]

theorem P_mul_pow {T P : G} (h2 : P * P = 1) (h3 : P * T * P = T⁻¹) (k : ℕ) :
    P * T ^ k = (T ^ k)⁻¹ * P := by
  have hP : P⁻¹ = P := inv_eq_of_mul_eq_one_right h2
  have h : P * T * P⁻¹ = T⁻¹ := by rw [hP]; exact h3
  have hk : P * T ^ k * P⁻¹ = (T ^ k)⁻¹ := by
    rw [← conj_pow, h, inv_pow]
  calc P * T ^ k = (P * T ^ k * P⁻¹) * P := by group
    _ = (T ^ k)⁻¹ * P := by rw [hk]

theorem comm_calc {T P f f₀ : G} (hT3 : T ^ 3 = 1) (h2 : P * P = 1) (h3 : P * T * P = T⁻¹)
    (h4 : f * T = T * f) (h5 : f * P = P * f) (h6 : f₀ * T = T * f₀) (h7 : f₀ * P = P * f₀)
    (h8 : f₀ * f = f * f₀) (k m : ℕ) :
    (T ^ k * f₀) * (T ^ m * (P * f)) = T ^ (2 * k) * ((T ^ m * (P * f)) * (T ^ k * f₀)) := by
  have c4 : ∀ n : ℕ, f * T ^ n = T ^ n * f := fun n =>
    ((Commute.pow_right (show Commute f T from h4) n)).eq
  have c6 : ∀ n : ℕ, f₀ * T ^ n = T ^ n * f₀ := fun n =>
    ((Commute.pow_right (show Commute f₀ T from h6) n)).eq
  have hPk := P_mul_pow h2 h3 k
  have hTk : (T ^ k)⁻¹ = T ^ (2 * k) := by
    have : T ^ k * T ^ (2 * k) = 1 := by
      rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hT3, one_pow]
    exact inv_eq_of_mul_eq_one_right this
  have hR : (T ^ m * (P * f)) * (T ^ k * f₀) = T ^ m * T ^ (2 * k) * P * f * f₀ := by
    calc (T ^ m * (P * f)) * (T ^ k * f₀) = T ^ m * P * (f * T ^ k) * f₀ := by simp only [mul_assoc]
      _ = T ^ m * P * (T ^ k * f) * f₀ := by rw [c4]
      _ = T ^ m * (P * T ^ k) * f * f₀ := by simp only [mul_assoc]
      _ = T ^ m * ((T ^ k)⁻¹ * P) * f * f₀ := by rw [hPk]
      _ = T ^ m * T ^ (2 * k) * P * f * f₀ := by rw [hTk]; simp only [mul_assoc]
  have hT4k : T ^ (2 * k) * (T ^ m * T ^ (2 * k)) = T ^ k * T ^ m := by
    have h3k : T ^ (3 * k) = 1 := by rw [pow_mul, hT3, one_pow]
    calc T ^ (2 * k) * (T ^ m * T ^ (2 * k)) = T ^ (2 * k + m + 2 * k) := by
          rw [← pow_add, ← pow_add]; congr 1; ring
      _ = T ^ (k + m) * T ^ (3 * k) := by rw [← pow_add]; congr 1; ring
      _ = T ^ k * T ^ m := by rw [h3k, mul_one, pow_add]
  rw [hR]
  calc (T ^ k * f₀) * (T ^ m * (P * f))
      = T ^ k * (f₀ * T ^ m) * (P * f) := by simp only [mul_assoc]
    _ = T ^ k * (T ^ m * f₀) * (P * f) := by rw [c6]
    _ = T ^ k * T ^ m * (f₀ * P) * f := by simp only [mul_assoc]
    _ = T ^ k * T ^ m * (P * f₀) * f := by rw [h7]
    _ = T ^ k * T ^ m * P * (f₀ * f) := by simp only [mul_assoc]
    _ = T ^ k * T ^ m * P * (f * f₀) := by rw [h8]
    _ = (T ^ k * T ^ m) * P * f * f₀ := by simp only [mul_assoc]
    _ = (T ^ (2 * k) * (T ^ m * T ^ (2 * k))) * P * f * f₀ := by rw [hT4k]
    _ = T ^ (2 * k) * (T ^ m * T ^ (2 * k) * P * f * f₀) := by simp only [mul_assoc]

end CommCalc

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem not_conjAct_of_not_mem_sup {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range) (g : similarityPairs (coordinateQuadPlus 4 K)) :
    conjAct _ g ≠ α := by
  intro hg
  obtain ⟨ι', hι', k, c, hc, hαeq⟩ := exists_inner_mul_theta_pow_mul α
  obtain ⟨g₁, hg₁⟩ := exists_pair_of_mem_inner hι'
  obtain ⟨g₂, hg₂⟩ := exists_pair_of_mem_plusCompl hc
  have hθk : (theta : MulAut (Om8 K)) ^ k = conjAct _ (g₁⁻¹ * g * g₂⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, hg₁, hg, hg₂, hαeq]
    group
  have hθ1 := theta_pow_eq_one_of_eq_conjAct hθk
  rw [hθ1, one_mul] at hαeq
  obtain ⟨σ, rfl | rfl⟩ := hc
  · exact hα (hαeq ▸ Subgroup.mul_mem_sup hι' ⟨σ, rfl⟩)
  · obtain ⟨γ, rfl⟩ := hι'
    obtain ⟨γ', hγ'⟩ := conj_mul_cube (AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 σ) γ
    rw [← hαeq, hα3] at hγ'
    have hρφ : Commute (AutOm.plusRefl (K := K) one_le_four) (AutOm.fieldAutP 4 σ) :=
      AutOm.plusRefl_mul_fieldAutP one_le_four σ
    have hρρ : AutOm.plusRefl (K := K) one_le_four * AutOm.plusRefl one_le_four = 1 :=
      AutOm.plusRefl_mul_self one_le_four
    have hρ3 : (AutOm.plusRefl (K := K) one_le_four) ^ 3 = AutOm.plusRefl one_le_four := by
      rw [pow_succ, sq, hρρ, one_mul]
    have hx3 : (AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 σ) ^ 3 =
        AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 (σ ^ 3) := by
      rw [hρφ.mul_pow, hρ3, map_pow]
    rw [hx3] at hγ'
    have hmem : AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 (σ ^ 3) ∈ Inn (Om8 K) := by
      have : AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 (σ ^ 3) = MulAut.conj γ'⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_right hγ'.symm
      rw [this]
      exact ⟨_, rfl⟩
    have hbot : AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 (σ ^ 3) ∈
        Inn (Om8 K) ⊓ AutOm.plusCompl (K := K) one_le_four :=
      ⟨hmem, ⟨σ ^ 3, Or.inr rfl⟩⟩
    rw [AutOm.inner_inf_plusCompl (K := K) (n := 4) (by norm_num)] at hbot
    have h1 : AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 (σ ^ 3) = 1 := hbot
    have h2 : AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 σ =
        AutOm.fieldAutP 4 (σ⁻¹ ^ 2) := by
      have h3 : AutOm.plusRefl (K := K) one_le_four = (AutOm.fieldAutP 4 (σ ^ 3))⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      rw [h3, ← map_inv, ← map_mul]
      congr 1
      group
    rw [h2] at hαeq
    exact hα (hαeq ▸ Subgroup.mul_mem_sup ⟨γ, rfl⟩ ⟨σ⁻¹ ^ 2, rfl⟩)

theorem commutator_mem_inner_of_mem_sup (hcomm : ∀ σ τ : K ≃+* K, σ * τ = τ * σ)
    {α : MulAut (Om8 K)} (hα : α ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range)
    (γ : MulAut (Om8 K)) : γ * α * γ⁻¹ * α⁻¹ ∈ Inn (Om8 K) := by
  haveI : (Inn (Om8 K)).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set π : MulAut (Om8 K) →* MulAut (Om8 K) ⧸ Inn (Om8 K) := QuotientGroup.mk' (Inn (Om8 K)) with hπ
  have hπ1 : ∀ x ∈ Inn (Om8 K), π x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).2 hx
  obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hιa⟩ := Subgroup.mem_sup_of_normal_left.1 hα
  obtain ⟨ι₂, hι₂, m, c, hc, hγ⟩ := exists_inner_mul_theta_pow_mul γ
  have hπα : π α = π (AutOm.fieldAutP 4 σ) := by
    rw [← hιa, map_mul, hπ1 ι hι, one_mul]
  have hπγ : π γ = π theta ^ m * π c := by
    rw [hγ, map_mul, hπ1 ι₂ hι₂, one_mul, map_mul, map_pow]
  have hcomm1 : Commute (π theta) (π (AutOm.fieldAutP 4 σ)) :=
    (Commute.map (theta_fieldAutP σ : Commute theta (AutOm.fieldAutP 4 σ)) π)
  have hcomm2 : Commute (π c) (π (AutOm.fieldAutP 4 σ)) := by
    obtain ⟨τ, rfl | rfl⟩ := hc
    · refine Commute.map ?_ π
      show AutOm.fieldAutP 4 τ * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * AutOm.fieldAutP 4 τ
      rw [← map_mul, ← map_mul, hcomm τ σ]
    · refine Commute.map ?_ π
      show (AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 τ) * AutOm.fieldAutP 4 σ =
        AutOm.fieldAutP 4 σ * (AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 τ)
      have h1 : AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 σ =
        AutOm.fieldAutP 4 σ * AutOm.plusRefl one_le_four := AutOm.plusRefl_mul_fieldAutP one_le_four σ
      have h2 : AutOm.fieldAutP (K := K) 4 τ * AutOm.fieldAutP 4 σ =
        AutOm.fieldAutP 4 σ * AutOm.fieldAutP 4 τ := by
        rw [← map_mul, ← map_mul, hcomm τ σ]
      rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hcomm3 : Commute (π γ) (π α) := by
    rw [hπγ, hπα]
    exact ((hcomm1.symm.pow_right m).symm).mul_left hcomm2
  rw [← QuotientGroup.eq_one_iff (N := Inn (Om8 K))]
  change π (γ * α * γ⁻¹ * α⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm3.eq]
  group

theorem two_subgroup_le_inner (hGal : Odd (Nat.card (K ≃+* K)))
    (hcomm : ∀ σ τ : K ≃+* K, σ * τ = τ * σ)
    {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range)
    {S : Subgroup (MulAut (Om8 K))} (hS2 : IsPGroup 2 S)
    (hαS : α ∈ Subgroup.normalizer (S : Set (MulAut (Om8 K)))) : S ≤ Inn (Om8 K) := by
  haveI : (Inn (Om8 K)).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : MulAut (Om8 K) →* MulAut (Om8 K) ⧸ Inn (Om8 K) := QuotientGroup.mk' (Inn (Om8 K)) with hπ
  have hπ1 : ∀ x ∈ Inn (Om8 K), π x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).2 hx
  have hπ1' : ∀ x, π x = 1 → x ∈ Inn (Om8 K) := fun x hx => (QuotientGroup.eq_one_iff x).1 hx
  have hns := not_conjAct_of_not_mem_sup hα3 hα
  obtain ⟨γ, k, σ₀, hk, hαeq⟩ := exists_conj_theta_pow_fieldAutP α hα3 hns
  have hθ1 : (theta : MulAut (Om8 K)) ≠ 1 := fun h => conjAct_ne_theta (K := K) 1 (by rw [map_one, h])
  have hθord : orderOf (theta : MulAut (Om8 K)) = 3 := orderOf_eq_prime theta_cube hθ1
  have hθdvd : ∀ n : ℕ, (theta : MulAut (Om8 K)) ^ n = 1 → 3 ∣ n := fun n h =>
    hθord ▸ orderOf_dvd_of_pow_eq_one h
  have hρρ : AutOm.plusRefl (K := K) one_le_four * AutOm.plusRefl one_le_four = 1 :=
    AutOm.plusRefl_mul_self one_le_four
  intro t ht
  obtain ⟨e, he⟩ := hS2 ⟨t, ht⟩
  have hte : t ^ 2 ^ e = 1 := congrArg Subtype.val he
  obtain ⟨ι, hι, m, c, hc, htm⟩ := exists_inner_mul_theta_pow_mul t
  obtain ⟨τ, rfl | rfl⟩ := hc
  ·
    obtain ⟨δ, rfl⟩ := hι
    set N : ℕ := 2 ^ e with hN
    have hNd : ¬ 3 ∣ N := by
      intro h
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    have hcθ : Commute ((theta : MulAut (Om8 K)) ^ m) (AutOm.fieldAutP 4 τ) :=
      Commute.pow_left (theta_fieldAutP τ : Commute theta (AutOm.fieldAutP 4 τ)) m
    have hπt : π (MulAut.conj δ * (theta ^ m * AutOm.fieldAutP 4 τ)) =
        π (theta ^ m * AutOm.fieldAutP 4 τ) := by
      rw [map_mul, hπ1 _ ⟨δ, rfl⟩, one_mul]
    have hpow : (theta ^ m * AutOm.fieldAutP 4 τ : MulAut (Om8 K)) ^ N =
        theta ^ (m * N) * AutOm.fieldAutP 4 (τ ^ N) := by
      rw [hcθ.mul_pow, ← pow_mul, map_pow]
    have h1 : theta ^ (m * N) * AutOm.fieldAutP 4 (τ ^ N) ∈ Inn (Om8 K) := by
      rw [← hpow]
      apply hπ1'
      rw [map_pow, ← hπt, ← map_pow, ← htm, hte, map_one]
    obtain ⟨h2, h3⟩ := theta_pow_mul_mem_inner (m * N) ⟨τ ^ N, Or.inl rfl⟩ h1
    have h3m : 3 ∣ m := by
      have := hθdvd _ h2
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h | h
      · exact h
      · exact absurd h hNd
    have hθm : (theta : MulAut (Om8 K)) ^ m = 1 := by
      obtain ⟨r, rfl⟩ := h3m
      rw [pow_mul, theta_cube, one_pow]
    have hφ1 : AutOm.fieldAutP (K := K) 4 τ = 1 := by
      have hdN : orderOf (AutOm.fieldAutP (K := K) 4 τ) ∣ N := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow]; exact h3
      have hdg : orderOf (AutOm.fieldAutP (K := K) 4 τ) ∣ Nat.card (K ≃+* K) :=
        (orderOf_map_dvd _ τ).trans (orderOf_dvd_natCard τ)
      have hcop : Nat.Coprime N (Nat.card (K ≃+* K)) :=
        Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hGal)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdN hdg)
    rw [htm, hθm, hφ1, one_mul, mul_one]
    exact ⟨δ, rfl⟩
  ·
    exfalso
    obtain ⟨δ, rfl⟩ := hι
    have hcc := comm_calc (G := MulAut (Om8 K)) (T := theta) (P := AutOm.plusRefl one_le_four)
      (f := AutOm.fieldAutP 4 τ) (f₀ := AutOm.fieldAutP 4 σ₀) theta_cube hρρ
      plusRefl_theta_plusRefl (theta_fieldAutP τ).symm
      (AutOm.plusRefl_mul_fieldAutP one_le_four τ).symm (theta_fieldAutP σ₀).symm
      (AutOm.plusRefl_mul_fieldAutP one_le_four σ₀).symm
      (by rw [← map_mul, ← map_mul, hcomm σ₀ τ]) k m
    set A : MulAut (Om8 K) := theta ^ k * AutOm.fieldAutP 4 σ₀ with hA
    set Tt : MulAut (Om8 K) := theta ^ m * (AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 τ)
      with hTt
    have hπα : π α = π A := by
      rw [hαeq, map_mul, hπ1 _ ⟨γ, rfl⟩, one_mul]
    have hπt : π t = π Tt := by
      rw [htm, map_mul, hπ1 _ ⟨δ, rfl⟩, one_mul]
    set u : MulAut (Om8 K) := α * t * α⁻¹ * t⁻¹ with hu
    have huS : u ∈ S := by
      have h1 := (Subgroup.mem_normalizer_iff.1 hαS t).1 ht
      exact S.mul_mem h1 (S.inv_mem ht)
    have hπu : π u = π (theta ^ (2 * k)) := by
      have h := congrArg π hcc
      rw [map_mul π A Tt, map_mul π (theta ^ (2 * k)) (Tt * A), map_mul π Tt A] at h
      rw [hu, map_mul π _ (t⁻¹), map_mul π _ (α⁻¹), map_mul π α t, map_inv π α, map_inv π t,
        hπα, hπt]
      rw [h]
      group
    obtain ⟨e', he'⟩ := hS2 ⟨u, huS⟩
    have hue : u ^ 2 ^ e' = 1 := congrArg Subtype.val he'
    have h1 : (theta : MulAut (Om8 K)) ^ (2 * k * 2 ^ e') ∈ Inn (Om8 K) := by
      apply hπ1'
      rw [pow_mul, map_pow, ← hπu, ← map_pow, hue, map_one]
    have h2 := (theta_pow_mul_mem_inner (K := K) (2 * k * 2 ^ e') (c := 1)
      (AutOm.plusCompl (K := K) one_le_four).one_mem (by rw [mul_one]; exact h1)).1
    have h3 := hθdvd _ h2
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h' | h'
      · omega
      · rcases hk with rfl | rfl <;> omega
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega

omit [Finite K] in
theorem conj_injective_om8' : Function.Injective (MulAut.conj : Om8 K →* MulAut (Om8 K)) :=
  CFSG.StandardType.NbrGraphD4.conj_injective

theorem card_inf_inner_le_three (hQ3 : Nat.card K % 3 = 2) (hGal : Odd (Nat.card (K ≃+* K)))
    (hcomm : ∀ σ τ : K ≃+* K, σ * τ = τ * σ)
    {A : Subgroup (MulAut (Om8 K))} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    {α : MulAut (Om8 K)} (hαA : α ∈ A)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range)
    {S : Subgroup (MulAut (Om8 K))} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hAS : A ≤ Subgroup.normalizer (S : Set (MulAut (Om8 K)))) :
    Nat.card ↥(A ⊓ Inn (Om8 K)) ≤ 3 := by
  classical
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have hns := not_conjAct_of_not_mem_sup hα3 hα
  have hSi : S ≤ Inn (Om8 K) := two_subgroup_le_inner hGal hcomm hα3 hα hS2 (hAS hαA)
  have hcomm' : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set E : Subgroup (Om8 K) := A.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)) with hEdef
  have hE : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun u v => Subtype.ext (conj_injective_om8' ?_)⟩⟩, fun γ hγ => conj_injective_om8' ?_⟩
    · change MulAut.conj ((u : Om8 K) * v) = MulAut.conj ((v : Om8 K) * u)
      rw [map_mul, map_mul]
      exact hcomm' _ u.2 _ v.2
    · rw [map_pow, map_one]
      exact hA.2 _ hγ
  have hfix : ∀ γ ∈ E, α γ = γ := by
    intro γ hγ
    apply conj_injective_om8'
    have h2 := hcomm' α hαA _ hγ
    rw [D4Rank.mulAut_mul_conj α γ] at h2
    exact mul_right_cancel h2
  have hmap : E.map MulAut.conj = A ⊓ Inn (Om8 K) := by
    ext a
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hγ, γ, rfl⟩
    · rintro ⟨haA, γ, rfl⟩
      exact ⟨γ, haA, rfl⟩
  have hEcard : Nat.card E = Nat.card ↥(A ⊓ Inn (Om8 K)) := by
    rw [← hmap, Subgroup.card_map_of_injective conj_injective_om8']
  set R : Subgroup (Om8 K) := S.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)) with hRdef
  have hR2 : IsPGroup 2 R := hS2.comap_of_injective _ conj_injective_om8'
  have hR : R ≠ ⊥ := by
    intro hbot
    apply hS1
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨γ, rfl⟩ := hSi hs
    have hγ : γ ∈ R := hs
    rw [hbot, Subgroup.mem_bot] at hγ
    rw [hγ, map_one]
    exact Subgroup.one_mem _
  have hER : E ≤ Subgroup.normalizer (R : Set (Om8 K)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have h := Subgroup.mem_normalizer_iff.1 (hAS he) (MulAut.conj r)
    simp only [hRdef, Subgroup.mem_comap, map_mul, map_inv]
    exact h
  by_contra hgt
  have hEgt : 3 < Nat.card E := by rw [hEcard]; omega
  have hEp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hEp.exists_card_eq
  have h9 : 9 ≤ Nat.card E := by
    rw [hj] at hEgt ⊢
    rcases j with _ | _ | j
    · omega
    · omega
    · calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact core_odd hQ3 hα3 hns hE hfix h9 hR2 hR hER

end Aut


end CFSG.LocalAnalysis.GLTheoremA.D4YF
