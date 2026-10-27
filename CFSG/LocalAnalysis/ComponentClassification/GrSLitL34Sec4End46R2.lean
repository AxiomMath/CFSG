module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46R
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem card_filter_pow_two_pow_le' {B : Type*} [Group B] [Fintype B] [DecidableEq B]
    (hcomm : ∀ a b : B, a * b = b * a)
    (h1 : (Finset.univ.filter fun x : B => x ^ 2 = 1).card ≤ 2) (j : ℕ) :
    (Finset.univ.filter fun x : B => x ^ 2 ^ j = 1).card ≤ 2 ^ j := by
  induction j with
  | zero =>
    rw [pow_zero]
    refine le_of_eq ?_
    rw [Finset.card_eq_one]
    exact ⟨1, by ext x; simp⟩
  | succ j ih =>
    set T := Finset.univ.filter fun x : B => x ^ 2 ^ (j + 1) = 1
    have himg : T.image (fun x => x ^ 2) ⊆ Finset.univ.filter fun x : B => x ^ 2 ^ j = 1 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← pow_mul, ← pow_succ']
      exact hx
    have hfib : ∀ y ∈ T.image (fun x => x ^ 2), (T.filter fun x => x ^ 2 = y).card ≤ 2 := by
      intro y hy
      obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hy
      refine le_trans ?_ h1
      refine Finset.card_le_card_of_injOn (fun x => x * x₀⁻¹) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx ⊢
        rw [Commute.mul_pow (hcomm x x₀⁻¹), hx.2, inv_pow, mul_inv_cancel]
      · intro x _ y _ hxy
        simpa using hxy
    calc T.card ≤ 2 * (T.image fun x => x ^ 2).card := Finset.card_le_mul_card_image T 2 hfib
      _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 ((Finset.card_le_card himg).trans ih)
      _ = 2 ^ (j + 1) := by rw [pow_succ, mul_comm]

theorem isCyclic_of_card_sq_eq_one_le' {B : Type*} [Group B] [Finite B] (hB : IsPGroup 2 B)
    (hcomm : ∀ a b : B, a * b = b * a) (h1 : Nat.card {x : B // x ^ 2 = 1} ≤ 2) :
    IsCyclic B := by
  classical
  have : Fintype B := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
  refine isCyclic_of_card_pow_eq_one_le fun n hn => ?_
  have hsub : (Finset.univ.filter fun x : B => x ^ n = 1) ⊆
      Finset.univ.filter fun x : B => x ^ 2 ^ n.factorization 2 = 1 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨k, hk⟩ := hB x
    have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hn' : 2 ^ i ∣ n := hi ▸ orderOf_dvd_of_pow_eq_one hx
    have hle : i ≤ n.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp hn'
    rw [← orderOf_dvd_iff_pow_eq_one, hi]
    exact Nat.pow_dvd_pow 2 hle
  calc (Finset.univ.filter fun x : B => x ^ n = 1).card
      ≤ (Finset.univ.filter fun x : B => x ^ 2 ^ n.factorization 2 = 1).card :=
        Finset.card_le_card hsub
    _ ≤ 2 ^ n.factorization 2 := card_filter_pow_two_pow_le' hcomm h1 _
    _ ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n 2)

theorem exists_two_involutions_of_not_isCyclic [Finite G] {Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hnc : ¬ IsCyclic Z) :
    ∃ a₁ ∈ Z, ∃ a₂ ∈ Z, a₁ * a₁ = 1 ∧ a₂ * a₂ = 1 ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₁ ≠ a₂ := by
  classical
  by_contra hno
  push Not at hno
  apply hnc
  refine isCyclic_of_card_sq_eq_one_le' hZ (fun x y => Subtype.ext (hcomm _ x.2 _ y.2)) ?_
  calc Nat.card {x : Z // x ^ 2 = 1} ≤ Nat.card Bool := by
        refine Nat.card_le_card_of_injective (fun x => decide ((x : Z) = 1)) ?_
        intro x y hxy
        by_cases hx : (x : Z) = 1
        · have hy : (y : Z) = 1 := by
            by_contra hy
            simp [hx, hy] at hxy
          exact Subtype.ext (hx.trans hy.symm)
        · have hy : (y : Z) ≠ 1 := by
            intro hy
            simp [hx, hy] at hxy
          have hx2 := x.2
          have hy2 := y.2
          rw [pow_two] at hx2 hy2
          exact Subtype.ext (Subtype.ext (hno x (x : Z).2 y (y : Z).2 (congrArg Subtype.val hx2)
            (congrArg Subtype.val hy2) (fun h => hx (Subtype.ext h))
            (fun h => hy (Subtype.ext h))))
    _ = 2 := by simp

theorem exists_eight_of_sq_mem [Finite G] (hSqC : L34SquareCenterFact) {J S : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hS2 : IsPGroup 2 S)
    (hP : IsSylowTwoIn (S ⊓ J) J) {a₁ a₂ : G} (ha₁ : a₁ ∈ S ⊓ zStarIn J)
    (ha₂ : a₂ ∈ S ⊓ zStarIn J) (ha₁₁ : a₁ * a₁ = 1) (ha₂₂ : a₂ * a₂ = 1) (ha₁1 : a₁ ≠ 1)
    (ha₂1 : a₂ ≠ 1) (ha₁₂ : a₁ ≠ a₂) {u : G} (hu : u ∈ S ⊓ J) (huZ : u ∉ zStarIn J)
    (hu2 : u * u ∈ zStarIn J) :
    ∃ E : Subgroup G, E ≤ S ⊓ J ⊓ centralizer ({u} : Set G) ∧ IsElemTwo E ∧ Nat.card E = 2 ^ 3 := by
  have hZK : ∀ {z : G}, z ∈ zStarIn J → z ∈ coreActionKernel J := fun hz => by
    have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    rw [h] at hz
    exact (mem_inf.mp hz).2
  have hZJ : ∀ {z : G}, z ∈ zStarIn J → z ∈ J := fun hz => map_subtype_le _ hz
  have hcZ : ∀ z ∈ S ⊓ zStarIn J, ∀ p ∈ S ⊓ J, z * p = p * z := fun z hz p hp =>
    mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hz).1 (hZK (mem_inf.mp hz).2)
      (mem_inf.mp hp).1 (mem_inf.mp hp).2
  have hZP : ∀ {z : G}, z ∈ S ⊓ zStarIn J → z ∈ S ⊓ J := fun hz =>
    mem_inf.mpr ⟨(mem_inf.mp hz).1, hZJ (mem_inf.mp hz).2⟩
  obtain ⟨z, hz, hzu⟩ := hSqC G J (S ⊓ J) hJ hL hP u hu hu2
  have hz' : z ∈ S ⊓ zStarIn J := mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hz).1).1, (mem_inf.mp hz).2⟩
  have hzu' : z * u = u * z := hcZ z hz' u hu
  set y : G := u * z⁻¹ with hy
  have hyP : y ∈ S ⊓ J := mul_mem hu (inv_mem (hZP hz'))
  have hyy : y * y = 1 := by
    have hzi : z⁻¹ * u = u * z⁻¹ := by
      calc z⁻¹ * u = z⁻¹ * (u * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * u) * z⁻¹ := by rw [hzu']
        _ = u * z⁻¹ := by group
    calc y * y = u * (z⁻¹ * u) * z⁻¹ := by rw [hy]; group
      _ = u * u * (z * z)⁻¹ := by rw [hzi]; group
      _ = 1 := by rw [hzu, mul_inv_cancel]
  have hyZ : y ∉ S ⊓ zStarIn J := fun h => huZ (by
    rw [show u = y * z by rw [hy]; group]
    exact mul_mem (mem_inf.mp h).2 (mem_inf.mp hz').2)
  have hyu : y * u = u * y := by
    rw [hy]
    calc u * z⁻¹ * u = u * (z⁻¹ * u) := by group
      _ = u * (u * z⁻¹) := by
        congr 1
        calc z⁻¹ * u = z⁻¹ * (u * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * u) * z⁻¹ := by rw [hzu']
          _ = u * z⁻¹ := by group
  have hE₁ : IsElemTwo (zpowers a₁) := isElemTwo_zpowers ha₁₁
  have hc₁ : Nat.card ↥(zpowers a₁) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha₁₁) ha₁1
  have hZab : ∀ x ∈ S ⊓ zStarIn J, ∀ w ∈ S ⊓ zStarIn J, x * w = w * x := fun x hx w hw =>
    hcZ x hx w (hZP hw)
  have hE₂le : zpowers a₁ ⊔ zpowers a₂ ≤ S ⊓ zStarIn J :=
    sup_le (zpowers_le.mpr ha₁) (zpowers_le.mpr ha₂)
  obtain ⟨hE₂, hc₂⟩ := isElemTwo_sup_zpowers hE₁ ha₂₂ (fun h => by
    rcases eq_one_or_eq_of_mem_zpowers ha₁₁ h with h1 | h1
    · exact ha₂1 h1
    · exact ha₁₂ h1.symm) (fun e he => hZab e (zpowers_le.mpr ha₁ he) a₂ ha₂)
  obtain ⟨hE₃, hc₃⟩ := isElemTwo_sup_zpowers hE₂ hyy (fun h => hyZ (hE₂le h))
    (fun e he => hcZ e (hE₂le he) y hyP)
  refine ⟨zpowers a₁ ⊔ zpowers a₂ ⊔ zpowers y, ?_, hE₃, by rw [hc₃, hc₂, hc₁]; norm_num⟩
  refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
  · have heZ := hE₂le he
    exact mem_inf.mpr ⟨hZP heZ, mem_centralizer_singleton_iff.mpr (hcZ e heZ u hu)⟩
  · exact mem_inf.mpr ⟨hyP, mem_centralizer_singleton_iff.mpr hyu⟩

theorem exists_eight_le_of_l34 [Finite G] {J P : Subgroup G}
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemTwo E ∧ 8 ≤ Nat.card E := by
  obtain ⟨F, hFJ, hF, hF8⟩ := exists_isElemTwo_of_three_le_pRank (GrS5.three_le_pRank_of_l34 hL)
  obtain ⟨h, -, hh⟩ := exists_conj_mem_of_isSylowTwoIn hP hFJ hF.isPGroup
  refine ⟨F.map (MulAut.conj h⁻¹).toMonoidHom, ?_, hF.map_conj h⁻¹, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    simpa [MulAut.conj_apply] using hh f hf
  · rw [card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact hF8

end CFSG.ComponentClassification.GrSLit.GrS4
