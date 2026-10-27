module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413Two

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_ge_mem_normalizer {D P : Subgroup G} (hPD : P ≤ D)
    (hP : IsPGroup 2 P) {y : G} (hy2 : y ^ 2 = 1) (hyD : y ∈ normalizer (D : Set G))
    (hyP : y ∈ normalizer (P : Set G)) :
    ∃ T : Subgroup G, IsSylowOf 2 T D ∧ P ≤ T ∧ y ∈ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXD : D ⊔ zpowers y ≤ normalizer (D : Set G) := sup_le le_normalizer (zpowers_le.mpr hyD)
  have hPy : IsPGroup 2 ↥(P ⊔ zpowers y) :=
    hP.to_sup_of_normal_left' (isPGroup_two_zpowers_of_sq_eq_one hy2) (zpowers_le.mpr hyP)
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge_of_le (sup_le_sup_right hPD _) hPy
  refine ⟨Q ⊓ D, hQ.inf_of_le_normalizer le_sup_left hXD,
    le_inf (le_sup_left.trans hPQ) hPD, ?_⟩
  exact mem_normalizer_inf_of_mem (le_normalizer (hPQ (mem_sup_right (mem_zpowers y)))) hyD

theorem exists_card_eight_le_of_sq_eq_one {V : Subgroup G} (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hV8 : 8 ≤ Nat.card V) :
    ∃ E : Subgroup G, E ≤ V ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 8 := by
  obtain ⟨W, hW, hWV⟩ := exists_isKleinFour_le hV2 (by omega)
  obtain ⟨x, hxV, hxW⟩ : ∃ x ∈ V, x ∉ W := by
    by_contra hall
    push Not at hall
    have h1 := card_le_of_le (fun x hx => hall x hx : V ≤ W)
    rw [hW.card_four] at h1
    omega
  obtain ⟨h2, h8⟩ := sup_zpowers_spec hW hxW (hV2 x hxV)
    fun w hw => commute_of_sq_eq_one hV2 (hWV hw) hxV
  exact ⟨W ⊔ zpowers x, sup_le hWV (zpowers_le.mpr hxV), h2, h8⟩

theorem card_le_two_of_lt_eight {U V : Subgroup G} (hU : IsPGroup 2 U) (hVU : V ≤ U)
    (hU8 : Nat.card U < 8) {t : G} (htU : t ∈ U) (htV : t ∉ V) : Nat.card V ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := card_dvd_of_le hVU
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    have h1 : V = U := eq_of_le_of_card_ge hVU hm.le
    exact htV (by rw [h1]; exact htU)
  have h2 : Nat.card V * 2 ≤ Nat.card U := by
    rw [hm]
    exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨j, hj⟩ := (hU.to_le hVU).exists_card_eq
  rw [hj] at h2 ⊢
  rcases j with _ | _ | j
  · norm_num
  · norm_num
  · have h3 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    rw [pow_succ, pow_succ] at h2
    omega

omit [Finite G] in
theorem mul_conj_mem_inf_centralizer {F : Subgroup G} (hF2 : ∀ x ∈ F, x ^ 2 = 1) {y : G}
    (hy2 : y ^ 2 = 1) (hyF : y ∈ normalizer (F : Set G)) {x : G} (hx : x ∈ F) :
    x * (y * x * y⁻¹) ∈ F ⊓ centralizer ({y} : Set G) := by
  have hyx : y * x * y⁻¹ ∈ F := (mem_normalizer_iff.mp hyF x).mp hx
  refine mem_inf.mpr ⟨mul_mem hx hyx, mem_centralizer_singleton_iff.mpr ?_⟩
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hy2)
  have hc := commute_of_sq_eq_one hF2 hx hyx
  rw [hyi] at hc ⊢
  calc x * (y * x * y) * y = y * x * y * x * y := by rw [hc]
    _ = y * (x * (y * x * y)) := by group

theorem exists_commutator_mem_pair {A K : Subgroup G} (hA2 : ∀ x ∈ A, x ^ 2 = 1) {y t : G}
    (hy2 : y ^ 2 = 1) (hyA : y ∈ normalizer (A : Set G)) (hyK : y ∈ normalizer (K : Set G))
    (htA : t ∈ A) (hyt : y * t = t * y) (hdec : ∀ x ∈ A, x ∈ K ∨ x * t ∈ K)
    (h4 : 4 ≤ Nat.card ↥(A ⊓ K))
    (hfix : Nat.card ↥(A ⊓ K ⊓ centralizer ({y} : Set G)) ≤ 2) :
    ∃ f ∈ A ⊓ K, f ≠ 1 ∧ y * f = f * y ∧
      ∀ x ∈ A, x * (y * x * y⁻¹) = 1 ∨ x * (y * x * y⁻¹) = f := by
  classical
  set F := A ⊓ K with hF
  have hF2 : ∀ x ∈ F, x ^ 2 = 1 := fun x hx => hA2 x (mem_inf.mp hx).1
  have hyF : y ∈ normalizer (F : Set G) := mem_normalizer_inf_of_mem hyA hyK
  have hcF := fun {x : G} (hx : x ∈ F) => mul_conj_mem_inf_centralizer hF2 hy2 hyF hx
  obtain ⟨a, haF, hay⟩ : ∃ a ∈ F, y * a * y⁻¹ ≠ a := by
    by_contra hall
    push Not at hall
    have hle : F ≤ F ⊓ centralizer ({y} : Set G) := fun x hx =>
      mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr (by
        calc x * y = y * x * y⁻¹ * y := by rw [hall x hx]
          _ = y * x := by group)⟩
    have h1 := card_le_of_le hle
    omega
  set f := a * (y * a * y⁻¹) with hf
  have hfV := hcF haF
  have hf1 : f ≠ 1 := by
    intro h1
    apply hay
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hF2 a haF)
    calc y * a * y⁻¹ = a⁻¹ * (a * (y * a * y⁻¹)) := by group
      _ = a := by rw [← hf, h1, mul_one, h2]
  have hpair : ∀ b ∈ F, b * (y * b * y⁻¹) = 1 ∨ b * (y * b * y⁻¹) = f := by
    intro b hb
    by_contra hne
    push Not at hne
    have hsub : ({1, f, b * (y * b * y⁻¹)} : Set G) ⊆
        ((F ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) := by
      intro u hu
      rcases hu with rfl | rfl | rfl
      · exact one_mem _
      · exact hfV
      · exact hcF hb
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_eq_three.mpr ⟨1, f, _, hf1.symm, hne.1.symm, hne.2.symm, rfl⟩,
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h3
    omega
  refine ⟨f, (mem_inf.mp hfV).1, hf1, (mem_centralizer_singleton_iff.mp (mem_inf.mp hfV).2).symm,
    fun x hx => ?_⟩
  rcases hdec x hx with hxK | hxK
  · exact hpair x (mem_inf.mpr ⟨hx, hxK⟩)
  · have hxt : x * t ∈ F := mem_inf.mpr ⟨mul_mem hx htA, hxK⟩
    have hyx : y * x * y⁻¹ ∈ A := (mem_normalizer_iff.mp hyA x).mp hx
    have htt : t * t = 1 := by rw [← sq]; exact hA2 t htA
    have hc : (y * x * y⁻¹) * t = t * (y * x * y⁻¹) := commute_of_sq_eq_one hA2 hyx htA
    have heq : x * t * (y * (x * t) * y⁻¹) = x * (y * x * y⁻¹) := by
      have h1 : y * (x * t) * y⁻¹ = y * x * y⁻¹ * t := by
        calc y * (x * t) * y⁻¹ = y * x * y⁻¹ * (y * t * y⁻¹) := by group
          _ = y * x * y⁻¹ * t := by rw [hyt]; group
      rw [h1]
      calc x * t * (y * x * y⁻¹ * t) = x * (t * (y * x * y⁻¹)) * t := by group
        _ = x * ((y * x * y⁻¹) * t) * t := by rw [hc]
        _ = x * (y * x * y⁻¹) * (t * t) := by group
        _ = x * (y * x * y⁻¹) := by rw [htt, mul_one]
    rw [← heq]
    exact hpair _ hxt

omit [Finite G] in
theorem conj_eq_of_commutator_mem_pair {A K : Subgroup G} (hA2 : ∀ x ∈ A, x ^ 2 = 1) {y f : G}
    (hyK : y ∈ normalizer (K : Set G)) (hfA : f ∈ A) (hfK : f ∉ K) (hyf : y * f = f * y)
    (hdec : ∀ x ∈ A, x ∈ K ∨ x * f ∈ K)
    (hc : ∀ x ∈ A, x * (y * x * y⁻¹) = 1 ∨ x * (y * x * y⁻¹) = f) :
    ∀ x ∈ A, y * x * y⁻¹ = x := by
  have hK : ∀ x ∈ A, x ∈ K → y * x * y⁻¹ = x := by
    intro x hx hxK
    have hyx : y * x * y⁻¹ ∈ K := (mem_normalizer_iff.mp hyK x).mp hxK
    rcases hc x hx with h1 | h1
    · have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA2 x hx)
      calc y * x * y⁻¹ = x⁻¹ * (x * (y * x * y⁻¹)) := by group
        _ = x := by rw [h1, mul_one, h2]
    · exact absurd (h1 ▸ mul_mem hxK hyx) hfK
  intro x hx
  rcases hdec x hx with hxK | hxK
  · exact hK x hx hxK
  · have h1 := hK _ (mul_mem hx hfA) hxK
    have h2 : y * f * y⁻¹ = f := by rw [hyf]; group
    calc y * x * y⁻¹ = y * (x * f) * y⁻¹ * (y * f * y⁻¹)⁻¹ := by group
      _ = x := by rw [h1, h2]; group

end CFSG.ComponentClassification.FooteLit
