module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510E

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_ge_four {A : Subgroup G} (hAsq : ∀ a ∈ A, a * a = 1)
    (hA8 : Nat.card A = 8) {v : G} (hv2 : v * v = 1) (hvA : ∀ a ∈ A, v * a * v⁻¹ ∈ A) :
    4 ≤ Nat.card ↥(A ⊓ centralizer ({v} : Set G)) := by
  classical
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hAsq ha hb
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  generalize hC : A ⊓ centralizer ({v} : Set G) = C
  let φ : ↥A →* ↥A :=
    { toFun := fun a => ⟨a * (v * a * v⁻¹), mul_mem a.2 (hvA a a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (a : G) * b * (v * ((a : G) * b) * v⁻¹) =
          (a : G) * (v * a * v⁻¹) * ((b : G) * (v * b * v⁻¹))
        calc (a : G) * b * (v * ((a : G) * b) * v⁻¹) =
            a * (b * (v * a * v⁻¹)) * (v * b * v⁻¹) := by group
          _ = a * ((v * a * v⁻¹) * b) * (v * b * v⁻¹) := by rw [hAc b b.2 _ (hvA a a.2)]
          _ = (a : G) * (v * a * v⁻¹) * ((b : G) * (v * b * v⁻¹)) := by group) }
  have hφ : ∀ a : ↥A, ((φ a : ↥A) : G) = a * (v * a * v⁻¹) := fun a => rfl
  have hCA : ∀ x ∈ C, x ∈ A := fun x hx => (mem_inf.mp (hC ▸ hx)).1
  have hmemC : ∀ x, x ∈ A → v * x = x * v → x ∈ C := fun x hxA hxv => by
    rw [← hC]
    exact mem_inf.mpr ⟨hxA, mem_centralizer_singleton_iff.mpr hxv.symm⟩
  have hcardC : ∀ K : Subgroup ↥A, (∀ a ∈ K, (a : G) ∈ C) → Nat.card K ≤ Nat.card C := by
    intro K hK
    refine Nat.card_le_card_of_injective (fun a : K => (⟨((a : A) : G), hK a a.2⟩ : C)) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun c : C => (c : G)) hab))
  have hker : ∀ a ∈ φ.ker, (a : G) ∈ C := by
    intro a ha
    have h1 : ((φ a : ↥A) : G) = 1 := by rw [MonoidHom.mem_ker.mp ha]; rfl
    rw [hφ] at h1
    refine hmemC _ a.2 ?_
    have h2 : v * a * v⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [inv_eq_of_mul_eq_one_right (hAsq a a.2)] at h2
    calc v * (a : G) = v * a * v⁻¹ * v := by group
      _ = a * v := by rw [h2]
  have hrange : ∀ a ∈ φ.range, (a : G) ∈ C := by
    rintro _ ⟨a, rfl⟩
    refine hmemC _ (φ a).2 ?_
    rw [hφ]
    have h1 : v * (v * a * v⁻¹) * v⁻¹ = (a : G) := by
      rw [hvi]
      calc v * (v * a * v) * v = (v * v) * a * (v * v) := by group
        _ = a := by rw [hv2, one_mul, mul_one]
    calc v * ((a : G) * (v * a * v⁻¹)) = (v * a * v⁻¹) * (v * (v * a * v⁻¹) * v⁻¹) * v := by
          group
      _ = (v * a * v⁻¹) * a * v := by rw [h1]
      _ = a * (v * a * v⁻¹) * v := by rw [hAc _ (hvA a a.2) a a.2]
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card ↥A ≤ Nat.card C * Nat.card C := by
    rw [← h1]
    exact Nat.mul_le_mul (hcardC _ hker) (hcardC _ hrange)
  rw [hA8] at h2
  have hCleA : C ≤ A := fun x hx => hCA x hx
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hCleA
  rw [hA8] at hk
  have hC8 : Nat.card C ≤ 8 := by
    have := card_le_of_le hCleA
    omega
  interval_cases h3 : Nat.card C <;> omega

theorem exists_mem_not_mem_of_lt' {T V X : Subgroup G} (hT : IsPGroup 2 T) (hVX : V < X)
    (hXT : X ≤ T) (hTV : T ≤ normalizer (V : Set G)) (hTX : T ≤ normalizer (X : Set G)) :
    ∃ x ∈ X, x ∉ V ∧ ∀ g ∈ T, g * x * g⁻¹ * x⁻¹ ∈ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V' := V.subgroupOf T with hV'
  have hV'n : V'.Normal := ⟨fun a ha g => by
    rw [mem_subgroupOf] at ha ⊢
    exact (mem_normalizer_iff.mp (hTV g.2) a).mp ha⟩
  set X' := (X.subgroupOf T).map (QuotientGroup.mk' V') with hX'
  have hX'n : X'.Normal := by
    have : (X.subgroupOf T).Normal := ⟨fun a ha g => by
      rw [mem_subgroupOf] at ha ⊢
      exact (mem_normalizer_iff.mp (hTX g.2) a).mp ha⟩
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective V')
  have hQ : IsPGroup 2 (T ⧸ V') := hT.to_quotient V'
  obtain ⟨x₀, hx₀X, hx₀V⟩ := IsConcreteLE.exists_of_lt hVX
  have hX'ne : X' ≠ ⊥ := by
    intro h1
    have h2 : QuotientGroup.mk' V' (⟨x₀, hXT hx₀X⟩ : T) ∈ X' :=
      mem_map_of_mem _ (mem_subgroupOf.mpr hx₀X)
    rw [h1, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
    exact hx₀V h2
  obtain ⟨u, huX, hu2, huZ⟩ := exists_involution_center (hQ.to_subgroup ⊤) le_top
    (by rw [normalizer_eq_top_iff.mpr hX'n]) hX'ne
  obtain ⟨⟨x, hxT⟩, hxX, rfl⟩ := mem_map.mp huX
  refine ⟨x, mem_subgroupOf.mp hxX, fun h1 => ?_, fun g hg => ?_⟩
  · have h2 : QuotientGroup.mk' V' (⟨x, hxT⟩ : T) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact h1
    rw [h2, orderOf_one] at hu2
    omega
  · have h1 := huZ (QuotientGroup.mk' V' ⟨g, hg⟩) (mem_top _)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 := mem_subgroupOf.mp h1
    simp only [coe_mul, coe_inv, mul_inv_rev] at h2
    have h3 := (mem_normalizer_iff.mp (hTV hg) _).mp (inv_mem h2)
    have h4 := (mem_normalizer_iff.mp (hTV hxT) _).mp h3
    convert h4 using 1
    group

theorem exists_normal_e8_ge {T A V : Subgroup G} (hT : IsPGroup 2 T) (hAT : A ≤ T)
    (hTA : T ≤ normalizer (A : Set G)) (hAsq : ∀ a ∈ A, a * a = 1) (hA8 : Nat.card A = 8)
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G)) (hVsq : ∀ v ∈ V, v * v = 1)
    (hV4 : Nat.card V = 4) :
    ∃ E : Subgroup G, V ≤ E ∧ E ≤ T ∧ T ≤ normalizer (E : Set G) ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hVA : V ≤ A
  · exact ⟨A, hVA, hAT, hTA, hAsq, hA8⟩
  have hVne : V ≠ ⊥ := fun h1 => by rw [h1, card_bot] at hV4; omega
  obtain ⟨u, huV, hu2, huZ⟩ := exists_involution_center hT hVT hTV hVne
  have hu1 : u ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hu2; omega
  obtain ⟨v, hvV, hv1, huv⟩ : ∃ v ∈ V, v ≠ 1 ∧ u ≠ v := by
    by_contra hno
    push Not at hno
    have h1 := SmallLocal.card_le_of_forall_mem_finset ({1, u} : Finset G) fun w hw => by
      by_cases hw1 : w = 1
      · rw [hw1]
        exact Finset.mem_insert_self _ _
      · rw [← hno w hw hw1]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h2 : ({1, u} : Finset G).card ≤ 2 := Finset.card_le_two
    omega
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hVsq ha hb
  set C := A ⊓ centralizer (V : Set G) with hCdef
  have hCv : A ⊓ centralizer ({v} : Set G) ≤ C := by
    intro x hx
    refine mem_inf.mpr ⟨(mem_inf.mp hx).1, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hxv := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    have hxu : x * u = u * x := huZ x (hAT (mem_inf.mp hx).1)
    rcases eq_of_mem_four hV4 hVsq huV hvV hu1 hv1 huv hw with rfl | rfl | rfl | rfl
    · rw [mul_assoc, ← hxv, ← mul_assoc, ← hxu, mul_assoc]
    · exact hxu.symm
    · exact hxv.symm
    · rw [one_mul, mul_one]
  have hC4 : 4 ≤ Nat.card C := (card_centralizer_ge_four hAsq hA8 (hVsq v hvV)
    fun a ha => (mem_normalizer_iff.mp (hTA (hVT hvV)) a).mp ha).trans (card_le_of_le hCv)
  obtain ⟨d, hdC, hdV⟩ : ∃ d ∈ C, d ∉ V := by
    by_contra hno
    push Not at hno
    have h1 : C = V := eq_of_le_of_card_ge (fun x hx => hno x hx) (by rw [hV4]; exact hC4)
    exact hVA (h1 ▸ inf_le_left)
  have hCc : ∀ a ∈ C, ∀ w ∈ V, a * w = w * a := fun a ha w hw =>
    (mem_centralizer_iff.mp (mem_inf.mp ha).2 w hw).symm
  have hCsq : ∀ a ∈ C, a * a = 1 := fun a ha => hAsq a (mem_inf.mp ha).1
  set X := C ⊔ V with hXdef
  have hXT : X ≤ T := sup_le (inf_le_left.trans hAT) hVT
  have hTC : T ≤ normalizer (C : Set G) := le_normalizer_of_conj_mem fun g hg a ha =>
    mem_inf.mpr ⟨(mem_normalizer_iff.mp (hTA hg) a).mp (mem_inf.mp ha).1,
      mem_centralizer_iff.mpr fun w hw => by
        have h1 := hCc a ha _ ((mem_normalizer_iff.mp (hTV (inv_mem hg)) w).mp hw)
        rw [inv_inv] at h1
        calc w * (g * a * g⁻¹) = g * ((g⁻¹ * w * g) * a) * g⁻¹ := by group
          _ = g * (a * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
          _ = g * a * g⁻¹ * w := by group⟩
  have hTX : T ≤ normalizer (X : Set G) := le_normalizer_of_conj_mem fun g hg y hy => by
    obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_sup_commute hCc hy
    rw [show g * (a * w) * g⁻¹ = (g * a * g⁻¹) * (g * w * g⁻¹) by group]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hTC hg) a).mp ha))
      (mem_sup_right ((mem_normalizer_iff.mp (hTV hg) w).mp hw))
  have hVX : V < X := lt_of_le_of_ne le_sup_right fun h1 =>
    hdV (h1 ▸ (mem_sup_left hdC : d ∈ X))
  obtain ⟨x, hxX, hxV, hxT⟩ := exists_mem_not_mem_of_lt' hT hVX hXT hTV hTX
  have hXsq : ∀ y ∈ X, y * y = 1 := fun y hy => sq_eq_one_of_mem_sup hCsq hVsq hCc hy
  have hx2 := hXsq x hxX
  have hxVc : ∀ w ∈ V, w * x = x * w := by
    intro w hw
    obtain ⟨a, ha, w', hw', rfl⟩ := exists_mul_of_mem_sup_commute hCc hxX
    rw [← mul_assoc, ← hCc a ha w hw, mul_assoc, hVc w hw w' hw', mul_assoc]
  have hcz : ∀ w ∈ V, ∀ y ∈ zpowers x, w * y = y * w := by
    intro w hw y hy
    rcases eq_one_or_eq_of_mem_zpowers_sq hx2 hy with rfl | rfl
    · rw [mul_one, one_mul]
    · exact hxVc w hw
  have hdisj : V ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases eq_one_or_eq_of_mem_zpowers_sq hx2 (mem_inf.mp hy).2 with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.mp hy).1 hxV
  have hx1 : x ≠ 1 := fun h1 => hxV (h1 ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  refine ⟨V ⊔ zpowers x, le_sup_left, sup_le hVT (zpowers_le.mpr (hXT hxX)), ?_, ?_, ?_⟩
  · refine le_normalizer_of_conj_mem fun g hg y hy => ?_
    obtain ⟨w, hw, y', hy', rfl⟩ := exists_mul_of_mem_sup_commute hcz hy
    rw [show g * (w * y') * g⁻¹ = (g * w * g⁻¹) * (g * y' * g⁻¹) by group]
    refine mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hTV hg) w).mp hw)) ?_
    rcases eq_one_or_eq_of_mem_zpowers_sq hx2 hy' with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [show g * y' * g⁻¹ = (g * y' * g⁻¹ * y'⁻¹) * y' by group]
      exact mul_mem (mem_sup_left (hxT g hg)) (mem_sup_right (mem_zpowers _))
  · exact fun y hy => sq_eq_one_of_mem_sup hVsq (fun y hy => by
      rcases eq_one_or_eq_of_mem_zpowers_sq hx2 hy with rfl | rfl
      · exact one_mul 1
      · exact hx2) hcz hy
  · rw [card_sup_eq_mul_of_disjoint_of_le_normalizer V (zpowers x)
      (le_normalizer_of_commute hcz) (disjoint_iff.mpr hdisj), hV4, Nat.card_zpowers, hxo]

end CFSG.ComponentClassification.Foote5
