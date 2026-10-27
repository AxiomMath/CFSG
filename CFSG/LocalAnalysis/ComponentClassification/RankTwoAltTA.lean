module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

section Perm

variable {n : ℕ} (ι : Fin 4 ↪ Fin n)

theorem exists_pair_not_mem_range (hn : 6 ≤ n) :
    ∃ a b : Fin n, a ∉ Set.range ι ∧ b ∉ Set.range ι ∧ a ≠ b := by
  classical
  have hcard : 1 < (Finset.univ \ Finset.univ.map ι).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_map, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have hout : ∀ x ∈ Finset.univ \ Finset.univ.map ι, x ∉ Set.range ι := by
    rintro x hx ⟨i, rfl⟩
    rw [Finset.mem_sdiff] at hx
    exact hx.2 (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  exact ⟨a, b, hout a ha, hout b hb, hab⟩

theorem commute_swap_viaEmbeddingHom {a b : Fin n} (ha : a ∉ Set.range ι) (hb : b ∉ Set.range ι)
    (k : Perm (Fin 4)) : Commute (swap a b) (viaEmbeddingHom ι k) := by
  apply Disjoint.commute
  intro y
  by_cases hy : y = a ∨ y = b
  · right
    rw [viaEmbeddingHom_apply, viaEmbedding_apply_of_notMem]
    rcases hy with rfl | rfl <;> assumption
  · left
    push Not at hy
    exact swap_apply_of_ne_of_ne hy.1 hy.2

theorem conj_mul_swap {a b : Fin n} (ha : a ∉ Set.range ι) (hb : b ∉ Set.range ι)
    (s k : Perm (Fin 4)) :
    viaEmbeddingHom ι s * swap a b * viaEmbeddingHom ι k * (viaEmbeddingHom ι s * swap a b)⁻¹ =
      viaEmbeddingHom ι (s * k * s⁻¹) := by
  have hc := (commute_swap_viaEmbeddingHom ι ha hb k).eq
  rw [map_mul, map_mul, map_inv]
  calc viaEmbeddingHom ι s * swap a b * viaEmbeddingHom ι k * (viaEmbeddingHom ι s * swap a b)⁻¹
      = viaEmbeddingHom ι s * (swap a b * viaEmbeddingHom ι k) * (swap a b)⁻¹ *
          (viaEmbeddingHom ι s)⁻¹ := by group
    _ = viaEmbeddingHom ι s * (viaEmbeddingHom ι k * swap a b) * (swap a b)⁻¹ *
          (viaEmbeddingHom ι s)⁻¹ := by rw [hc]
    _ = viaEmbeddingHom ι s * viaEmbeddingHom ι k * (viaEmbeddingHom ι s)⁻¹ := by group

theorem mul_swap_mem_alternatingGroup {a b : Fin n} (hab : a ≠ b) {i j : Fin 4} (hij : i ≠ j) :
    viaEmbeddingHom ι (swap i j) * swap a b ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, Perm.sign_mul, sign_viaEmbeddingHom, sign_swap hij, sign_swap hab]
  rfl

end Perm

section TA

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include hc h32 h4 h34

omit h4 h34 in
theorem eq_one_of_conj {t₁ t₂ p₁ p₂ r₁ r₂ x : G} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R) (he₁ : t₁ = p₁ * r₁) (he₂ : t₂ = p₂ * r₂) (hx : x ∈ A)
    (h1 : x * p₁ * x⁻¹ = p₁) (h2 : x * p₂ * x⁻¹ = p₁ * p₂) (ht₁1 : t₁ ≠ 1) : r₁ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxr : ∀ {r : G}, r ∈ R → x * r = r * x := fun hr =>
    mem_centralizer_iff.mp (R_le_centralizer hc hr) x hx
  have htr : ∀ {t r : G}, t ∈ T → r ∈ R → t * r = r * t := fun ht hr =>
    (mem_centralizer_iff.mp (hc.le_centralizer ht) _ hr).symm
  have hxt₁ : x * t₁ = t₁ * x := by
    have hxp : x * p₁ = p₁ * x := by
      calc x * p₁ = x * p₁ * x⁻¹ * x := by group
        _ = p₁ * x := by rw [h1]
    rw [he₁, ← mul_assoc, hxp, mul_assoc, hxr hr₁, mul_assoc]
  have hKt : TightlyEmbedded (rightConjugate (Subgroup.centralizer (A : Set G)) g) :=
    tightlyEmbedded_rightConjugate' (tightlyEmbedded_centralizer_of_standard hc.hyp.standard) g
  have hxN := mem_normalizer_of_commute_of_tightlyEmbedded hKt (hc.sylowT.le ht₁) ht₁1
    ((hc.elemT h32).2 _ ht₁) hxt₁
  have hconj : x * t₂ * x⁻¹ = t₁ * r₁⁻¹ * t₂ := by
    have hp₁' : p₁ = t₁ * r₁⁻¹ := by rw [he₁]; group
    have hp₂' : p₂ = t₂ * r₂⁻¹ := by rw [he₂]; group
    calc x * t₂ * x⁻¹ = x * p₂ * x⁻¹ * (x * r₂) * x⁻¹ := by rw [he₂]; group
      _ = p₁ * p₂ * (r₂ * x) * x⁻¹ := by rw [h2, hxr hr₂]
      _ = t₁ * r₁⁻¹ * t₂ := by rw [hp₁', hp₂']; group
  have heq := hc.sylowT.eq_of_le (le_inf hc.sylowT.le le_sup_right) inf_le_left
    (hc.isPGroup_sup.to_le inf_le_right)
  have hmem : x * t₂ * x⁻¹ ∈ T := by
    rw [← heq]
    refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hxN t₂).mp (hc.sylowT.le ht₂), ?_⟩
    rw [hconj]
    exact mul_mem (mul_mem (le_sup_right (a := R) ht₁) (inv_mem (le_sup_left (b := T) hr₁)))
      (le_sup_right (a := R) ht₂)
  have hrT : r₁⁻¹ ∈ T := by
    have : r₁⁻¹ = t₁⁻¹ * (x * t₂ * x⁻¹) * t₂⁻¹ := by
      rw [hconj]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem ht₁) hmem) (inv_mem ht₂)
  have hbot : r₁⁻¹ ∈ R ⊓ T := Subgroup.mem_inf.mpr ⟨inv_mem hr₁, hrT⟩
  rw [hc.inf_eq_bot, mem_bot, inv_eq_one] at hbot
  exact hbot

variable (h2 : Asc76Theorem2) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
include h2 hOut

theorem le_of_center_eq_bot {n : ℕ} (hn : 7 ≤ n) {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : IsActionHom A (alternatingGroup (Fin n)) ψ) (hZ : center ↥A = ⊥) : T ≤ A := by
  obtain ⟨ι, hι⟩ := exists_eq_kleinFour_map hc h32 h4 h34 h2 hOut hn hψ
  have hinj : ∀ u v : normalizer (A : Set G), (u : G) ∈ A → (v : G) ∈ A → ψ u = ψ v → u = v := by
    intro u v hu hv huv
    have hk : (restrictA hψ).ker = ⊥ := by rw [ker_restrictA, hZ]
    have h := (MonoidHom.ker_eq_bot_iff _).mp hk (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩)
      (Subtype.ext huv)
    have h' : (u : G) = v := congrArg (fun z : ↥A => (z : G)) h
    exact Subtype.ext h'
  have hmemE : ∀ k ∈ kleinFour, ∃ t : normalizer (A : Set G), (t : G) ∈ T ∧
      ψ t = viaEmbeddingHom ι k := by
    intro k hk
    have : viaEmbeddingHom ι k ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := by
      rw [hι]
      exact ⟨k, hk, rfl⟩
    obtain ⟨t, ht, hte⟩ := this
    exact ⟨t, ht, hte⟩
  have hd₁ : (swap 0 1 * swap 2 3 : Perm (Fin 4)) ∈ kleinFour := subset_closure (Set.mem_insert _ _)
  have hd₂ : (swap 0 2 * swap 1 3 : Perm (Fin 4)) ∈ kleinFour :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨t₁, ht₁, hψ₁⟩ := hmemE _ hd₁
  obtain ⟨t₂, ht₂, hψ₂⟩ := hmemE _ hd₂
  have hpart : ∀ t : normalizer (A : Set G), (t : G) ∈ T → ∃ (p : G) (hp : p ∈ A) (r : G),
      r ∈ R ∧ (t : G) = p * r ∧ ψ ⟨p, le_normalizer hp⟩ = ψ t := by
    intro t ht
    obtain ⟨p, hp, r, hr, he⟩ := exists_mul_of_mem_T hc h32 h4 h34 ht
    refine ⟨p, hp, r, hr, he, ?_⟩
    have hrN : r ∈ normalizer (A : Set G) := R_le_normalizer hc hr
    have hr1 : ψ ⟨r, hrN⟩ = 1 := (hψ.eq_one_iff _).mpr (R_le_centralizer hc hr)
    rw [show t = ⟨p, le_normalizer hp⟩ * ⟨r, hrN⟩ from Subtype.ext he, map_mul, hr1, mul_one]
  obtain ⟨p₁, hp₁, r₁, hr₁, he₁, hψp₁⟩ := hpart t₁ ht₁
  obtain ⟨p₂, hp₂, r₂, hr₂, he₂, hψp₂⟩ := hpart t₂ ht₂
  have hne1 : ∀ t : normalizer (A : Set G), ∀ k : Perm (Fin 4), k ≠ 1 →
      ψ t = viaEmbeddingHom ι k → (t : G) ≠ 1 := by
    intro t k hk hte h
    have ht : t = 1 := Subtype.ext h
    rw [ht, map_one] at hte
    exact hk ((viaEmbeddingHom_injective ι) (hte.symm.trans (map_one _).symm))
  have ht₁1 := hne1 t₁ _ (by decide) hψ₁
  have ht₂1 := hne1 t₂ _ (by decide) hψ₂
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_not_mem_range ι (by omega)
  obtain ⟨x₁, hx₁, hψx₁⟩ := hψ.exists_eq _
    (mul_swap_mem_alternatingGroup ι hab (show (0 : Fin 4) ≠ 1 by decide))
  obtain ⟨x₂, hx₂, hψx₂⟩ := hψ.exists_eq _
    (mul_swap_mem_alternatingGroup ι hab (show (0 : Fin 4) ≠ 2 by decide))
  set xN₁ : normalizer (A : Set G) := ⟨x₁, le_normalizer hx₁⟩
  set xN₂ : normalizer (A : Set G) := ⟨x₂, le_normalizer hx₂⟩
  set pN₁ : normalizer (A : Set G) := ⟨p₁, le_normalizer hp₁⟩
  set pN₂ : normalizer (A : Set G) := ⟨p₂, le_normalizer hp₂⟩
  have hmemA : ∀ {u v : G}, u ∈ A → v ∈ A → u * v * u⁻¹ ∈ A := fun hu hv =>
    mul_mem (mul_mem hu hv) (inv_mem hu)
  have c11 : x₁ * p₁ * x₁⁻¹ = p₁ := by
    have h := hinj (xN₁ * pN₁ * xN₁⁻¹) pN₁ (hmemA hx₁ hp₁) hp₁ (by
      rw [map_mul, map_mul, map_inv, hψx₁, hψp₁, hψ₁, conj_mul_swap ι ha hb,
        show (swap 0 1 : Perm (Fin 4)) * (swap 0 1 * swap 2 3) * (swap 0 1)⁻¹ =
          swap 0 1 * swap 2 3 by decide])
    exact congrArg Subtype.val h
  have hprod : ψ (pN₁ * pN₂) = viaEmbeddingHom ι (swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)) := by
    rw [map_mul, hψp₁, hψp₂, hψ₁, hψ₂, ← map_mul]
  have hprod' : ψ (pN₂ * pN₁) = viaEmbeddingHom ι (swap 0 2 * swap 1 3 * (swap 0 1 * swap 2 3)) := by
    rw [map_mul, hψp₁, hψp₂, hψ₁, hψ₂, ← map_mul]
  have c12 : x₁ * p₂ * x₁⁻¹ = p₁ * p₂ := by
    have h := hinj (xN₁ * pN₂ * xN₁⁻¹) (pN₁ * pN₂) (hmemA hx₁ hp₂) (mul_mem hp₁ hp₂) (by
      rw [hprod, map_mul, map_mul, map_inv, hψx₁, hψp₂, hψ₂, conj_mul_swap ι ha hb,
        show (swap 0 1 : Perm (Fin 4)) * (swap 0 2 * swap 1 3) * (swap 0 1)⁻¹ =
          swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3) by decide])
    exact congrArg Subtype.val h
  have c22 : x₂ * p₂ * x₂⁻¹ = p₂ := by
    have h := hinj (xN₂ * pN₂ * xN₂⁻¹) pN₂ (hmemA hx₂ hp₂) hp₂ (by
      rw [map_mul, map_mul, map_inv, hψx₂, hψp₂, hψ₂, conj_mul_swap ι ha hb,
        show (swap 0 2 : Perm (Fin 4)) * (swap 0 2 * swap 1 3) * (swap 0 2)⁻¹ =
          swap 0 2 * swap 1 3 by decide])
    exact congrArg Subtype.val h
  have c21 : x₂ * p₁ * x₂⁻¹ = p₂ * p₁ := by
    have h := hinj (xN₂ * pN₁ * xN₂⁻¹) (pN₂ * pN₁) (hmemA hx₂ hp₁) (mul_mem hp₂ hp₁) (by
      rw [hprod', map_mul, map_mul, map_inv, hψx₂, hψp₁, hψ₁, conj_mul_swap ι ha hb,
        show (swap 0 2 : Perm (Fin 4)) * (swap 0 1 * swap 2 3) * (swap 0 2)⁻¹ =
          swap 0 2 * swap 1 3 * (swap 0 1 * swap 2 3) by decide])
    exact congrArg Subtype.val h
  have hr₁1 := eq_one_of_conj hc h32 ht₁ ht₂ hr₁ hr₂ he₁ he₂ hx₁ c11 c12 ht₁1
  have hr₂1 := eq_one_of_conj hc h32 ht₂ ht₁ hr₂ hr₁ he₂ he₁ hx₂ c22 c21 ht₂1
  have ht₁A : (t₁ : G) ∈ A := by rw [he₁, hr₁1, mul_one]; exact hp₁
  have ht₂A : (t₂ : G) ∈ A := by rw [he₂, hr₂1, mul_one]; exact hp₂
  intro t ht
  have htN : t ∈ normalizer (A : Set G) := hc.le_normalizer ht
  have hE : ψ ⟨t, htN⟩ ∈ (closure {t₁, t₂}).map ψ := by
    have h1 : ψ ⟨t, htN⟩ ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := ⟨_, ht, rfl⟩
    rw [hι, kleinFour, MonoidHom.map_closure] at h1
    rw [MonoidHom.map_closure, Set.image_pair, hψ₁, hψ₂]
    simpa [Set.image_pair] using h1
  obtain ⟨u, hu, hut⟩ := hE
  have huTA : u ∈ (T ⊓ A).subgroupOf (normalizer (A : Set G)) := by
    refine (closure_le _).mpr ?_ hu
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_inf.mpr ⟨ht₁, ht₁A⟩
    · exact Subgroup.mem_inf.mpr ⟨ht₂, ht₂A⟩
  have huTA' : (u : G) ∈ T ⊓ A := huTA
  obtain ⟨huT, huA⟩ := Subgroup.mem_inf.mp huTA'
  have hk : (u⁻¹ * ⟨t, htN⟩ : normalizer (A : Set G)) = 1 := by
    have hC : ((u⁻¹ * ⟨t, htN⟩ : normalizer (A : Set G)) : G) ∈
        T ⊓ Subgroup.centralizer (A : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem huT) ht, ?_⟩
      rw [← hψ.eq_one_iff, map_mul, map_inv, hut, inv_mul_cancel]
    obtain ⟨⟨-, -, -, hTC⟩, -⟩ :=
      Lemma39.lemma39_three h4 h32 h34 h2 hc.hyp hc.not_mem hc.sylowT hc.le_normalizer hOut
    rw [hTC, mem_bot] at hC
    exact Subtype.ext hC
  have htu : (⟨t, htN⟩ : normalizer (A : Set G)) = u := (inv_mul_eq_one.mp hk).symm
  have : t = (u : G) := congrArg Subtype.val htu
  rw [this]
  exact huA

end TA

end CFSG.ComponentClassification.RankTwoAlt
