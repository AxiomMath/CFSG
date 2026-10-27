module

public import CFSG.GH74.GLS.Bg.Statements

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg
open scoped commutatorElement

variable {A G : Type} [Group A] [Group G] (φ : A →* G) (hφ : Function.Injective φ)

include hφ

theorem map_le_map_iff' {B C : Subgroup A} : B.map φ ≤ C.map φ ↔ B ≤ C :=
  Subgroup.map_le_map_iff_of_injective hφ

theorem map_inj' {B C : Subgroup A} : B.map φ = C.map φ ↔ B = C :=
  (Subgroup.map_injective hφ).eq_iff

theorem map_eq_bot' (B : Subgroup A) : B.map φ = ⊥ ↔ B = ⊥ := by
  rw [← Subgroup.map_bot φ, map_inj' φ hφ]

theorem map_zOf (B : Subgroup A) : zOf (B.map φ) = (zOf B).map φ := by
  unfold zOf
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hc⟩
    refine ⟨b, ⟨hb, fun c hc' => ?_⟩, rfl⟩
    apply hφ
    rw [map_mul, map_mul]
    exact hc (φ c) ⟨c, hc', rfl⟩
  · rintro ⟨b, ⟨hb, hc⟩, rfl⟩
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    rintro _ ⟨c, hc', rfl⟩
    rw [← map_mul, ← map_mul, hc c hc']

theorem map_mem_normalizer_iff {Q B : Subgroup A} :
    Q.map φ ≤ normalizer ((B.map φ : Subgroup G) : Set G) ↔ Q ≤ normalizer (B : Set A) := by
  constructor
  · intro h q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.mp (h ⟨q, hq, rfl⟩) (φ x)
    rw [← map_mul, ← map_inv, ← map_mul] at this
    constructor
    · intro hx
      have := this.mp (Subgroup.mem_map_of_mem φ hx)
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
      have := hφ hyx
      rw [← this]; exact hy
    · intro hx
      have h1 := this.mpr (Subgroup.mem_map_of_mem φ hx)
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
      rw [hφ hyx] at hy
      exact hy
  · intro h y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hz := Subgroup.mem_normalizer_iff.mp (h hq)
    constructor
    · intro hzB
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hzB
      have := (hz x).mp hx
      rw [← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem φ this
    · intro hzB
      obtain ⟨b, hb, hbw⟩ := Subgroup.mem_map.mp hzB
      have h1 := (Subgroup.mem_normalizer_iff.mp (h (Q.inv_mem hq)) b).mp hb
      have h2 : φ (q⁻¹ * b * q⁻¹⁻¹) = z := by
        simp only [map_mul, map_inv, inv_inv]
        rw [hbw]; group
      rw [← h2]
      exact Subgroup.mem_map_of_mem φ h1

omit hφ in
theorem map_commutator' (B C : Subgroup A) : ⁅B.map φ, C.map φ⁆ = (⁅B, C⁆).map φ :=
  (Subgroup.map_commutator B C φ).symm

theorem map_mem_classTwo {P B : Subgroup A} :
    B.map φ ∈ classTwo (P.map φ) ↔ B ∈ classTwo P := by
  unfold classTwo
  simp only [Set.mem_ofPred_eq]
  rw [map_le_map_iff' φ hφ, map_commutator' φ, map_commutator' φ, map_eq_bot' φ hφ]

theorem map_klow_cond (B C : Subgroup A) :
    (⁅B.map φ, ⁅C.map φ, C.map φ⁆⁆ = ⊥ → ⁅⁅zOf (B.map φ), C.map φ⁆, C.map φ⁆ = ⊥ →
        ⁅B.map φ, C.map φ⁆ ≤ zOf (B.map φ)) ↔
      (⁅B, ⁅C, C⁆⁆ = ⊥ → ⁅⁅zOf B, C⁆, C⁆ = ⊥ → ⁅B, C⁆ ≤ zOf B) := by
  rw [map_zOf φ hφ, map_commutator' φ, map_commutator' φ, map_commutator' φ, map_commutator' φ,
    map_commutator' φ, map_eq_bot' φ hφ, map_eq_bot' φ hφ, map_le_map_iff' φ hφ]

theorem map_mem_Klow {P Q B : Subgroup A} :
    B.map φ ∈ Klow (P.map φ) (Q.map φ) ↔ B ∈ Klow P Q := by
  constructor
  · rintro ⟨hB, hQ, hall⟩
    refine ⟨(map_mem_classTwo φ hφ).mp hB, (map_mem_normalizer_iff φ hφ).mp hQ,
      fun A' hA' hA'Q hBA' => ?_⟩
    have := hall (A'.map φ) ((map_mem_classTwo φ hφ).mpr hA') ((map_le_map_iff' φ hφ).mpr hA'Q)
      ((map_mem_normalizer_iff φ hφ).mpr hBA')
    exact (map_klow_cond φ hφ B A').mp this
  · rintro ⟨hB, hQ, hall⟩
    refine ⟨(map_mem_classTwo φ hφ).mpr hB, (map_mem_normalizer_iff φ hφ).mpr hQ,
      fun A' hA' hA'Q hBA' => ?_⟩
    have hA'le : A' ≤ φ.range := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hA'.1 hx)
      exact ⟨y, rfl⟩
    set A : Subgroup A := A'.comap φ with hAdef
    have hAmap : A.map φ = A' := Subgroup.map_comap_eq_self hA'le
    rw [← hAmap] at hA' hA'Q hBA' ⊢
    have := hall A ((map_mem_classTwo φ hφ).mp hA') ((map_le_map_iff' φ hφ).mp hA'Q)
      ((map_mem_normalizer_iff φ hφ).mp hBA')
    exact (map_klow_cond φ hφ B A).mpr this

theorem map_mem_Kup {P Q B : Subgroup A} :
    B.map φ ∈ Kup (P.map φ) (Q.map φ) ↔ B ∈ Kup P Q := by
  unfold Kup
  simp only [Set.mem_ofPred_eq]
  rw [map_mem_classTwo φ hφ, map_zOf φ hφ, map_commutator' φ, map_le_map_iff' φ hφ]

omit hφ in
theorem gen_map_image (S : Set (Subgroup A)) :
    gen ((fun B : Subgroup A => B.map φ) '' S) = (gen S).map φ := by
  unfold gen
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨B', ⟨B, hB, rfl⟩, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨B, hB, hx⟩, rfl⟩
  · rintro ⟨x, ⟨B, hB, hx⟩, rfl⟩
    exact ⟨B.map φ, ⟨B, hB, rfl⟩, Subgroup.mem_map_of_mem φ hx⟩

theorem Kfam_map_iff (P : Subgroup A) (n : ℕ) (B' : Subgroup G) :
    B' ∈ Kfam (P.map φ) n ↔ ∃ B ∈ Kfam P n, B.map φ = B' := by
  induction n generalizing B' with
  | zero =>
    show B' ∈ classTwo (P.map φ) ↔ _
    constructor
    · intro hB'
      have hle : B' ≤ φ.range := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hB'.1 hx)
        exact ⟨y, rfl⟩
      refine ⟨B'.comap φ, ?_, Subgroup.map_comap_eq_self hle⟩
      show B'.comap φ ∈ classTwo P
      rw [← map_mem_classTwo φ hφ, Subgroup.map_comap_eq_self hle]
      exact hB'
    · rintro ⟨B, hB, rfl⟩
      exact (map_mem_classTwo φ hφ).mpr hB
  | succ n ih =>
    have hgen : gen (Kfam (P.map φ) n) = (gen (Kfam P n)).map φ := by
      rw [← gen_map_image φ]
      congr 1
      ext B'
      rw [ih B']
      simp
    show B' ∈ (if Even n then Klow (P.map φ) (gen (Kfam (P.map φ) n))
        else Kup (P.map φ) (gen (Kfam (P.map φ) n))) ↔
      ∃ B ∈ (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n))), B.map φ = B'
    rw [hgen]
    have key : ∀ (S : Subgroup A → Prop) (S' : Subgroup G → Prop),
        (∀ B, S' (B.map φ) ↔ S B) → (∀ B', S' B' → B' ≤ φ.range) →
        (S' B' ↔ ∃ B, S B ∧ B.map φ = B') := by
      intro S S' hS hrange
      constructor
      · intro h
        have hle := hrange B' h
        refine ⟨B'.comap φ, ?_, Subgroup.map_comap_eq_self hle⟩
        rw [← hS, Subgroup.map_comap_eq_self hle]
        exact h
      · rintro ⟨B, hB, rfl⟩
        exact (hS B).mpr hB
    by_cases hn : Even n
    · simp only [hn, ↓reduceIte]
      refine key (fun B => B ∈ Klow P (gen (Kfam P n))) (fun B' => B' ∈ Klow (P.map φ) _)
        (fun B => map_mem_Klow φ hφ) ?_
      intro B' hB' x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hB'.1.1 hx)
      exact ⟨y, rfl⟩
    · simp only [hn, ↓reduceIte]
      refine key (fun B => B ∈ Kup P (gen (Kfam P n))) (fun B' => B' ∈ Kup (P.map φ) _)
        (fun B => map_mem_Kup φ hφ) ?_
      intro B' hB' x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hB'.1.1 hx)
      exact ⟨y, rfl⟩

theorem kInfty_map' (P : Subgroup A) : kInfty (P.map φ) = (kInfty P).map φ := by
  unfold kInfty
  rw [← gen_map_image φ]
  congr 1
  ext B'
  simp only [Set.mem_iInter, Set.mem_image]
  constructor
  · intro h
    have h0 : B' ∈ classTwo (P.map φ) := h 0
    have hle : B' ≤ φ.range := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (h0.1 hx)
      exact ⟨y, rfl⟩
    refine ⟨B'.comap φ, fun i => ?_, Subgroup.map_comap_eq_self hle⟩
    obtain ⟨B, hB, hBφ⟩ := (Kfam_map_iff φ hφ P (2 * i) B').mp (h i)
    have : B = B'.comap φ := by rw [← hBφ, Subgroup.comap_map_eq_self_of_injective hφ]
    rw [← this]; exact hB
  · rintro ⟨B, hB, rfl⟩ i
    exact (Kfam_map_iff φ hφ P (2 * i) _).mpr ⟨B, hB i, rfl⟩

theorem kLowInfty_map' (P : Subgroup A) : kLowInfty (P.map φ) = (kLowInfty P).map φ := by
  unfold kLowInfty
  rw [← gen_map_image φ]
  congr 1
  ext B'
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨B, hB, hBφ⟩ := (Kfam_map_iff φ hφ P (2 * i + 1) B').mp hi
    exact ⟨B, ⟨i, hB⟩, hBφ⟩
  · rintro ⟨B, ⟨i, hB⟩, rfl⟩
    exact ⟨i, (Kfam_map_iff φ hφ P (2 * i + 1) _).mpr ⟨B, hB, rfl⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.L53
