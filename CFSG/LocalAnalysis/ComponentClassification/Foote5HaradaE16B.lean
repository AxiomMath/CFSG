module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HaradaE16A
public import CFSG.LocalAnalysis.OddStandard.Harada75Rank

public section

namespace CFSG.ComponentClassification.Foote5

open Subgroup
open scoped commutatorElement

variable {S : Type*} [Group S] [Finite S]

theorem harE16_card_le_four {T U A : Subgroup S} (hT16 : Nat.card T = 16) (hUT : U ≤ T)
    (hU4 : Nat.card U = 4) (hAT : A ≤ T) (hAU : ∀ u ∈ A, u ∈ U → u = 1) : Nat.card A ≤ 4 := by
  have h := harE16_card_mul_card_le hAT hUT
  have hbot : A ⊓ U = ⊥ := eq_bot_iff.mpr fun u hu => (mem_bot).mpr (hAU u hu.1 hu.2)
  rw [hbot, card_bot, hT16, hU4] at h
  omega

omit [Finite S] in
theorem harE16_eq_one_of_commute {T U : Subgroup S}
    (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T) {g u : S} (hg : g ∉ T)
    (hu : u ∈ U) (hgu : g * u = u * g) : u = 1 := by
  by_contra hu1
  exact hg (hcent u hu hu1 g hgu)

theorem harE16_card_le_of_comm_mem {T U A : Subgroup S}
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hT16 : Nat.card T = 16) (hUT : U ≤ T)
    (hU4 : Nat.card U = 4) (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T) {s : S}
    (hs : s ∈ normalizer (T : Set S)) (hsT : s ∉ T) (hA : ∀ x ∈ T, s * x * s⁻¹ * x⁻¹ ∈ A) :
    Nat.card T ≤ 4 * Nat.card A := by
  have h1 := card_ker_mul_card_range (harE16CommHom hTab hs)
  have hker : Nat.card (harE16CommHom hTab hs).ker ≤ 4 := by
    rw [← card_map_of_injective T.subtype_injective]
    refine harE16_card_le_four hT16 hUT hU4 (map_subtype_le _) fun u hu huU => ?_
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hu
    exact harE16_eq_one_of_commute hcent hsT huU
      ((harE16CommHom_eq_one_iff hTab hs x).mp hx)
  have hran : Nat.card (harE16CommHom hTab hs).range ≤ Nat.card A := by
    rw [← card_map_of_injective T.subtype_injective]
    apply card_le_of_le
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hA x x.2
  calc Nat.card T = Nat.card (harE16CommHom hTab hs).ker *
        Nat.card (harE16CommHom hTab hs).range := h1.symm
    _ ≤ 4 * Nat.card A := Nat.mul_le_mul hker hran

omit [Finite S] in
theorem harE16_commute_comm {T : Subgroup S} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTsq : ∀ a ∈ T, a * a = 1) {s x : S} (hs : s ∈ normalizer (T : Set S)) (hss : s * s ∈ T)
    (hx : x ∈ T) : s * (s * x * s⁻¹ * x⁻¹) = s * x * s⁻¹ * x⁻¹ * s := by
  have hy : s * x * s⁻¹ ∈ T := (mem_normalizer_iff.mp hs x).mp hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hTsq x hx)
  have h1 : s * s * x = x * (s * s) := hTab _ hss _ hx
  have h2 : x * (s * x * s⁻¹) = s * x * s⁻¹ * x := hTab _ hx _ hy
  rw [hxinv]
  calc s * (s * x * s⁻¹ * x) = s * s * x * s⁻¹ * x := by group
    _ = x * (s * s) * s⁻¹ * x := by rw [h1]
    _ = x * (s * x * s⁻¹) * s := by group
    _ = s * x * s⁻¹ * x * s := by rw [h2]

omit [Finite S] in
theorem harE16_conj_comm {T : Subgroup S} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {s r x : S} (hr : r ∈ normalizer (T : Set S)) (hrs : s⁻¹ * (r * s * r⁻¹) ∈ T) (hx : x ∈ T) :
    r * (s * x * s⁻¹ * x⁻¹) * r⁻¹ = s * (r * x * r⁻¹) * s⁻¹ * (r * x * r⁻¹)⁻¹ := by
  have hy : r * x * r⁻¹ ∈ T := (mem_normalizer_iff.mp hr x).mp hx
  have hty := hTab _ hrs _ hy
  calc r * (s * x * s⁻¹ * x⁻¹) * r⁻¹
      = s * ((s⁻¹ * (r * s * r⁻¹)) * (r * x * r⁻¹)) * (s⁻¹ * (r * s * r⁻¹))⁻¹ * s⁻¹ *
          (r * x * r⁻¹)⁻¹ := by group
    _ = s * ((r * x * r⁻¹) * (s⁻¹ * (r * s * r⁻¹))) * (s⁻¹ * (r * s * r⁻¹))⁻¹ * s⁻¹ *
          (r * x * r⁻¹)⁻¹ := by rw [hty]
    _ = s * (r * x * r⁻¹) * s⁻¹ * (r * x * r⁻¹)⁻¹ := by group

omit [Finite S] in
theorem harE16_commute_of_comm_eq {T : Subgroup S} (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {s x y : S} (hs : s ∈ normalizer (T : Set S)) (hx : x ∈ T) (hy : y ∈ T)
    (h : s * x * s⁻¹ * x⁻¹ = s * y * s⁻¹ * y⁻¹) : s * (x⁻¹ * y) = x⁻¹ * y * s := by
  have h1 : harE16CommHom hTab hs ((⟨x, hx⟩ : ↥T)⁻¹ * ⟨y, hy⟩) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext (by rw [harE16CommHom_apply, harE16CommHom_apply]; exact h)
  simpa using (harE16CommHom_eq_one_iff hTab hs _).mp h1

theorem harE16_card_normalizer_le {T U : Subgroup S} (hS : IsPGroup 2 S)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTsq : ∀ a ∈ T, a * a = 1)
    (hT16 : Nat.card T = 16) (hUT : U ≤ T) (hU4 : Nat.card U = 4)
    (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T) :
    Nat.card (normalizer (T : Set S)) ≤ 64 := by
  by_cases hRT : normalizer (T : Set S) ≤ T
  · exact (card_le_of_le hRT).trans (by omega)
  obtain ⟨r₀, hr₀, hr₀T⟩ := IsConcreteLE.not_le_iff_exists.mp hRT
  obtain ⟨s, hsR, hsT, hss, hsc⟩ :=
    harE16_exists_central_mod (hS.to_subgroup (normalizer (T : Set S))) le_rfl hr₀ hr₀T
  have hmemC : ∀ x, x ∈ T ⊓ centralizer {s} ↔ x ∈ T ∧ s * x = x * s := fun x => by
    rw [mem_inf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => eq_comm
  have hCT : T ⊓ centralizer {s} ≤ T := inf_le_left
  have hCR : T ⊓ centralizer {s} ≤ normalizer (T : Set S) := hCT.trans le_normalizer
  have hφC : ∀ x ∈ T, s * x * s⁻¹ * x⁻¹ ∈ T ⊓ centralizer {s} := fun x hx =>
    (hmemC _).mpr ⟨T.mul_mem ((mem_normalizer_iff.mp hsR x).mp hx) (T.inv_mem hx),
      harE16_commute_comm hTab hTsq hsR hss hx⟩
  have hC4 : Nat.card ↥(T ⊓ centralizer {s}) ≤ 4 :=
    harE16_card_le_four hT16 hUT hU4 hCT fun u hu huU =>
      harE16_eq_one_of_commute hcent hsT huU ((hmemC u).mp hu).2
  set ψ := (harE16CommHom hTab hsR).comp (inclusion hUT) with hψ
  have hψker : ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [mem_bot]
    have h1 : s * (u : S) = u * s := (harE16CommHom_eq_one_iff hTab hsR _).mp hu
    exact Subtype.ext (harE16_eq_one_of_commute hcent hsT u.2 h1)
  have hψran : Nat.card ψ.range = 4 := by
    have h1 := card_ker_mul_card_range ψ
    rw [hψker, card_bot, one_mul, hU4] at h1
    exact h1
  have hran_le : ψ.range ≤ (T ⊓ centralizer {s}).subgroupOf T := by
    rintro _ ⟨u, rfl⟩
    exact hφC u (hUT u.2)
  have hCsub : Nat.card ((T ⊓ centralizer {s}).subgroupOf T) = Nat.card ↥(T ⊓ centralizer {s}) :=
    Nat.card_congr (subgroupOfEquivOfLe hCT).toEquiv
  have hran_eq : ψ.range = (T ⊓ centralizer {s}).subgroupOf T :=
    eq_of_le_of_card_ge hran_le (by rw [hCsub, hψran]; exact hC4)
  have hCne : T ⊓ centralizer {s} ≠ ⊥ := by
    intro h
    have h1 := hCsub
    rw [← hran_eq, hψran, h, card_bot] at h1
    omega
  have hconj : ∀ r ∈ normalizer (T : Set S), ∀ x ∈ T,
      r * (s * x * s⁻¹ * x⁻¹) * r⁻¹ = s * (r * x * r⁻¹) * s⁻¹ * (r * x * r⁻¹)⁻¹ :=
    fun r hr x hx => harE16_conj_comm hTab hr (hsc r hr) hx
  have hkey : ∀ r ∈ normalizer (T : Set S), ∀ n ∈ T ⊓ centralizer {s},
      r * n * r⁻¹ ∈ T ⊓ centralizer {s} := by
    intro r hr n hn
    have hnT := ((hmemC n).mp hn).1
    have hnc : s * n * s⁻¹ * n⁻¹ = 1 := harE16_comm_eq_one_iff.mpr ((hmemC n).mp hn).2
    have h1 := hconj r hr n hnT
    rw [hnc, mul_one, mul_inv_cancel] at h1
    exact (hmemC _).mpr ⟨(mem_normalizer_iff.mp hr n).mp hnT,
      harE16_comm_eq_one_iff.mp h1.symm⟩
  have hRC : normalizer (T : Set S) ≤ normalizer ((T ⊓ centralizer {s} : Subgroup S) : Set S) := by
    intro r hr
    rw [mem_normalizer_iff]
    intro n
    refine ⟨hkey r hr n, fun h => ?_⟩
    have h1 := hkey r⁻¹ ((normalizer (T : Set S)).inv_mem hr) _ h
    simpa [mul_assoc] using h1
  obtain ⟨c₀, hc₀C, hc₀1, hc₀R⟩ :=
    harE16_exists_mem_center (hS.to_subgroup _) hCR hRC hCne
  have hc₀ran : (⟨c₀, hCT hc₀C⟩ : ↥T) ∈ ψ.range := by rw [hran_eq]; exact hc₀C
  obtain ⟨u₀, hu₀⟩ := hc₀ran
  have hu₀' : s * (u₀ : S) * s⁻¹ * (u₀ : S)⁻¹ = c₀ := congrArg Subtype.val hu₀
  have hu₀T : (u₀ : S) ∈ T := hUT u₀.2
  have hu₀1 : (u₀ : S) ≠ 1 := by
    intro h
    rw [h] at hu₀'
    exact hc₀1 (by rw [← hu₀']; group)
  have hC' : ∀ r ∈ normalizer (T : Set S), (u₀ : S)⁻¹ * (r * u₀ * r⁻¹) ∈ T ⊓ centralizer {s} := by
    intro r hr
    have hv : r * (u₀ : S) * r⁻¹ ∈ T := (mem_normalizer_iff.mp hr _).mp hu₀T
    have h1 := hconj r hr u₀ hu₀T
    have h2 : r * c₀ * r⁻¹ = c₀ := by rw [hc₀R r hr]; group
    rw [hu₀', h2] at h1
    refine (hmemC _).mpr ⟨T.mul_mem (T.inv_mem hu₀T) hv, ?_⟩
    exact harE16_commute_of_comm_eq hTab hsR hu₀T hv (hu₀'.trans h1)
  have h3 := harE16_card_le_of_conj le_normalizer hCR (le_normalizer hu₀T)
    (fun r _ hru => hcent u₀ u₀.2 hu₀1 r hru) (fun t ht => hTab t ht u₀ hu₀T) hC'
  rw [hT16] at h3
  omega

theorem harE16_noE32 {S : Type} [Group S] [Finite S] {T U : Subgroup S}
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hT16 : Nat.card T = 16) (hUT : U ≤ T)
    (hU4 : Nat.card U = 4) (hcent : ∀ u ∈ U, u ≠ 1 → ∀ g : S, g * u = u * g → g ∈ T)
    (hS64 : Nat.card S ≤ 64) (hN : ∀ g : S, g ∈ normalizer (T : Set S)) :
    OddStandard.Harada75.NoE32 S := by
  rintro T' U' ⟨-, -, hcomm, hcard⟩
  have hT'le : Nat.card T' ≤ 64 := (card_le_card_group T').trans hS64
  have hU'pos : 0 < Nat.card U' := Nat.card_pos
  rcases (show Nat.card U' = 1 ∨ Nat.card U' = 2 by omega) with h1 | h2
  · have hU'bot : U' = ⊥ := card_eq_one.mp h1
    have hT'ab : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x := by
      intro x hx y hy
      have h3 := hcomm x hx y hy
      rw [hU'bot, mem_bot, commutatorElement_eq_one_iff_commute] at h3
      exact h3
    have h32 : Nat.card T' = 32 := by rw [hcard, h1]
    have hKI1 := harE16_card_mul_card_le (le_top : T' ≤ ⊤) (le_top : T ≤ ⊤)
    rw [card_top, h32, hT16] at hKI1
    have hKI2 := harE16_card_mul_card_le (inf_le_right : T' ⊓ T ≤ T) hUT
    rw [hT16, hU4] at hKI2
    have h8 : 8 ≤ Nat.card ↥(T' ⊓ T) := by nlinarith
    have hne : T' ⊓ T ⊓ U ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hKI2
      omega
    obtain ⟨⟨u, hu⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hne
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hT'T : T' ≤ T := fun g hg =>
      hcent u (mem_inf.mp hu).2 hu1' g (hT'ab g hg u (mem_inf.mp (mem_inf.mp hu).1).1)
    have h4 := card_le_of_le hT'T
    omega
  · have h64 : Nat.card T' = 64 := by rw [hcard, h2]
    have hT'S := card_le_card_group T'
    have hT'top : T' = ⊤ := eq_top_of_card_eq _ (by omega)
    obtain ⟨s, hsT⟩ : ∃ s : S, s ∉ T := by
      by_contra h
      have hT : T = ⊤ := eq_top_iff.mpr fun g _ => by
        by_contra hg
        exact h ⟨g, hg⟩
      have h5 := card_top (G := S)
      rw [← hT, hT16, ← card_top (G := S), ← hT'top, h64] at h5
      omega
    have h3 := harE16_card_le_of_comm_mem (A := U') hTab hT16 hUT hU4 hcent (hN s) hsT
      fun x _ => by
        have h4 := hcomm s (hT'top ▸ mem_top s) x (hT'top ▸ mem_top x)
        rwa [commutatorElement_def] at h4
    rw [hT16, h2] at h3
    omega

end CFSG.ComponentClassification.Foote5
