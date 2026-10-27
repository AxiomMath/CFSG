module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Norm
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Emb
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open scoped MatrixGroups
open CFSG.Quasithin CFSG.Open

theorem wrp_normalizes_spE {n : Sp8} (hn : n ∈ wrp slD) {s : Sp8} (hs : s ∈ spE) :
    n * s * n⁻¹ ∈ spE := by
  rw [mem_spE_iff_cube] at hs ⊢
  refine ⟨wrp_normalizes_spT0 hn hs.1, ?_⟩
  rw [conj_pow, hs.2]
  group

theorem isSolvable_of_card_dvd_two_three {H : Type*} [Group H] [Finite H] {a b : ℕ}
    (h : Nat.card H ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

section Cls

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8}
  {T : Subgroup Y} {y : Y}

omit [K.Normal] in
theorem emb_mem_normalizer_E {n : Sp8} (hn : n ∈ wrp slD) :
    emb e n ∈ Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨n * s * n⁻¹, wrp_normalizes_spE hn hs, ?_⟩
  simp [map_mul, map_inv]

theorem eq_top_of_K_le (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760)
    {Y₀ : Subgroup Y} (hK : K ≤ Y₀)
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀) : Y₀ = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hS : Nat.card (spT0.map (adHom K e g).toMonoidHom) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (f := (adHom K e g).toMonoidHom) (adHom K e g).injective,
      card_spT0]
    norm_num
  obtain ⟨m, hm⟩ := sylow_conj_sp8 hcard _ hS
  have hu : emb e m * g ∈ Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) := by
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨m * adHom K e g s * m⁻¹, ?_, ?_⟩
    · have hs' : s ∈ spE := hs
      show m * adHom K e g s * m⁻¹ ∈ spE
      rw [mem_spE_iff_cube] at hs' ⊢
      refine ⟨?_, ?_⟩
      · rw [hm]
        have : m⁻¹ * (m * adHom K e g s * m⁻¹) * m = adHom K e g s := by group
        rw [this]
        exact ⟨s, hs'.1, rfl⟩
      · rw [conj_pow, ← map_pow, hs'.2, map_one]
        group
    · rw [map_mul, map_mul, map_inv, emb_adHom]
      group
  have h1 : emb e m * g ∈ Y₀ := hNE hu
  have h2 : (emb e m)⁻¹ ∈ Y₀ := Y₀.inv_mem (hK (emb_mem e m))
  have := Y₀.mul_mem h2 h1
  simpa using this

theorem classify_comap (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760)
    (hsimple : IsSimpleGroup Sp8) {Y₀ : Subgroup Y}
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀) (hY₀ : Y₀ ≠ ⊤) :
    ∃ θ : Sp8 ≃* Sp8, (∀ x, x ∈ spT0 ↔ θ x ∈ spT0) ∧ θ spZ1 = spZ12 ∧
      (Y₀.comap (emb e) = wrp slD ∨ Y₀.comap (emb e) = wrp (⊤ : Subgroup Sl28) ∨
        Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map θ.toMonoidHom) := by
  obtain ⟨θ, hθT, hθz, hlat⟩ := sp8_lattice hcard hsimple
  refine ⟨θ, hθT, hθz, ?_⟩
  have hN : wrp slD ≤ Y₀.comap (emb e) := fun n hn => hNE (emb_mem_normalizer_E hn)
  rcases hlat _ hN with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    apply hY₀
    refine eq_top_of_K_le (e := e) hcard ?_ hNE
    intro t ht
    obtain ⟨k, rfl⟩ := exists_emb e ht
    have : k ∈ Y₀.comap (emb e) := by rw [h]; exact Subgroup.mem_top k
    exact this

theorem Sp48Setup.normal_dichotomy (S : Sp48Setup e T y)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) {Y₀ : Subgroup Y} {θ : Sp8 ≃* Sp8}
    (hθT : ∀ x, x ∈ spT0 ↔ θ x ∈ spT0)
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀)
    (hcl : Y₀.comap (emb e) = wrp slD ∨ Y₀.comap (emb e) = wrp (⊤ : Subgroup Sl28) ∨
      Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map θ.toMonoidHom)
    {W : Subgroup Y} (hWY : W ≤ Y₀) (hn : Y₀ ≤ Subgroup.normalizer (W : Set Y)) :
    W = ⊥ ∨ spE.map (emb e) ≤ W := by
  have hle : W.comap (emb e) ≤ Y₀.comap (emb e) := fun w hw => hWY hw
  have hn' : ∀ h ∈ Y₀.comap (emb e), ∀ w ∈ W.comap (emb e), h * w * h⁻¹ ∈ W.comap (emb e) := by
    intro h hh w hw
    show emb e (h * w * h⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hn hh) _).1 hw
  rcases normal_dichotomy_sp8 θ hθT hcl hle hn' with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have hHp : wrp slD ≤ Y₀.comap (emb e) := fun n hn => hNE (emb_mem_normalizer_E hn)
    have hcomm : ∀ s ∈ Y₀.comap (emb e), w * emb e s = emb e s * w := by
      intro s hs
      have h1 : emb e s * w * (emb e s)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (hn hs) w).1 hw
      have h2 : (emb e s * w * (emb e s)⁻¹) * w⁻¹ ∈ W := W.mul_mem h1 (W.inv_mem hw)
      have h3 : (emb e s * w * (emb e s)⁻¹) * w⁻¹ ∈ K := by
        have : (emb e s * w * (emb e s)⁻¹) * w⁻¹ = emb e s * (w * (emb e s)⁻¹ * w⁻¹) := by
          group
        rw [this]
        exact K.mul_mem (emb_mem e s)
          (Subgroup.Normal.conj_mem (inferInstance : K.Normal) _ (K.inv_mem (emb_mem e s)) w)
      obtain ⟨k, hk⟩ := exists_emb e h3
      have hk1 : k ∈ W.comap (emb e) := by
        show emb e k ∈ W
        rw [hk]
        exact h2
      rw [h, Subgroup.mem_bot] at hk1
      rw [hk1, map_one] at hk
      have : emb e s * w * (emb e s)⁻¹ = w := by
        calc emb e s * w * (emb e s)⁻¹ = ((emb e s * w * (emb e s)⁻¹) * w⁻¹) * w := by group
          _ = w := by rw [← hk]; group
      calc w * emb e s = (emb e s * w * (emb e s)⁻¹) * emb e s := by rw [this]
        _ = emb e s * w := by group
    have hwT : w ∈ T := by
      refine S.cent_E_le hC fun z hz => ?_
      obtain ⟨s, hs, rfl⟩ := hz
      exact hcomm s (hHp (spT0_le_wrp (spE_le_spT0 hs)))
    obtain ⟨k, hk, hwk⟩ := S.cent_T0 hwT fun s hs =>
      hcomm s (hHp (spT0_le_wrp hs))
    have hk1 : k ∈ W.comap (emb e) := by
      show emb e k ∈ W
      rw [← hwk]
      exact hw
    rw [h, Subgroup.mem_bot] at hk1
    rw [hwk, hk1, map_one]
    exact Subgroup.one_mem _
  · right
    rintro _ ⟨s, hs, rfl⟩
    exact h hs

theorem Sp48Setup.solvable_of_comap_eq (S : Sp48Setup e T y)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760)
    {Y₀ : Subgroup Y} (h : Y₀.comap (emb e) = wrp slD) : Group.IsSolvable Y₀ := by
  have hKi : K.index ≤ 6 := index_le_six (eK := e) hC
  have hcardK : Nat.card K = 3 ^ 4 * 13045760 := by
    rw [← hcard]
    exact Nat.card_congr e.toEquiv
  have h3 : 3 ∣ K.index := by
    have h1 : Nat.card T ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card T
    rw [S.card_T, ← Subgroup.card_mul_index K, hcardK] at h1
    have h1' : 3 ^ 4 * 3 ∣ 3 ^ 4 * (13045760 * K.index) := by
      rw [← mul_assoc]
      exact h1
    have h2 : 3 ∣ 13045760 * K.index := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1'
    have hcop : Nat.Coprime 3 13045760 := by norm_num
    exact hcop.dvd_of_dvd_mul_left h2
  have hKi' : K.index = 3 ∨ K.index = 6 := by
    have hpos : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hA : Nat.card (K.subgroupOf Y₀) = 648 := by
    have h1 : Nat.card ((K.subgroupOf Y₀).map Y₀.subtype) = Nat.card (K.subgroupOf Y₀) :=
      Subgroup.card_map_of_injective Y₀.subtype_injective
    rw [← h1, Subgroup.subgroupOf_map_subtype]
    have h2 : K ⊓ Y₀ = (Y₀.comap (emb e)).map (emb e) := by
      ext t
      constructor
      · rintro ⟨htK, htY⟩
        obtain ⟨k, rfl⟩ := exists_emb e htK
        exact ⟨k, htY, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨emb_mem e k, hk⟩
    rw [h2, Subgroup.card_map_of_injective (emb_injective e), h, card_wrp_slD]
  have hmul : Nat.card (K.subgroupOf Y₀) * (K.subgroupOf Y₀).index = Nat.card Y₀ :=
    Subgroup.card_mul_index _
  have hrel : (K.subgroupOf Y₀).index ∣ K.index := Subgroup.relIndex_dvd_index_of_normal K Y₀
  have hm6 : (K.subgroupOf Y₀).index ∣ 6 := by
    rcases hKi' with h | h
    · rw [h] at hrel
      exact hrel.trans (by norm_num)
    · rw [h] at hrel
      exact hrel
  apply isSolvable_of_card_dvd_two_three (a := 4) (b := 5)
  rw [← hmul, hA]
  have : (2 : ℕ) ^ 4 * 3 ^ 5 = 648 * 6 := by norm_num
  rw [this]
  exact Nat.mul_dvd_mul_left 648 hm6

end Cls

end CFSG.AGLEmbedding.KFactProofs.Sp48
