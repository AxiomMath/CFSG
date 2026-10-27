module

public import CFSG.GH74.GLS.Stage4.T6Aut
public import CFSG.GH74.GLS.Stage4.T6Aut3

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem t6_map_comap {φ : SL2 F →* G} {Y : Subgroup G} (h : Y ≤ φ.range) : (Y.comap φ).map φ = Y :=
  Subgroup.map_comap_eq_self h

theorem t6_irr_u {φ : SL2 F →* G} (hφ : Function.Injective φ) (hodd : Odd (Nat.card F))
    {Y : Subgroup G} (hY : Y ≤ (uSub F).map φ)
    (hT : ∀ t ∈ tSub F, ∀ y ∈ Y, φ t * y * (φ t)⁻¹ ∈ Y) : Y = ⊥ ∨ Y = (uSub F).map φ := by
  have hYr : Y ≤ φ.range := hY.trans (Subgroup.map_le_range φ _)
  have hY' : Y.comap φ ≤ uSub F := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hY hy
    have : x = y := hφ hxy
    rwa [this] at hx
  have hT' : ∀ t ∈ tSub F, ∀ y ∈ Y.comap φ, t * y * t⁻¹ ∈ Y.comap φ := by
    intro t ht y hy
    have := hT t ht (φ y) hy
    simpa [Subgroup.mem_comap] using this
  rcases t6_torus_inv_u hodd _ hY' hT' with h | h
  · left
    rw [← t6_map_comap hYr, h]; simp
  · right
    rw [← t6_map_comap hYr, h]

theorem t6_pSub_inv {φ : SL2 F →* G} (hφ : Function.Injective φ) {p m : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ m) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) {B : Subgroup G}
    (hBr : B ≤ φ.range) (hB : IsPGroup p ↥B) (hT : ∀ t ∈ tSub F, ∀ b ∈ B, φ t * b * (φ t)⁻¹ ∈ B) :
    B = ⊥ ∨ B = (uSub F).map φ ∨ B = (lSub F).map φ := by
  have hB' : IsPGroup p ↥(B.comap φ) := by
    have : IsPGroup p ↥(B.comap φ) := by
      intro x
      obtain ⟨k, hk⟩ := hB ⟨φ x, x.2⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      apply hφ
      have := congrArg Subtype.val hk
      simpa using this
    exact this
  have hT' : ∀ t ∈ tSub F, ∀ y ∈ B.comap φ, t * y * t⁻¹ ∈ B.comap φ := by
    intro t ht y hy
    have := hT t ht (φ y) hy
    simpa [Subgroup.mem_comap] using this
  rcases t6_pSub_torus hp hF hodd h5 _ hB' hT' with h | h | h
  · left
    rw [← t6_map_comap hBr, h]; simp
  · right; left
    rw [← t6_map_comap hBr, h]
  · right; right
    rw [← t6_map_comap hBr, h]

theorem t6_cent_torus {φ : SL2 F →* G} (hφ : Function.Injective φ) (h5 : 5 ≤ Nat.card F) {k : G}
    (hk : k ∈ φ.range) (hc : ∀ t ∈ tSub F, k * φ t = φ t * k) : k ∈ (tSub F).map φ := by
  obtain ⟨g, rfl⟩ := hk
  refine ⟨g, t6_cent_tSub h5 g (fun t ht => ?_), rfl⟩
  apply hφ
  have := hc t ht
  simpa [map_mul] using this.symm

theorem t6_aut_X {φ : SL2 F →* G} (hφ : Function.Injective φ) (hodd : Odd (Nat.card F))
    (h3 : 3 ≤ Nat.card F) {y : G} (hy : ∀ g ∈ φ.range, y * g * y⁻¹ ∈ φ.range)
    (hyX : ∀ c : F, y * φ (sl2U c) * y⁻¹ = φ (sl2U c)) :
    ∃ s : F, ∀ g : SL2 F, y * φ g * y⁻¹ = φ (sl2U s) * φ g * (φ (sl2U s))⁻¹ := by
  have : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hyn : y ∈ normalizer (φ.range : Set G) := Subgroup.mem_normalizer_fintype (fun n hn => hy n hn)
  let ρ : MulAut ↥φ.range := Subgroup.normalizerMonoidHom φ.range ⟨y, hyn⟩
  have hρ : ∀ g : ↥φ.range, ((ρ g : ↥φ.range) : G) = y * g * y⁻¹ := fun g => rfl
  let eφ : SL2 F ≃* ↥φ.range := MonoidHom.ofInjective hφ
  have heφ : ∀ g : SL2 F, ((eφ g : ↥φ.range) : G) = φ g := fun g => rfl
  let α : MulAut (SL2 F) := eφ.trans (ρ.trans eφ.symm)
  have hα : ∀ g : SL2 F, φ (α g) = y * φ g * y⁻¹ := by
    intro g
    have h1 : eφ (α g) = ρ (eφ g) := by
      show eφ (eφ.symm (ρ (eφ g))) = ρ (eφ g)
      exact eφ.apply_symm_apply _
    have h2 := congrArg (fun x : ↥φ.range => (x : G)) h1
    simpa [heφ, hρ] using h2
  have hαfix : ∀ c : F, α (sl2U c) = sl2U c := by
    intro c
    apply hφ
    rw [hα, hyX]
  obtain ⟨s, hs⟩ : ∃ s : F, ∀ g : SL2 F, α g = sl2U s * g * (sl2U s)⁻¹ := by
    rcases h3.eq_or_lt with h | h
    · exact t6_aut_fix_u3 h.symm α hαfix
    · exact t6_aut_fix_u hodd h α hαfix
  refine ⟨s, fun g => ?_⟩
  rw [← hα, hs]
  simp [map_mul, map_inv]

theorem t6_pSub_card {φ : SL2 F →* G} (hφ : Function.Injective φ) {p m : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ m) (hm : 1 ≤ m) (hodd : Odd (Nat.card F)) {B : Subgroup G}
    (hBr : B ≤ φ.range) (hB : IsPGroup p ↥B)
    (hT : ∀ t ∈ tSub F, ∀ b ∈ B, φ t * b * (φ t)⁻¹ ∈ B) :
    (Nat.card B = 1 ∨ Nat.card B = p ^ m) ∧ ∀ b ∈ B, b ^ p = 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hF] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hfinR : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hfinB : Finite ↥B := Finite.of_injective (Subgroup.inclusion hBr) (Subgroup.inclusion_injective hBr)
  by_cases hm1 : m = 1
  · subst hm1
    obtain ⟨n, hn⟩ := hB.exists_card_eq
    have hBd : Nat.card B ∣ Nat.card (SL2 F) := by
      have : Nat.card B ∣ Nat.card φ.range := Subgroup.card_dvd_of_le hBr
      have h2 : Nat.card φ.range = Nat.card (SL2 F) :=
        Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
      rwa [h2] at this
    rw [t2C_card_sl2, hF, hn] at hBd
    have hnd : ¬ p ∣ (p ^ 1) ^ 2 - 1 := by
      intro h
      have h1 : p ∣ (p ^ 1) ^ 2 := dvd_pow (dvd_pow_self p one_ne_zero) two_ne_zero
      have h2 : p ∣ (p ^ 1) ^ 2 - ((p ^ 1) ^ 2 - 1) := Nat.dvd_sub h1 h
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (pow_pos (by omega : 0 < p) 1))] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    have hcop : Nat.Coprime (p ^ n) ((p ^ 1) ^ 2 - 1) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    have hdvd : p ^ n ∣ p ^ 1 := hcop.dvd_of_dvd_mul_right hBd
    have hn1 : n ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
    refine ⟨?_, fun b hb => ?_⟩
    · rw [hn]
      interval_cases n
      · left; simp
      · right; simp
    · have h1 : (⟨b, hb⟩ : ↥B) ^ Nat.card B = 1 := pow_card_eq_one'
      have h2 : Nat.card B ∣ p := by rw [hn]; simpa using (pow_dvd_pow p hn1 : p ^ n ∣ p ^ 1)
      have h3 : (⟨b, hb⟩ : ↥B) ^ p = 1 := by
        obtain ⟨c, hc⟩ := h2
        rw [hc, pow_mul, h1, one_pow]
      simpa using congrArg Subtype.val h3
  · have hm2 : 2 ≤ m := by omega
    have h5 : 5 ≤ Nat.card F := by
      rw [hF]
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ p ^ m := (Nat.pow_le_pow_left hp3 2).trans (Nat.pow_le_pow_right (by omega) hm2)
    have hcharP : CharP F p := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (R := F) (p := p) (f := m) (by rw [← Nat.card_eq_fintype_card]; exact hF)
    rcases t6_pSub_inv hφ hp hF hodd h5 hBr hB hT with h | h | h
    · refine ⟨Or.inl (by rw [h]; simp), fun b hb => ?_⟩
      rw [h] at hb
      rw [Subgroup.mem_bot.1 hb]; simp
    · refine ⟨Or.inr (by rw [h, Subgroup.card_map_of_injective hφ, card_uSub, hF]), fun b hb => ?_⟩
      rw [h] at hb
      obtain ⟨x, hx, rfl⟩ := hb
      rw [← map_pow, pow_char_uSub p x hx, map_one]
    · refine ⟨Or.inr (by rw [h, Subgroup.card_map_of_injective hφ, card_lSub, hF]), fun b hb => ?_⟩
      rw [h] at hb
      obtain ⟨x, hx, rfl⟩ := hb
      rw [← map_pow, pow_char_lSub p x hx, map_one]

end CFSG.GH74.GLS.Stage4.Rest.T6
