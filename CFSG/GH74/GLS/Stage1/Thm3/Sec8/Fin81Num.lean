module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx16
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx67

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem imgBar_conjugate {K : Subgroup G} (hKC : K ≤ Cz z) {x : G} (hxC : x ∈ Cz z)
    (hKC' : conjugate K x ≤ Cz z) :
    imgBar z (conjugate K x) =
      (imgBar z K).map (MulAut.conj ((piC z ⟨x, hxC⟩)⁻¹)).toMonoidHom := by
  ext y
  rw [mem_imgBar hKC']
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : x * k * x⁻¹ ∈ K := mem_conjugate_iff.1 hk
    refine ⟨piC z ⟨x * k * x⁻¹, hKC hk'⟩, piC_mem_imgBar hKC hk', ?_⟩
    have hX : (⟨k, hKC' hk⟩ : ↥(Cz z)) =
        (⟨x, hxC⟩ : ↥(Cz z))⁻¹ * ⟨x * k * x⁻¹, hKC hk'⟩ * ⟨x, hxC⟩ :=
      Subtype.ext (by simp [mul_assoc])
    show (MulAut.conj ((piC z ⟨x, hxC⟩)⁻¹)) (piC z ⟨x * k * x⁻¹, hKC hk'⟩) = piC z ⟨k, hKC' hk⟩
    rw [MulAut.conj_apply, hX]
    simp only [map_mul, map_inv, inv_inv]
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨k, hk, rfl⟩ := (mem_imgBar hKC).1 hy'
    have hkc : x⁻¹ * k * x ∈ conjugate K x := by
      rw [mem_conjugate_iff]
      have e : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
      rw [e]; exact hk
    refine ⟨x⁻¹ * k * x, hkc, ?_⟩
    have hX : (⟨x⁻¹ * k * x, hKC' hkc⟩ : ↥(Cz z)) =
        (⟨x, hxC⟩ : ↥(Cz z))⁻¹ * ⟨k, hKC hk⟩ * ⟨x, hxC⟩ := Subtype.ext (by simp [mul_assoc])
    show piC z ⟨x⁻¹ * k * x, hKC' hkc⟩ = (MulAut.conj ((piC z ⟨x, hxC⟩)⁻¹)) (piC z ⟨k, hKC hk⟩)
    rw [MulAut.conj_apply, hX]
    simp only [map_mul, map_inv, inv_inv]


theorem mod8_of_two_val {r : ℕ} (hodd : Odd r) (hv : (r ^ 2 - 1).factorization 2 = 3) :
    r % 8 = 3 ∨ r % 8 = 5 := by
  have hr0 : 1 < r := by
    rcases hodd with ⟨k, hk⟩
    by_contra hcon
    have : r = 1 := by omega
    subst this
    simp at hv
  have hpos : r ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ r ^ 2 := by nlinarith
    omega
  have h8 : 2 ^ 3 ∣ r ^ 2 - 1 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).2 (by omega)
  have h16 : ¬ 2 ^ 4 ∣ r ^ 2 - 1 := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos]; omega
  have hsq : r ^ 2 % 16 = 9 := by
    have h1 : r ^ 2 - 1 ≡ 0 [MOD 8] := (Nat.modEq_zero_iff_dvd).2 (by simpa using h8)
    have h2 : ¬ (r ^ 2 - 1) % 16 = 0 := fun h => h16 (by
      have := Nat.dvd_of_mod_eq_zero h
      simpa using this)
    have : 1 ≤ r ^ 2 := by nlinarith
    unfold Nat.ModEq at h1
    omega
  have hmod : r % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have : (r % 16) ^ 2 % 16 = 9 := by rw [← Nat.pow_mod]; exact hsq
  have ho : r % 2 = 1 := by
    rcases hodd with ⟨k, hk⟩; omega
  interval_cases h : r % 16 <;> simp_all <;> omega


namespace Fused8

theorem exists_SL2' (h44 : II4_44) (hf : Fused8 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) (hdK : ¬ IsDoubleCoverOfAlt (HatT K) 7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧
      Nonempty (↥(imgBar z K) ≃* StatedSL 2 F) := by
  have hc : IsPCompIn 2 (Cz z) K := hf.std.comp_isPCompIn hK
  have := h44 G hf.std.simple z hf.std.orderOf_z K hc (hf.std.comp_pRank hK)
  rcases this.1 with ⟨F, hF, hFin, ⟨hodd, h5⟩, he⟩ | h7
  · obtain ⟨e⟩ := he
    obtain ⟨ι⟩ := imgBar_equiv hc
    exact ⟨F, hF, hFin, hodd, h5, ⟨ι.symm.trans e⟩⟩
  · exact absurd h7 hdK

end Fused8

namespace Setup8

variable {W₁ W₂ U : Subgroup G} {u h : G}

theorem exists_data_F (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h44 : II4_44) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : Nat.card ↥S = 2 ^ 7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧
      (Nat.card F ^ 2 - 1).factorization 2 = 3 ∧
      Nonempty (↥(imgBar z K₁) ≃* StatedSL 2 F) ∧ Nonempty (↥(imgBar z K₂) ≃* StatedSL 2 F) := by
  have hf := hs.fused
  obtain ⟨F, hF, hFin, hodd, h5, ⟨e₁⟩⟩ := hf.exists_SL2' h44 (K := K₁) (Or.inl rfl) hf.d₁
  obtain ⟨e, hPe, hve⟩ := hf.card_P_hat hII (K := K₁) (Or.inl rfl)
  have he3 : e = 3 := by
    have : (2 : ℕ) ^ e = 2 ^ 3 := by rw [← hPe, hP8]; norm_num
    exact Nat.pow_right_injective le_rfl this
  obtain ⟨ι₁⟩ := imgBar_equiv (hf.std.comp_isPCompIn (Or.inl rfl : K₁ = K₁ ∨ K₁ = K₂))
  have hv : (Nat.card F ^ 2 - 1).factorization 2 = 3 := by
    rw [← Basic.two_val_statedSL F hodd, ← Nat.card_congr e₁.toEquiv,
      ← Nat.card_congr ι₁.toEquiv, hve, he3]
  obtain ⟨-, hcases⟩ := cases8 hII hq hrec G z S K₁ K₂ W₁ W₂ U u h hs hP8
  have hSne : S ≠ S1 S K₁ := by
    rcases hcases with ⟨h1, h2, -⟩ | ⟨h1, -, -⟩ | ⟨h1, h2, -⟩
    · exfalso
      rw [hS7] at h2
      omega
    · exact h1
    · exfalso
      rw [hS7] at h2
      omega
  obtain ⟨x, hxS, hxn⟩ : ∃ x ∈ S, x ∉ S1 S K₁ := by
    by_contra hcon
    have hall : ∀ x ∈ S, x ∈ S1 S K₁ := fun x hx => by_contra fun hn => hcon ⟨x, hx, hn⟩
    exact hSne (le_antisymm hall S1_le_S)
  obtain ⟨hK2, -⟩ := hf.swap_of_not_mem hII hxS hxn
  have hxC : x ∈ Cz z := (hf.m4 hII).S_syl.1 hxS
  have hK₁C : K₁ ≤ Cz z := (hf.m4 hII).K₁_le
  have hK₂C : K₂ ≤ Cz z := (hf.m4 hII).K₂_le
  have hconj := imgBar_conjugate hK₁C hxC (hK2 ▸ hK₂C)
  rw [hK2] at hconj
  refine ⟨F, hF, hFin, hodd, h5, hv, ⟨e₁⟩, ⟨?_⟩⟩
  refine ((MulEquiv.subgroupCongr hconj).trans
    (MulEquiv.subgroupMap (MulAut.conj ((piC z ⟨x, hxC⟩)⁻¹)) (imgBar z K₁)).symm).trans e₁

theorem exists_numbers (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h44 : II4_44) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : Nat.card ↥S = 2 ^ 7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ 0 < f ∧
      Nat.card F = p ^ f ∧ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ 5 ≤ p ^ f ∧
      Nonempty (↥(imgBar z K₁) ≃* StatedSL 2 F) ∧ Nonempty (↥(imgBar z K₂) ≃* StatedSL 2 F) := by
  obtain ⟨F, hF, hFin, hodd, h5, hv, e₁, e₂⟩ := hs.exists_data_F hII hq hrec h44 hP8 hS7
  obtain ⟨p, f, hp, hp2, hpf⟩ := Basic.exists_odd_prime_pow F hodd
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · rw [pow_zero] at hpf; omega
    · exact hf
  have hmod := mod8_of_two_val hodd hv
  rw [← hpf] at hmod h5
  exact ⟨F, hF, hFin, p, f, hp, hp2, hf, hpf.symm, hmod, h5, e₁, e₂⟩

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
