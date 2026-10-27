module

public import CFSG.CGT.Stroth77.Section310CharB
public import CFSG.CGT.Stroth77.Section42CoreT101
public import CFSG.CGT.Stroth77.Section33Frame

public section

namespace CFSG.CGT.Stroth77

namespace Stroth42Core

variable {s : ℕ}

theorem t101_fixed_uv_dvd (hs : 1 ≤ s) (x : Fin 3 → ℤ)
    (hx : (StrothTypeIndex.t101 s).action.φuv (Torus.ofInt _ x) = Torus.ofInt _ x) :
    (2 : ℤ) ^ (s + 1) ∣ x 0 - (2 ^ s + 1) * x 1 ∧ (2 : ℤ) ^ (s + 1) ∣ x 2 - x 1 := by
  rw [t101_φuv, t101_ofInt_eq_iff] at hx
  obtain ⟨-, h1, h2⟩ := hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1 h2
  have h2' : (2 : ℤ) ^ (s + 1) ∣ x 0 - (2 ^ s + 1) * x 1 := by
    have e : x 2 - (-2 * x 0 + (2 * 2 ^ s + 2) * x 1 + x 2) =
        2 * (x 0 - (2 ^ s + 1) * x 1) := by ring
    rw [e, pow_succ' (2 : ℤ) (s + 1)] at h2
    exact (mul_dvd_mul_iff_left two_ne_zero).mp h2
  have h1' : (2 : ℤ) ^ (s + 1) ∣ x 0 - (2 * (2 ^ s) ^ 2 + 3 * 2 ^ s + 1) * x 2 := by
    have e : x 1 - (-2 * x 0 + x 1 + (4 * (2 ^ s) ^ 2 + 6 * 2 ^ s + 2) * x 2) =
        2 * (x 0 - (2 * (2 ^ s) ^ 2 + 3 * 2 ^ s + 1) * x 2) := by ring
    rw [e, pow_succ' (2 : ℤ) (s + 1)] at h1
    exact (mul_dvd_mul_iff_left two_ne_zero).mp h1
  refine ⟨h2', ?_⟩
  have h3 : (2 : ℤ) ^ (s + 1) ∣ (2 ^ s + 1) * (x 2 - x 1) := by
    have h := dvd_sub h2' h1'
    have e : x 0 - (2 ^ s + 1) * x 1 - (x 0 - (2 * (2 ^ s) ^ 2 + 3 * 2 ^ s + 1) * x 2) =
        (2 ^ s + 1) * (x 2 - x 1) + 2 ^ (s + 1) * ((2 ^ s + 1) * x 2) := by ring
    rw [e] at h
    exact (dvd_add_left (dvd_mul_right _ _)).mp h
  have hcop : IsCoprime ((2 : ℤ) ^ (s + 1)) (2 ^ s + 1) := by
    apply IsCoprime.pow_left
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    exact ⟨-2 ^ t, 1, by ring⟩
  exact hcop.dvd_of_dvd_mul_left h3

theorem t101_card_fixed_uv_le (hs : 1 ≤ s) :
    Nat.card {v : Torus (StrothTypeIndex.t101 s).k //
      (StrothTypeIndex.t101 s).action.φuv v = v} ≤ 2 ^ (s + 3) := by
  classical
  choose lift hlift using fun v : Torus (StrothTypeIndex.t101 s).k => Torus.exists_ofInt v
  let f : {v : Torus (StrothTypeIndex.t101 s).k // (StrothTypeIndex.t101 s).action.φuv v = v} →
      ZMod (2 ^ (s + 2)) × ZMod 2 := fun v =>
    ((lift v.1 1 : ZMod (2 ^ (s + 2))), (((lift v.1 2 - lift v.1 1) / 2 ^ (s + 1) : ℤ) : ZMod 2))
  have hf : Function.Injective f := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
    simp only [f, Prod.mk.injEq] at hvw
    obtain ⟨h1, h2⟩ := hvw
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1 h2
    push_cast at h1 h2
    have hxv := hlift v
    have hyw := hlift w
    set x := lift v
    set y := lift w
    rw [← hxv] at hv
    rw [← hyw] at hw
    obtain ⟨hx0, hx2⟩ := t101_fixed_uv_dvd hs x hv
    obtain ⟨hy0, hy2⟩ := t101_fixed_uv_dvd hs y hw
    apply Subtype.ext
    change v = w
    rw [← hxv, ← hyw, t101_ofInt_eq_iff]
    have h1' : (2 : ℤ) ^ (s + 1) ∣ y 1 - x 1 := (pow_dvd_pow 2 (by omega)).trans h1
    refine ⟨?_, h1, ?_⟩
    · have h := dvd_add (dvd_sub hy0 hx0) (Dvd.dvd.mul_left h1' (2 ^ s + 1))
      have e : y 0 - (2 ^ s + 1) * y 1 - (x 0 - (2 ^ s + 1) * x 1) + (2 ^ s + 1) * (y 1 - x 1) =
          y 0 - x 0 := by ring
      rwa [e] at h
    · obtain ⟨qx, hqx⟩ := hx2
      obtain ⟨qy, hqy⟩ := hy2
      have hpos : (2 : ℤ) ^ (s + 1) ≠ 0 := by positivity
      rw [hqx, hqy, Int.mul_ediv_cancel_left _ hpos, Int.mul_ediv_cancel_left _ hpos] at h2
      obtain ⟨r, hr⟩ := h2
      have e : y 2 - x 2 = (y 1 - x 1) + 2 ^ (s + 2) * r := by
        have ex : x 2 = x 1 + 2 ^ (s + 1) * qx := by linear_combination hqx
        have ey : y 2 = y 1 + 2 ^ (s + 1) * qy := by linear_combination hqy
        rw [ex, ey, pow_succ (2 : ℤ) (s + 1)]
        linear_combination 2 ^ (s + 1) * hr
      rw [e]
      exact dvd_add h1 (dvd_mul_right _ _)
  calc Nat.card _ ≤ Nat.card (ZMod (2 ^ (s + 2)) × ZMod 2) := Nat.card_le_card_of_injective f hf
    _ = 2 ^ (s + 3) := by
      rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, pow_succ 2 (s + 2)]

theorem t101_φuv_om_ne :
    (StrothTypeIndex.t101 s).action.φuv (om101 s ![1, 0, 0]) ≠ om101 s ![1, 0, 0] := by
  rw [t101_φuv_om]
  intro h
  have h1 := (om101_eq_iff _ _).mp h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
  norm_num [Int.ModEq] at h1

end Stroth42Core

open Stroth42Core

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {s : ℕ}
  {dD : StrothWeakTypeData D (.t101 s)}

theorem StrothFrame.IsD.mem_normalizer_omegaIn_t101 (h : F.IsD D dD)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) →
        (StrothTypeIndex.t101 s).m = (StrothTypeIndex.t101 s).n)
    {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine h.mem_normalizer_omegaIn_of_card_le ?_ hgS
    rw [dD.card]
    decide
  refine h.mem_normalizer_omegaIn_of_R_eq (by change s + 1 ≠ s + 2; omega) t101_one_le_k
    (dD.not_forall_commute_uv_of_torus (by rw [two_nsmul]; exact om101_add_self _)
      t101_φuv_om_ne) h226 (h.stroth_3_3 hs) ?_ hgN
  rw [card_inf_centralizer_eq_card_fixed dD.e dD.uv_mem dD.uv_conj, dD.card]
  have hfix := t101_card_fixed_uv_le hs
  have hlt : 2 ^ (s + 5) < 2 ^ ((StrothTypeIndex.t101 s).k 0 + (StrothTypeIndex.t101 s).k 1 +
      (StrothTypeIndex.t101 s).k 2) := by
    change 2 ^ (s + 5) < 2 ^ (s + 1 + (s + 2) + (s + 2))
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc 4 * Nat.card {v // (StrothTypeIndex.t101 s).action.φuv v = v} ≤ 4 * 2 ^ (s + 3) :=
        Nat.mul_le_mul_left 4 hfix
    _ = 2 ^ (s + 5) := by ring
    _ < _ := hlt

end CFSG.CGT.Stroth77
