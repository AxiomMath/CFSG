module

public import CFSG.LieType.SeitzGeneration.HeisTorusU86
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Core

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K] {r : ℕ}

theorem ug87_diag_unitary (h : UnitaryFieldData ℓ f K) {d : Fin r → K}
    (hd : ∀ k, d k ^ (ℓ ^ f + 1) = 1) :
    ((diagonal d : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ * diagonal d = 1 := by
  rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [ug86_bar_eq_inv h (hd i)]
  exact inv_mul_cancel₀ (ug86_ne_zero_of_pow_eq_one (hd i))

theorem ug87_exists_mem_diag (h : UnitaryFieldData ℓ f K) (H : Subgroup (GL (Fin r) K))
    (hT : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) = diagonal t) → g ∈ H)
    {d : Fin r → K} (hd : ∀ k, d k ^ (ℓ ^ f + 1) = 1) (hdet : ∏ k, d k = 1) :
    ∃ t ∈ H, (t : Matrix (Fin r) (Fin r) K) = diagonal d := by
  have hdet' : (diagonal d : Matrix (Fin r) (Fin r) K).det = 1 := by rw [det_diagonal, hdet]
  let t : GL (Fin r) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal d)
    (by rw [hdet']; exact one_ne_zero)
  have ht : t ∈ unitarySU ℓ f K r := (mem_unitarySU_iff h).mpr ⟨hdet', ug87_diag_unitary h hd⟩
  exact ⟨t, hT t ht ⟨d, rfl⟩, rfl⟩

theorem exists_fixer_of_fermat (h : UnitaryFieldData ℓ f K) {r : ℕ} [Fact r.Prime] (hr : 17 ≤ r)
    (hrq : ℓ ^ f + 1 = r) {ζ : K} (hζ : IsPrimitiveRoot ζ r)
    (H : Subgroup (GL (Fin r) K))
    (hT : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) = diagonal t) → g ∈ H)
    (hTw : ∀ g ∈ unitarySU ℓ f K r, (∃ t, (g : Matrix (Fin r) (Fin r) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin r) (Fin r) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin r) (Fin r) K) := by
  have hrodd : Odd r := (Fact.out : r.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hℓ : ℓ = 2 := by
    by_contra hne
    have hoddℓ : Odd ℓ := h.prime.eq_two_or_odd'.resolve_left hne
    have hevenr : Even r := by
      rw [← hrq]
      exact hoddℓ.pow.add_one
    exact (Nat.not_even_iff_odd.mpr hrodd) hevenr
  subst hℓ
  have hf : 4 ≤ f := by
    by_contra hlt
    have h1 : 2 ^ f ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 8 ∣ 2 ^ f := by
    have : 2 ^ 3 ∣ 2 ^ f := pow_dvd_pow 2 (by omega)
    simpa using this
  have hr8 : r % 8 = 1 := by omega
  haveI : CharP K 2 := h.charP
  have hrq' : r ∣ 2 ^ f + 1 := hrq ▸ dvd_refl r
  obtain ⟨t, s, ht, hs, htdet, hsdet, hy0, hmono⟩ := ug87_core hr8 hζ
  obtain ⟨γ, hγH, hγ⟩ := ug86_exists_mem_fourier h hζ (by omega) hrq' H hTw
    (d := t) (fun k => by rw [hrq]; exact ht k) htdet
  obtain ⟨t', ht'H, ht'⟩ := ug87_exists_mem_diag h H hT (d := s)
    (fun k => by rw [hrq]; exact hs k) hsdet
  have hgmat : ((γ * t' * γ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹ * diagonal s *
        (heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hγ, ht']
  refine ⟨γ * t' * γ, H.mul_mem (H.mul_mem hγH ht'H) hγH, ?_, ?_⟩
  · intro i hi
    rw [hgmat]
    exact hy0 i hi
  · rw [hgmat]
    exact hmono

end CFSG.LieType.SeitzGeneration

end
