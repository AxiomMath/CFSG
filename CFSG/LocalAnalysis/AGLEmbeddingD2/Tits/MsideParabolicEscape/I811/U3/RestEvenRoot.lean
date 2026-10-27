module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Even

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

local notation "𝔾" => SU (unitaryInvolution F 2 f) 3
local notation "𝔤₀" => g0SU (unitaryInvolution F 2 f)
local notation "𝔰₁" => s1SU (unitaryInvolution F 2 f)

theorem rootU_le_conj_of_not_two_dvd_index (hF : Nat.card F = (2 ^ f) ^ 2)
    (hq3 : 2 ^ f % 3 = 1) {ω : Fˣ} (hω : orderOf ω = 3)
    {W : Subgroup (SU (unitaryInvolution F 2 f) 3)}
    (hNW : Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) :
      Subgroup (SU (unitaryInvolution F 2 f) 3)) : Set (SU (unitaryInvolution F 2 f) 3)) ≤ W)
    (hodd : ¬ 2 ∣ W.index) :
    rootU hF ≤ W.map (MulAut.conj (g0SU (unitaryInvolution F 2 f))⁻¹).toMonoidHom ∧
      ∀ μ ∈ rootsOfUnity (2 ^ f + 1) F,
        tSU hF μ ∈ W.map (MulAut.conj (g0SU (unitaryInvolution F 2 f))⁻¹).toMonoidHom := by
  classical
  have hω' : ω ^ (2 ^ f) = ω := pow_eq_self_of_orderOf_three hω hq3
  have hsW : (sSU : 𝔾) ∈ W := by
    refine hNW (mem_normalizer_zpowers_of_inv sSU_mul_self ?_)
    rw [sSU_conj_tSU, hω', map_inv]
  have hZW : ∀ μ ∈ rootsOfUnity (2 ^ f + 1) F, tSU hF μ ∈ W := by
    intro μ _
    refine hNW (mem_normalizer_zpowers_of_commute ?_)
    show tSU hF μ * tSU hF ω = tSU hF ω * tSU hF μ
    rw [← map_mul, ← map_mul, mul_comm]
  have hconj : ∀ y : 𝔾, (MulAut.conj 𝔤₀⁻¹).toMonoidHom y = 𝔤₀⁻¹ * y * 𝔤₀ := by
    intro y
    simp
  have hidx : (W.map (MulAut.conj 𝔤₀⁻¹).toMonoidHom).index = W.index :=
    Subgroup.index_map_equiv W (MulAut.conj 𝔤₀⁻¹)
  generalize hW' : W.map (MulAut.conj 𝔤₀⁻¹).toMonoidHom = W'
  have hs₁ : 𝔰₁ ∈ W' := by
    rw [← hW']
    exact ⟨sSU, hsW, by rw [hconj, s1_eq_conj]⟩
  have hZW' : ∀ μ ∈ rootsOfUnity (2 ^ f + 1) F, tSU hF μ ∈ W' := by
    intro μ hμ
    rw [← hW']
    refine ⟨tSU hF μ, hZW μ hμ, ?_⟩
    rw [hconj, mul_assoc, ← g0_comm_tSU hF hμ, inv_mul_cancel_left]
  have hs₁sq : 𝔰₁ * 𝔰₁ = 1 := mat_injective (by rw [map_mul, mat_s1SU, s1Mat_mul_self, map_one])
  have hs₁ne : 𝔰₁ ≠ 1 := by
    intro h
    have h' := congrArg (fun y : 𝔾 => mat (unitaryInvolution F 2 f) 3 y 0 2) h
    simp only [mat_s1SU, map_one] at h'
    simp [s1Mat] at h'
  have hs₁2 : IsPGroup 2 (Subgroup.zpowers (⟨𝔰₁, hs₁⟩ : W')) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by rw [SubgroupClass.coe_pow, pow_two]; exact hs₁sq)
    · intro h
      exact hs₁ne (congrArg Subtype.val h)
  obtain ⟨P₀, hP₀⟩ := hs₁2.exists_le_sylow
  have hP2 : IsPGroup 2 ((P₀ : Subgroup W').map W'.subtype) := P₀.isPGroup'.map _
  have hPs : 𝔰₁ ∈ (P₀ : Subgroup W').map W'.subtype :=
    ⟨⟨𝔰₁, hs₁⟩, hP₀ (Subgroup.mem_zpowers _), rfl⟩
  have hPU : (P₀ : Subgroup W').map W'.subtype ≤ rootU hF := le_rootU_of_mem hF hP2 hPs
  have hPW : (P₀ : Subgroup W').map W'.subtype ≤ W' := Subgroup.map_subtype_le _
  have hS := eq_top_or_ca_eq_zero (p := 2) hF hq3 (S := W' ⊓ rootU hF) inf_le_right
    fun μ hμ x hx => ⟨W'.mul_mem (W'.mul_mem (hZW' μ hμ) hx.1) (W'.inv_mem (hZW' μ hμ)),
      tSU_conj_mem_rootU hF μ hx.2⟩
  rcases hS with hS | hS
  ·
    exact ⟨by rw [← hS]; exact inf_le_left, hZW'⟩
  ·
    exfalso
    have hcardS : Nat.card (W' ⊓ rootU hF : Subgroup 𝔾) ≤ 2 ^ f := by
      rw [← card_traceZero (p := 2) hF]
      refine Nat.card_le_card_of_injective
        (fun x : (W' ⊓ rootU hF : Subgroup 𝔾) =>
          (⟨cb (x : 𝔾), cb_add_of_ca_eq_zero hF x.2.2 (hS _ x.2)⟩ :
            traceZero (unitaryInvolution F 2 f))) ?_
      intro x y hxy
      have hb : cb (x : 𝔾) = cb (y : 𝔾) := congrArg Subtype.val hxy
      exact Subtype.ext (eq_of_ca_cb hF x.2.2 y.2.2 ((hS _ x.2).trans (hS _ y.2).symm) hb)
    have hPS : Nat.card ((P₀ : Subgroup W').map W'.subtype) ≤ 2 ^ f :=
      (Subgroup.card_le_of_le (le_inf hPW hPU)).trans hcardS
    have hPcard : Nat.card ((P₀ : Subgroup W').map W'.subtype) =
        2 ^ (Nat.card W').factorization 2 := by
      rw [Subgroup.card_map_of_injective W'.subtype_injective]
      exact P₀.card_eq_multiplicity
    have hv : (Nat.card W').factorization 2 ≤ f := by
      rw [hPcard] at hPS
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hPS
    have hf2 := two_le_f hF hq3
    have hdvd := two_pow_dvd_of_mul (N := Nat.card 𝔾) (a := Nat.card W') (b := W'.index)
      (n := 3 * f) (v := f)
      W'.card_mul_index.symm Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite
      (by rw [card_SU_even hF]; exact factorization_two_pow_mul_odd (odd_index_factor hF))
      hv (by omega)
    have h16 : 16 ∣ W'.index :=
      (Nat.pow_dvd_pow 2 (by omega : 4 ≤ 3 * f - f)).trans hdvd
    have hidx' : W'.index = W.index := hW' ▸ hidx
    exact hodd (hidx' ▸ (by norm_num : 2 ∣ 16).trans h16)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
