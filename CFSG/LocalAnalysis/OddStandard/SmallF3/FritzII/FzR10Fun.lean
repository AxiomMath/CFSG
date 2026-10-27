module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRFu
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzRNum t x₁ x₂ lam rho tau T₂)

private theorem fzrAux_xor_decide (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (h : P ↔ (Q ↔ R)) :
    Bool.not (decide P) = Bool.xor (Bool.not (decide Q)) (Bool.not (decide R)) := by
  by_cases hq : Q <;> by_cases hr : R <;> by_cases hP : P <;>
    simp_all [Bool.decide_iff]

private theorem fzrAux_not_decide_eq_false {P : Prop} [Decidable P] :
    Bool.not (decide P) = false ↔ P := by
  by_cases h : P <;> simp [h]

theorem fzr_S_iff (h : Ctx t L S x₁ x₂ lam rho tau) (hT2 : IsFzT2 t x₁ x₂ S T₂) {n : ℕ}
    (hn : n < 512) : fzrS (fzrPar D) n ↔ fzrMu D n ∈ S := by
  have hP : (fzrPar D).tI = 64 := (fzrPar_nums D).1
  have hS_eq : T₂ ⊓ invCent t = S :=
    fzr_T2_inf_cent (fzr_isSylowOf_S h.toCtx0) hT2.isPGroup hT2.S_le
  have hmemT : fzrMu D n ∈ T₂ := fzrMu_mem D n
  have h64 : fzrMu D 64 = t := fzrMu_tI D
  have he_lt1 : (fzrPar D).e n 64 < 512 := (fzrPar_mul D).lt n 64 hn (by norm_num)
  have he_lt2 : (fzrPar D).e 64 n < 512 := (fzrPar_mul D).lt 64 n (by norm_num) hn
  have key : (fzrPar D).e n 64 = (fzrPar D).e 64 n ↔
      fzrMu D n * t = t * fzrMu D n := by
    constructor
    · intro he
      calc fzrMu D n * t = fzrMu D n * fzrMu D 64 := by rw [h64]
        _ = fzrMu D ((fzrPar D).e n 64) := (fzrMu_mul D hn (by norm_num)).symm
        _ = fzrMu D ((fzrPar D).e 64 n) := by rw [he]
        _ = fzrMu D 64 * fzrMu D n := fzrMu_mul D (by norm_num) hn
        _ = t * fzrMu D n := by rw [h64]
    · intro hc
      apply fzrMu_inj D he_lt1 he_lt2
      calc fzrMu D ((fzrPar D).e n 64) = fzrMu D n * fzrMu D 64 :=
            fzrMu_mul D hn (by norm_num)
        _ = fzrMu D n * t := by rw [h64]
        _ = t * fzrMu D n := hc
        _ = fzrMu D 64 * fzrMu D n := by rw [h64]
        _ = fzrMu D ((fzrPar D).e 64 n) := (fzrMu_mul D (by norm_num) hn).symm
  constructor
  · intro hs
    have he : (fzrPar D).e n 64 = (fzrPar D).e 64 n := by
      have h2 := hs.2
      rwa [hP] at h2
    have hc : fzrMu D n * t = t * fzrMu D n := key.mp he
    rw [← hS_eq]
    exact ⟨hmemT, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
  · intro hs
    rw [← hS_eq] at hs
    have hc : fzrMu D n * t = t * fzrMu D n :=
      Subgroup.mem_centralizer_singleton_iff.mp hs.2
    refine ⟨hn, ?_⟩
    rw [hP]
    exact key.mpr hc

theorem fzr_funcs (h : Ctx t L S x₁ x₂ lam rho tau) (hT2 : IsFzT2 t x₁ x₂ S T₂)
    {H₁ : Subgroup G} (hH₁S : H₁ ≤ S) (htH : t ∈ H₁) (hidx : H₁.relIndex S ≤ 4) :
    ∃ f₀ f₁ : ℕ → Bool,
      (∀ x y, fzrS (fzrPar D) x → fzrS (fzrPar D) y →
        f₀ ((fzrPar D).e x y) = xor (f₀ x) (f₀ y)) ∧
      (∀ x y, fzrS (fzrPar D) x → f₀ x = false → fzrS (fzrPar D) y → f₀ y = false →
        f₁ ((fzrPar D).e x y) = xor (f₁ x) (f₁ y)) ∧
      f₀ (fzrPar D).tI = false ∧ f₁ (fzrPar D).tI = false ∧
      ∀ n, fzrS (fzrPar D) n → (f₀ n = false ∧ f₁ n = false ↔ fzrMu D n ∈ H₁) := by
  classical
  obtain ⟨M, hH₁M, hMS, hMrel, hH₁Mrel⟩ := fzr_chain h.isPGroup hH₁S hidx
  have hdecM : ∀ {a b : G}, a ∈ S → b ∈ S →
      Bool.not (decide (a * b ∈ M)) =
        Bool.xor (Bool.not (decide (a ∈ M))) (Bool.not (decide (b ∈ M))) :=
    fun ha hb => fzrAux_xor_decide _ _ _ (fzr_mul_mem_iff hMS hMrel ha hb)
  have hdecH : ∀ {a b : G}, a ∈ M → b ∈ M →
      Bool.not (decide (a * b ∈ H₁)) =
        Bool.xor (Bool.not (decide (a ∈ H₁))) (Bool.not (decide (b ∈ H₁))) :=
    fun ha hb => fzrAux_xor_decide _ _ _ (fzr_mul_mem_iff hH₁M hH₁Mrel ha hb)
  refine ⟨fun n => Bool.not (decide (fzrMu D n ∈ M)),
    fun n => Bool.not (decide (fzrMu D n ∈ H₁)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    have hxS : fzrMu D x ∈ S := (fzr_S_iff D h hT2 hx.1).mp hx
    have hyS : fzrMu D y ∈ S := (fzr_S_iff D h hT2 hy.1).mp hy
    dsimp only
    rw [fzrMu_mul D hx.1 hy.1]
    exact hdecM hxS hyS
  · intro x y hx hfx hy hfy
    have hxS : fzrMu D x ∈ S := (fzr_S_iff D h hT2 hx.1).mp hx
    have hyS : fzrMu D y ∈ S := (fzr_S_iff D h hT2 hy.1).mp hy
    have hxM : fzrMu D x ∈ M := fzrAux_not_decide_eq_false.mp hfx
    have hyM : fzrMu D y ∈ M := fzrAux_not_decide_eq_false.mp hfy
    dsimp only
    rw [fzrMu_mul D hx.1 hy.1]
    exact hdecH hxM hyM
  · have htM : t ∈ M := hH₁M htH
    dsimp only
    rw [(fzrPar_nums D).1, fzrMu_tI D]
    simp [htM]
  · dsimp only
    rw [(fzrPar_nums D).1, fzrMu_tI D]
    simp [htH]
  · intro n _
    constructor
    · rintro ⟨-, hf1⟩
      exact fzrAux_not_decide_eq_false.mp hf1
    · intro hnH
      exact ⟨fzrAux_not_decide_eq_false.mpr (hH₁M hnH),
        fzrAux_not_decide_eq_false.mpr hnH⟩

end CFSG.OddStandard.SmallF3.FritzII
