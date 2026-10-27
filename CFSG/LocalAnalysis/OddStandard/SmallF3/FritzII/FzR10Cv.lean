module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRTr

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzRNum t x₁ x₂ lam rho tau T₂)

private theorem fzrAux_f_zero (f : ℕ → Bool)
    (hadd : ∀ x y, x < 512 → y < 512 → f ((fzrPar D).e x y) = xor (f x) (f y)) :
    f 0 = false := by
  have h := hadd 0 0 (by norm_num) (by norm_num)
  rw [show (fzrPar D).e 0 0 = 0 from (fzrPar_mul D).one_l 0 (by norm_num)] at h
  cases h0 : f 0 <;> simp [h0] at h ⊢

private noncomputable def fzrKer (f : ℕ → Bool)
    (hadd : ∀ x y, x < 512 → y < 512 → f ((fzrPar D).e x y) = xor (f x) (f y)) :
    Subgroup G where
  carrier := {g | ∃ n, n < 512 ∧ f n = false ∧ fzrMu D n = g}
  one_mem' := by
    refine ⟨0, by norm_num, fzrAux_f_zero D f hadd, ?_⟩
    exact fzrMu_zero D
  mul_mem' := by
    rintro g₁ g₂ ⟨n₁, hn₁, hf₁, hmu₁⟩ ⟨n₂, hn₂, hf₂, hmu₂⟩
    refine ⟨(fzrPar D).e n₁ n₂, (fzrPar_mul D).lt n₁ n₂ hn₁ hn₂, ?_, ?_⟩
    · rw [hadd n₁ n₂ hn₁ hn₂, hf₁, hf₂]
      rfl
    · rw [fzrMu_mul D hn₁ hn₂, hmu₁, hmu₂]
  inv_mem' := by
    rintro g ⟨n, hn, hfn, hmu⟩
    subst hmu
    have hgT : fzrMu D n ∈ T₂ := fzrMu_mem D n
    obtain ⟨k, hk, hkmu⟩ := fzrMu_surj D (T₂.inv_mem hgT)
    have he : (fzrPar D).e n k = 0 := by
      apply fzrMu_inj D ((fzrPar_mul D).lt n k hn hk) (by norm_num : 0 < 512)
      rw [fzrMu_mul D hn hk, hkmu, fzrMu_zero]
      group
    have h0 := fzrAux_f_zero D f hadd
    have hh := hadd n k hn hk
    rw [he, h0, hfn] at hh
    refine ⟨k, hk, ?_, hkmu⟩
    cases hfk : f k <;> simp [hfk] at hh ⊢

private theorem fzrAux_mem_ker (f : ℕ → Bool)
    (hadd : ∀ x y, x < 512 → y < 512 → f ((fzrPar D).e x y) = xor (f x) (f y))
    {g : G} : g ∈ fzrKer D f hadd ↔
      ∃ n, n < 512 ∧ f n = false ∧ fzrMu D n = g := Iff.rfl

private theorem fzrAux_mu_mem_iff (f : ℕ → Bool)
    (hadd : ∀ x y, x < 512 → y < 512 → f ((fzrPar D).e x y) = xor (f x) (f y))
    {n : ℕ} (hn : n < 512) : fzrMu D n ∈ fzrKer D f hadd ↔ f n = false := by
  rw [fzrAux_mem_ker]
  constructor
  · rintro ⟨m, hm, hfm, hmu⟩
    have hmn : m = n := fzrMu_inj D hm hn hmu
    rwa [hmn] at hfm
  · intro hfn
    exact ⟨n, hn, hfn, rfl⟩

private theorem fzrAux_ker_le (f : ℕ → Bool)
    (hadd : ∀ x y, x < 512 → y < 512 → f ((fzrPar D).e x y) = xor (f x) (f y)) :
    fzrKer D f hadd ≤ T₂ := by
  rintro g ⟨n, hn, hf, rfl⟩
  exact fzrMu_mem D n

private theorem fzrAux_relIndex (f : ℕ → Bool)
    (hadd : ∀ x y, x < 512 → y < 512 → f ((fzrPar D).e x y) = xor (f x) (f y))
    (hf : f (fzrPar D).tI = true) : (fzrKer D f hadd).relIndex T₂ = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, D.t_mem, ?_⟩
  intro b hb
  obtain ⟨n, hn, hmu⟩ := fzrMu_surj D hb
  have hbt : b * t = fzrMu D ((fzrPar D).e n 64) := by
    rw [fzrMu_mul D hn (by norm_num)]
    rw [hmu, fzrMu_tI D]
  have hbM : b ∈ fzrKer D f hadd ↔ f n = false := by
    rw [← hmu]
    exact fzrAux_mu_mem_iff D f hadd hn
  have hbtM : b * t ∈ fzrKer D f hadd ↔ f ((fzrPar D).e n 64) = false := by
    rw [hbt]
    exact fzrAux_mu_mem_iff D f hadd ((fzrPar_mul D).lt n 64 hn (by norm_num))
  rw [hbM, hbtM, hadd n 64 hn (by norm_num)]
  rw [(fzrPar_nums D).1] at hf
  rw [hf]
  cases hn' : f n <;> simp [hn', xor_def]

theorem fzr_th_cover [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) (hT : FzSylow T₂)
    (f : ℕ → Bool)
    (hadd : ∀ x y, x < 512 → y < 512 → f ((fzrPar D).e x y) = xor (f x) (f y))
    (hf : f (fzrPar D).tI = true) : ∃ x, x < 512 ∧ fzrTh D x ∧ f x = false := by
  have hMT : fzrKer D f hadd ≤ T₂ := fzrAux_ker_le D f hadd
  have hM : (fzrKer D f hadd).relIndex T₂ = 2 := fzrAux_relIndex D f hadd hf
  have htsq : t * t = 1 := by
    rw [← pow_two]
    exact D.t_sq
  obtain ⟨x, hxM⟩ := fzr_transfer (fzr_nonabelian_of_wreath h.wreath) hT hMT hM
    (g := t) D.t_mem htsq
  rw [fzrAux_mem_ker] at hxM
  obtain ⟨n, hn, hfn, hmu⟩ := hxM
  refine ⟨n, hn, ?_⟩
  refine ⟨⟨hn, ?_⟩, hfn⟩
  refine ⟨x⁻¹, ?_⟩
  rw [hmu]
  group

end CFSG.OddStandard.SmallF3.FritzII

