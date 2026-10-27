module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Fun
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Cent

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzRNum t x₁ x₂ lam rho tau T₂)

open Classical in
theorem fzr_card_nums {H₁ : Subgroup G} (hH₁ : H₁ ≤ T₂) :
    ((Finset.range 512).filter fun n => fzrMu D n ∈ H₁).card = Nat.card H₁ := by
  classical
  set s : Finset ℕ := (Finset.range 512).filter fun n => fzrMu D n ∈ H₁ with hs
  have hmem : ∀ n, n ∈ s ↔ n < 512 ∧ fzrMu D n ∈ H₁ := by
    intro n
    rw [hs, Finset.mem_filter, Finset.mem_range]
  let f : ↥s → H₁ := fun x => ⟨fzrMu D x.1, ((hmem x.1).mp x.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : fzrMu D x.1 = fzrMu D y.1 := congrArg Subtype.val hxy
      have hx : x.1 < 512 := ((hmem x.1).mp x.2).1
      have hy : y.1 < 512 := ((hmem y.1).mp y.2).1
      exact Subtype.ext (fzrMu_inj D hx hy h1)
    · intro y
      obtain ⟨n, hn, hmu⟩ := fzrMu_surj D (hH₁ y.2)
      refine ⟨⟨n, (hmem n).mpr ⟨hn, ?_⟩⟩, ?_⟩
      · rw [hmu]; exact y.2
      · ext; exact hmu
  have hcard : s.card = Nat.card H₁ := by
    calc s.card = Nat.card s := (Nat.card_eq_finsetCard s).symm
      _ = Nat.card H₁ := Nat.card_congr (Equiv.ofBijective f hf)
  rwa [hs] at hcard

theorem fzr_th_prof (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    (hT2 : IsFzT2 t x₁ x₂ S T₂) {u : ℕ} (hu : fzrTh D u)
    (hcard : 32 ≤ (fzrCent (fzrPar D) u).card) :
    ∃ f₀ f₁ : ℕ → Bool,
      (∀ x y, fzrS (fzrPar D) x → fzrS (fzrPar D) y →
        f₀ ((fzrPar D).e x y) = xor (f₀ x) (f₀ y)) ∧
      (∀ x y, fzrS (fzrPar D) x → f₀ x = false → fzrS (fzrPar D) y → f₀ y = false →
        f₁ ((fzrPar D).e x y) = xor (f₁ x) (f₁ y)) ∧
      f₀ (fzrPar D).tI = false ∧ f₁ (fzrPar D).tI = false ∧
      (fzrH (fzrPar D) f₀ f₁).card = (fzrCent (fzrPar D) u).card ∧
      ∀ k, ((fzrH (fzrPar D) f₀ f₁).filter fun x => fzrKey (fzrPar D) (fzrTh D) x = k).card =
        ((fzrCent (fzrPar D) u).filter fun x => fzrKey (fzrPar D) (fzrTh D) x = k).card := by
  classical
  obtain ⟨H₁, ψ, hH₁S, htH, hbij, hkey⟩ := fzr_cent_embed D h hT2 hu
  have hTset : (↑((Finset.range 512).filter fun n => fzrMu D n ∈ H₁) : Set ℕ) =
      {n | n < 512 ∧ fzrMu D n ∈ H₁} := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
  have hbij' : Set.BijOn ψ ↑(fzrCent (fzrPar D) u)
      ↑((Finset.range 512).filter fun n => fzrMu D n ∈ H₁) := by
    rw [hTset]; exact hbij
  have hcardT : ((Finset.range 512).filter fun n => fzrMu D n ∈ H₁).card = Nat.card H₁ :=
    fzr_card_nums D (hH₁S.trans hT2.S_le)
  have hCent : (fzrCent (fzrPar D) u).card = Nat.card H₁ := by
    have h1 := Finset.card_nbij ψ hbij'.mapsTo hbij'.injOn hbij'.surjOn
    rwa [hcardT] at h1
  have hcardH : 32 ≤ Nat.card H₁ := hCent ▸ hcard
  have hS : Nat.card S = 128 := by
    rw [h.card_S, hK]; norm_num
  have hrel : H₁.relIndex S * Nat.card H₁ = Nat.card S := by
    have h1 := Subgroup.relIndex_mul_card (H := H₁) (K := S)
    rwa [inf_eq_left.mpr hH₁S] at h1
  have hidx : H₁.relIndex S ≤ 4 := by
    have hle : H₁.relIndex S * 32 ≤ 128 := by
      calc H₁.relIndex S * 32 ≤ H₁.relIndex S * Nat.card H₁ := Nat.mul_le_mul_left _ hcardH
        _ = Nat.card S := hrel
        _ = 128 := hS
    omega
  obtain ⟨f₀, f₁, hf₀, hf₁, ht₀, ht₁, hmem⟩ := fzr_funcs D h hT2 hH₁S htH hidx
  have hH_eq : fzrH (fzrPar D) f₀ f₁ =
      (Finset.range 512).filter fun n => fzrMu D n ∈ H₁ := by
    rw [fzrH]
    apply Finset.filter_congr
    intro n hn
    rw [Finset.mem_range] at hn
    constructor
    · rintro ⟨hs, h0, h1⟩
      exact (hmem n hs).mp ⟨h0, h1⟩
    · intro hH
      have hs : fzrS (fzrPar D) n := (fzr_S_iff D h hT2 hn).mpr (hH₁S hH)
      exact ⟨hs, (hmem n hs).mpr hH⟩
  have hHcard : (fzrH (fzrPar D) f₀ f₁).card = Nat.card H₁ := by
    rw [hH_eq, hcardT]
  refine ⟨f₀, f₁, hf₀, hf₁, ht₀, ht₁, hHcard.trans hCent.symm, ?_⟩
  intro k
  have hfil : Set.BijOn ψ
      ↑((fzrCent (fzrPar D) u).filter fun x => fzrKey (fzrPar D) (fzrTh D) x = k)
      ↑((fzrH (fzrPar D) f₀ f₁).filter fun x => fzrKey (fzrPar D) (fzrTh D) x = k) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨by rw [hH_eq]; exact hbij'.mapsTo hx.1, by rw [hkey x hx.1, hx.2]⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      exact hbij'.injOn hx.1 hy.1 hxy
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy
      obtain ⟨x, hx, hxy⟩ := hbij'.surjOn (by rw [← hH_eq]; exact hy.1)
      rw [Finset.mem_coe] at hx
      refine ⟨x, ?_, hxy⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hx, by rw [← hkey x hx, hxy, hy.2]⟩
  exact (Finset.card_nbij ψ hfil.mapsTo hfil.injOn hfil.surjOn).symm

end CFSG.OddStandard.SmallF3.FritzII
