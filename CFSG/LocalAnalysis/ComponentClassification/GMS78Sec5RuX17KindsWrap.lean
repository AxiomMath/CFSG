module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModel
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCenter
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTrans

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

namespace RuKinds

theorem linApply_dCode_dCode : ∀ d e t : Fin 8,
    linApply (dCode d) (linApply (dCode e) t) = linApply (dCode (dMul d e)) t := by decide

theorem exists_dCode_inv : ∀ d : Fin 8, ∃ e : Fin 8, ∀ t : Fin 8,
    linApply (dCode e) (linApply (dCode d) t) = t := by decide

theorem linApply_dCode_zero : ∀ t : Fin 8, linApply (dCode 0) t = t := by decide

theorem linApply_dCode_one : ∀ d : Fin 8, linApply (dCode d) 1 = 1 := by decide

theorem exists_code_one : ∀ t : Fin 8, t ≠ 0 → ∃ r ∈ glList, linApply r 1 = t := by
  decide +kernel

theorem ppOf_one : 0 :: RuQCode.ppOf 1 = [0, 1, 2, 3] := by decide

end RuKinds

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem exists_sylowD8 :
    ∃ S₀ : Subgroup G, ∀ g, g ∈ S₀ ↔ g ∈ normalizer (R : Set G) ∧
      ∃ d : Fin 8, ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply (dCode d) (ν b) := by
  refine ⟨{ carrier := {g | g ∈ normalizer (R : Set G) ∧
              ∃ d : Fin 8, ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply (dCode d) (ν b)}
            mul_mem' := ?_
            one_mem' := ⟨one_mem _, 0, fun b _ => by rw [RuKinds.linApply_dCode_zero]; simp⟩
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro g h ⟨hg, d, hd⟩ ⟨hh, e, he⟩
    refine ⟨mul_mem hg hh, dMul d e, fun b hb => ?_⟩
    have hb' : h * b * h⁻¹ ∈ gmsA L T := hM.normA h hh b hb
    rw [show g * h * b * (g * h)⁻¹ = g * (h * b * h⁻¹) * g⁻¹ by group, hd _ hb', he b hb,
      RuKinds.linApply_dCode_dCode]
  · rintro g ⟨hg, d, hd⟩
    obtain ⟨e, he⟩ := RuKinds.exists_dCode_inv d
    refine ⟨inv_mem hg, e, fun b hb => ?_⟩
    have hb' : g⁻¹ * b * g⁻¹⁻¹ ∈ gmsA L T := hM.normA g⁻¹ (inv_mem hg) b hb
    have h1 := hd _ hb'
    rw [show g * (g⁻¹ * b * g⁻¹⁻¹) * g⁻¹ = b by group] at h1
    rw [h1, he]

omit hM in
theorem card_sylowD8 {ε : Bool} {Φ : ℕ × Fin 8 × Fin 8 → G} (hΦ : SModel L T R μ ν ε Φ)
    {S₀ : Subgroup G} (hS₀ : ∀ g, g ∈ S₀ ↔ g ∈ normalizer (R : Set G) ∧
      ∃ d : Fin 8, ∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply (dCode d) (ν b)) :
    Nat.card S₀ = 2 ^ 14 := by
  let ψ : Fin 256 × Fin 8 × Fin 8 → S₀ := fun q =>
    ⟨Φ (q.1.val, q.2.1, q.2.2), (hS₀ _).mpr ⟨hΦ.mem _, q.2.2, hΦ.code _⟩⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro ⟨c, t, d⟩ ⟨c', t', d'⟩ h
      have h1 := hΦ.inj (c.val, t, d) (c'.val, t', d') c.2 c'.2 (congrArg Subtype.val h)
      simp only [Prod.mk.injEq] at h1
      obtain ⟨hc, ht, hd⟩ := h1
      rw [Fin.ext hc, ht, hd]
    · rintro ⟨g, hg⟩
      obtain ⟨hgN, d, hd⟩ := (hS₀ g).mp hg
      obtain ⟨p, hp, -, hpg⟩ := hΦ.surj g hgN d hd
      exact ⟨(⟨p.1, hp⟩, p.2.1, p.2.2), Subtype.ext hpg⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ hψ), Nat.card_prod, Nat.card_prod, Nat.card_fin,
    Nat.card_fin]
  norm_num

end Sec3.SzR.MaskCoords

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem hkinds_of_core
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G)))
    (hcore : ∀ (μ : G → ℕ) (ν : G → Fin 8), MaskCoords L T R μ ν →
      ∀ (ε : Bool) (Φ : ℕ × Fin 8 × Fin 8 → G), SModel L T R μ ν ε Φ →
      ∀ h ∈ centralizer ({Φ (0, 1, 0)} : Set G), ∀ p : ℕ × Fin 8 × Fin 8, p.1 < 256 →
        Φ p = h * Φ (0, 2, 0) * h⁻¹ → Φ p ∈ R ∧ μ (Φ p) ∈ [0, 1, 2, 3]) :
    ∀ (μ : G → ℕ) (ν : G → Fin 8), MaskCoords L T R μ ν → ∀ f ∈ gmsA L T, f ≠ 1 →
      ∀ X : Subgroup G, (∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)) →
      ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ R ≤ S ∧ S ≤ normalizer (R : Set G) ∧
        S ≤ centralizer ({f} : Set G) ∧ X ≤ S ∧
        ∀ f₁ ∈ gmsA L T, f₁ ≠ 1 → f₁ ≠ f →
          ∀ h ∈ centralizer ({f} : Set G), h * f₁ * h⁻¹ ∈ S → h * f₁ * h⁻¹ ∈ X := by
  intro μ ν hM f hfA hf1 X hX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC := normalizer_inf_centralizer_eq hS h34 hR₂ h4 hCV
  have hidx := relIndex_normalizer_eq hS h34 hR₂ h4 hCV hNS
  obtain ⟨ε, Φ, hΦ⟩ := hM.exists_sModel hNC hidx
  obtain ⟨S₀, hS₀⟩ := hM.exists_sylowD8
  set f₀ := Φ (0, 1, 0) with hf₀
  have hf₀A : f₀ ∈ gmsA L T := hΦ.mem_A 1
  have hνf₀ : ν f₀ = 1 := hΦ.ν_eq 1
  have hf₁A : Φ (0, 2, 0) ∈ gmsA L T := hΦ.mem_A 2
  have hνf₁ : ν (Φ (0, 2, 0)) = 2 := hΦ.ν_eq 2
  have hcen : ∀ g ∈ normalizer (R : Set G), g * f₀ * g⁻¹ = f₀ →
      g ∈ centralizer ({f₀} : Set G) := fun g _ hgf => mem_centralizer_singleton_iff.mpr (by
    calc g * f₀ = g * f₀ * g⁻¹ * g := by group
      _ = f₀ * g := by rw [hgf])
  have hS₀N : S₀ ≤ normalizer (R : Set G) := fun g hg => ((hS₀ g).mp hg).1
  have hRS₀ : R ≤ S₀ := fun r hr => (hS₀ r).mpr ⟨le_normalizer hr, 0, fun b hb => by
    rw [RuKinds.linApply_dCode_zero, hM.central r hr b hb, mul_inv_cancel_right]⟩
  have hS₀C : S₀ ≤ centralizer ({f₀} : Set G) := fun g hg => by
    obtain ⟨hgN, e, he⟩ := (hS₀ g).mp hg
    exact hcen g hgN (hM.eq_of_ν_eq (hM.normA g hgN f₀ hf₀A) hf₀A
      (by rw [he f₀ hf₀A, hνf₀, RuKinds.linApply_dCode_one]))
  have hS₀card := MaskCoords.card_sylowD8 hΦ hS₀
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (normalizer (R : Set G))
  have hS₀Syl : IsSylowOf 2 S₀ (normalizer (R : Set G)) := isSylowOf_of_card hS₀N (by
    rw [hS₀card, ← card_sylow_normalizer hS h34 hR₂ h4 hCV hNS hP, hP.card_eq])
  have hS₀ST := isSylowOf_top_of_isSylowOf_normalizer hS h34 hR₂ h4 hCV hCe hCL hNS hS₀Syl
  have hk₀ : ∀ f₁ ∈ gmsA L T, f₁ ≠ 1 → f₁ ≠ f₀ → ∀ h ∈ centralizer ({f₀} : Set G),
      h * f₁ * h⁻¹ ∈ S₀ → h * f₁ * h⁻¹ ∈ R ∧ μ (h * f₁ * h⁻¹) ∈ 0 :: RuQCode.ppOf 1 := by
    intro f₁ hf₁A' hf₁1 hf₁f h hh hmem
    have hs0 : ν f₁ ≠ 0 := fun h0 => hf₁1 (hM.ν_inj f₁ hf₁A' h0)
    have hs1 : ν f₁ ≠ 1 := fun h0 => hf₁f (hM.eq_of_ν_eq hf₁A' hf₀A (by rw [h0, hνf₀]))
    obtain ⟨r, hr, hr1, hr2⟩ := RuQCode.exists_stab_code (t := 1) (by decide) (s₁ := 2)
      (s₂ := ν f₁) (by decide) (by decide) hs0 hs1
    obtain ⟨n, hnN, hnA, -⟩ := hM.exists_code_eq hNC hidx hr
    have hnf₀ : n * f₀ * n⁻¹ = f₀ :=
      hM.eq_of_ν_eq (hM.normA n hnN f₀ hf₀A) hf₀A (by rw [hnA f₀ hf₀A, hνf₀, hr1])
    have hnf₁ : n * Φ (0, 2, 0) * n⁻¹ = f₁ :=
      hM.eq_of_ν_eq (hM.normA n hnN _ hf₁A) hf₁A' (by rw [hnA _ hf₁A, hνf₁, hr2])
    have hhn : h * n ∈ centralizer ({f₀} : Set G) := mul_mem hh (hcen n hnN hnf₀)
    have he : h * f₁ * h⁻¹ = (h * n) * Φ (0, 2, 0) * (h * n)⁻¹ := by
      rw [← hnf₁]
      group
    obtain ⟨hgN, e, hcode⟩ := (hS₀ _).mp hmem
    obtain ⟨p, hp, -, hpg⟩ := hΦ.surj _ hgN e hcode
    obtain ⟨hpR, hpμ⟩ := hcore μ ν hM ε Φ hΦ (h * n) hhn p hp (hpg.trans he)
    rw [← hpg]
    exact ⟨hpR, RuKinds.ppOf_one ▸ hpμ⟩
  have hνf : ν f ≠ 0 := fun h0 => hf1 (hM.ν_inj f hfA h0)
  obtain ⟨r, hr, hr1⟩ := RuKinds.exists_code_one (ν f) hνf
  obtain ⟨g, hgN, hgA, hgR⟩ := hM.exists_code_eq hNC hidx hr
  have hgf : g * f₀ * g⁻¹ = f :=
    hM.eq_of_ν_eq (hM.normA g hgN f₀ hf₀A) hfA (by rw [hgA f₀ hf₀A, hνf₀, hr1])
  set S := S₀.map (MulAut.conj g).toMonoidHom with hSdef
  have hmemS : ∀ x, x ∈ S ↔ g⁻¹ * x * g ∈ S₀ := by
    intro x
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hgR' : ∀ x, x ∈ R ↔ g⁻¹ * x * g ∈ R := by
    intro x
    have h1 := (mem_normalizer_iff.mp (inv_mem hgN) x)
    simpa [mul_assoc] using h1
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine isSylowOf_of_card le_top ?_
    rw [hSdef, card_map_of_injective (MulAut.conj g).injective, hS₀ST.card_eq]
  ·
    intro x hx
    rw [hmemS]
    exact hRS₀ ((hgR' x).mp hx)
  ·
    intro x hx
    have h1 := hS₀N ((hmemS x).mp hx)
    have h2 := mul_mem (mul_mem hgN h1) (inv_mem hgN)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h2
  ·
    intro x hx
    have h1 := mem_centralizer_singleton_iff.mp (hS₀C ((hmemS x).mp hx))
    rw [mem_centralizer_singleton_iff, ← hgf]
    calc x * (g * f₀ * g⁻¹) = g * ((g⁻¹ * x * g) * f₀) * g⁻¹ := by group
      _ = g * (f₀ * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * f₀ * g⁻¹ * x := by group
  ·
    intro x hx
    rw [hmemS]
    exact hRS₀ ((hgR' x).mp ((hX x).mp hx).1)
  ·
    intro f₁ hf₁A' hf₁1 hf₁f h hh hmem
    have hf₁A'' : g⁻¹ * f₁ * g ∈ gmsA L T := by
      have := hM.normA g⁻¹ (inv_mem hgN) f₁ hf₁A'
      simpa using this
    have hf₁1' : g⁻¹ * f₁ * g ≠ 1 := fun h0 => hf₁1 (by
      calc f₁ = g * (g⁻¹ * f₁ * g) * g⁻¹ := by group
        _ = 1 := by rw [h0]; group)
    have hf₁f' : g⁻¹ * f₁ * g ≠ f₀ := fun h0 => hf₁f (by
      rw [← hgf, ← h0]
      group)
    have hh' : g⁻¹ * h * g ∈ centralizer ({f₀} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := mem_centralizer_singleton_iff.mp hh
      rw [← hgf] at h1
      calc g⁻¹ * h * g * f₀ = g⁻¹ * (h * (g * f₀ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * f₀ * g⁻¹) * h) * g := by rw [h1]
        _ = f₀ * (g⁻¹ * h * g) := by group
    have he : g⁻¹ * h * g * (g⁻¹ * f₁ * g) * (g⁻¹ * h * g)⁻¹ = g⁻¹ * (h * f₁ * h⁻¹) * g := by
      group
    obtain ⟨hwR, hwμ⟩ := hk₀ _ hf₁A'' hf₁1' hf₁f' _ hh' (by rw [he]; exact (hmemS _).mp hmem)
    rw [he] at hwR hwμ
    refine (hX _).mpr ⟨(hgR' _).mpr hwR, ?_⟩
    have hμ := hgR (g⁻¹ * (h * f₁ * h⁻¹) * g) hwR
    rw [show g * (g⁻¹ * (h * f₁ * h⁻¹) * g) * g⁻¹ = h * f₁ * h⁻¹ by group] at hμ
    rw [hμ]
    rcases List.mem_cons.mp hwμ with h0 | hpp
    · rw [h0, RuQCode.maskApply_zero]
      exact List.mem_cons_self
    · rw [← hr1]
      exact List.mem_cons_of_mem _ (RuQCode.ppOf_equiv hr hpp)

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
