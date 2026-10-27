module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmcInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.GH74.Uniqueness.Bender

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmc_outer_card {x : G} (hxS₂ : x ∈ swapS₂ P U T) (hx2 : x ^ 2 = 1)
    (hxt : x * t * x⁻¹ = w)
    (hout : ¬ ∃ k ∈ L ⊓ centralizer ({w} : Set G), ∀ y ∈ L ⊓ centralizer ({w} : Set G),
      x * y * x⁻¹ = k * y * k⁻¹) :
    ∃ m : ℕ, f = 2 * m ∧
      Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 ^ m := by
  obtain ⟨-, -, hB, hA₁K, -⟩ := hW.gmc_K_facts
  obtain ⟨-, -, -, -, -, hA₁2, -⟩ := hW.step.start.facts_of_card_sylow hW.step.card_sylow
  set K := L ⊓ centralizer ({w} : Set G) with hKdef
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hxN : x ∈ normalizer (K : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hW.gmc_conj_K hxS₂ hx2 hxt hy, fun hy => ?_⟩
    have h1 := hW.gmc_conj_K hxS₂ hx2 hxt hy
    rwa [show x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ by group, hxx, one_mul,
      inv_one, mul_one] at h1
  set α : MulAut K := K.normalizerMonoidHom ⟨x, hxN⟩ with hαdef
  have hα : ∀ y : K, ((α y : K) : G) = x * y * x⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨x, hxN⟩ y
  have hαα : α * α = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hα, hα]
    calc x * (x * (y : G) * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hxx]; group
  have hαout : ¬ ∃ g : K, ∀ y : K, α y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hout ⟨g, g.2, fun y hy => ?_⟩
    have h1 := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hα] at h1
    simpa using h1
  obtain ⟨m, hm, ⟨e⟩, -⟩ := hB.fixed_linear α hαα hαout
  refine ⟨m, hm, ?_⟩
  have hm1 : 1 ≤ m := by have := hW.step.start.two_le; omega
  set C := szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) with hCdef
  have hCK : C ≤ K := inf_le_left.trans hA₁K
  have hfix : ∀ c : C, α ⟨(c : G), hCK c.2⟩ = ⟨(c : G), hCK c.2⟩ := by
    intro c
    apply Subtype.ext
    rw [hα]
    have hcx := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
    calc x * (c : G) * x⁻¹ = (c : G) * x * x⁻¹ := by rw [hcx]
      _ = c := by group
  let ψ : C →* autFixed α :=
    { toFun := fun c => ⟨⟨(c : G), hCK c.2⟩, mem_autFixed_iff.mpr (hfix c)⟩
      map_one' := Subtype.ext (Subtype.ext rfl)
      map_mul' := fun a b => Subtype.ext (Subtype.ext rfl) }
  have hψ : Function.Injective ψ := fun a b hab =>
    Subtype.ext (congrArg (fun z : autFixed α => ((z : K) : G)) hab)
  let φ := e.toMonoidHom.comp ψ
  have hφ : Function.Injective φ := e.injective.comp hψ
  have hsq : ∀ z ∈ φ.range, z * z = 1 := by
    rintro _ ⟨c, rfl⟩
    rw [← map_mul]
    have hcc : c * c = 1 := Subtype.ext (by
      change (c : G) * (c : G) = 1
      rw [← sq]
      exact hA₁2 _ (mem_inf.mp c.2).1)
    rw [hcc, map_one]
  have h1 := card_le_of_sq_eq_one_psl2 hm1 φ.range hsq
  rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h1

end U3C1OuterSwapHigh

@[expose] def U3C1GmcRootInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
        ∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∉ U ⊔ T →
          (g * t * g⁻¹) * t * (g * t * g⁻¹)⁻¹ = w →
          (¬ ∃ k ∈ L ⊓ centralizer ({w} : Set G), ∀ y ∈ L ⊓ centralizer ({w} : Set G),
              (g * t * g⁻¹) * y * (g * t * g⁻¹)⁻¹ = k * y * k⁻¹) →
            ∀ m : ℕ, f = 2 * m →
              Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) ≤
                2 ^ m → False

theorem u3C1GmcInnerInput_of_root (hR : U3C1GmcRootInput) :
    U3C1GmcInnerInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW h1 h2 g hg hgS hgt
  by_contra hout
  have hx2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [show (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ by rw [sq, sq]; group,
      hW.step.start.sq_eq_one]
    group
  obtain ⟨m, hm, hcard⟩ := hW.gmc_outer_card hg hx2 hgt hout
  exact hR G L f t T R₂ D d V U U₁ w s P hW h1 h2 g hg hgS hgt hout m hm hcard

theorem u3C1GmsFusionInput_of_root (hR : U3C1GmcRootInput) :
    U3C1GmsFusionInput :=
  u3C1GmsFusionInput_of_inner (u3C1GmcInnerInput_of_root hR)

end CFSG.SeitzReduction.RankOne
