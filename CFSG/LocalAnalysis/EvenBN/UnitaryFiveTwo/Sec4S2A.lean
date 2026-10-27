module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S1C

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

@[expose] def cenMod {G : Type*} [Group G] (N M : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ normalizer (N : Set G) ∧ ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ N}
  one_mem' := ⟨one_mem _, fun m _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxa⟩ ⟨hy, hya⟩
    refine ⟨mul_mem hx hy, fun m hm => ?_⟩
    have e : x * y * m * (x * y)⁻¹ * m⁻¹ =
        x * (y * m * y⁻¹ * m⁻¹) * x⁻¹ * (x * m * x⁻¹ * m⁻¹) := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 hx _).1 (hya m hm)) (hxa m hm)
  inv_mem' := by
    rintro x ⟨hx, hxa⟩
    refine ⟨inv_mem hx, fun m hm => ?_⟩
    have e : x⁻¹ * m * x⁻¹⁻¹ * m⁻¹ = x⁻¹ * (x * m * x⁻¹ * m⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hx) _).1 (inv_mem (hxa m hm))

theorem cenMod_anti {G : Type*} [Group G] {N M M' : Subgroup G} (h : M' ≤ M) :
    cenMod N M ≤ cenMod N M' := fun _ hx => ⟨hx.1, fun m hm => hx.2 m (h hm)⟩

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem S_le_NHA₂ (h : d.Hyp) : d.S ≤ normalizer (d.A₂ : Set G) ⊓ d.H := fun s hs =>
  Subgroup.mem_inf.2 ⟨normalizer_S_le_normalizer_A₂ (d.S.le_normalizer hs),
    h.L_le_H (d.pull_le_L _ hs)⟩

theorem R_le_NHA₂ (h : d.Hyp) : d.R ≤ normalizer (d.A₂ : Set G) ⊓ d.H :=
  sup_le h.S_le_NHA₂ (zpowers_le.2 h.t_mem_NHA₂)

theorem NHS_le_NHA₂ (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.A₂ : Set G) ⊓ d.H := fun _ hg =>
  Subgroup.mem_inf.2 ⟨normalizer_S_le_normalizer_A₂ (Subgroup.mem_inf.1 hg).1,
    (Subgroup.mem_inf.1 hg).2⟩

theorem R_le_XC₀ (h : d.Hyp) : d.R ≤ d.XC₀ := h.R_le_NHA₂.trans h.NHA₂_le_XC₀

theorem NHS_le_XC₀ (h : d.Hyp) : normalizer (d.S : Set G) ⊓ d.H ≤ d.XC₀ :=
  h.NHS_le_NHA₂.trans h.NHA₂_le_XC₀

theorem R₃_le_XC₀ (h : d.Hyp) : d.R₃ ≤ d.XC₀ := by
  rw [h.R₃_eq]
  exact sup_le (sup_le h.R_le_XC₀ h.Y_le_XC₀) h.D₃_le_XC₀

theorem XC₀_le_normalizer_D₂ (h : d.Hyp) : d.XC₀ ≤ normalizer (d.D₂ : Set G) := fun _ hx =>
  mem_normalizer_fintype fun _ hu => h.conj_mem_D₂ hx hu

theorem R₃_le_normalizer_D₂ (h : d.Hyp) : d.R₃ ≤ normalizer (d.D₂ : Set G) :=
  h.R₃_le_XC₀.trans h.XC₀_le_normalizer_D₂

theorem R_le_normalizer_D₂ (h : d.Hyp) : d.R ≤ normalizer (d.D₂ : Set G) :=
  h.R_le_XC₀.trans h.XC₀_le_normalizer_D₂

theorem isPGroup_R₃_sup_D₂ (h : d.Hyp) : IsPGroup 2 (d.R₃ ⊔ d.D₂ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isPGroup_oTwo _).to_sup_of_normal_right' (IsPGroup.of_card h.card_D₂)
    h.R₃_le_normalizer_D₂

theorem D₃_conj_X₄_mem_Y (h : d.Hyp) {u a : G} (hu : u ∈ d.D₃) (ha : a ∈ d.X₄) :
    u * a * u⁻¹ * a⁻¹ ∈ d.Y := by
  have huU := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).2).1
  have haA : a⁻¹ ∈ d.A₁ := inv_mem (d.pull_mono X₄sub_le_A₁sub' ha)
  have := ((mem_UA₁_iff.1 huU).2 a⁻¹ haA).1
  have h2 := d.W_le_Y (inv_mem this)
  rwa [show ((a⁻¹)⁻¹ * u * a⁻¹ * u⁻¹)⁻¹ = u * a * u⁻¹ * a⁻¹ by group] at h2

theorem R_le_cenMod (h : d.Hyp) : d.R ≤ cenMod d.Y d.X₄ := by
  refine sup_le (fun s hs => ⟨h.S_le_normalizer_Y hs, fun a ha => ?_⟩)
    (zpowers_le.2 ⟨h.R_le_normalizer_Y (mem_sup_right (mem_zpowers _)), fun a ha => ?_⟩)
  · exact h.F_le_Y (S_comm_mod_F hs (mem_sup_left ha))
  · have hat : a * d.t = d.t * a := h.t_comm_of_mem_L (d.pull_le_L _ ha)
    have e : d.t * a * d.t⁻¹ * a⁻¹ = 1 := by
      rw [← hat]
      group
    rw [e]
    exact one_mem _

theorem Y_le_cenMod (h : d.Hyp) : d.Y ≤ cenMod d.Y d.X₄ := fun y hy =>
  ⟨(d.Y).le_normalizer hy, fun a ha => by
    have e := Y_comm_D₀ hy (h.A₂_le_D₀ (d.pull_mono X₄sub_le_A₂sub ha))
    rw [e]
    group
    exact one_mem _⟩

theorem D₃_le_cenMod (h : d.Hyp) : d.D₃ ≤ cenMod d.Y d.X₄ := fun u hu =>
  ⟨h.XC₀_le_normalizer_Y (h.D₃_le_XC₀ hu), fun a ha => h.D₃_conj_X₄_mem_Y hu ha⟩

theorem R₃_le_cenMod (h : d.Hyp) : d.R₃ ≤ cenMod d.Y d.X₄ := by
  rw [h.R₃_eq]
  exact sup_le (sup_le h.R_le_cenMod h.Y_le_cenMod) h.D₃_le_cenMod

theorem D₂_le_cenMod_D₀ (h : d.Hyp) : d.D₂ ≤ cenMod d.Y d.D₀ := fun u hu =>
  ⟨h.XC₀_le_normalizer_Y (D₂_le_XC₀ hu), fun a ha => by
    have := inv_mem ((mem_UD₀_iff.1 (D₂_le_UD₀ hu)).2 a⁻¹ (inv_mem ha)).1
    rwa [show ((a⁻¹)⁻¹ * u * a⁻¹ * u⁻¹)⁻¹ = u * a * u⁻¹ * a⁻¹ by group] at this⟩

theorem D₂_le_cenMod (h : d.Hyp) : d.D₂ ≤ cenMod d.Y d.X₄ :=
  (cenMod_anti (d.pull_mono X₄sub_le_A₂sub |>.trans h.A₂_le_D₀)) |>.trans' h.D₂_le_cenMod_D₀

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
