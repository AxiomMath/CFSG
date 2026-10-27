module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseRepAbs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

@[expose] def KeyNormalizer : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
    1 ≤ Module.finrank (ZMod 2) W →
    ∀ (H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)),
      (∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) W),
        (∀ t ∈ S, IsF2Transvection t) ∧ H = Subgroup.closure S) →
      (∀ U : Submodule (ZMod 2) W,
        (∀ g ∈ H, ∀ u ∈ U, (g : W →ₗ[ZMod 2] W) u ∈ U) → U = ⊥ ∨ U = ⊤) →
      L ≤ H → L.relIndex H = 2 → ⁅L, L⁆ = L → L ≠ ⊥ →
      ∀ g ∈ Subgroup.normalizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)), g ∈ H

variable {G : Type} [Group G] [Finite G]

theorem inf_normalizer_le_of_key (hKey : KeyNormalizer) {M₀ M L V : Subgroup G} {s : G}
    (h : TransvIrr.Setting M₀ L V s) (hV2 : ∀ v ∈ V, v * v = 1)
    (hsn : s ∉ L ⊔ M₀ ⊓ Subgroup.centralizer (V : Set G))
    (hN : ∀ T : Subgroup G, T ≤ M₀ → M₀ ≤ Subgroup.normalizer (T : Set G) →
      M₀ ⊓ Subgroup.centralizer (V : Set G) ≤ T → ∀ x ∈ T,
        x ∉ L ⊔ M₀ ⊓ Subgroup.centralizer (V : Set G) → L ≤ T)
    (hM₀M : M₀ ≤ M) (hMU : M ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G))
    (hMCl : M ≤ Subgroup.normalizer ((⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G))
    (hNM : ∀ T : Subgroup G, T ≤ M → M ≤ Subgroup.normalizer (T : Set G) →
      M ⊓ Subgroup.centralizer (V : Set G) ≤ T → ∀ x ∈ T,
        x ∉ L ⊔ M ⊓ Subgroup.centralizer (V : Set G) → L ≤ T)
    (hCM : M ⊓ Subgroup.centralizer (V : Set G) ≤ M₀)
    {b : G} (hbM : b ∈ M) (hbN : b ∈ Subgroup.normalizer (M₀ : Set G)) : b ∈ M₀ := by
  obtain ⟨W, _, _, _, _, ρ₁, ρ, hρρ₁, hirr, htr, hgen, hM, hperf, hL1, hs, hC₁, hL1₁⟩ :=
    TransvIrr.exists_rep_ext h hV2 hsn hN M hM₀M hMU hMCl
  set s' : ↥M₀ := ⟨s, h.mem⟩ with hs'
  have : (L.subgroupOf M₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normL
  have hrange := range_eq_closure_conj ρ s' hgen
  have hperf' : ⁅(L.subgroupOf M₀).map ρ, (L.subgroupOf M₀).map ρ⁆ = (L.subgroupOf M₀).map ρ := by
    apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun x hx y hy => by
        have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · calc (L.subgroupOf M₀).map ρ ≤ (⁅L.subgroupOf M₀, L.subgroupOf M₀⁆ ⊔ ρ.ker).map ρ :=
            Subgroup.map_mono hperf
        _ = ⁅(L.subgroupOf M₀).map ρ, (L.subgroupOf M₀).map ρ⁆ := by
          rw [Subgroup.map_sup, Subgroup.map_commutator,
            (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  have hgenρ : ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ t ∈ S, IsF2Transvection t) ∧ ρ.range = Subgroup.closure S := by
    refine ⟨_, ?_, hrange⟩
    rintro _ ⟨g, -, rfl⟩
    exact isF2Transvection_conj htr g
  have hirrρ : ∀ P : Submodule (ZMod 2) W,
      (∀ g ∈ ρ.range, ∀ u ∈ P, (g : W →ₗ[ZMod 2] W) u ∈ P) → P = ⊥ ∨ P = ⊤ := by
    intro P hP
    exact hirr P fun m w hw => hP (ρ m) ⟨m, rfl⟩ w hw
  have hkey := hKey W Module.finrank_pos ρ.range ((L.subgroupOf M₀).map ρ) hgenρ hirrρ
    (Subgroup.map_le_range ρ _) (relIndex_map_eq_two ρ (L.subgroupOf M₀) s' htr hM hs) hperf'
    (fun h0 => hL1 ((Subgroup.map_eq_bot_iff _).mp h0))
  set g : LinearMap.GeneralLinearGroup (ZMod 2) W := ρ₁ ⟨b, hbM⟩ with hg
  have hconj : ∀ m : ↥M₀, g * ρ m * g⁻¹ = ρ ⟨b * m * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbN m).mp m.2⟩ := by
    intro m
    rw [hρρ₁, hρρ₁, hg, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hgn : g ∈ Subgroup.normalizer (ρ.range : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨_, (hconj m).symm⟩
    · rintro ⟨m', hm'⟩
      have hm'M : b⁻¹ * m' * b ∈ M₀ := by
        refine (Subgroup.mem_normalizer_iff.mp hbN _).mpr ?_
        have : b * (b⁻¹ * (m' : G) * b) * b⁻¹ = m' := by group
        rw [this]; exact m'.2
      refine ⟨⟨b⁻¹ * m' * b, hm'M⟩, ?_⟩
      have h1 := hconj ⟨b⁻¹ * m' * b, hm'M⟩
      have e : (⟨b * (b⁻¹ * (m' : G) * b) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbN _).mp hm'M⟩ :
          ↥M₀) = m' := Subtype.ext (by group)
      rw [e, hm'] at h1
      calc ρ ⟨b⁻¹ * m' * b, hm'M⟩ = g⁻¹ * (g * ρ ⟨b⁻¹ * m' * b, hm'M⟩ * g⁻¹) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = x := by group
  obtain ⟨m, hm⟩ := hkey g hgn
  have hx0 : (Subgroup.inclusion hM₀M m)⁻¹ * ⟨b, hbM⟩ ∈ ρ₁.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hρρ₁, hm, inv_mul_cancel]
  have hx0mem : ((((Subgroup.inclusion hM₀M m)⁻¹ * ⟨b, hbM⟩ : ↥M)) : G) ∈
      L ⊔ M ⊓ Subgroup.centralizer (V : Set G) := by
    by_contra hnot
    apply hL1₁
    have hTM : (ρ₁.ker).map M.subtype ≤ M := Subgroup.map_subtype_le _
    have hMT : M ≤ Subgroup.normalizer (((ρ₁.ker).map M.subtype : Subgroup G) : Set G) := by
      apply TransvIrr.le_normalizer_of_conj_mem
      rintro g hg _ ⟨k, hk, rfl⟩
      exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, (MonoidHom.normal_ker ρ₁).conj_mem k hk _, rfl⟩
    have hCT : M ⊓ Subgroup.centralizer (V : Set G) ≤ (ρ₁.ker).map M.subtype := by
      rintro c ⟨hcM, hcV⟩
      exact ⟨⟨c, hcM⟩, hC₁ ⟨c, hcM⟩ hcV, rfl⟩
    have hLT := hNM _ hTM hMT hCT _ ⟨_, hx0, rfl⟩ hnot
    intro l hl
    obtain ⟨k, hk, hkl⟩ := hLT (show (l : G) ∈ L from hl)
    have : k = l := Subtype.ext hkl
    rwa [← this]
  have hb : b = (m : G) * ((((Subgroup.inclusion hM₀M m)⁻¹ * ⟨b, hbM⟩ : ↥M)) : G) := by
    simp
  rw [hb]
  refine M₀.mul_mem m.2 ?_
  exact (sup_le h.le hCM) hx0mem

end CFSG.HardMathSupport.Cooperstein.StructureLie
