module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbEmb

public section

open Subgroup CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace IIbSyl

theorem card_P_model : Nat.card P = 64 := by
  rw [P, ← Nat.card_congr (MonoidHom.ofInjective (SemidirectProduct.inl_injective
    (N := P0) (G := Multiplicative (ZMod 2)) (φ := psi))).toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  rfl

theorem v0Hom_injective : Function.Injective v0Hom := by decide

theorem rHom_injective : Function.Injective rHom := by decide

theorem vHom_injective : Function.Injective vHom := by decide

theorem card_V0_model : Nat.card V0 = 4 := by
  rw [V0, ← Nat.card_congr (MonoidHom.ofInjective v0Hom_injective).toEquiv,
    Nat.card_eq_fintype_card]
  rfl

theorem card_R_model : Nat.card R = 4 := by
  rw [R, ← Nat.card_congr (MonoidHom.ofInjective rHom_injective).toEquiv,
    Nat.card_eq_fintype_card]
  rfl

theorem card_V_model : Nat.card V = 16 := by
  rw [V, ← Nat.card_congr (MonoidHom.ofInjective vHom_injective).toEquiv,
    Nat.card_eq_fintype_card]
  rfl

theorem z0_eq_inl :
    z0 = SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (2, 0))) := by
  decide

theorem a_eq_inl :
    a = SemidirectProduct.inl (SemidirectProduct.inr (Multiplicative.ofAdd (1, 0))) := by
  decide

theorem sigma_eq_inl :
    sigma = SemidirectProduct.inl (SemidirectProduct.inr (Multiplicative.ofAdd (0, 1))) := by
  decide

theorem v0Hom_cases_inl : ∀ y : Multiplicative (ZMod 2 × ZMod 2),
    v0Hom y = 1 ∨
      v0Hom y = SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (2, 0))) ∨
      v0Hom y = SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (0, 2))) ∨
      v0Hom y = SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (2, 2))) := by
  decide

theorem rHom_eq_inl : ∀ y : Multiplicative (ZMod 2 × ZMod 2),
    rHom y = SemidirectProduct.inl (SemidirectProduct.inr y) := by
  decide

theorem vHom_eq_mul : ∀ p : Multiplicative ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)),
    vHom p = v0Hom (Multiplicative.ofAdd (Multiplicative.toAdd p).1) *
      rHom (Multiplicative.ofAdd (Multiplicative.toAdd p).2) := by
  decide

end IIbSyl

variable {G : Type*} [Group G]

namespace P0Gens

variable (q : P0Gens G)

theorem homC_mem {H : Subgroup G} (h₁ : q.g₁ ∈ H) (h₂ : q.g₂ ∈ H) (c : IIbSyl.C0) :
    q.homC c ∈ H :=
  mul_mem (pow_mem h₁ _) (pow_mem h₂ _)

theorem homR_mem {H : Subgroup G} (ha : q.a ∈ H) (hσ : q.σ ∈ H) (r : IIbSyl.R0) :
    q.homR r ∈ H :=
  mul_mem (pow_mem ha _) (pow_mem hσ _)

theorem hom_mem {H : Subgroup G} (h₁ : q.g₁ ∈ H) (h₂ : q.g₂ ∈ H) (ha : q.a ∈ H)
    (hσ : q.σ ∈ H) (p : IIbSyl.P0) : q.hom p ∈ H := by
  rw [← SemidirectProduct.inl_left_mul_inr_right p, map_mul, hom_inl, hom_inr]
  exact mul_mem (q.homC_mem h₁ h₂ _) (q.homR_mem ha hσ _)

end P0Gens

namespace SGens

variable (q : SGens G)

theorem hom_inl_inl (c : IIbSyl.C0) :
    q.hom (SemidirectProduct.inl (SemidirectProduct.inl c)) = q.toP0Gens.homC c := by
  rw [hom_inl, P0Gens.hom_inl]

theorem hom_inl_inr (r : IIbSyl.R0) :
    q.hom (SemidirectProduct.inl (SemidirectProduct.inr r)) = q.toP0Gens.homR r := by
  rw [hom_inl, P0Gens.hom_inr]

theorem hom_t : q.hom IIbSyl.t = q.t := by
  rw [IIbSyl.t, hom_inr, chi_ofAdd]

theorem hom_z0 : q.hom IIbSyl.z0 = q.g₁ ^ 2 := by
  rw [IIbSyl.z0_eq_inl, hom_inl_inl]
  change q.g₁ ^ 2 * q.g₂ ^ 0 = q.g₁ ^ 2
  rw [pow_zero, mul_one]

theorem hom_a : q.hom IIbSyl.a = q.a := by
  rw [IIbSyl.a_eq_inl, hom_inl_inr, P0Gens.homR_a]

theorem chi_mem (e : Multiplicative (ZMod 2)) : q.chi e ∈ zpowers q.t := by
  change (if e = 1 then 1 else q.t) ∈ zpowers q.t
  split_ifs
  · exact one_mem _
  · exact mem_zpowers _

theorem hom_mem_sup {H : Subgroup G} (h₁ : q.g₁ ∈ H) (h₂ : q.g₂ ∈ H) (ha : q.a ∈ H)
    (hσ : q.σ ∈ H) (s : IIbSyl) : q.hom s ∈ H ⊔ zpowers q.t := by
  rw [← SemidirectProduct.inl_left_mul_inr_right s, map_mul, hom_inl, hom_inr]
  exact mul_mem (mem_sup_left (q.toP0Gens.hom_mem h₁ h₂ ha hσ _)) (mem_sup_right (q.chi_mem _))

theorem map_P_le {H : Subgroup G} (h₁ : q.g₁ ∈ H) (h₂ : q.g₂ ∈ H) (ha : q.a ∈ H)
    (hσ : q.σ ∈ H) : IIbSyl.P.map q.hom ≤ H := by
  rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
  rw [hom_inl]
  exact q.toP0Gens.hom_mem h₁ h₂ ha hσ p

theorem map_V0_le {H : Subgroup G} (h₁ : q.g₁ ^ 2 ∈ H) (h₂ : q.g₂ ^ 2 ∈ H) :
    IIbSyl.V0.map q.hom ≤ H := by
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  rcases IIbSyl.v0Hom_cases_inl y with e | e | e | e <;> rw [e]
  · rw [map_one]
    exact one_mem H
  · rw [hom_inl_inl]
    change q.g₁ ^ 2 * q.g₂ ^ 0 ∈ H
    rw [pow_zero, mul_one]
    exact h₁
  · rw [hom_inl_inl]
    change q.g₁ ^ 0 * q.g₂ ^ 2 ∈ H
    rw [pow_zero, one_mul]
    exact h₂
  · rw [hom_inl_inl]
    exact mul_mem h₁ h₂

theorem map_R_le {H : Subgroup G} (ha : q.a ∈ H) (hσ : q.σ ∈ H) : IIbSyl.R.map q.hom ≤ H := by
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [IIbSyl.rHom_eq_inl, hom_inl_inr]
  exact q.toP0Gens.homR_mem ha hσ y

theorem map_V_le {H K : Subgroup G} (h₁ : q.g₁ ^ 2 ∈ H) (h₂ : q.g₂ ^ 2 ∈ H) (ha : q.a ∈ K)
    (hσ : q.σ ∈ K) : IIbSyl.V.map q.hom ≤ H ⊔ K := by
  rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
  rw [IIbSyl.vHom_eq_mul, map_mul]
  exact mul_mem (mem_sup_left (q.map_V0_le h₁ h₂ ⟨_, ⟨_, rfl⟩, rfl⟩))
    (mem_sup_right (q.map_R_le ha hσ ⟨_, ⟨_, rfl⟩, rfl⟩))

end SGens

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

theorem exists_hom_of_mType (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64) :
    ∃ f : IIbSyl →* G, Function.Injective f ∧ f.range = P ⊔ zpowers x ∧
      IIbSyl.P.map f = P ∧ IIbSyl.V0.map f = V₀ ∧ IIbSyl.R.map f = R ∧
      IIbSyl.V.map f = R ⊔ T ∧ f IIbSyl.t = x ∧ f IIbSyl.z0 = z ∧ f IIbSyl.a = r₁ := by
  obtain ⟨q, hqt, hqa, hg₁, hg₂, hσR, -, -, hz, hw, -, -⟩ := h.exists_sGens hP hPC hx hm hP64
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hinj : Function.Injective q.hom := IIbSyl.injective_of_ne_one q.hom (by
    rw [q.hom_z0, sq, hz]
    exact hx.z_ne)
  have haR : q.a ∈ R := hqa ▸ hx.r_mem
  have haP : q.a ∈ P := hVP (mem_sup_left haR)
  have hσP : q.σ ∈ P := hVP (mem_sup_left hσR)
  have hz₁ : q.g₁ ^ 2 ∈ V₀ := by
    rw [sq, hz]
    exact hx.z_mem
  have hz₂ : q.g₂ ^ 2 ∈ V₀ := by
    rw [sq]
    exact hw
  have hPmap : IIbSyl.P.map q.hom = P :=
    eq_of_le_of_card_ge (q.map_P_le hg₁ hg₂ haP hσP)
      (le_of_eq (by rw [card_map_of_injective hinj, IIbSyl.card_P_model, hP64]))
  have hV0map : IIbSyl.V0.map q.hom = V₀ :=
    eq_of_le_of_card_ge (q.map_V0_le hz₁ hz₂)
      (le_of_eq (by rw [card_map_of_injective hinj, IIbSyl.card_V0_model, h.card_V₀]))
  have hRmap : IIbSyl.R.map q.hom = R :=
    eq_of_le_of_card_ge (q.map_R_le haR hσR)
      (le_of_eq (by rw [card_map_of_injective hinj, IIbSyl.card_R_model, h.cardR]))
  have hVmap : IIbSyl.V.map q.hom = R ⊔ T := by
    have hle : V₀ ⊔ R ≤ R ⊔ T := sup_le h.V₀_le le_sup_left
    exact eq_of_le_of_card_ge ((q.map_V_le hz₁ hz₂ haR hσR).trans hle)
      (le_of_eq (by rw [card_map_of_injective hinj, IIbSyl.card_V_model, h.loc.card]))
  have hrange : q.hom.range = P ⊔ zpowers x := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      rw [← hqt]
      exact q.hom_mem_sup hg₁ hg₂ haP hσP s
    · refine sup_le ?_ (zpowers_le.mpr ⟨IIbSyl.t, by rw [q.hom_t, hqt]⟩)
      rw [← hPmap]
      exact map_le_range q.hom IIbSyl.P
  refine ⟨q.hom, hinj, hrange, hPmap, hV0map, hRmap, hVmap, by rw [q.hom_t, hqt], ?_, ?_⟩
  · rw [q.hom_z0, sq, hz]
  · rw [q.hom_a, hqa]

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
