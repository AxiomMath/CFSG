module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatural

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 Matrix CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization

section Helpers

variable {G : Type*} [Group G]

theorem card_eq_card_map_mul_card_inf_ker [Finite G] {H : Type*} [Group H] (f : G →* H)
    (A : Subgroup G) :
    Nat.card A = Nat.card (A.map f) * Nat.card (A ⊓ f.ker : Subgroup G) := by
  have h1 := Subgroup.card_ker_mul_card_range (f.comp A.subtype)
  have hrange : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : (f.comp A.subtype).ker = (A ⊓ f.ker).subgroupOf A := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hcard : Nat.card (f.comp A.subtype).ker = Nat.card (A ⊓ f.ker : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hrange, hcard] at h1
  rw [← h1, mul_comm]

theorem centralizer_cj (A : Subgroup G) (g : G) :
    Subgroup.centralizer ((cj A g : Subgroup G) : Set G) =
      cj (Subgroup.centralizer (A : Set G)) g := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (g⁻¹ * a * g) (mem_cj_of_mem ha)
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * a := by group
  · intro h a ha
    have ha' : g * a * g⁻¹ ∈ A := mem_cj.mp ha
    have h1 := h _ ha'
    have h2 : g * (a * x) * g⁻¹ = g * (x * a) * g⁻¹ := by
      calc g * (a * x) * g⁻¹ = (g * a * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * a * g⁻¹) := h1
        _ = g * (x * a) * g⁻¹ := by group
    simpa using h2

theorem map_cj {H : Type*} [Group H] (f : G →* H) (A : Subgroup G) (g : G) :
    (cj A g).map f = cj (A.map f) (f g) := by
  ext x
  rw [mem_cj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g * y * g⁻¹, mem_cj.mp hy, ?_⟩
    simp [map_mul, map_inv]
  · rintro ⟨a, ha, hax⟩
    refine ⟨g⁻¹ * a * g, mem_cj_of_mem ha, ?_⟩
    have : f g * x * (f g)⁻¹ = f a := hax.symm
    calc f (g⁻¹ * a * g) = (f g)⁻¹ * (f g * x * (f g)⁻¹) * f g := by simp [map_mul, map_inv, this]
      _ = x := by group

theorem cj_rootGrp {k : Type*} [Field k] (m : SpecialLinearGroup (Fin 2) k)
    (ℓ : ℙ k (Fin 2 → k)) : cj (rootGrp ℓ) m = rootGrp (m⁻¹ • ℓ) :=
  (rootGrp_smul_eq_map m⁻¹ ℓ).symm

open scoped Pointwise in
theorem exists_lift_hom {M : Type*} [Group M] [Finite G] {E X C : Subgroup G} (hXE : X ≤ E)
    (hCE : C ≤ E) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsup : X ⊔ C = E)
    (ψ : X →* M) (hker : ∀ x : X, (x : G) ∈ C → ψ x = 1) :
    ∃ ψE : E →* M, ∀ (x : X) (c : C),
      ψE ⟨(x : G) * (c : G), mul_mem (hXE x.2) (hCE c.2)⟩ = ψ x := by
  classical
  let f : X × C →* E := (Subgroup.inclusion hXE).noncommCoprod (Subgroup.inclusion hCE)
    (fun x c => Subtype.ext (hcomm _ (hXE x.2) _ (hCE c.2)))
  have hfapply : ∀ p : X × C, (f p : G) = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hf : Function.Surjective f := by
    intro e
    have he : (e : G) ∈ X ⊔ C := hsup ▸ e.2
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X C
      (fun x hx y hy => hcomm x (hXE hx) y (hCE hy))).2
    have : (e : G) ∈ (X : Set G) * (C : Set G) := by rw [← hset]; exact he
    obtain ⟨x, hx, c, hc, hxc⟩ := this
    exact ⟨(⟨x, hx⟩, ⟨c, hc⟩), Subtype.ext hxc⟩
  have hle : f.ker ≤ (ψ.comp (MonoidHom.fst X C)).ker := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    have h1 : (p.1 : G) * (p.2 : G) = 1 := by
      have := congrArg Subtype.val hp
      rwa [hfapply] at this
    have h2 : (p.1 : G) = ((p.2 : G))⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hker p.1 (by rw [h2]; exact inv_mem p.2.2)
  refine ⟨MonoidHom.liftOfRightInverse f (Function.surjInv hf) (Function.rightInverse_surjInv hf)
    ⟨ψ.comp (MonoidHom.fst X C), hle⟩, fun x c => ?_⟩
  have : (⟨(x : G) * (c : G), mul_mem (hXE x.2) (hCE c.2)⟩ : E) = f (x, c) :=
    Subtype.ext rfl
  rw [this, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

end Helpers

section Seed

variable {G : Type*} [Group G] {k : Type*} [Field k]
  {S : Sylow 2 G} {ρ : G →* SpecialLinearGroup (Fin 2) k} {X : Subgroup G}
  {ψ : X →* Multiplicative (Fin 2 → k)}

theorem Ecore_le_core : Ecore G ≤ CFSG.pCore 2 G := centerTorsion_le _ _

theorem Ecore_commute {x y : G} (hx : x ∈ Ecore G) (hy : y ∈ Ecore G) : x * y = y * x :=
  (mem_centerTorsion_iff.mp hy).2.1 x (Ecore_le_core hx)

theorem Ecore_commute_core {x y : G} (hx : x ∈ CFSG.pCore 2 G) (hy : y ∈ Ecore G) :
    x * y = y * x :=
  (mem_centerTorsion_iff.mp hy).2.1 x hx

theorem Ecore_sq {x : G} (hx : x ∈ Ecore G) : x ^ 2 = 1 := (mem_centerTorsion_iff.mp hx).2.2

theorem isElemAbelian_Ecore : CFSG.Open.IsElemAbelian 2 (Ecore G) :=
  isElemAbelian_iff.mpr ⟨fun _ hx _ hy => Ecore_commute hx hy, fun _ hx => Ecore_sq hx⟩

theorem isElemAbelian_of_le_Ecore {Y : Subgroup G} (hY : Y ≤ Ecore G) :
    CFSG.Open.IsElemAbelian 2 Y :=
  isElemAbelian_mono isElemAbelian_Ecore hY

theorem Ecore_le_sylow {S : Sylow 2 G} : Ecore G ≤ (S : Subgroup G) :=
  Ecore_le_core.trans (core_le_sylow S)

namespace IsNatBase

theorem ψ_conj (h : IsNatBase S ρ X ψ) (g : G) (x : X) :
    Multiplicative.toAdd (ψ ⟨g * x * g⁻¹, h.normal.conj_mem x x.2 g⟩) =
      (ρ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψ x)) :=
  h.ψ_equiv g x _ rfl

theorem X_le_core (h : IsNatBase S ρ X ψ) : X ≤ CFSG.pCore 2 G := h.le_E.trans Ecore_le_core

theorem ψ_mem_line (h : IsNatBase S ρ X ψ) {ℓ : ℙ k (Fin 2 → k)} {a : G} (ha : ρ a ∈ rootGrp ℓ)
    (ha1 : ρ a ≠ 1) {x : G} (hx : x ∈ X) (hax : a * x * a⁻¹ = x) :
    Multiplicative.toAdd (ψ ⟨x, hx⟩) ∈ ℓ.submodule := by
  have h1 := h.ψ_equiv a ⟨x, hx⟩ ⟨x, hx⟩ hax.symm
  have h2 : ρ a • Multiplicative.toAdd (ψ ⟨x, hx⟩) = Multiplicative.toAdd (ψ ⟨x, hx⟩) := by
    rw [Matrix.SpecialLinearGroup.smul_def]; exact h1.symm
  exact (smul_eq_self_iff_mem_of_mem_rootGrp ha ha1 _).mp h2

theorem card_X [Finite G] [Finite k] (h : IsNatBase S ρ X ψ) :
    Nat.card X = Nat.card (X ⊓ Subgroup.center G : Subgroup G) * Nat.card k ^ 2 := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective h.ψ_surj
  have hk : Nat.card (Multiplicative (Fin 2 → k)) = Nat.card k ^ 2 :=
    (Nat.card_congr Multiplicative.toAdd).trans card_fin_two_pi
  have hker : Nat.card ψ.ker = Nat.card (X ⊓ Subgroup.center G : Subgroup G) := by
    rw [h.ψ_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hk, hker] at h1
  exact h1.symm

theorem card_lineMult [Finite k] (ℓ : ℙ k (Fin 2 → k)) : Nat.card (lineMult ℓ) = Nat.card k := by
  rw [← card_submodule_line ℓ]
  exact Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd y.1, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_k_mul_card_centralizer_le [Finite G] [Finite k] (h : IsNatBase S ρ X ψ)
    {ℓ : ℙ k (Fin 2 → k)} {A : Subgroup G} {a : G} (haA : a ∈ A) (ha : ρ a ∈ rootGrp ℓ)
    (ha1 : ρ a ≠ 1) :
    Nat.card k * Nat.card (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤ Nat.card X := by
  classical
  set C : Subgroup G := X ⊓ Subgroup.centralizer (A : Set G) with hC
  have hCX : C ≤ X := inf_le_left
  let ψC : C →* Multiplicative (Fin 2 → k) := ψ.comp (Subgroup.inclusion hCX)
  have hrange : ψC.range ≤ lineMult ℓ := by
    rintro _ ⟨c, rfl⟩
    show Multiplicative.toAdd (ψ (Subgroup.inclusion hCX c)) ∈ ℓ.submodule
    refine h.ψ_mem_line ha ha1 (hCX c.2) ?_
    have hc : a * (c : G) = (c : G) * a := Subgroup.mem_centralizer_iff.mp c.2.2 a haA
    rw [hc]; group
  have hle : (X ⊓ Subgroup.center G : Subgroup G) ≤ C := by
    intro x hx
    refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun g _ => ?_⟩
    exact (Subgroup.mem_center_iff.mp hx.2 g)
  have hker : ψC.ker = (X ⊓ Subgroup.center G : Subgroup G).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have : (ψC c = 1) ↔ Subgroup.inclusion hCX c ∈ ψ.ker := Iff.rfl
    rw [this, h.ψ_ker, Subgroup.mem_subgroupOf]
    rfl
  have hkcard : Nat.card ψC.ker = Nat.card (X ⊓ Subgroup.center G : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range ψC
  rw [hkcard] at h1
  have h2 : Nat.card ψC.range ≤ Nat.card k := by
    rw [← card_lineMult ℓ]
    exact Subgroup.card_le_of_le hrange
  have h3 := h.card_X
  calc Nat.card k * Nat.card C = Nat.card k * (Nat.card (X ⊓ Subgroup.center G : Subgroup G) *
          Nat.card ψC.range) := by rw [h1]
    _ ≤ Nat.card k * (Nat.card (X ⊓ Subgroup.center G : Subgroup G) * Nat.card k) := by
        gcongr
    _ = Nat.card X := by rw [h3]; ring

theorem X_le_sylow (h : IsNatBase S ρ X ψ) : X ≤ (S : Subgroup G) :=
  h.X_le_core.trans (core_le_sylow S)


theorem max_outside [Finite G] [Finite k] (h : IsNatBase S ρ X ψ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    A.map ρ = (S : Subgroup G).map ρ ∧
      Nat.card k * Nat.card (A ⊓ CFSG.pCore 2 G : Subgroup G) = Nat.card A ∧
      Nat.card k * Nat.card (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = Nat.card X ∧
      Nat.card k * Nat.card (Ecore G ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
        Nat.card (Ecore G) ∧
      Ecore G ⊓ Subgroup.centralizer (A : Set G) = A ⊓ Ecore G ∧
      IsMaxElemAbelian (S : Subgroup G) ((A ⊓ CFSG.pCore 2 G) ⊔ Ecore G) := by
  classical
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  set Q := CFSG.pCore 2 G with hQdef
  set E := Ecore G with hEdef
  have hAS : A ≤ (S : Subgroup G) := hA.1
  have hAker : A ⊓ ρ.ker = A ⊓ Q := by
    apply le_antisymm
    · rintro x ⟨hxA, hxk⟩
      have hx : x ∈ (S : Subgroup G) ⊓ ρ.ker := ⟨hAS hxA, hxk⟩
      rw [h.sylow_inf_ker] at hx
      exact ⟨hxA, hx⟩
    · rintro x ⟨hxA, hxQ⟩
      exact ⟨hxA, h.core_le hxQ⟩
  have hcardA : Nat.card (A.map ρ) * Nat.card (A ⊓ Q : Subgroup G) = Nat.card A := by
    have := card_eq_card_map_mul_card_inf_ker ρ A
    rw [hAker] at this
    exact this.symm
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have hρa : ρ a ∈ rootGrp ℓ := by
    rw [← hℓ]; exact ⟨a, hAS haA, rfl⟩
  have hρa1 : ρ a ≠ 1 := by
    intro h1
    apply haQ
    have hx : a ∈ (S : Subgroup G) ⊓ ρ.ker := ⟨hAS haA, h1⟩
    rwa [h.sylow_inf_ker] at hx
  have hq1 := h.card_k_mul_card_centralizer_le haA hρa hρa1
  have hX7 := action_inequality hA h.X_le_sylow (isElemAbelian_of_le_Ecore h.le_E)
  have hE7 := action_inequality hA (Ecore_le_sylow (S := S)) isElemAbelian_Ecore
  have hAQcX : A ⊓ Q ≤ A ⊓ Subgroup.centralizer (X : Set G) := by
    rintro x ⟨hxA, hxQ⟩
    refine ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (Ecore_commute_core hxQ (h.le_E hy)).symm
  have hAQcE : A ⊓ Q ≤ A ⊓ Subgroup.centralizer (E : Set G) := by
    rintro x ⟨hxA, hxQ⟩
    refine ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (Ecore_commute_core hxQ hy).symm
  have hrS : Nat.card (A.map ρ) ≤ Nat.card k := by
    have := Subgroup.card_le_of_le (Subgroup.map_mono (f := ρ) hAS)
    rw [hℓ, card_rootGrp] at this
    exact this
  have hpos : ∀ (K : Subgroup G), 0 < Nat.card K := fun K => Nat.card_pos
  have hcX := hpos (X ⊓ Subgroup.centralizer (A : Set G))
  have hcA := hpos (A ⊓ Subgroup.centralizer (X : Set G))
  have haQpos := hpos (A ⊓ Q)
  have h7 := hX7.2
  have hle1 : Nat.card (A ⊓ Q : Subgroup G) ≤ Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hAQcX
  set q := Nat.card k with hq
  set r := Nat.card (A.map ρ) with hr_def
  set aQ := Nat.card (A ⊓ Q : Subgroup G) with haQ_def
  set aA := Nat.card A with haA_def
  set cX := Nat.card (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) with hcX_def
  set cA := Nat.card (A ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) with hcA_def
  set xX := Nat.card X with hxX_def
  have e1 : q * cA * cX ≤ r * aQ * cX := by
    calc q * cA * cX = (q * cX) * cA := by ring
      _ ≤ xX * cA := Nat.mul_le_mul_right _ hq1
      _ ≤ aA * cX := h7
      _ = r * aQ * cX := by rw [← hcardA]
  have e2 : q * cA ≤ r * aQ := Nat.le_of_mul_le_mul_right e1 hcX
  have e3 : q * aQ ≤ r * aQ := (Nat.mul_le_mul_left q hle1).trans e2
  have hqr : q ≤ r := Nat.le_of_mul_le_mul_right e3 haQpos
  have hr : r = q := le_antisymm hrS hqr
  have hcardAq : q * aQ = aA := by rw [← hr, hcardA]
  have hcAeq : cA = aQ := by
    have : q * cA ≤ q * aQ := by rw [hr] at e2; exact e2
    exact le_antisymm (Nat.le_of_mul_le_mul_left this (by rw [hq]; exact Nat.card_pos)) hle1
  have hXeq : q * cX = xX := by
    refine le_antisymm hq1 ?_
    have : xX * cA ≤ (q * cX) * cA := by
      calc xX * cA ≤ aA * cX := h7
        _ = q * aQ * cX := by rw [hcardAq]
        _ = (q * cX) * cA := by rw [hcAeq]; ring
    exact Nat.le_of_mul_le_mul_right this hcA
  have hmap : A.map ρ = (S : Subgroup G).map ρ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hAS) ?_
    rw [hℓ, card_rootGrp]
    exact hr.ge
  set xE := Nat.card E with hxE_def
  set cE := Nat.card (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) with hcE_def
  have hE72 := hE7.2
  have hle2 : Nat.card (A ⊓ Q : Subgroup G) ≤
      Nat.card (A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) := Subgroup.card_le_of_le hAQcE
  have hE_le : xE ≤ q * cE := by
    have h1 : xE * aQ ≤ q * cE * aQ := by
      calc xE * aQ ≤ xE * Nat.card (A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) :=
            Nat.mul_le_mul_left _ hle2
        _ ≤ aA * cE := hE72
        _ = q * cE * aQ := by rw [← hcardAq]; ring
    exact Nat.le_of_mul_le_mul_right h1 haQpos
  have hE_ge : q * cE ≤ xE := by
    have hcomm : ∀ x ∈ X, ∀ y ∈ (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G), x * y = y * x :=
      fun x hx y hy => Ecore_commute (h.le_E hx) hy.1
    have hprod := card_sup_mul_card_inf hcomm
    have hinf : (X ⊓ (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Subgroup G) =
        X ⊓ Subgroup.centralizer (A : Set G) := by
      ext x
      constructor
      · rintro ⟨hx, -, hxc⟩
        exact ⟨hx, hxc⟩
      · rintro ⟨hx, hxc⟩
        exact ⟨hx, h.le_E hx, hxc⟩
    rw [hinf] at hprod
    have hsup : Nat.card (X ⊔ (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Subgroup G) ≤ xE :=
      Subgroup.card_le_of_le (sup_le h.le_E inf_le_left)
    have : (q * cE) * cX ≤ xE * cX := by
      calc (q * cE) * cX = (q * cX) * cE := by ring
        _ = xX * cE := by rw [hXeq]
        _ = Nat.card (X ⊔ (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Subgroup G) * cX := by
            rw [← hprod]
        _ ≤ xE * cX := Nat.mul_le_mul_right _ hsup
    exact Nat.le_of_mul_le_mul_right this hcX
  have hEeq : q * cE = xE := le_antisymm hE_ge hE_le
  have hBel : CFSG.Open.IsElemAbelian 2 ((A ⊓ Q) ⊔ E : Subgroup G) :=
    isElemAbelian_sup (isElemAbelian_mono hA.2.1 inf_le_left) isElemAbelian_Ecore
      fun x hx y hy => Ecore_commute_core hx.2 hy
  have hBQ : (A ⊓ Q) ⊔ E ≤ Q := sup_le inf_le_right Ecore_le_core
  have hBS : (A ⊓ Q) ⊔ E ≤ (S : Subgroup G) := hBQ.trans (core_le_sylow S)
  have hBcard : Nat.card ((A ⊓ Q) ⊔ E : Subgroup G) = aA := by
    have hcomm : ∀ x ∈ (A ⊓ Q : Subgroup G), ∀ y ∈ E, x * y = y * x :=
      fun x hx y hy => Ecore_commute_core hx.2 hy
    have hprod := card_sup_mul_card_inf hcomm
    have hinf : ((A ⊓ Q : Subgroup G) ⊓ E : Subgroup G) = A ⊓ E := by
      ext x
      constructor
      · rintro ⟨⟨hxA, -⟩, hxE⟩
        exact ⟨hxA, hxE⟩
      · rintro ⟨hxA, hxE⟩
        exact ⟨⟨hxA, Ecore_le_core hxE⟩, hxE⟩
    rw [hinf] at hprod
    have hcE' : cE = Nat.card (A ⊓ E : Subgroup G) := by rw [hcE_def, hE7.1]
    have hw : 0 < Nat.card (A ⊓ E : Subgroup G) := Nat.card_pos
    have : Nat.card ((A ⊓ Q) ⊔ E : Subgroup G) * Nat.card (A ⊓ E : Subgroup G) =
        aA * Nat.card (A ⊓ E : Subgroup G) := by
      rw [hprod, ← hcardAq]
      calc Nat.card (A ⊓ Q : Subgroup G) * Nat.card E = aQ * xE := rfl
        _ = aQ * (q * cE) := by rw [hEeq]
        _ = q * aQ * Nat.card (A ⊓ E : Subgroup G) := by rw [hcE']; ring
    exact Nat.eq_of_mul_eq_mul_right hw this
  refine ⟨hmap, hcardAq, hXeq, hEeq, hE7.1, hBS, hBel, fun B hBS' hB => ?_⟩
  rw [hBcard]
  exact maxElem_card_le hA hBS' hB


end IsNatBase

namespace IsSeed

theorem exists_max_outside [Finite G] (h : IsSeed S ρ X ψ) :
    ∃ A : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A ∧ ¬ A ≤ CFSG.pCore 2 G := by
  by_contra hcon
  push Not at hcon
  exact h.not_le (iSup₂_le fun A hA => hcon A hA)

end IsSeed

instance Ecore_normal {G : Type*} [Group G] : (Ecore G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨hnQ, hnc, hnp⟩ := mem_centerTorsion_iff.mp hn
  rw [Ecore, mem_centerTorsion_iff]
  refine ⟨(CFSG.pCore_normal (G := G) (p := 2)).conj_mem _ hnQ g, fun k hk => ?_, ?_⟩
  · have h1 := (CFSG.pCore_normal (G := G) (p := 2)).conj_mem k hk g⁻¹
    have h2 := hnc _ h1
    calc k * (g * n * g⁻¹) = g * ((g⁻¹ * k * g⁻¹⁻¹) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * k * g⁻¹⁻¹)) * g⁻¹ := by rw [h2]
      _ = (g * n * g⁻¹) * k := by group
  · rw [conj_pow, hnp]; simp

theorem relIndex_eq_of_mul_card {G : Type*} [Group G] {C E : Subgroup G} (hCE : C ≤ E) {n : ℕ}
    (hC : 0 < Nat.card C) (h : n * Nat.card C = Nat.card E) : C.relIndex E = n := by
  have h1 := Subgroup.relIndex_mul_card C E
  rw [inf_of_le_left hCE] at h1
  have : C.relIndex E * Nat.card C = n * Nat.card C := by rw [h1, h]
  exact Nat.eq_of_mul_eq_mul_right hC this

theorem exists_smul_eq' {k : Type*} [Field k] (p m : ℙ k (Fin 2 → k)) :
    ∃ s : SpecialLinearGroup (Fin 2) k, s • p = m :=
  MulAction.exists_smul_eq _ _ _

namespace IsSeed

variable {G : Type*} [Group G] {k : Type*} [Field k]
  {S : Sylow 2 G} {ρ : G →* SpecialLinearGroup (Fin 2) k} {X : Subgroup G}
  {ψ : X →* Multiplicative (Fin 2 → k)}

theorem Ecore_eq_sup [Finite G] [Finite k] (h : IsSeed S ρ X ψ) :
    Ecore G = X ⊔ (Ecore G ⊓ Subgroup.center G) := by
  classical
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  obtain ⟨hmap, hcardAq, hXeq, hEeq, hEcent, hB⟩ := h.max_outside hA hAQ
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  set Q := CFSG.pCore 2 G with hQdef
  set E := Ecore G with hEdef
  obtain ⟨m, hm⟩ := exists_ne_point ℓ
  obtain ⟨s, hs⟩ := exists_smul_eq' ℓ m
  obtain ⟨g, hg⟩ := h.surj s⁻¹
  set A₁ := cj A g with hA₁def
  have hA₁ : A₁.map ρ = rootGrp m := by
    rw [hA₁def, map_cj, hmap, hℓ, cj_rootGrp, hg]
    simp [hs]
  have hQmap : Q.map ρ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr h.core_le
  have hY : (Q ⊔ A ⊔ A₁).map ρ = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hQmap, hA₁, hmap, hℓ, bot_sup_eq]
    exact rootGrp_sup_rootGrp (Ne.symm hm)
  have hYtop : Q ⊔ A ⊔ A₁ = ⊤ := h.eq_top_of_map_eq_top (le_sup_left.trans le_sup_left) hY
  have hC0 : E ⊓ Subgroup.center G =
      (E ⊓ Subgroup.centralizer (A : Set G)) ⊓ (E ⊓ Subgroup.centralizer (A₁ : Set G)) := by
    apply le_antisymm
    · rintro z ⟨hzE, hz⟩
      exact ⟨⟨hzE, Subgroup.mem_centralizer_iff.mpr fun a _ => Subgroup.mem_center_iff.mp hz a⟩,
        ⟨hzE, Subgroup.mem_centralizer_iff.mpr fun a _ => Subgroup.mem_center_iff.mp hz a⟩⟩
    · rintro e ⟨⟨heE, heA⟩, -, heA₁⟩
      refine ⟨heE, Subgroup.mem_center_iff.mpr fun x => ?_⟩
      have hle : Q ⊔ A ⊔ A₁ ≤ Subgroup.centralizer ({e} : Set G) := by
        refine sup_le (sup_le ?_ ?_) ?_
        · intro x hx
          exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
            rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (Ecore_commute_core hx heE).symm
        · intro x hx
          exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
            rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (Subgroup.mem_centralizer_iff.mp heA x hx).symm
        · intro x hx
          exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
            rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (Subgroup.mem_centralizer_iff.mp heA₁ x hx).symm
      rw [hYtop] at hle
      exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top x)) e (Set.mem_singleton e)).symm
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hC1pos : 0 < Nat.card (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hC1idx : (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G).relIndex E = Nat.card k :=
    relIndex_eq_of_mul_card inf_le_left hC1pos hEeq
  have hC2eq : (E ⊓ Subgroup.centralizer (A₁ : Set G) : Subgroup G) =
      cj (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) g := by
    have hEcj : cj E g = E := cj_eq_self_of_normal
    rw [hA₁def, centralizer_cj, cj_inf, hEcj]
  have hC2card : Nat.card (E ⊓ Subgroup.centralizer (A₁ : Set G) : Subgroup G) =
      Nat.card (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
    rw [hC2eq, card_cj]
  have hC2idx : (E ⊓ Subgroup.centralizer (A₁ : Set G) : Subgroup G).relIndex E = Nat.card k :=
    relIndex_eq_of_mul_card inf_le_left (by rw [hC2card]; exact hC1pos) (by rw [hC2card]; exact hEeq)
  have hidx0 : (E ⊓ Subgroup.center G : Subgroup G).relIndex E ≤ Nat.card k * Nat.card k := by
    rw [hC0]
    calc _ ≤ (E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G).relIndex E *
          (E ⊓ Subgroup.centralizer (A₁ : Set G) : Subgroup G).relIndex E :=
          Subgroup.relIndex_inf_le
      _ = _ := by rw [hC1idx, hC2idx]
  have hC0pos : 0 < Nat.card (E ⊓ Subgroup.center G : Subgroup G) := Nat.card_pos
  have hEC : Nat.card E = (E ⊓ Subgroup.center G : Subgroup G).relIndex E *
      Nat.card (E ⊓ Subgroup.center G : Subgroup G) := by
    have := Subgroup.relIndex_mul_card (E ⊓ Subgroup.center G : Subgroup G) E
    rw [inf_of_le_left inf_le_left] at this
    exact this.symm
  have hcomm : ∀ x ∈ X, ∀ y ∈ (E ⊓ Subgroup.center G : Subgroup G), x * y = y * x :=
    fun x hx y hy => Ecore_commute (h.le_E hx) hy.1
  have hprod := card_sup_mul_card_inf hcomm
  have hinf : (X ⊓ (E ⊓ Subgroup.center G : Subgroup G) : Subgroup G) = X ⊓ Subgroup.center G := by
    ext x
    constructor
    · rintro ⟨hx, -, hxc⟩
      exact ⟨hx, hxc⟩
    · rintro ⟨hx, hxc⟩
      exact ⟨hx, h.le_E hx, hxc⟩
  rw [hinf] at hprod
  have hXc : 0 < Nat.card (X ⊓ Subgroup.center G : Subgroup G) := Nat.card_pos
  have hsupcard : Nat.card (X ⊔ (E ⊓ Subgroup.center G : Subgroup G) : Subgroup G) =
      Nat.card k ^ 2 * Nat.card (E ⊓ Subgroup.center G : Subgroup G) := by
    have : Nat.card (X ⊔ (E ⊓ Subgroup.center G : Subgroup G) : Subgroup G) *
        Nat.card (X ⊓ Subgroup.center G : Subgroup G) =
        (Nat.card k ^ 2 * Nat.card (E ⊓ Subgroup.center G : Subgroup G)) *
          Nat.card (X ⊓ Subgroup.center G : Subgroup G) := by
      rw [hprod, h.card_X]; ring
    exact Nat.eq_of_mul_eq_mul_right hXc this
  have hle : X ⊔ (E ⊓ Subgroup.center G : Subgroup G) ≤ E := sup_le h.le_E inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hsupcard, hEC]
  calc _ ≤ (Nat.card k * Nat.card k) * Nat.card (E ⊓ Subgroup.center G : Subgroup G) :=
        Nat.mul_le_mul_right _ hidx0
    _ = _ := by ring

open scoped Pointwise in
theorem exists_decomp [Finite G] [Finite k] (h : IsSeed S ρ X ψ) (e : Ecore G) :
    ∃ (x : X) (c : Ecore G), (c : G) ∈ Subgroup.center G ∧ (e : G) = (x : G) * (c : G) := by
  have he : (e : G) ∈ X ⊔ (Ecore G ⊓ Subgroup.center G) := h.Ecore_eq_sup ▸ e.2
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X (Ecore G ⊓ Subgroup.center G)
    (fun x hx y hy => Ecore_commute (h.le_E hx) hy.1)).2
  have : (e : G) ∈ (X : Set G) * ((Ecore G ⊓ Subgroup.center G : Subgroup G) : Set G) := by
    rw [← hset]; exact he
  obtain ⟨x, hx, c, hc, hxc⟩ := this
  exact ⟨⟨x, hx⟩, ⟨c, hc.1⟩, hc.2, hxc.symm⟩

theorem toEcore [Finite G] [Finite k] (h : IsSeed S ρ X ψ) :
    ∃ ψE : Ecore G →* Multiplicative (Fin 2 → k), IsSeed S ρ (Ecore G) ψE ∧
      ∀ x : X, ψE ⟨x, h.le_E x.2⟩ = ψ x := by
  classical
  obtain ⟨ψE, hψE⟩ := exists_lift_hom (E := Ecore G) (X := X) (C := Ecore G ⊓ Subgroup.center G)
    h.le_E inf_le_left (fun x hx y hy => Ecore_commute hx hy) h.Ecore_eq_sup.symm ψ (by
      intro x hx
      have : x ∈ ψ.ker := by
        rw [h.ψ_ker, Subgroup.mem_subgroupOf]
        exact ⟨x.2, hx.2⟩
      exact this)
  have hext : ∀ x : X, ψE ⟨x, h.le_E x.2⟩ = ψ x := by
    intro x
    have := hψE x ⟨1, one_mem _⟩
    simpa using this
  have hcen : ∀ (c : Ecore G), (c : G) ∈ Subgroup.center G → ψE c = 1 := by
    intro c hc
    have := hψE 1 ⟨c, ⟨c.2, hc⟩⟩
    simpa using this
  refine ⟨ψE, ⟨⟨h.card_k, h.surj, h.core_le, h.frattini_le, inferInstance, le_rfl, ?_, ?_, ?_⟩,
    h.not_le⟩, hext⟩
  · intro w
    obtain ⟨x, hx⟩ := h.ψ_surj w
    exact ⟨⟨x, h.le_E x.2⟩, by rw [hext, hx]⟩
  · intro g e e' hee'
    obtain ⟨x, c, hc, hxc⟩ := h.exists_decomp e
    have hge : (e' : G) = (g * x * g⁻¹) * c := by
      have hcg : (c : G) * g⁻¹ = g⁻¹ * c := ((Subgroup.mem_center_iff.mp hc g⁻¹)).symm
      rw [hee', hxc]
      calc g * (↑x * ↑c) * g⁻¹ = g * ↑x * (↑c * g⁻¹) := by group
        _ = g * ↑x * (g⁻¹ * ↑c) := by rw [hcg]
        _ = (g * ↑x * g⁻¹) * ↑c := by group
    have hxn : g * (x : G) * g⁻¹ ∈ X := h.normal.conj_mem x x.2 g
    have h1 : ψE e' = ψ ⟨g * x * g⁻¹, hxn⟩ := by
      have := hψE ⟨g * x * g⁻¹, hxn⟩ ⟨c, ⟨c.2, hc⟩⟩
      have he' : e' = ⟨(g * (x : G) * g⁻¹) * (c : G), mul_mem (h.le_E hxn) c.2⟩ := Subtype.ext hge
      rw [he']; exact this
    have h2 : ψE e = ψ x := by
      have := hψE x ⟨c, ⟨c.2, hc⟩⟩
      have he'' : e = ⟨(x : G) * (c : G), mul_mem (h.le_E x.2) c.2⟩ := Subtype.ext hxc
      rw [he'']; exact this
    rw [h1, h2]
    exact h.ψ_conj g x
  · ext e
    constructor
    · intro he
      obtain ⟨x, c, hc, hxc⟩ := h.exists_decomp e
      have h2 : ψE e = ψ x := by
        have := hψE x ⟨c, ⟨c.2, hc⟩⟩
        have he'' : e = ⟨(x : G) * (c : G), mul_mem (h.le_E x.2) c.2⟩ := Subtype.ext hxc
        rw [he'']; exact this
      have hx1 : ψ x = 1 := by rw [← h2]; exact he
      have hxk : x ∈ ψ.ker := hx1
      rw [h.ψ_ker, Subgroup.mem_subgroupOf] at hxk
      rw [Subgroup.mem_subgroupOf]
      refine ⟨e.2, ?_⟩
      rw [hxc]
      exact mul_mem (hxk.2) hc
    · intro he
      rw [Subgroup.mem_subgroupOf] at he
      exact hcen e he.2

theorem max_core_facts [Finite G] [Finite k] (h : IsSeed S ρ X ψ) :
    (∀ B : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) B → IsMaxElemAbelian (S : Subgroup G) B) ∧
    (∀ A B : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A →
      IsMaxElemAbelian (CFSG.pCore 2 G) B → Nat.card B = Nat.card A) := by
  obtain ⟨A₀, hA₀, hA₀Q⟩ := h.exists_max_outside
  obtain ⟨-, -, -, -, -, hB₀⟩ := h.max_outside hA₀ hA₀Q
  have hB₀Q : (A₀ ⊓ CFSG.pCore 2 G) ⊔ Ecore G ≤ CFSG.pCore 2 G :=
    sup_le inf_le_right Ecore_le_core
  have key : ∀ B : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) B →
      IsMaxElemAbelian (S : Subgroup G) B := by
    intro B hB
    refine ⟨hB.1.trans (core_le_sylow S), hB.2.1, fun B' hB'S hB' => ?_⟩
    exact (maxElem_card_le hB₀ hB'S hB').trans (maxElem_card_le hB hB₀Q hB₀.2.1)
  exact ⟨key, fun A B hA hB => maxElem_card_eq (key B hB) hA⟩

theorem natural_seed_exhausts_elementary_core_center [Finite G] [Finite k]
    (h : IsSeed S ρ X ψ) :
    Ecore G = X ⊔ (Ecore G ⊓ Subgroup.center G) ∧
    (∃ ψE : Ecore G →* Multiplicative (Fin 2 → k), Function.Surjective ψE ∧
      (∀ (g : G) (e e' : Ecore G), (e' : G) = g * e * g⁻¹ →
        Multiplicative.toAdd (ψE e') =
          (ρ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψE e))) ∧
      ψE.ker = (Ecore G ⊓ Subgroup.center G).subgroupOf (Ecore G) ∧
      ∀ x : X, ψE ⟨x, h.le_E x.2⟩ = ψ x) ∧
    (∀ A : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A → ¬ A ≤ CFSG.pCore 2 G →
      A.map ρ = (S : Subgroup G).map ρ ∧
      (Ecore G ⊓ Subgroup.centralizer (A : Set G)).relIndex (Ecore G) = Nat.card k ∧
      Ecore G ⊓ Subgroup.centralizer (A : Set G) = A ⊓ Ecore G ∧
      IsMaxElemAbelian (S : Subgroup G) ((A ⊓ CFSG.pCore 2 G) ⊔ Ecore G)) ∧
    (∀ A B : Subgroup G, IsMaxElemAbelian (S : Subgroup G) A →
      IsMaxElemAbelian (CFSG.pCore 2 G) B → Nat.card B = Nat.card A) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) B →
      IsMaxElemAbelian (S : Subgroup G) B) := by
  obtain ⟨ψE, hψE, hext⟩ := h.toEcore
  refine ⟨h.Ecore_eq_sup, ⟨ψE, hψE.ψ_surj, hψE.ψ_equiv, hψE.ψ_ker, hext⟩, ?_,
    h.max_core_facts.2, h.max_core_facts.1⟩
  intro A hA hAQ
  obtain ⟨hmap, -, -, hEeq, hEcent, hB⟩ := h.max_outside hA hAQ
  exact ⟨hmap, relIndex_eq_of_mul_card inf_le_left Nat.card_pos hEeq, hEcent, hB⟩

end IsSeed

end Seed

end CFSG.QuasithinUnique.Setup.Campbell
