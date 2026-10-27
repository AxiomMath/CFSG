module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf30Setup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf25Out

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace Out

section Generic

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_eq_oddCoreOf (X : Subgroup G) : Balance.oddCoreIn X = oddCoreOf X := rfl

@[expose] def psi1 (K X : Subgroup G) (hX : X ≤ Subgroup.normalizer (K : Set G)) :
    ↥X →* Equiv.Perm (Idx2 (Kbar K)) :=
  (psiK K).comp (Subgroup.inclusion hX)

@[expose] def gconj (K X : Subgroup G) (g : G)
    (hX : ∀ x ∈ X, g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G)) :
    ↥X →* ↥(Subgroup.normalizer (K : Set G)) :=
  MonoidHom.mk' (fun x => ⟨g⁻¹ * (x : G) * g, hX x x.2⟩) (by
    intro a b
    apply Subtype.ext
    simp [mul_assoc])

@[expose] def psi2 (K X : Subgroup G) (g : G)
    (hX : ∀ x ∈ X, g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G)) :
    ↥X →* Equiv.Perm (Idx2 (Kbar K)) :=
  (psiK K).comp (gconj K X g hX)

theorem psi1_apply (K X : Subgroup G) (hX : X ≤ Subgroup.normalizer (K : Set G)) (x : ↥X) :
    psi1 K X hX x = psiK K ⟨x, hX x.2⟩ := rfl

theorem psi2_apply (K X : Subgroup G) (g : G)
    (hX : ∀ x ∈ X, g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G)) (x : ↥X) :
    psi2 K X g hX x = psiK K ⟨g⁻¹ * x * g, hX x x.2⟩ := rfl

theorem psiK_eq_one_of_mem_trivialOnQuot (K : Subgroup G) {x : G} (hx : x ∈ trivialOnQuot K) :
    psiK K ⟨x, hx.1⟩ = 1 := by
  refine psiK_eq_one_of_conj K ⟨x, hx.1⟩ 1 ?_
  rw [rhoK_eq_conj_iff]
  intro y
  have := hx.2 y y.2
  simpa [commutatorElement_def, oddCoreIn_eq_oddCoreOf] using this

theorem psiK_eq_one_of_mem (K : Subgroup G) {x : G} (hx : x ∈ K) :
    psiK K ⟨x, Subgroup.le_normalizer hx⟩ = 1 := by
  refine psiK_eq_one_of_conj K _ ⟨x, hx⟩ ?_
  rw [rhoK_eq_conj_iff]
  intro y
  simp

theorem oddCoreOf_inf_le {K X : Subgroup G} (hKX : K ≤ X) : oddCoreOf X ⊓ K ≤ oddCoreOf K := by
  refine le_oddCoreOf_of_normalizes inf_le_right ?_
    (Odd.of_dvd_nat (oddCoreOf_odd_natCard X) (Subgroup.card_dvd_of_le inf_le_left))
  intro k hk
  have h1 : k ∈ Subgroup.normalizer (oddCoreOf X : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hKX hk))
  have h2 : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩

theorem psiK_eq_one_of_mem_oddCore (K X : Subgroup G) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ oddCoreOf X) :
    psiK K ⟨x, hXN (oddCoreOf_le_self X hx)⟩ = 1 := by
  have hxX : x ∈ X := oddCoreOf_le_self X hx
  have htriv : x ∈ trivialOnQuot K := by
    refine ⟨hXN hxX, fun y hy => ?_⟩
    have hyX : y ∈ X := hKX hy
    have h1 : ⁅x, y⁆ ∈ oddCoreOf X := by
      have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      refine (oddCoreOf X).mul_mem hx ?_
      have := conj_mem_oddCoreIn_of_mem_normalizer (Subgroup.le_normalizer hyX)
        ((oddCoreOf X).inv_mem hx)
      simpa [oddCoreIn_eq_oddCoreOf] using this
    have h2 : ⁅x, y⁆ ∈ K := by
      have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by
        simp [commutatorElement_def]
      rw [e]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN hxX) y).mp hy) (K.inv_mem hy)
    exact oddCoreOf_inf_le hKX ⟨h1, h2⟩
  exact psiK_eq_one_of_mem_trivialOnQuot K htriv

noncomputable instance (A : Type) [Group A] [Finite A] : Fintype (Idx2 A) := Fintype.ofFinite _

noncomputable instance (A : Type) [Group A] [Finite A] : DecidableEq (Idx2 A) :=
  Classical.decEq _

theorem sign_eq_neg_one_of_invol {A : Type} [Group A] [Finite A] (hc : Nat.card (Idx2 A) = 3)
    (σ : Equiv.Perm (Idx2 A)) (h1 : σ ≠ 1) (h2 : σ * σ = 1) : Equiv.Perm.sign σ = -1 := by
  have hf : Fintype.card (Idx2 A) = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact hc
  let eT : Idx2 A ≃ Fin 3 := Fintype.equivFinOfCardEq hf
  have h3 : eT.permCongr σ ≠ 1 := by
    intro h
    apply h1
    exact (map_eq_one_iff _ eT.permCongrHom.injective).mp h
  have h4 : eT.permCongr σ * eT.permCongr σ = 1 := by
    have h5 : eT.permCongr (σ * σ) = eT.permCongr σ * eT.permCongr σ :=
      map_mul eT.permCongrHom σ σ
    have h6 : eT.permCongr (1 : Equiv.Perm (Idx2 A)) = 1 := map_one eT.permCongrHom
    rw [← h5, h2, h6]
  rw [← Equiv.Perm.sign_permCongr eT σ]
  exact sign_of_invol _ h3 h4

open Classical in
noncomputable def epsK (K : Subgroup G) (y : G) : ℤˣ :=
  if hy : y ∈ Subgroup.normalizer (K : Set G) then Equiv.Perm.sign (psiK K ⟨y, hy⟩) else 1

theorem epsK_of_mem (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    epsK K y = Equiv.Perm.sign (psiK K ⟨y, hy⟩) := by
  unfold epsK
  exact dif_pos hy

theorem epsK_mul (K : Subgroup G) {a b : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) : epsK K (a * b) = epsK K a * epsK K b := by
  rw [epsK_of_mem K ((Subgroup.normalizer (K : Set G)).mul_mem ha hb), epsK_of_mem K ha,
    epsK_of_mem K hb]
  have : (⟨a * b, (Subgroup.normalizer (K : Set G)).mul_mem ha hb⟩ :
      ↥(Subgroup.normalizer (K : Set G))) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [this, map_mul, map_mul]

theorem epsK_one (K : Subgroup G) : epsK K 1 = 1 := by
  rw [epsK_of_mem K (Subgroup.one_mem _)]
  have : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 := rfl
  rw [this, map_one, map_one]

theorem epsK_inv (K : Subgroup G) {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    epsK K a⁻¹ = (epsK K a)⁻¹ := by
  have h := epsK_mul K ha ((Subgroup.normalizer (K : Set G)).inv_mem ha)
  rw [mul_inv_cancel, epsK_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem epsK_conj (K : Subgroup G) {a w : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hw : w ∈ Subgroup.normalizer (K : Set G)) : epsK K (a * w * a⁻¹) = epsK K w := by
  rw [epsK_mul K ((Subgroup.normalizer (K : Set G)).mul_mem ha hw)
    ((Subgroup.normalizer (K : Set G)).inv_mem ha), epsK_mul K ha hw, epsK_inv K ha,
    mul_comm (epsK K a), mul_inv_cancel_right]

@[expose] def kerG (K : Subgroup G) : Subgroup G :=
  (psiK K).ker.map (Subgroup.normalizer (K : Set G)).subtype

theorem mem_kerG {K : Subgroup G} {y : G} :
    y ∈ kerG K ↔ ∃ h : y ∈ Subgroup.normalizer (K : Set G), psiK K ⟨y, h⟩ = 1 := by
  unfold kerG
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨u, hu⟩, hk, rfl⟩
    exact ⟨hu, hk⟩
  · rintro ⟨h, h1⟩
    exact ⟨⟨y, h⟩, h1, rfl⟩

end Generic

end Out

open Out


variable {G : Type} [Group G] [Finite G] [FrameSimple G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
