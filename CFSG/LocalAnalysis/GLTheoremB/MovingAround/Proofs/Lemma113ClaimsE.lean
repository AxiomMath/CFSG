module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsD
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsGamma
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsP2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

namespace EG

theorem psi_cube {M : Type*} [CommGroup M] (σ : M →* M) (hσ : ∀ m, σ (σ (σ m)) = m)
    (h3 : ∀ m : M, m ^ 3 = 1) (m : M) :
    (σ ((σ (σ m * m⁻¹)) * (σ m * m⁻¹)⁻¹) * ((σ (σ m * m⁻¹)) * (σ m * m⁻¹)⁻¹)⁻¹) = 1 := by
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, hσ]
  have h1 := h3 (σ m)
  have h2 := h3 (σ (σ m))
  calc _ = (σ m ^ 3) * ((σ (σ m)) ^ 3)⁻¹ * (m * m⁻¹) := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
    _ = 1 := by rw [h1, h2]; simp

theorem norm_eq {M : Type*} [CommGroup M] (a b d : M) (hb : b ^ 3 = 1) :
    d * b⁻¹ * (a * b⁻¹) = a * b * d := by
  have h2 : b⁻¹ * b⁻¹ = b := by
    have h3 : b * b * b = 1 := by simpa [pow_succ] using hb
    calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * (b * b * b) := by rw [h3, mul_one]
      _ = b := by group
  calc d * b⁻¹ * (a * b⁻¹) = a * d * (b⁻¹ * b⁻¹) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = a * b * d := by
        rw [h2]
        simp only [mul_assoc, mul_comm, mul_left_comm]

section MaxElemSec

variable {G : Type} [Group G] [Finite G]

@[expose] def MaxElem (V : Subgroup G) : Prop :=
  IsElemAbelian 3 V ∧ ∀ W : Subgroup G, IsElemAbelian 3 W → V ≤ W → W = V

theorem mem_map_conj {V : Subgroup G} {g y : G} :
    y ∈ V.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ V := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    show g⁻¹ * (g * v * g⁻¹) * g ∈ V
    rw [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
    exact hv
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem MaxElem.map {V : Subgroup G} (hV : MaxElem V) (g : G) :
    MaxElem (V.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Lemma113d.isElemAbelian_map_any _ hV.1, fun W hW hle => ?_⟩
  have hW' : IsElemAbelian 3 (W.map (MulAut.conj g⁻¹).toMonoidHom) :=
    Lemma113d.isElemAbelian_map_any _ hW
  have hVW' : V ≤ W.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro v hv
    have h1 : g * v * g⁻¹ ∈ W := hle (mem_map_conj.2 (by
      rw [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
      exact hv))
    exact mem_map_conj.2 (by simpa using h1)
  have hW'V := hV.2 _ hW' hVW'
  apply le_antisymm _ hle
  intro y hy
  have h2 : g⁻¹ * y * g ∈ W.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [mem_map_conj, show g⁻¹⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y by group]
    exact hy
  rw [hW'V] at h2
  exact mem_map_conj.2 h2

theorem MaxElem.eq_of_le {V W : Subgroup G} (hV : MaxElem V) (hW : IsElemAbelian 3 W)
    (hle : V ≤ W) : W = V := hV.2 W hW hle

end MaxElemSec

variable {G : Type} [Group G] [Finite G] {E A : Subgroup G} {e : G} {K Q R : Subgroup G}

section Lemmas

variable (r : RCfg E A e K Q R)
include r

theorem card_centralizer_x_le_three {x : G} (hxR : x ∈ R) (hxT : x ∉ R ⊓ N0 E (Q ⊓ K)) :
    Nat.card ↥((Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ 3 := by
  by_contra hgt
  push Not at hgt
  set W : Subgroup G := (Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) with hW
  have hdvd : Nat.card ↥W ∣ 3 ^ 3 := by
    have h27 : Nat.card ↥(Q ⊓ K : Subgroup G) = 3 ^ 3 := by rw [r.ctx.card_Q0]; norm_num
    rw [← h27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hiW⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hW9 : 9 ≤ Nat.card ↥W := by
    rw [hiW]
    by_contra hlt
    push Not at hlt
    have : i ≤ 1 := by
      by_contra hi2
      push Not at hi2
      have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
      omega
    have : 3 ^ i ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hxc := r.hfix hxR (W := W) inf_le_left hW9 (fun w hw =>
    Subgroup.mem_centralizer_iff.1 hw.2 x (Set.mem_singleton x))
  apply hxT
  refine ⟨hxR, r.mem_N0_of_mem_R hxR fun q hq => ?_⟩
  calc x * q * x⁻¹ = (q * x) * x⁻¹ := by rw [hxc q hq]
    _ = q := by group


theorem exists_psi_psi_ne_one {x : G} (hxR : x ∈ R) (hxT : x ∉ R ⊓ N0 E (Q ⊓ K)) :
    ∃ w ∈ (Q ⊓ K : Subgroup G),
      x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have c := r.ctx
  have hxQ : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
    fun q hq => c.Q0_invariant r.hB (r.hRN hxR) hq
  let φ : ↥(Q ⊓ K : Subgroup G) →* ↥(Q ⊓ K : Subgroup G) :=
    { toFun := fun w => ⟨x * w * x⁻¹ * w⁻¹,
        (Q ⊓ K : Subgroup G).mul_mem (hxQ w w.2) ((Q ⊓ K : Subgroup G).inv_mem w.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show x * ((a : G) * (b : G)) * x⁻¹ * ((a : G) * (b : G))⁻¹ =
          (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹)
        have hu : x * (b : G) * x⁻¹ * (b : G)⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
          (Q ⊓ K : Subgroup G).mul_mem (hxQ b b.2) ((Q ⊓ K : Subgroup G).inv_mem b.2)
        have hcomm : (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
            (a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹) :=
          c.Q0_comm hu ((Q ⊓ K : Subgroup G).inv_mem a.2)
        have e1 : x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹ =
            (x * a * x⁻¹) * ((x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
        have e2 : (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹) =
            (x * a * x⁻¹) * ((a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹)) := by group
        rw [e1, e2, hcomm] }
  have hker_le : (Subgroup.map (Q ⊓ K : Subgroup G).subtype φ.ker : Subgroup G) ≤
      (Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w.2, ?_⟩
    show (w : G) ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    have h1 : x * (w : G) * x⁻¹ * (w : G)⁻¹ = 1 := congrArg Subtype.val hw
    calc x * (w : G) = (x * (w : G) * x⁻¹ * (w : G)⁻¹) * (w : G) * x := by group
      _ = (w : G) * x := by rw [h1]; group
  have hkerc : Nat.card ↥φ.ker ≤ 3 := by
    calc Nat.card ↥φ.ker = Nat.card ↥(Subgroup.map (Q ⊓ K : Subgroup G).subtype φ.ker) :=
          (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
      _ ≤ Nat.card ↥((Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
          Subgroup.card_le_of_le hker_le
      _ ≤ 3 := card_centralizer_x_le_three r hxR hxT
  have hrk : φ.range ≤ φ.ker := by
    rintro _ ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hcon w w.2
  have hrc : Nat.card ↥φ.range ≤ 3 := (Subgroup.card_le_of_le hrk).trans hkerc
  have h := Subgroup.card_ker_mul_card_range φ
  have h27 : Nat.card ↥(Q ⊓ K : Subgroup G) = 27 := r.ctx.card_Q0
  rw [h27] at h
  have h9 : Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ 3 * 3 := Nat.mul_le_mul hkerc hrc
  omega


theorem nine_le_card_centralizer_E {x : G} (hxR : x ∈ R) (hxT : x ∉ R ⊓ N0 E (Q ⊓ K))
    (hx3 : x ^ 3 = 1) :
    9 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  classical
  have c := r.ctx
  have hxN : x ∈ Subgroup.normalizer (E : Set G) := r.hRN hxR
  have hxE : ∀ y ∈ E, x * y * x⁻¹ ∈ E := fun y hy => (Subgroup.mem_normalizer_iff.1 hxN y).1 hy
  have hxN1 : x ∈ N1 E (Q ⊓ K) := r.R_le_N1 hxR
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (c.E_comm a.2 b.2) }
  let X : ↥E →* ↥E :=
    { toFun := fun y => ⟨x * y * x⁻¹, hxE y y.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show x * ((a : G) * (b : G)) * x⁻¹ = (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹)
        group }
  have hXXX : ∀ m : ↥E, X (X (X m)) = m := by
    intro m
    apply Subtype.ext
    show x * (x * (x * (m : G) * x⁻¹) * x⁻¹) * x⁻¹ = m
    have hxxx : x * x * x = 1 := by simpa [pow_succ] using hx3
    have : x * (x * (x * (m : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * (m : G) * (x * x * x)⁻¹ := by
      group
    rw [this, hxxx]
    group
  have h3 : ∀ m : ↥E, m ^ 3 = 1 := fun m => Subtype.ext (by simpa using c.hEel.2 m m.2)
  let ψ : ↥E →* ↥E :=
    { toFun := fun y => X y * y⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        show X (a * b) * (a * b)⁻¹ = (X a * a⁻¹) * (X b * b⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hψ : ∀ y : ↥E, ((ψ y : ↥E) : G) = x * (y : G) * x⁻¹ * (y : G)⁻¹ := fun y => rfl
  set Q0E : Subgroup ↥E := (Q ⊓ K : Subgroup G).subgroupOf E with hQ0E
  have hQ0Ecard : Nat.card ↥Q0E = 27 := by
    rw [hQ0E, Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.Q0_le_E).toEquiv]
    exact c.card_Q0
  have hrange_le : ψ.range ≤ Q0E := by
    rintro _ ⟨y, rfl⟩
    rw [hQ0E, Subgroup.mem_subgroupOf, hψ]
    exact (mem_N1.1 hxN1).2.2 y y.2
  have hrange9 : Nat.card ↥ψ.range ≤ 9 := by
    have hdvd : Nat.card ↥ψ.range ∣ 3 ^ 4 := by
      rw [← c.hEcard]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi, hiR⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    by_contra hgt
    push Not at hgt
    have hi3 : 3 ≤ i := by
      by_contra hlt
      push Not at hlt
      have : 3 ^ i ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h27 : 27 ≤ Nat.card ↥ψ.range := by
      rw [hiR]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi3
    have heq : ψ.range = Q0E :=
      Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hQ0Ecard]; exact h27)
    obtain ⟨w, hw, hwne⟩ := exists_psi_psi_ne_one r hxR hxT
    have hwE : (⟨w, c.Q0_le_E hw⟩ : ↥E) ∈ Q0E := by
      rw [hQ0E, Subgroup.mem_subgroupOf]
      exact hw
    rw [← heq] at hwE
    obtain ⟨y, hy⟩ := hwE
    have hcube := psi_cube X hXXX h3 y
    apply hwne
    have e1 : ((ψ y : ↥E) : G) = w := congrArg Subtype.val hy
    have e2 : ((ψ (ψ y) : ↥E) : G) = x * w * x⁻¹ * w⁻¹ := by rw [hψ, e1]
    have e3 : ((ψ (ψ (ψ y)) : ↥E) : G) =
        x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ := by rw [hψ, e2]
    have e4 : ψ (ψ (ψ y)) = 1 := hcube
    rw [← e3, e4]
    rfl
  have hker_le : (Subgroup.map E.subtype ψ.ker : Subgroup G) ≤
      E ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    show (y : G) ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    have h1 : x * (y : G) * x⁻¹ * (y : G)⁻¹ = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
      simpa [hψ] using this
    calc x * (y : G) = (x * (y : G) * x⁻¹ * (y : G)⁻¹) * (y : G) * x := by group
      _ = (y : G) * x := by rw [h1]; group
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [c.hEcard] at hmul
  have hkerc : 9 ≤ Nat.card ↥ψ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥ψ.ker * Nat.card ↥ψ.range ≤ 8 * 9 :=
      Nat.mul_le_mul (by omega) hrange9
    omega
  calc 9 ≤ Nat.card ↥ψ.ker := hkerc
    _ = Nat.card ↥(Subgroup.map E.subtype ψ.ker) :=
        (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
    _ ≤ _ := Subgroup.card_le_of_le hker_le


theorem psi_psi_eq_norm {x : G} (hxR : x ∈ R) {w : G} (hw : w ∈ (Q ⊓ K : Subgroup G)) :
    x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ =
      w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) := by
  have c := r.ctx
  have hxQ : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
    fun q hq => c.Q0_invariant r.hB (r.hRN hxR) hq
  letI : CommGroup ↥(Q ⊓ K : Subgroup G) :=
    { (inferInstance : Group ↥(Q ⊓ K : Subgroup G)) with
      mul_comm := fun a b => Subtype.ext (c.Q0_comm a.2 b.2) }
  let a : ↥(Q ⊓ K : Subgroup G) := ⟨w, hw⟩
  let b : ↥(Q ⊓ K : Subgroup G) := ⟨x * w * x⁻¹, hxQ w hw⟩
  let d : ↥(Q ⊓ K : Subgroup G) := ⟨x * (x * w * x⁻¹) * x⁻¹, hxQ _ (hxQ w hw)⟩
  have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using c.Q0_pow_three b.2)
  have key := congrArg Subtype.val (norm_eq a b d hb3)
  calc x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹
      = (x * (x * w * x⁻¹) * x⁻¹) * (x * w * x⁻¹)⁻¹ * (w * (x * w * x⁻¹)⁻¹) := by group
    _ = w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) := by
        have h := key
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, a, b, d] at h
        rw [h]

theorem exists_u {x : G} (hxR : x ∈ R) (hxT : x ∉ R ⊓ N0 E (Q ⊓ K)) (hx3 : x ^ 3 = 1)
    {F : Subgroup G} (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hFcube : ∀ f ∈ F, f ^ 3 ∈ (Q ⊓ K : Subgroup G))
    (hFonto : ∀ q ∈ (Q ⊓ K : Subgroup G), ∃ f ∈ F, f ^ 3 = q)
    (hFx : ∀ f ∈ F, x * f * x⁻¹ ∈ F) :
    ∃ u ∈ F, x * u * x⁻¹ = u ∧ u ^ 3 ≠ 1 ∧ u ^ 9 = 1 := by
  have c := r.ctx
  obtain ⟨w, hw, hwne⟩ := exists_psi_psi_ne_one r hxR hxT
  obtain ⟨f, hfF, hf3⟩ := hFonto w hw
  set f₁ : G := x * f * x⁻¹ with hf₁
  set f₂ : G := x * f₁ * x⁻¹ with hf₂
  have hf₁F : f₁ ∈ F := hFx f hfF
  have hf₂F : f₂ ∈ F := hFx f₁ hf₁F
  have hu : f * f₁ * f₂ ∈ F := F.mul_mem (F.mul_mem hfF hf₁F) hf₂F
  have hxxx : x * x * x = 1 := by simpa [pow_succ] using hx3
  have hc1 : f * f₁ = f₁ * f := hFcomm f hfF f₁ hf₁F
  have hc2 : f * f₂ = f₂ * f := hFcomm f hfF f₂ hf₂F
  have hc3 : f₁ * f₂ = f₂ * f₁ := hFcomm f₁ hf₁F f₂ hf₂F
  have hu3 : (f * f₁ * f₂) ^ 3 = f ^ 3 * f₁ ^ 3 * f₂ ^ 3 := by
    have h1 : Commute (f * f₁) f₂ := by
      show f * f₁ * f₂ = f₂ * (f * f₁)
      calc f * f₁ * f₂ = f * (f₁ * f₂) := by group
        _ = f * (f₂ * f₁) := by rw [hc3]
        _ = (f * f₂) * f₁ := by group
        _ = (f₂ * f) * f₁ := by rw [hc2]
        _ = f₂ * (f * f₁) := by group
    rw [h1.mul_pow, (show Commute f f₁ from hc1).mul_pow]
  refine ⟨f * f₁ * f₂, hu, ?_, ?_, ?_⟩
  · have hf₃ : x * f₂ * x⁻¹ = f := by
      calc x * f₂ * x⁻¹ = (x * x * x) * f * (x * x * x)⁻¹ := by simp only [hf₂, hf₁]; group
        _ = f := by rw [hxxx]; group
    have h1 : x * (f * f₁ * f₂) * x⁻¹ = f₁ * f₂ * f := by
      calc x * (f * f₁ * f₂) * x⁻¹ = (x * f * x⁻¹) * (x * f₁ * x⁻¹) * (x * f₂ * x⁻¹) := by group
        _ = f₁ * f₂ * f := by rw [← hf₁, ← hf₂, hf₃]
    rw [h1]
    calc f₁ * f₂ * f = f₁ * (f₂ * f) := by group
      _ = f₁ * (f * f₂) := by rw [hc2]
      _ = (f₁ * f) * f₂ := by group
      _ = (f * f₁) * f₂ := by rw [hc1]
  · have h1 : f₁ ^ 3 = x * w * x⁻¹ := by
      rw [hf₁, conj_pow, hf3]
    have h2 : f₂ ^ 3 = x * (x * w * x⁻¹) * x⁻¹ := by
      rw [hf₂, conj_pow, h1]
    rw [hu3, hf3, h1, h2, ← psi_psi_eq_norm r hxR hw]
    exact hwne
  · have hmem : (f * f₁ * f₂) ^ 3 ∈ (Q ⊓ K : Subgroup G) := hFcube _ hu
    have : (f * f₁ * f₂) ^ 9 = ((f * f₁ * f₂) ^ 3) ^ 3 := by rw [← pow_mul]
    rw [this]
    exact c.Q0_pow_three hmem


omit r in
theorem normalizes_map {U : Subgroup G} {u : G} (hu : ∀ y ∈ U, u * y * u⁻¹ ∈ U) (g : G) :
    ∀ y ∈ U.map (MulAut.conj g).toMonoidHom,
      (g * u * g⁻¹) * y * (g * u * g⁻¹)⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨u * v * u⁻¹, hu v hv, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem core (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G))
    {F : Subgroup G} (hFT : F ≤ R ⊓ N0 E (Q ⊓ K))
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hFcube : ∀ f ∈ F, f ^ 3 ∈ (Q ⊓ K : Subgroup G))
    (hFonto : ∀ q ∈ (Q ⊓ K : Subgroup G), ∃ f ∈ F, f ^ 3 = q)
    (hFinv : ∀ g : G, (∀ t ∈ R ⊓ N0 E (Q ⊓ K), g * t * g⁻¹ ∈ R ⊓ N0 E (Q ⊓ K)) →
      ∀ f ∈ F, g * f * g⁻¹ ∈ F)
    (hΩ : ∀ t ∈ R ⊓ N0 E (Q ⊓ K), t ^ 3 = 1 → t ∈ E)
    {x : G} (hxQ : x ∈ Q) (hxE : x ∉ E) (hx3 : x ^ 3 = 1) {g : G} (hg : g * x * g⁻¹ = e) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := r.ctx
  have hB := r.hB
  have hxR : x ∈ R := r.hQR hxQ
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ E.one_mem)
  have hxT : x ∉ R ⊓ N0 E (Q ⊓ K) := fun h => hxE (hΩ x h hx3)
  have hPE : (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K = E := by
    rw [c.centBar_eq_zpowers hB, ← c.hEeq]
  have hxP : x ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by rw [hPE]; exact hxE
  set Y : Subgroup G := E ⊓ Subgroup.centralizer ({x} : Set G) with hY
  have hY9 : 9 ≤ Nat.card ↥Y := nine_le_card_centralizer_E r hxR hxT hx3
  have hYel : IsElemAbelian 3 Y := isElemAbelian_of_le' c.hEel inf_le_left
  have hXel : IsElemAbelian 3 (Subgroup.zpowers x) := l113_isElemAbelian_zpowers hx3
  have hxcomm : ∀ y ∈ Y, x * y = y * x := fun y hy =>
    Subgroup.mem_centralizer_iff.1 hy.2 x (Set.mem_singleton x)
  have hYcent : Y ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((Commute.zpow_left (show Commute x y from hxcomm y hy) k).eq)
  set U : Subgroup G := Y ⊔ Subgroup.zpowers x with hU
  have hUel : IsElemAbelian 3 U := isElemAbelian_sup_of_commute hYel hXel hYcent
  have hxY : x ∉ Y := fun h => hxE h.1
  have hnormY : Subgroup.zpowers x ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_le fun y hy => ?_
    have : x * y * x⁻¹ = y := by rw [hxcomm y hy]; group
    rw [this]
    exact hy
  have hUcard : Nat.card ↥U = 3 * Nat.card ↥Y := l113_card_sup_zpowers Y hx3 hx1 hxY hnormY
  have hUQ : U ≤ Q := sup_le (inf_le_left.trans c.hEQ) (Subgroup.zpowers_le.2 hxQ)
  have hUR : U ≤ R := hUQ.trans r.hQR
  have hUC : U ≤ Subgroup.centralizer ({x} : Set G) := by
    apply sup_le inf_le_right
    rw [Subgroup.zpowers_le]
    show x ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
  obtain ⟨q, hqQ, hqx⟩ := Lemma113Claims.B.exists_conj_mem_A c hxQ hx3 hxP
  have hqxE : q * x * q⁻¹ ∉ E := by
    intro h
    apply hxE
    have hqN : q⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      inv_mem (Lemma113Claims.Gamma.mem_normalizer_E c hB hqQ)
    have h2 := (Subgroup.mem_normalizer_iff.1 hqN _).1 h
    simp only [inv_inv] at h2
    rwa [show q⁻¹ * (q * x * q⁻¹) * q = x by group] at h2
  have hqxP : q * x * q⁻¹ ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by rw [hPE]; exact hqxE
  have hU1Q : U.map (MulAut.conj q).toMonoidHom ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact Q.mul_mem (Q.mul_mem hqQ (hUQ hy)) (Q.inv_mem hqQ)
  have hU1A : U.map (MulAut.conj q).toMonoidHom ≤ A :=
    Lemma113Claims.B.le_A_of_mem c hZ9 hU1Q (Lemma113d.isElemAbelian_map_any _ hUel)
      (y := q * x * q⁻¹)
      (mem_map_conj.2 (by
        rw [show q⁻¹ * (q * x * q⁻¹) * q = x by group]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
      hqx hqxP
  have hU1card : Nat.card ↥(U.map (MulAut.conj q).toMonoidHom) = Nat.card ↥U :=
    Subgroup.card_map_of_injective (MulAut.conj q).injective
  have hU27 : 27 ≤ Nat.card ↥U := by omega
  have hU1eq : U.map (MulAut.conj q).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hU1A (by rw [c.hAcard, hU1card]; norm_num; omega)
  have hUcard27 : Nat.card ↥U = 27 := by
    have : Nat.card ↥A = 27 := by rw [c.hAcard]; norm_num
    rw [← hU1card, hU1eq, this]
  have hMaxA : MaxElem A := ⟨c.hAel, fun W hW hle => c.hAmax W le_top hW hle⟩
  have hUeq : U = A.map (MulAut.conj q⁻¹).toMonoidHom := by
    ext y
    rw [mem_map_conj, ← hU1eq, mem_map_conj]
    simp only [inv_inv]
    constructor
    · intro hy; rw [show q⁻¹ * (q * y * q⁻¹) * q = y by group]; exact hy
    · intro hy
      have := hy
      rw [show q⁻¹ * (q * y * q⁻¹) * q = y by group] at this
      exact this
  have hMaxU : MaxElem U := by rw [hUeq]; exact hMaxA.map q⁻¹
  have hFx : ∀ f ∈ F, x * f * x⁻¹ ∈ F :=
    hFinv x (fun t ht => (Subgroup.mem_normalizer_iff.1 (r.R_normalizes_T hxR) t).1 ht)
  obtain ⟨u, huF, hxu, hu3, -⟩ := exists_u r hxR hxT hx3 hFcomm hFcube hFonto hFx
  have huT := hFT huF
  have hux : u * x = x * u := by
    calc u * x = (x * u * x⁻¹) * x := by rw [hxu]
      _ = x * u := by group
  have hunorm : ∀ y ∈ U, u * y * u⁻¹ ∈ U := by
    have hW : U ≤ U.comap (MulAut.conj u).toMonoidHom := by
      apply sup_le
      · intro y hy
        show u * y * u⁻¹ ∈ U
        have hc₁ : u * y * u⁻¹ * y⁻¹ ∈ (Q ⊓ K : Subgroup G) := N0.shear_mem huT.2 hy.1
        have hxy : x * y * x⁻¹ = y := by rw [hxcomm y hy]; group
        have hc₁x : u * y * u⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff.1 hz]
          have : x * (u * y * u⁻¹ * y⁻¹) * x⁻¹ = u * y * u⁻¹ * y⁻¹ := by
            calc x * (u * y * u⁻¹ * y⁻¹) * x⁻¹
                = (x * u * x⁻¹) * (x * y * x⁻¹) * (x * u * x⁻¹)⁻¹ * (x * y * x⁻¹)⁻¹ := by group
              _ = u * y * u⁻¹ * y⁻¹ := by rw [hxu, hxy]
          calc x * (u * y * u⁻¹ * y⁻¹) = (x * (u * y * u⁻¹ * y⁻¹) * x⁻¹) * x := by group
            _ = (u * y * u⁻¹ * y⁻¹) * x := by rw [this]
        have hc₁Y : u * y * u⁻¹ * y⁻¹ ∈ Y := ⟨c.Q0_le_E hc₁, hc₁x⟩
        have : u * y * u⁻¹ = (u * y * u⁻¹ * y⁻¹) * y := by group
        rw [this]
        exact U.mul_mem (Subgroup.mem_sup_left hc₁Y) (Subgroup.mem_sup_left hy)
      · rw [Subgroup.zpowers_le]
        show u * x * u⁻¹ ∈ U
        rw [show u * x * u⁻¹ = x by rw [hux]; group]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    intro y hy
    exact hW hy
  set S : Subgroup G := R ⊓ Subgroup.centralizer ({x} : Set G) with hS
  have hSp : IsPGroup 3 ↥S := r.hRp.to_le inf_le_left
  have hSC : S.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({e} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz, ← hg]
    have hxs : x * s = s * x := Subgroup.mem_centralizer_iff.1 hs.2 x (Set.mem_singleton x)
    show g * x * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * s * g⁻¹) = g * (x * s) * g⁻¹ := by group
      _ = g * (s * x) * g⁻¹ := by rw [hxs]
      _ = g * s * g⁻¹ * (g * x * g⁻¹) := by group
  obtain ⟨c', hc'C, hc'⟩ := Lemma113b.exists_conj_mem_of_isSylowIn c.hQ hSC (hSp.map _)
  have hec : e * c' = c' * e := Subgroup.mem_centralizer_iff.1 hc'C e (Set.mem_singleton e)
  set g' : G := c' * g with hg'
  have hg'x : g' * x * g'⁻¹ = e := by
    calc g' * x * g'⁻¹ = c' * (g * x * g⁻¹) * c'⁻¹ := by rw [hg']; group
      _ = e := by rw [hg, ← hec]; group
  have hg'S : ∀ s ∈ S, g' * s * g'⁻¹ ∈ Q := by
    intro s hs
    have h1 := hc' (g * s * g⁻¹) ⟨s, hs, rfl⟩
    have h2 : g' * s * g'⁻¹ = c' * (g * s * g⁻¹) * c'⁻¹ := by rw [hg']; group
    rw [h2]
    exact h1
  have hUS : U ≤ S := le_inf hUR hUC
  have huS : u ∈ S := ⟨huT.1, by
    show u ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact hux.symm⟩
  set U' : Subgroup G := U.map (MulAut.conj g').toMonoidHom with hU'
  have hU'Q : U' ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg'S y (hUS hy)
  have hMaxU' : MaxElem U' := hMaxU.map g'
  have hU'card : Nat.card ↥U' = 27 := by
    rw [hU', Subgroup.card_map_of_injective (MulAut.conj g').injective, hUcard27]
  have hU'E : ¬ U' ≤ E := by
    intro h
    have hEeq : E = U' := hMaxU'.eq_of_le c.hEel h
    have h81 := c.hEcard
    rw [hEeq, hU'card] at h81
    norm_num at h81
  obtain ⟨y', hy'U', hy'E⟩ := SetLike.not_le_iff_exists.1 hU'E
  have hy'Q : y' ∈ Q := hU'Q hy'U'
  have hy'3 : y' ^ 3 = 1 := hMaxU'.1.2 y' hy'U'
  have hy'P : y' ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by rw [hPE]; exact hy'E
  obtain ⟨q₁, hq₁Q, hq₁y⟩ := Lemma113Claims.B.exists_conj_mem_A c hy'Q hy'3 hy'P
  have hq₁yE : q₁ * y' * q₁⁻¹ ∉ E := by
    intro h
    apply hy'E
    have hqN : q₁⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      inv_mem (Lemma113Claims.Gamma.mem_normalizer_E c hB hq₁Q)
    have h2 := (Subgroup.mem_normalizer_iff.1 hqN _).1 h
    simp only [inv_inv] at h2
    rwa [show q₁⁻¹ * (q₁ * y' * q₁⁻¹) * q₁ = y' by group] at h2
  have hq₁yP : q₁ * y' * q₁⁻¹ ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
    rw [hPE]; exact hq₁yE
  set U'' : Subgroup G := U'.map (MulAut.conj q₁).toMonoidHom with hU''
  have hU''Q : U'' ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact Q.mul_mem (Q.mul_mem hq₁Q (hU'Q hy)) (Q.inv_mem hq₁Q)
  have hU''el : IsElemAbelian 3 U'' := Lemma113d.isElemAbelian_map_any _ hMaxU'.1
  have hU''A : U'' ≤ A :=
    Lemma113Claims.B.le_A_of_mem c hZ9 hU''Q hU''el (y := q₁ * y' * q₁⁻¹)
      (mem_map_conj.2 (by
        rw [show q₁⁻¹ * (q₁ * y' * q₁⁻¹) * q₁ = y' by group]
        exact hy'U'))
      hq₁y hq₁yP
  have hU''card : Nat.card ↥U'' = 27 := by
    rw [hU'', Subgroup.card_map_of_injective (MulAut.conj q₁).injective, hU'card]
  have hU''eq : U'' = A :=
    Subgroup.eq_of_le_of_card_ge hU''A (by rw [c.hAcard, hU''card]; norm_num)
  have hu'norm := normalizes_map hunorm g'
  have hu''norm := normalizes_map hu'norm q₁
  have hu''Q : q₁ * (g' * u * g'⁻¹) * q₁⁻¹ ∈ Q :=
    Q.mul_mem (Q.mul_mem hq₁Q (hg'S u huS)) (Q.inv_mem hq₁Q)
  have hcube := Lemma113Claims.Gamma.normalizer_A_cube c hB hu''Q (fun a ha => by
    rw [← hU''eq] at ha ⊢
    exact hu''norm a ha)
  apply hu3
  have e1 : q₁ * (g' * u * g'⁻¹) * q₁⁻¹ = (q₁ * g') * u * (q₁ * g')⁻¹ := by group
  rw [e1, conj_pow] at hcube
  calc u ^ 3 = (q₁ * g')⁻¹ * ((q₁ * g') * u ^ 3 * (q₁ * g')⁻¹) * (q₁ * g') := by group
    _ = 1 := by rw [hcube]; group


theorem conj_e_mem_E (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G))
    {F : Subgroup G} (hFT : F ≤ R ⊓ N0 E (Q ⊓ K))
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hFcube : ∀ f ∈ F, f ^ 3 ∈ (Q ⊓ K : Subgroup G))
    (hFonto : ∀ q ∈ (Q ⊓ K : Subgroup G), ∃ f ∈ F, f ^ 3 = q)
    (hFinv : ∀ g : G, (∀ t ∈ R ⊓ N0 E (Q ⊓ K), g * t * g⁻¹ ∈ R ⊓ N0 E (Q ⊓ K)) →
      ∀ f ∈ F, g * f * g⁻¹ ∈ F)
    (hΩ : ∀ t ∈ R ⊓ N0 E (Q ⊓ K), t ^ 3 = 1 → t ∈ E)
    {g : G} (hg : g⁻¹ * e * g ∈ R) : g⁻¹ * e * g ∈ E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := r.ctx
  have hB := r.hB
  by_contra hxE
  set x₀ : G := g⁻¹ * e * g with hx₀
  have hx₀3 : x₀ ^ 3 = 1 := by
    have h1 := conj_pow (a := g⁻¹) (b := e) (i := 3)
    simp only [inv_inv] at h1
    rw [hx₀, h1, c.he3]
    group
  have hx₀R : x₀ ∈ R := hg
  have hx₀T : x₀ ∉ R ⊓ N0 E (Q ⊓ K) := fun h => hxE (hΩ x₀ h hx₀3)
  have hY9 := nine_le_card_centralizer_E r hx₀R hx₀T hx₀3
  have hex : ∃ e₁ ∈ E ⊓ Subgroup.centralizer ({x₀} : Set G), e₁ ∉ (Q ⊓ K : Subgroup G) := by
    by_contra hcon
    push Not at hcon
    have hle : (E ⊓ Subgroup.centralizer ({x₀} : Set G) : Subgroup G) ≤
        (Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({x₀} : Set G) :=
      le_inf (fun y hy => hcon y hy) inf_le_right
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_centralizer_x_le_three r hx₀R hx₀T
    omega
  obtain ⟨e₁, he₁, he₁Q⟩ := hex
  have he₁C : x₀ * e₁ = e₁ * x₀ := Subgroup.mem_centralizer_iff.1 he₁.2 x₀ (Set.mem_singleton x₀)
  obtain ⟨q, hq, hzq⟩ := c.zpowers_form he₁.1 he₁Q
  have he₁mem : e₁ ∈ Subgroup.zpowers (e * q) := hzq ▸ Subgroup.mem_zpowers e₁
  have hy3 : (e * q) ^ 3 = 1 := by
    have hqe : Commute e q := c.hKe q hq.2
    rw [hqe.mul_pow, c.he3, c.Q0_pow_three hq, one_mul]
  have he₁1 : e₁ ≠ 1 := fun h => he₁Q (h ▸ (Q ⊓ K : Subgroup G).one_mem)
  have hcomm : x₀ * (e * q) = (e * q) * x₀ := by
    rcases mem_zpowers_cases hy3 he₁mem with h1 | h1 | h1
    · exact absurd h1 he₁1
    · rw [h1] at he₁C; exact he₁C
    · rw [h1] at he₁C
      have h2 : Commute x₀ (e * q)⁻¹ := he₁C
      exact (Commute.inv_right_iff.1 h2).eq
  obtain ⟨ρ, hρR, hρ⟩ := P2.R_class_of_e r hq
  set x₁ : G := ρ⁻¹ * x₀ * ρ with hx₁
  have hx₁R : x₁ ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hρR) hx₀R) hρR
  have hx₁e : e * x₁ = x₁ * e := by
    calc e * x₁ = ρ⁻¹ * ((ρ * e * ρ⁻¹) * x₀) * ρ := by simp only [hx₁]; group
      _ = ρ⁻¹ * (x₀ * (ρ * e * ρ⁻¹)) * ρ := by rw [hρ, hcomm]
      _ = x₁ * e := by simp only [hx₁]; group
  have hRC : R ⊓ Subgroup.centralizer ({e} : Set G) = Q :=
    c.hQ.2.2 (R ⊓ Subgroup.centralizer ({e} : Set G)) inf_le_right
      (r.hRp.to_le inf_le_left) (le_inf r.hQR c.hQ.1)
  have hx₁Q : x₁ ∈ Q := by
    rw [← hRC]
    refine ⟨hx₁R, ?_⟩
    show x₁ ∈ Subgroup.centralizer ({e} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact hx₁e
  have hx₁E : x₁ ∉ E := by
    intro h
    apply hxE
    have hρN : ρ ∈ Subgroup.normalizer (E : Set G) := r.hRN hρR
    have h2 := (Subgroup.mem_normalizer_iff.1 hρN _).1 h
    have e1 : ρ * x₁ * ρ⁻¹ = x₀ := by simp only [hx₁]; group
    rwa [e1] at h2
  have hx₁3 : x₁ ^ 3 = 1 := by
    have h1 := conj_pow (a := ρ⁻¹) (b := x₀) (i := 3)
    simp only [inv_inv] at h1
    rw [hx₁, h1, hx₀3]
    group
  have hgx : (g * ρ) * x₁ * (g * ρ)⁻¹ = e := by
    simp only [hx₁, hx₀]
    group
  exact core r hZ9 hFT hFcomm hFcube hFonto hFinv hΩ hx₁Q hx₁E hx₁3 hgx

end Lemmas

end EG

end Lemma113Claims

theorem pieceD_subEConj_holds : Lemma113g.PieceD_SubEConj := by
  intro G _ _ m B M E A a e K Q h hC R hR hQR g hg
  have h0 := lemma113_ii_piece0_holds h
  have hA := lemma113_ii_pieceA_of_inputs' Lemma113Claims.hC113 h h0
  have hB := lemma113_ii_pieceB_holds' h hA
  have r := Lemma113Claims.D.rcfg_of_sylow h hA hB hR hQR
  have hZ9 := Lemma113Claims.B.card_inf_ge_nine h r.ctx.hAel
  have hΩ := r.omega_le_E h.ha.1 (Lemma113Claims.normalizer_le_M h) h0
  have hWC := Lemma113e.pieceB_WC_of h hA
  rcases r.dichotomy with ⟨F, hFT, -, hFcomm, hFcube, -, hFonto, -, hFinv, -⟩ | hF
  · have hE := Lemma113Claims.EG.conj_e_mem_E r hZ9 hFT hFcomm hFcube hFonto hFinv hΩ hg
    exact ⟨hE, Lemma113Claims.P2.part2 r hWC hE⟩
  · exact absurd hF (r.no_big_abelian h.ha.1 (Lemma113Claims.normalizer_le_M h) h0)

theorem lemma113_ii_pieceD_of_inputs' : Lemma113_ii_pieceDStatement :=
  Lemma113g.lemma113_ii_pieceD_of_subclaims pieceD_subEConj_holds pieceD_subNorm_holds
    pieceD_subOut_holds pieceD_subR4_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
