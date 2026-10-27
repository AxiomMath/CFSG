module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnerAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts (centerDescend centerDescend_mk psuConj psuField)
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (conjAut fieldAut linearAutGroup
  conjAut_mem_linearAutGroup)

section Perfect

theorem eq_of_inv_mul_mem_center {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (φ₁ φ₂ : G →* H) (h : ∀ g, (φ₂ g)⁻¹ * φ₁ g ∈ Subgroup.center H) (g : G) :
    φ₁ g = φ₂ g := by
  let δ : G →* Subgroup.center H :=
    { toFun := fun g => ⟨(φ₂ g)⁻¹ * φ₁ g, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hca : (φ₂ b)⁻¹ * ((φ₂ a)⁻¹ * φ₁ a) = ((φ₂ a)⁻¹ * φ₁ a) * (φ₂ b)⁻¹ :=
          Subgroup.mem_center_iff.1 (h a) ((φ₂ b)⁻¹)
        show (φ₂ (a * b))⁻¹ * φ₁ (a * b) = ((φ₂ a)⁻¹ * φ₁ a) * ((φ₂ b)⁻¹ * φ₁ b)
        rw [map_mul, map_mul]
        calc (φ₂ a * φ₂ b)⁻¹ * (φ₁ a * φ₁ b)
            = ((φ₂ b)⁻¹ * ((φ₂ a)⁻¹ * φ₁ a)) * φ₁ b := by group
          _ = (((φ₂ a)⁻¹ * φ₁ a) * (φ₂ b)⁻¹) * φ₁ b := by rw [hca]
          _ = ((φ₂ a)⁻¹ * φ₁ a) * ((φ₂ b)⁻¹ * φ₁ b) := by group }
  have hker : commutator G ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  have h1 : δ g = 1 := hker (Subgroup.mem_top g)
  have h2 : (φ₂ g)⁻¹ * φ₁ g = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.1 h2).symm

end Perfect

section Forms

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]

@[expose] def IsLiftAt (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (g : X) (y : GL (Fin 3) K) : Prop :=
  y ∈ glPi π 3 (p ^ f) K ∧ ∀ s t : ↥(slPi π 3 (p ^ f) K),
    (t : GL (Fin 3) K) = y * s * y⁻¹ → g * ((ν s : ↥L) : X) * g⁻¹ = ((ν t : ↥L) : X)

@[expose] def IsFieldAt (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (g : X) (σ : K ≃+* K)
    (H : GL (Fin 3) K) : Prop :=
  orderOf σ = 3 ∧ H ∈ glPi π 3 (p ^ f) K ∧ ∀ s t : ↥(slPi π 3 (p ^ f) K),
    (t : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹ →
      g * ((ν s : ↥L) : X) * g⁻¹ = ((ν t : ↥L) : X)

theorem IsLiftAt.mem {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {g : X} {y : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) : y ∈ glPi π 3 (p ^ f) K :=
  hg.1

theorem IsLiftAt.act {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {g : X} {y : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) (s t : ↥(slPi π 3 (p ^ f) K)) (ht : (t : GL (Fin 3) K) = y * s * y⁻¹) :
    g * ((ν s : ↥L) : X) * g⁻¹ = ((ν t : ↥L) : X) :=
  hg.2 s t ht

theorem IsFieldAt.order {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {g : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hg : IsFieldAt ν g σ H) : orderOf σ = 3 :=
  hg.1

theorem IsFieldAt.mem {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {g : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hg : IsFieldAt ν g σ H) : H ∈ glPi π 3 (p ^ f) K :=
  hg.2.1

theorem IsFieldAt.act {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {g : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hg : IsFieldAt ν g σ H) (s t : ↥(slPi π 3 (p ^ f) K))
    (ht : (t : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹) :
    g * ((ν s : ↥L) : X) * g⁻¹ = ((ν t : ↥L) : X) :=
  hg.2.2 s t ht

end Forms

namespace LModel

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem hπ (M : LModel L π p f K ν) :
    π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
  fun h => by subst h; exact M.piField.unitary

theorem hq' (M : LModel L π p f K ν) : π = false → ModThree false (p ^ f) :=
  fun h => by subst h; exact M.modThree

@[expose] noncomputable def conjBy (M : LModel L π p f K ν) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) : MulAut ↥(slPi π 3 (p ^ f) K) :=
  (conjSL' M.hπ hy).symm

theorem coe_conjBy (M : LModel L π p f K ν) {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K)
    (s : ↥(slPi π 3 (p ^ f) K)) : ((M.conjBy hy s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
      y * s * y⁻¹ :=
  rfl

@[expose] noncomputable def fieldBy (M : LModel L π p f K ν) (σ : K ≃+* K) {H : GL (Fin 3) K}
    (hH : H ∈ glPi π 3 (p ^ f) K) : MulAut ↥(slPi π 3 (p ^ f) K) :=
  M.conjBy hH * frobSL M.piField σ * (M.conjBy hH)⁻¹

theorem coe_fieldBy (M : LModel L π p f K ν) (σ : K ≃+* K) {H : GL (Fin 3) K}
    (hH : H ∈ glPi π 3 (p ^ f) K) (s : ↥(slPi π 3 (p ^ f) K)) :
    ((M.fieldBy σ hH s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
      H * frobGL σ (H⁻¹ * s * H) * H⁻¹ :=
  rfl

end LModel

section Lifts

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem IsLiftAt.mul (M : LModel L π p f K ν) {g h : X} {y z : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) (hh : IsLiftAt ν h z) : IsLiftAt ν (g * h) (y * z) := by
  refine ⟨mul_mem hg.1 hh.1, fun s t ht => ?_⟩
  set u : ↥(slPi π 3 (p ^ f) K) := M.conjBy hh.1 s
  have h1 : h * ((ν s : ↥L) : X) * h⁻¹ = ((ν u : ↥L) : X) := hh.2 s u (M.coe_conjBy hh.1 s)
  have h2 : g * ((ν u : ↥L) : X) * g⁻¹ = ((ν t : ↥L) : X) :=
    hg.2 u t (by rw [ht, M.coe_conjBy]; group)
  rw [← h2, ← h1]
  group

theorem IsLiftAt.pow (M : LModel L π p f K ν) {g : X} {y : GL (Fin 3) K} (hg : IsLiftAt ν g y)
    (n : ℕ) : IsLiftAt ν (g ^ n) (y ^ n) := by
  induction n with
  | zero =>
    refine ⟨one_mem _, fun s t ht => ?_⟩
    have : t = s := Subtype.ext (by simpa using ht)
    rw [this]
    simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul M hg

theorem isLiftAt_one_of_mem_centralizer {c : X} (hc : c ∈ centralizer (L : Set X)) :
    IsLiftAt ν c 1 := by
  refine ⟨one_mem _, fun s t ht => ?_⟩
  have : t = s := Subtype.ext (by simpa using ht)
  rw [this]
  have := Subgroup.mem_centralizer_iff.1 hc ((ν s : ↥L) : X) (ν s).2
  calc c * ((ν s : ↥L) : X) * c⁻¹ = ((ν s : ↥L) : X) * c * c⁻¹ := by rw [this]
    _ = ((ν s : ↥L) : X) := mul_inv_cancel_right _ _

theorem isLiftAt_of_mem (M : LModel L π p f K ν) (s₀ : ↥(slPi π 3 (p ^ f) K)) :
    IsLiftAt ν ((ν s₀ : ↥L) : X) (s₀ : GL (Fin 3) K) := by
  refine ⟨slPi_le_glPi M.hπ s₀.2, fun s t ht => ?_⟩
  have : t = s₀ * s * s₀⁻¹ := Subtype.ext (by simpa using ht)
  rw [this, map_mul, map_mul, map_inv]
  simp

theorem IsLiftAt.mul_scalar {g : X} {y z : GL (Fin 3) K} (hg : IsLiftAt ν g y)
    (hzH : z ∈ glPi π 3 (p ^ f) K) (hzs : z ∈ StatedScalars (Fin 3) K) :
    IsLiftAt ν g (y * z) := by
  refine ⟨mul_mem hg.1 hzH, fun s t ht => hg.2 s t ?_⟩
  rw [ht]
  have hc := commute_of_mem_statedScalars hzs (s : GL (Fin 3) K)
  calc y * z * s * (y * z)⁻¹ = y * (z * s) * z⁻¹ * y⁻¹ := by group
    _ = y * (s * z) * z⁻¹ * y⁻¹ := by rw [hc]
    _ = y * s * y⁻¹ := by group

theorem mem_centralizer_of_isLiftAt (M : LModel L π p f K ν) {g : X} {z : GL (Fin 3) K}
    (hg : IsLiftAt ν g z) (hz : z ∈ StatedScalars (Fin 3) K) : g ∈ centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  obtain ⟨s, hs⟩ := M.surj ⟨l, hl⟩
  have hl' : l = ((ν s : ↥L) : X) := by rw [hs]
  have h1 := hg.2 s s (by
    have hc := commute_of_mem_statedScalars hz (s : GL (Fin 3) K)
    calc (s : GL (Fin 3) K) = s * z * z⁻¹ := (mul_inv_cancel_right _ _).symm
      _ = z * s * z⁻¹ := by rw [hc])
  rw [hl']
  calc ((ν s : ↥L) : X) * g = g * ((ν s : ↥L) : X) * g⁻¹ * g := by rw [h1]
    _ = g * ((ν s : ↥L) : X) := by group

theorem IsLiftAt.inv_mul_mem_zPi (M : LModel L π p f K ν) {g : X} {y y' : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) (hg' : IsLiftAt ν g y') : y⁻¹ * y' ∈ zPi π 3 (p ^ f) K := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  rw [zPi_eq M.hπ M.hq' hτ hτ1]
  refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hg.1) hg'.1, ?_⟩
  refine CFSG.HardMathSupport.Solomon.Coordinator.mem_statedScalars_of_comm_mod M.piField
    M.modThree M.two_lt fun s hs => ?_
  set s₀ : ↥(slPi π 3 (p ^ f) K) := ⟨s, hs⟩
  have h1 := hg.2 s₀ (M.conjBy hg.1 s₀) (M.coe_conjBy hg.1 s₀)
  have h2 := hg'.2 s₀ (M.conjBy hg'.1 s₀) (M.coe_conjBy hg'.1 s₀)
  have h3 : ν ((M.conjBy hg.1 s₀)⁻¹ * M.conjBy hg'.1 s₀) = 1 := by
    rw [map_mul, map_inv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [← h1, ← h2]
    group
  have h4 := M.ker_scalar _ h3
  rw [Subgroup.coe_mul, Subgroup.coe_inv, M.coe_conjBy, M.coe_conjBy] at h4
  set ζ : GL (Fin 3) K := (y * s * y⁻¹)⁻¹ * (y' * s * y'⁻¹) with hζ
  have hc := commute_of_mem_statedScalars h4
  have e1 : y⁻¹ * ζ * y = ζ := by rw [mul_assoc, ← hc y, ← mul_assoc, inv_mul_cancel, one_mul]
  have e2 : s * ζ * s⁻¹ = ζ := by rw [hc s, mul_inv_cancel_right]
  have key : ζ = (y⁻¹ * y') * s * (y⁻¹ * y')⁻¹ * s⁻¹ := by
    calc ζ = s * (y⁻¹ * ζ * y) * s⁻¹ := by rw [e1, e2]
      _ = (y⁻¹ * y') * s * (y⁻¹ * y')⁻¹ * s⁻¹ := by rw [hζ]; group
  rw [mem_centMod_iff_scalar]
  refine ⟨hs, ζ⁻¹, inv_mem h4, ?_⟩
  rw [key]
  group

end Lifts

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
