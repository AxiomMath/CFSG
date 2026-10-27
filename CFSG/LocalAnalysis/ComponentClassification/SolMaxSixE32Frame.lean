module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Ctx
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCL
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Abel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightCoordinates

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}

@[expose] def aF (s w₀ w₁ x : X) : Fin 4 → X := ![s * w₀, s * w₁, s * (w₀ * w₁), s * x]

structure IsFrame (Z : Ctx M θ ρ t s H Q) (w₀ w₁ x : X) : Prop where
  w₀M : w₀ ∈ M
  w₁M : w₁ ∈ M
  xM : x ∈ M
  E5 : IsE5 ![s, t, w₀, w₁, x]
  ρw₀ : rhoX ρ w₀ = p 1 * p 2
  ρw₁ : rhoX ρ w₁ = p 0 * p 2
  ρx : rhoX ρ x = πx

private theorem isE5_of_forall {g : Fin 5 → X} {S : Set X} (hsq : ∀ a ∈ S, a * a = 1)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hg : ∀ i, g i ∈ S) : IsE5 g :=
  ⟨fun i => hsq _ (hg i), fun i j => hcomm _ (hg i) _ (hg j)⟩

namespace Ctx

variable (Z : Ctx M θ ρ t s H Q)
include Z

private theorem lift_step {g : Fin 5 → X} (hg : IsE5 g) (hgN : ∀ i, g i ∈ normalizer (M : Set X))
    {b : Perm (Fin 9)} (hbA : b ∈ alternatingGroup (Fin 9)) (hb2 : b * b = 1)
    (hbc : ∀ i, b * rhoX ρ (g i) = rhoX ρ (g i) * b) :
    ∃ x ∈ M, (∀ i, g i * x = x * g i) ∧ x * x = 1 ∧ rhoX ρ x = b := by
  have hBN : Subgroup.closure (Set.range g) ≤ normalizer (M : Set X) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgN i
  have hbB : ∀ (y : X) (hy : y ∈ Subgroup.closure (Set.range g)),
      b * ρ ⟨y, hBN hy⟩ = ρ ⟨y, hBN hy⟩ * b := by
    set Zc : Subgroup X := ((centralizer ({b} : Set (Perm (Fin 9)))).comap ρ).map
      (normalizer (M : Set X)).subtype with hZc
    have hBZ : Subgroup.closure (Set.range g) ≤ Zc := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨⟨g i, hgN i⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr ?_), rfl⟩
      rw [← rhoX_of_mem (hgN i)]
      exact (hbc i).symm
    intro y hy
    obtain ⟨y', hy', hyy⟩ := hBZ hy
    have h1 : (⟨y, hBN hy⟩ : ↥(normalizer (M : Set X))) = y' := Subtype.ext hyy.symm
    rw [h1]
    exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hy')).symm
  obtain ⟨x, hxM, hxC, hx2, hρx⟩ :=
    exists_lift_involution Z.hρ hBN hg.isPGroup_closure hbA hb2 hbB
  refine ⟨x, hxM, fun i => ?_, hx2, ?_⟩
  · exact mem_centralizer_iff.mp hxC (g i) (Subgroup.subset_closure (Set.mem_range_self i))
  · rw [rhoX_of_mem (le_normalizer hxM)]
    exact hρx

theorem exists_frame : ∃ w₀ w₁ x : X, IsFrame Z w₀ w₁ x := by
  have hsN : s ∈ normalizer (M : Set X) := Z.s_mem_N
  have htN : t ∈ normalizer (M : Set X) := Z.t_mem_N
  have hρt : rhoX ρ t = 1 := Z.rho_t
  have hρs : rhoX ρ s = σ₀ := Z.hρs
  have hs2 : s * s = 1 := Z.hs2
  have ht2 : t * t = 1 := Z.ht2
  have hst : s * t = t * s := Z.hst
  have c12 : p 1 * p 2 * σ₀ = σ₀ * (p 1 * p 2) := by decide
  have c02 : p 0 * p 2 * σ₀ = σ₀ * (p 0 * p 2) := by decide
  have c02' : p 0 * p 2 * (p 1 * p 2) = p 1 * p 2 * (p 0 * p 2) := by decide
  have cx0 : πx * σ₀ = σ₀ * πx := by decide
  have cx12 : πx * (p 1 * p 2) = p 1 * p 2 * πx := by decide
  have cx02 : πx * (p 0 * p 2) = p 0 * p 2 * πx := by decide
  have sq12 : p 1 * p 2 * (p 1 * p 2) = 1 := by decide
  have sq02 : p 0 * p 2 * (p 0 * p 2) = 1 := by decide
  obtain ⟨w₀, hw₀M, hw₀c, hw₀2, hρw₀⟩ := Z.lift_step (g := ![s, t, t, t, t])
    (isE5_of_forall (S := {s, t})
      (by rintro a (rfl | rfl) <;> assumption)
      (by rintro a (rfl | rfl) b (rfl | rfl) <;> first | rfl | assumption | exact hst.symm)
      (fun i => by fin_cases i <;> simp))
    (fun i => by fin_cases i <;> simp [hsN, htN]) p12_mem_alt sq12
    (fun i => by fin_cases i <;> simp [hρs, hρt, c12])
  have hw₀N : w₀ ∈ normalizer (M : Set X) := le_normalizer hw₀M
  have hsw₀ : s * w₀ = w₀ * s := hw₀c 0
  have htw₀ : t * w₀ = w₀ * t := hw₀c 1
  obtain ⟨w₁, hw₁M, hw₁c, hw₁2, hρw₁⟩ := Z.lift_step (g := ![s, t, w₀, w₀, w₀])
    (isE5_of_forall (S := {s, t, w₀})
      (by rintro a (rfl | rfl | rfl) <;> assumption)
      (by
        rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) <;>
          first | rfl | assumption | (symm; assumption))
      (fun i => by fin_cases i <;> simp))
    (fun i => by fin_cases i <;> simp [hsN, htN, hw₀N]) p02_mem_alt sq02
    (fun i => by fin_cases i <;> simp [hρs, hρt, hρw₀, c02, c02'])
  have hw₁N : w₁ ∈ normalizer (M : Set X) := le_normalizer hw₁M
  have hsw₁ : s * w₁ = w₁ * s := hw₁c 0
  have htw₁ : t * w₁ = w₁ * t := hw₁c 1
  have hw₀w₁ : w₀ * w₁ = w₁ * w₀ := hw₁c 2
  obtain ⟨x, hxM, hxc, hx2, hρx⟩ := Z.lift_step (g := ![s, t, w₀, w₁, w₁])
    (isE5_of_forall (S := {s, t, w₀, w₁})
      (by rintro a (rfl | rfl | rfl | rfl) <;> assumption)
      (by
        rintro a (rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl) <;>
          first | rfl | assumption | (symm; assumption))
      (fun i => by fin_cases i <;> simp))
    (fun i => by fin_cases i <;> simp [hsN, htN, hw₀N, hw₁N]) πx_mem_alt πx_mul_self
    (fun i => by fin_cases i <;> simp [hρs, hρt, hρw₀, hρw₁, cx0, cx12, cx02])
  have hsx : s * x = x * s := hxc 0
  have htx : t * x = x * t := hxc 1
  have hw₀x : w₀ * x = x * w₀ := hxc 2
  have hw₁x : w₁ * x = x * w₁ := hxc 3
  refine ⟨w₀, w₁, x, ⟨hw₀M, hw₁M, hxM, ?_, hρw₀, hρw₁, hρx⟩⟩
  exact isE5_of_forall (S := {s, t, w₀, w₁, x})
    (by rintro a (rfl | rfl | rfl | rfl | rfl) <;> assumption)
    (by
      rintro a (rfl | rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl | rfl) <;>
        first | rfl | assumption | (symm; assumption))
    (fun i => by fin_cases i <;> simp)

end Ctx

namespace IsFrame

variable {Z : Ctx M θ ρ t s H Q} {w₀ w₁ x : X} (F : IsFrame Z w₀ w₁ x)
include F

private theorem rhoX_mono (u : Fin 5 → ZMod 2) :
    rhoX ρ (mono ![s, t, w₀, w₁, x] u) =
      σ₀ ^ (u 0).val * (p 1 * p 2) ^ (u 2).val * (p 0 * p 2) ^ (u 3).val * πx ^ (u 4).val := by
  have hs : s ∈ normalizer (M : Set X) := Z.s_mem_N
  have ht : t ∈ normalizer (M : Set X) := Z.t_mem_N
  have h0 : w₀ ∈ normalizer (M : Set X) := le_normalizer F.w₀M
  have h1 : w₁ ∈ normalizer (M : Set X) := le_normalizer F.w₁M
  have h2 : x ∈ normalizer (M : Set X) := le_normalizer F.xM
  show rhoX ρ (s ^ (u 0).val * t ^ (u 1).val * w₀ ^ (u 2).val * w₁ ^ (u 3).val *
    x ^ (u 4).val) = _
  rw [rhoX_mul (mul_mem (mul_mem (mul_mem (pow_mem hs _) (pow_mem ht _)) (pow_mem h0 _))
      (pow_mem h1 _)) (pow_mem h2 _),
    rhoX_mul (mul_mem (mul_mem (pow_mem hs _) (pow_mem ht _)) (pow_mem h0 _)) (pow_mem h1 _),
    rhoX_mul (mul_mem (pow_mem hs _) (pow_mem ht _)) (pow_mem h0 _),
    rhoX_mul (pow_mem hs _) (pow_mem ht _),
    Z.rhoX_pow hs, Z.rhoX_pow ht, Z.rhoX_pow h0, Z.rhoX_pow h1, Z.rhoX_pow h2,
    Z.hρs, Z.rho_t, F.ρw₀, F.ρw₁, F.ρx, one_pow, mul_one]

private theorem rho_sw₁ : rhoX ρ (s * w₁) = p 1 := by
  have h := F.rhoX_mono ![1, 0, 0, 1, 0]
  have hv : mono ![s, t, w₀, w₁, x] ![1, 0, 0, 1, 0] = s * w₁ := by
    simp [mono]
  rw [hv] at h
  rw [h]
  decide

private theorem rho_sw₀w₁x : rhoX ρ (s * w₀ * w₁ * x) = p 0 * p 1 * p 3 := by
  have h := F.rhoX_mono ![1, 0, 1, 1, 1]
  have hv : mono ![s, t, w₀, w₁, x] ![1, 0, 1, 1, 1] = s * w₀ * w₁ * x := by
    simp [mono]
  rw [hv] at h
  rw [h]
  decide

private theorem rho_w₀w₁x : rhoX ρ (w₀ * w₁ * x) = p 2 * p 3 := by
  have h := F.rhoX_mono ![0, 0, 1, 1, 1]
  have hv : mono ![s, t, w₀, w₁, x] ![0, 0, 1, 1, 1] = w₀ * w₁ * x := by
    simp [mono]
  rw [hv] at h
  rw [h]
  decide

theorem mono_injective : Function.Injective (mono ![s, t, w₀, w₁, x]) := by
  have hfin : ∀ a b c d : ZMod 2,
      σ₀ ^ a.val * (p 1 * p 2) ^ b.val * (p 0 * p 2) ^ c.val * πx ^ d.val = 1 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by decide
  have key : ∀ u : Fin 5 → ZMod 2, mono ![s, t, w₀, w₁, x] u = 1 → u = 0 := by
    intro u hu
    have h1 := congrArg (rhoX ρ) hu
    rw [F.rhoX_mono, rhoX_one] at h1
    obtain ⟨h0, h2, h3, h4⟩ := hfin _ _ _ _ h1
    have e1 : (1 : ZMod 2).val = 1 := rfl
    have hu' : mono ![s, t, w₀, w₁, x] u = t ^ (u 1).val := by
      show s ^ (u 0).val * t ^ (u 1).val * w₀ ^ (u 2).val * w₁ ^ (u 3).val *
        x ^ (u 4).val = _
      rw [h0, h2, h3, h4]
      simp
    have hu1 : u 1 = 0 := by
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (u 1) with h | h
      · exact h
      · exfalso
        rw [hu', h, e1, pow_one] at hu
        exact Z.ht1 hu
    funext i
    fin_cases i
    · exact h0
    · exact hu1
    · exact h2
    · exact h3
    · exact h4
  intro v w hvw
  have hvw0 : mono ![s, t, w₀, w₁, x] (v + w) = 1 := by
    rw [F.E5.mono_add, ← hvw]
    exact F.E5.mono_self v
  have h0 := key _ hvw0
  funext i
  have h1 := congrFun h0 i
  simp only [Pi.add_apply, Pi.zero_apply] at h1
  revert h1
  generalize v i = a
  generalize w i = b
  revert a b
  decide

theorem P1 {y : X} (hy : y ∈ centralizer ({t} : Set X)) :
    y * (s * w₁) * y⁻¹ ≠ s * w₀ * w₁ * x := by
  intro h
  have hyN : y ∈ normalizer (M : Set X) := Z.mem_normalizer_of_mem_C hy
  have h1 := congrArg (fun z => (rhoX ρ z).support.card) h
  rw [rhoX_conj hyN (mul_mem Z.s_mem_N (le_normalizer F.w₁M)), Perm.card_support_conj,
    F.rho_sw₁, card_support_p, F.rho_sw₀w₁x, card_support_p013] at h1
  exact absurd h1 (by decide)

theorem sixpoint_C : s * w₀ * w₁ * x ∈ centralizer ({t} : Set X) ∧
    (s * w₀ * w₁ * x) * (s * w₀ * w₁ * x) = 1 ∧
    (rhoX ρ (s * w₀ * w₁ * x)).support.card = 6 ∧
    s * w₀ * w₁ * x * t ∈ centralizer ({t} : Set X) ∧
    (s * w₀ * w₁ * x * t) * (s * w₀ * w₁ * x * t) = 1 ∧
    (rhoX ρ (s * w₀ * w₁ * x * t)).support.card = 6 := by
  have hv : mono ![s, t, w₀, w₁, x] ![1, 0, 1, 1, 1] = s * w₀ * w₁ * x := by
    simp [mono]
  have ht : mono ![s, t, w₀, w₁, x] (Pi.single 1 1) = t := F.E5.mono_single 1
  have hcomm : s * w₀ * w₁ * x * t = t * (s * w₀ * w₁ * x) := by
    have := F.E5.mono_comm ![1, 0, 1, 1, 1] (Pi.single 1 1)
    rwa [hv, ht] at this
  have hvt : mono ![s, t, w₀, w₁, x] (![1, 0, 1, 1, 1] + Pi.single 1 1) =
      s * w₀ * w₁ * x * t := by
    rw [F.E5.mono_add, hv, ht]
  have hsq : (s * w₀ * w₁ * x) * (s * w₀ * w₁ * x) = 1 := by
    rw [← hv]
    exact F.E5.mono_self _
  have hsqt : (s * w₀ * w₁ * x * t) * (s * w₀ * w₁ * x * t) = 1 := by
    rw [← hvt]
    exact F.E5.mono_self _
  have hcard : (rhoX ρ (s * w₀ * w₁ * x)).support.card = 6 := by
    rw [F.rho_sw₀w₁x]
    exact card_support_p013
  refine ⟨mem_centralizer_singleton_iff.mpr hcomm, hsq, hcard, ?_, hsqt, ?_⟩
  · refine mem_centralizer_singleton_iff.mpr ?_
    calc s * w₀ * w₁ * x * t * t = t * (s * w₀ * w₁ * x) * t := by rw [hcomm]
      _ = t * (s * w₀ * w₁ * x * t) := by rw [mul_assoc]
  · rw [rhoX_mul (mul_mem (mul_mem (mul_mem Z.s_mem_N (le_normalizer F.w₀M))
      (le_normalizer F.w₁M)) (le_normalizer F.xM)) Z.t_mem_N, Z.rho_t, mul_one]
    exact hcard

theorem fourpoint_M : w₀ * w₁ * x ∈ M ∧ (w₀ * w₁ * x) * (w₀ * w₁ * x) = 1 ∧
    (rhoX ρ (w₀ * w₁ * x)).support.card = 4 := by
  have hv : mono ![s, t, w₀, w₁, x] ![0, 0, 1, 1, 1] = w₀ * w₁ * x := by
    simp [mono]
  refine ⟨mul_mem (mul_mem F.w₀M F.w₁M) F.xM, ?_, ?_⟩
  · rw [← hv]
    exact F.E5.mono_self _
  · rw [F.rho_w₀w₁x]
    exact card_support_p23

end IsFrame

end CFSG.ComponentClassification.SolMax.Sig36.E32
