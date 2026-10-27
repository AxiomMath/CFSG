module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V6

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE (AEQ mkQ memBar Wr)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan)
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL (layerX_le_centralizer conjSub_layerX_of_mem le_layerX)
open Certificates.AE5X (memL zW labs)
open Certificates.AE5Sq (a0 b0)
open scoped commutatorElement


section CaseC

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

namespace TwinLab

variable {A : AE5Layer Ω z c} {α α' : Finset (Fin 5)} {h : α.card = 4} {h' : α'.card = 4} {b b' : Bool}
  (T : TwinLab A R R' α α' h h' b b') (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include T Λ

theorem trans_class {y y' : G} (hy : y ∈ R ⊔ R') (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyz : y ≠ z)
    (hy' : y' ∈ R ⊔ R') (hy'2 : y' * y' = 1) (hy'1 : y' ≠ 1) (hy'z : y' ≠ z)
    (hv : InV (A.ε y) ↔ InV (A.ε y')) :
    ∃ n ∈ layerX Ω c, (∀ w ∈ R ⊔ R', n * w * n⁻¹ ∈ R ⊔ R') ∧ n * z * n⁻¹ = z ∧
      n * y * n⁻¹ = y' := by
  classical
  have hfacts := twin_facts h h' (T.comm Λ)
  have hI := (T.inv18_iff Λ hy).1 ⟨hy2, hy1, hyz⟩
  have hI' := (T.inv18_iff Λ hy').1 ⟨hy'2, hy'1, hy'z⟩
  obtain ⟨x₀, hx₀I, hx₀v, hx₀⟩ := chkA2_spec hfacts.2.1 (decide (InV (A.ε y)))
  have hv₁ : InV (A.ε y) ↔ decide (InV (A.ε y)) = true := (decide_eq_true_iff).symm
  obtain ⟨u₁, hu₁, hN₁, hz₁, he₁⟩ := hx₀ (A.ε y) hI hv₁
  obtain ⟨u₂, hu₂, hN₂, hz₂, he₂⟩ := hx₀ (A.ε y') hI' (hv.symm.trans hv₁)
  obtain ⟨y₀, hy₀P, hy₀2, hy₀1, hy₀z, hy₀e⟩ := T.exists_inv18 Λ hx₀I
  obtain ⟨n₁, hn₁X, hn₁e, hn₁P, hn₁z⟩ := T.lift_norm Λ hu₁ hN₁ hz₁
  obtain ⟨n₂, hn₂X, hn₂e, hn₂P, hn₂z⟩ := T.lift_norm Λ hu₂ hN₂ hz₂
  have e₁ : n₁ * y₀ * n₁⁻¹ = y :=
    A.inj_P2 Λ (hn₁P y₀ hy₀P) hy (by rw [A.eps_conj hn₁X (Λ.P_le hy₀P), hn₁e, hy₀e, he₁])
  have e₂ : n₂ * y₀ * n₂⁻¹ = y' :=
    A.inj_P2 Λ (hn₂P y₀ hy₀P) hy' (by rw [A.eps_conj hn₂X (Λ.P_le hy₀P), hn₂e, hy₀e, he₂])
  have hn₁i := norm_inv_of_norm hn₁P
  have hc₁ : n₁ * z = z * n₁ := by
    calc n₁ * z = (n₁ * z * n₁⁻¹) * n₁ := by group
      _ = z * n₁ := by rw [hn₁z]
  have hz₁' : n₁⁻¹ * z * n₁ = z := by
    calc n₁⁻¹ * z * n₁ = n₁⁻¹ * (z * n₁) := by group
      _ = n₁⁻¹ * (n₁ * z) := by rw [hc₁]
      _ = z := by group
  have hy₀' : n₁⁻¹ * y * n₁ = y₀ := by
    calc n₁⁻¹ * y * n₁ = n₁⁻¹ * (n₁ * y₀ * n₁⁻¹) * n₁ := by rw [e₁]
      _ = y₀ := by group
  refine ⟨n₂ * n₁⁻¹, (layerX Ω c).mul_mem hn₂X ((layerX Ω c).inv_mem hn₁X), ?_, ?_, ?_⟩
  · intro w hw
    have h1 := hn₁i w hw
    have h2 := hn₂P _ h1
    have e : n₂ * (n₁⁻¹ * w * n₁) * n₂⁻¹ = (n₂ * n₁⁻¹) * w * (n₂ * n₁⁻¹)⁻¹ := by group
    rwa [e] at h2
  · calc (n₂ * n₁⁻¹) * z * (n₂ * n₁⁻¹)⁻¹ = n₂ * (n₁⁻¹ * z * n₁) * n₂⁻¹ := by group
      _ = z := by rw [hz₁', hn₂z]
  · calc (n₂ * n₁⁻¹) * y * (n₂ * n₁⁻¹)⁻¹ = n₂ * (n₁⁻¹ * y * n₁) * n₂⁻¹ := by group
      _ = y' := by rw [hy₀', e₂]

end TwinLab

theorem caseC {c₁ c₂ : G} (Λ₁ : Lay Ω K K' W S R R' z t u₁ u₂ c₁) (Λ₂ : Lay Ω K K' W S R R' z t u₁ u₂ c₂)
    (hc : c₂ * z = c₁) (A₁ : AE5Layer Ω z c₁) (A₂ : AE5Layer Ω z c₂) : False := by
  classical
  obtain ⟨α, α', h, h', b, b', T₁⟩ := A₁.exists_labels Λ₁
  obtain ⟨β, β', k, k', d, d', T₂⟩ := A₂.exists_labels Λ₂
  have hf₁ := twin_facts h h' (T₁.comm Λ₁)
  obtain ⟨⟨x₁, hx₁I, hx₁V⟩, ⟨x₂, hx₂I, hx₂V⟩⟩ := chkA1_spec hf₁.1
  obtain ⟨y₁, hy₁P, hy₁2, hy₁1, hy₁z, hy₁e⟩ := T₁.exists_inv18 Λ₁ hx₁I
  obtain ⟨y₂, hy₂P, hy₂2, hy₂1, hy₂z, hy₂e⟩ := T₁.exists_inv18 Λ₁ hx₂I
  have hy₁V : InV (A₁.ε y₁) := by rw [hy₁e]; exact hx₁V
  have hy₂V : ¬ InV (A₁.ε y₂) := by rw [hy₂e]; exact hx₂V
  have hinv : ∀ n : G, n * c₁ = c₁ * n → ∀ y ∈ R ⊔ R',
      (InV (A₁.ε (n * y * n⁻¹)) ↔ InV (A₁.ε y)) := by
    intro n hn y hy
    obtain ⟨x, hx⟩ := A₁.act n (Subgroup.mem_centralizer_singleton_iff.mpr hn)
    rw [hx y (Λ₁.P_le hy)]
    constructor
    · intro hh
      have := hh.conj x⁻¹
      simpa [mul_assoc] using this
    · intro hh
      exact hh.conj x
  have hlink : ∀ y ∈ R ⊔ R', y * y = 1 → y ≠ 1 → y ≠ z → ∀ y' ∈ R ⊔ R', y' * y' = 1 → y' ≠ 1 →
      y' ≠ z → (InV (A₂.ε y) ↔ InV (A₂.ε y')) → (InV (A₁.ε y) ↔ InV (A₁.ε y')) := by
    intro y hy hy2 hy1 hyz y' hy' hy'2 hy'1 hy'z hv
    obtain ⟨n, hnX, hnP, hnz, hny⟩ := T₂.trans_class Λ₂ hy hy2 hy1 hyz hy' hy'2 hy'1 hy'z hv
    have hnc₂ : n * c₂ = c₂ * n :=
      Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω c₂ hnX)
    have hnz' : n * z = z * n := by
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [hnz]
    have hnc₁ : n * c₁ = c₁ * n := by
      rw [← hc]
      calc n * (c₂ * z) = (n * c₂) * z := by group
        _ = (c₂ * n) * z := by rw [hnc₂]
        _ = c₂ * (n * z) := by group
        _ = c₂ * (z * n) := by rw [hnz']
        _ = (c₂ * z) * n := by group
    have := hinv n hnc₁ y hy
    rw [hny] at this
    exact this.symm
  have hdich : (∀ y ∈ R ⊔ R', y * y = 1 → y ≠ 1 → y ≠ z → (InV (A₁.ε y) ↔ InV (A₂.ε y))) ∨
      (∀ y ∈ R ⊔ R', y * y = 1 → y ≠ 1 → y ≠ z → (InV (A₁.ε y) ↔ ¬ InV (A₂.ε y))) := by
    by_cases hz1 : InV (A₂.ε y₁)
    · have hz2 : ¬ InV (A₂.ε y₂) := fun h2 =>
        hy₂V ((hlink y₂ hy₂P hy₂2 hy₂1 hy₂z y₁ hy₁P hy₁2 hy₁1 hy₁z (iff_of_true h2 hz1)).2 hy₁V)
      left
      intro y hy hy2 hy1 hyz
      by_cases hzy : InV (A₂.ε y)
      · have := hlink y hy hy2 hy1 hyz y₁ hy₁P hy₁2 hy₁1 hy₁z (iff_of_true hzy hz1)
        exact iff_of_true (this.2 hy₁V) hzy
      · have := hlink y hy hy2 hy1 hyz y₂ hy₂P hy₂2 hy₂1 hy₂z (iff_of_false hzy hz2)
        exact iff_of_false (fun hh => hy₂V (this.1 hh)) hzy
    · have hz2 : InV (A₂.ε y₂) := by
        by_contra h2
        exact hy₂V ((hlink y₂ hy₂P hy₂2 hy₂1 hy₂z y₁ hy₁P hy₁2 hy₁1 hy₁z
          (iff_of_false h2 hz1)).2 hy₁V)
      right
      intro y hy hy2 hy1 hyz
      by_cases hzy : InV (A₂.ε y)
      · have := hlink y hy hy2 hy1 hyz y₂ hy₂P hy₂2 hy₂1 hy₂z (iff_of_true hzy hz2)
        exact iff_of_false (fun hh => hy₂V (this.1 hh)) (not_not.mpr hzy)
      · have := hlink y hy hy2 hy1 hyz y₁ hy₁P hy₁2 hy₁1 hy₁z (iff_of_false hzy hz1)
        exact iff_of_true (this.2 hy₁V) hzy
  obtain ⟨τ, ⟨m₀, hm₀X, hτ⟩, hτz, hτne, hτ2, hτX, hτP, hτV, hS3⟩ := T₂.exists_swap Λ₂
  have hτc₂ : τ * c₂ = c₂ * τ :=
    Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω c₂ hτX)
  have hτc₁ : τ * c₁ = c₁ * τ := by
    rw [← hc]
    calc τ * (c₂ * z) = (τ * c₂) * z := by group
      _ = (c₂ * τ) * z := by rw [hτc₂]
      _ = c₂ * (τ * z) := by group
      _ = c₂ * (z * τ) := by rw [hτz]
      _ = (c₂ * z) * τ := by group
  have hτC₁ : τ ∈ Subgroup.centralizer ({c₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hτc₁
  have hfix : ∀ y ∈ R ⊔ R', y * y = 1 → y ≠ 1 → y ≠ z → InV (A₂.ε y) → τ * y * τ⁻¹ = y := by
    intro y hy hy2 hy1 hyz hV
    apply A₂.inj_P2 Λ₂ (hτP y hy) hy
    rw [A₂.eps_conj hτX (Λ₂.P_le hy), InV.comm hτV hV]
    group
  obtain ⟨x, hx⟩ := A₁.act τ hτC₁
  have hsq : ∀ y ∈ layerX Ω c₁, x * x * A₁.ε y = A₁.ε y * (x * x) := by
    intro y hy
    have hτy : τ * y * τ⁻¹ ∈ layerX Ω c₁ := AE5Layer.conj_mem Λ₁.hΩ hτC₁ hy
    have h1 := hx _ hτy
    rw [hx y hy] at h1
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
    have e : τ * (τ * y * τ⁻¹) * τ⁻¹ = y := by
      rw [hτi]
      calc τ * (τ * y * τ) * τ = (τ * τ) * y * (τ * τ) := by group
        _ = y := by rw [hτ2]; group
    rw [e] at h1
    calc x * x * A₁.ε y = (x * (x * A₁.ε y * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = A₁.ε y * (x * x) := by rw [← h1]
  have hc2a : x * x * mkQ 5 (a0 ()) = mkQ 5 (a0 ()) * (x * x) := by
    obtain ⟨ha0v, ha0p, -, -⟩ := AE5Sq.gens_spec
    obtain ⟨y, hy, hye⟩ := A₁.surj _ (AE5Sq.mkQ_mem_aeModel ha0v ha0p)
    rw [← hye]
    exact hsq y hy
  have hc2b : x * x * mkQ 5 (b0 ()) = mkQ 5 (b0 ()) * (x * x) := by
    obtain ⟨-, -, hb0v, hb0p⟩ := AE5Sq.gens_spec
    obtain ⟨y, hy, hye⟩ := A₁.surj _ (AE5Sq.mkQ_mem_aeModel hb0v hb0p)
    rw [← hye]
    exact hsq y hy
  have hN : NormGen (α, b) (α', b') x := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨r, hr, hre⟩ := T₁.R_surj (mkQ 5 g) ((TL4.Mdl117.mem_memBar_iff α h b _).2 ⟨g, hg, rfl⟩)
      have h1 := hx r (Λ₁.R_le hr)
      obtain ⟨m, hm, m', hm', hmm⟩ := T₁.mem_P Λ₁ (hτP r (Subgroup.mem_sup_left hr))
      exact ⟨m, hm, m', hm', by rw [← hre, ← h1, hmm]⟩
    · obtain ⟨r, hr, hre⟩ := T₁.R'_surj (mkQ 5 g)
        ((TL4.Mdl117.mem_memBar_iff α' h' b' _).2 ⟨g, hg, rfl⟩)
      have h1 := hx r (Λ₁.R'_le hr)
      obtain ⟨m, hm, m', hm', hmm⟩ := T₁.mem_P Λ₁ (hτP r (Subgroup.mem_sup_right hr))
      exact ⟨m, hm, m', hm', by rw [← hre, ← h1, hmm]⟩
  have hexc : ∀ l ∈ labs, ∀ m ∈ memL l, mkQ 5 m * mkQ 5 m ≠ 1 →
      mkQ 5 m * mkQ 5 m * (mkQ 5 m * mkQ 5 m) = 1 → x * mkQ 5 m * x⁻¹ ≠ mkQ 5 m := by
    intro l hl m hm h1 h2 hxm
    obtain ⟨α₂, b₂⟩ := l
    have hα₂ : α₂ ∈ Certificates.AE5Sq.alphas := fst_mem_alphas hl
    have hα₂c : α₂.card = 4 := AE5Sq.card_of_mem_alphas α₂ hα₂
    have hw : mkQ 5 m ∈ memBar α₂ hα₂c b₂ :=
      (TL4.Mdl117.mem_memBar_iff α₂ hα₂c b₂ _).2 ⟨m, hm, rfl⟩
    have hbC : m₀ * z * m₀⁻¹ ∈ Subgroup.centralizer ({c₁} : Set G) := by
      rw [← hτ]
      exact hτC₁
    obtain ⟨h₁, hh₁C, hh₁⟩ := A₁.exc m₀ hbC x (fun y hy => by rw [← hτ]; exact hx y hy) α₂ hα₂c b₂ _
      hw h1 h2 hxm
    exact hS3 h₁ (by rw [hh₁, ← hτ]) (by
      rw [hc]
      exact Subgroup.mem_centralizer_singleton_iff.mp hh₁C)
  obtain ⟨⟨x₁', hx₁'I, hx₁'V, hx₁'ne⟩, ⟨x₂', hx₂'I, hx₂'V, hx₂'ne⟩⟩ :=
    chkA5_spec hf₁.2.2.2 x hc2a hc2b hN hexc
  rcases hdich with hI | hII
  · obtain ⟨y, hyP, hy2, hy1, hyz, hye⟩ := T₁.exists_inv18 Λ₁ hx₁'I
    have hyV : InV (A₁.ε y) := by rw [hye]; exact hx₁'V
    have hf := hfix y hyP hy2 hy1 hyz ((hI y hyP hy2 hy1 hyz).1 hyV)
    apply hx₁'ne
    rw [← hye, ← hx y (Λ₁.P_le hyP), hf]
  · obtain ⟨y, hyP, hy2, hy1, hyz, hye⟩ := T₁.exists_inv18 Λ₁ hx₂'I
    have hyV : ¬ InV (A₁.ε y) := by rw [hye]; exact hx₂'V
    have hf := hfix y hyP hy2 hy1 hyz (not_not.mp (fun hh => hyV ((hII y hyP hy2 hy1 hyz).2 hh)))
    apply hx₂'ne
    rw [← hye, ← hx y (Λ₁.P_le hyP), hf]

end CaseC

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
