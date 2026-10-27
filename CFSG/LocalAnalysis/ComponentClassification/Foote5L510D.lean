module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510C
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L59
public import CFSG.Permutation.AlternatingAutomorphism

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

omit [Finite 𝕊] in
theorem card_le_four_of_inner {B : Subgroup (MulAut 𝕊)} (hBS : B ≤ actImage L ε S)
    (hBinn : B ≤ innAut5 𝕊) (hB2 : ∀ β ∈ B, β * β = 1) : Nat.card B ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := h.center_eq_bot ε
  have hinj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) := by
    intro a b hab
    have h1 : b⁻¹ * a ∈ center 𝕊 := by
      rw [mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut 𝕊 => φ g) hab
      simp only [MulAut.conj_apply] at h2
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
        _ = b⁻¹ * a * g := by group
    rw [hZ, mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  set B' := B.comap (MulAut.conj : 𝕊 →* MulAut 𝕊) with hB'
  have hcard : Nat.card B' = Nat.card B := by
    have h1 := Nat.card_congr (B'.equivMapOfInjective _ hinj).toEquiv
    rw [hB', map_comap_eq_self hBinn] at h1
    exact h1
  have hB'R : B' ≤ (h.Rbar ε : Subgroup 𝕊) := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_actImage ε h.S_le).mp (hBS hx)
    have hinn : actG L ε s ∈ innAut5 𝕊 := by rw [hsx]; exact ⟨x, rfl⟩
    obtain ⟨r, hr, hsr⟩ := h.exists_R_of_inner ε hs hinn
    rw [actG_of_mem_self ε (mem_inf.mp hr).2] at hsr
    have h1 : x = psi L ε ⟨r, (mem_inf.mp hr).2⟩ := hinj (by rw [← hsx, hsr])
    rw [h1]
    exact h.psi_mem_Rbar ε hr
  have hB'2 : ∀ x ∈ B', x * x = 1 := by
    intro x hx
    apply hinj
    rw [map_mul, map_one]
    exact hB2 _ hx
  obtain ⟨e⟩ := h.nonempty_Rbar_equiv ε
  obtain ⟨n, hn, ⟨d⟩⟩ := h.isDihedralTwoGroup_R
  have hdih : AschbacherTheorem3.IsDihedralTwoGroup (h.Rbar ε : Subgroup 𝕊) :=
    ⟨n, hn, ⟨e.trans d⟩⟩
  rw [← hcard]
  exact card_le_four_of_dihedral_or_semidihedral (Or.inl hdih) hB'R hB'2

include ε in
theorem exists_field_centralizer_R
    (h𝕊 : FooteSimpleType 𝕊) (hD : Foote5AutData 𝕊 Lin) {E : Subgroup G} (hES : E ≤ S)
    (hEsq : ∀ e ∈ E, e * e = 1) (hE32 : Nat.card E = 32) :
    ∃ e' ∈ S, e' * e' = 1 ∧ actG L ε e' ∉ innAut5 𝕊 ∧ (∀ r ∈ S ⊓ L, e' * r = r * e') ∧
      ∀ q ∈ E ⊓ Q, e' * q = q * e' := by
  classical
  have hEN : E ≤ normalizer (L : Set G) := hES.trans h.S_le
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hEsq ha hb
  set Eb := actImage L ε E with hEb
  have hEC : E ⊓ coreActionKernel L = E ⊓ Q := by
    rw [← h.inf_coreActionKernel, ← inf_assoc, inf_of_le_left hES]
  have h1 := card_eq_card_inf_mul_card_actImage ε hEN
  rw [hEC, hE32] at h1
  have hEQ4 := h.card_le_four_of_le_Q (E := E ⊓ Q) inf_le_right
    (fun e he => hEsq e (mem_inf.mp he).1)
  have hEb8 : 8 ≤ Nat.card Eb := by
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card ↥(E ⊓ Q) * Nat.card Eb ≤ 4 * 7 := Nat.mul_le_mul hEQ4 (by omega)
    rw [← h1] at h2
    omega
  have hEb2 : ∀ α ∈ Eb, α * α = 1 := by
    intro α hα
    obtain ⟨e, he, rfl⟩ := (mem_actImage ε hEN).mp hα
    rw [← actG_mul ε (hEN he) (hEN he), hEsq e he, actG_one]
  obtain ⟨e, he, hein⟩ : ∃ e ∈ E, actG L ε e ∉ innAut5 𝕊 := by
    by_contra hno
    push Not at hno
    have h2 := h.card_le_four_of_inner ε (B := Eb)
      (actImage_mono ε hES) (fun α hα => by
        obtain ⟨e, he, rfl⟩ := (mem_actImage ε hEN).mp hα
        exact hno e he) hEb2
    omega
  have heS := hES he
  have he2 := hEsq e he
  obtain ⟨r₁, hr₁, r₂, hr₂, -, -, -, hr₁1, hr₂1, hr₁₂, hEr⟩ :=
    h.exists_fourgroup_R_of_image ε h𝕊 hES hEsq hEb8
  have helin : actG L ε e ∉ Lin := by
    intro hlin
    rcases h.eq_one_or_eq_t_of_pgl ε hD heS he2 hlin hein hr₁ (hEr e he).1.symm with h2 | h2 <;>
      rcases h.eq_one_or_eq_t_of_pgl ε hD heS he2 hlin hein hr₂ (hEr e he).2.symm with h3 | h3
    · exact hr₁1 h2
    · exact hr₁1 h2
    · exact hr₂1 h3
    · exact hr₁₂ (h2.trans h3.symm)
  have heN := h.S_le heS
  have hsq : actG L ε e * actG L ε e = 1 := by rw [← actG_mul ε heN heN, he2, actG_one]
  obtain ⟨ρ₀, hρ₀R, hρ₀2, hρ₀⟩ :=
    hD.field_inner (h.Rbar ε) _ helin hsq (h.actG_map_Rbar ε heS)
  obtain ⟨r₀', hr₀, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ₀R
  set r₀ : G := (r₀' : G) with hr₀def
  have hr₀L : r₀ ∈ L := r₀'.2
  have hconj : ∀ r ∈ S ⊓ L, e * r * e⁻¹ = r₀ * r * r₀⁻¹ := by
    intro r hr
    have h2 := hρ₀ _ (h.psi_mem_Rbar ε hr)
    rw [actG_psi ε heN] at h2
    have h3 : psi L ε ⟨r₀ * r * r₀⁻¹, mul_mem (mul_mem hr₀L (mem_inf.mp hr).2) (inv_mem hr₀L)⟩ =
        psi L ε r₀' * psi L ε ⟨r, (mem_inf.mp hr).2⟩ * (psi L ε r₀')⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [← h3] at h2
    exact h.eq_of_psi_eq ε (h.conj_mem_R heS hr)
      (h.conj_mem_R (mem_inf.mp hr₀).1 hr) h2
  have hr₀2 : r₀ * r₀ = 1 := by
    have h2 : psi L ε ⟨r₀ * r₀, mul_mem hr₀L hr₀L⟩ = psi L ε ⟨1, one_mem _⟩ := by
      rw [show (⟨r₀ * r₀, mul_mem hr₀L hr₀L⟩ : L) = r₀' * r₀' from rfl, map_mul, hρ₀2]
      exact (map_one _).symm
    exact h.eq_of_psi_eq ε (mul_mem hr₀ hr₀) (one_mem _) h2
  have her₀ : e * r₀ = r₀ * e := by
    have h2 := hconj r₀ hr₀
    calc e * r₀ = e * r₀ * e⁻¹ * e := by group
      _ = r₀ * e := by rw [h2]; group
  refine ⟨r₀⁻¹ * e, mul_mem (inv_mem (mem_inf.mp hr₀).1) heS, ?_, ?_, ?_, ?_⟩
  · calc r₀⁻¹ * e * (r₀⁻¹ * e) = r₀⁻¹ * (e * r₀⁻¹) * e := by group
      _ = r₀⁻¹ * (r₀⁻¹ * e) * e := by
          rw [show e * r₀⁻¹ = r₀⁻¹ * e by
            calc e * r₀⁻¹ = r₀⁻¹ * (r₀ * e) * r₀⁻¹ := by group
              _ = r₀⁻¹ * (e * r₀) * r₀⁻¹ := by rw [her₀]
              _ = r₀⁻¹ * e := by group]
      _ = (r₀ * r₀)⁻¹ * (e * e) := by group
      _ = 1 := by rw [hr₀2, he2]; group
  · intro hinn
    apply hein
    have h2 : actG L ε e = actG L ε r₀ * actG L ε (r₀⁻¹ * e) := by
      rw [← actG_mul ε (h.S_le (mem_inf.mp hr₀).1)
        (mul_mem (inv_mem (h.S_le (mem_inf.mp hr₀).1)) heN)]
      group
    rw [h2, actG_of_mem_self ε hr₀L]
    exact mul_mem ⟨_, rfl⟩ hinn
  · intro r hr
    have h2 := hconj r hr
    calc r₀⁻¹ * e * r = r₀⁻¹ * (e * r * e⁻¹) * e := by group
      _ = r₀⁻¹ * (r₀ * r * r₀⁻¹) * e := by rw [h2]
      _ = r * (r₀⁻¹ * e) := by group
  · intro q hq
    have h2 := hEc e he q (mem_inf.mp hq).1
    have h3 := h.commute_Q_R (mem_inf.mp hq).2 hr₀
    calc r₀⁻¹ * e * q = r₀⁻¹ * (q * e) := by rw [mul_assoc, h2]
      _ = q * (r₀⁻¹ * e) := by
          rw [← mul_assoc, show r₀⁻¹ * q = q * r₀⁻¹ by
            calc r₀⁻¹ * q = r₀⁻¹ * (q * r₀) * r₀⁻¹ := by group
              _ = r₀⁻¹ * (r₀ * q) * r₀⁻¹ := by rw [h3]
              _ = q * r₀⁻¹ := by group, mul_assoc]

end Sec5

end CFSG.ComponentClassification.Foote5
