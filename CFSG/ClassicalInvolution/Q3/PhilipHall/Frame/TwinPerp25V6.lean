module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V5

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
open scoped commutatorElement


section Swap

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

theorem fst_mem_alphas {l : Certificates.AE5X.Lab} (hl : l ∈ labs) : l.1 ∈ Certificates.AE5Sq.alphas := by
  simp only [labs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hl
  obtain ⟨α, hα, rfl | rfl⟩ := hl <;> exact hα

namespace TwinLab

variable {A : AE5Layer Ω z c} {α α' : Finset (Fin 5)} {h : α.card = 4} {h' : α'.card = 4} {b b' : Bool}
  (T : TwinLab A R R' α α' h h' b b') (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include T Λ

theorem exists_swap :
    ∃ τ : G, (∃ m₀ ∈ layerX Ω c, τ = m₀ * z * m₀⁻¹) ∧ τ * z = z * τ ∧ τ ≠ z ∧ τ * τ = 1 ∧
      τ ∈ layerX Ω c ∧ (∀ y ∈ R ⊔ R', τ * y * τ⁻¹ ∈ R ⊔ R') ∧ InV (A.ε τ) ∧
      (∀ m : G, m * z * m⁻¹ = τ → m * (c * z) ≠ (c * z) * m) := by
  have hfacts := twin_facts h h' (T.comm Λ)
  obtain ⟨u, hu, s, hsdef, hs1, hs2, hsz, ⟨l, hl, m4, hm4, hm41, hm42, hm4c⟩, hM3⟩ :=
    chkA3_spec hfacts.2.2.1
  obtain ⟨w₀, hw₀, hw₀u⟩ := A.surj u hu
  have hzP : z ∈ R ⊔ R' := Subgroup.mem_sup_left Λ.z_mem_R
  have hzX : z ∈ layerX Ω c := Λ.P_le hzP
  have hzb : A.ε z = mkQ 5 (zW (α, b)) := T.eps_z Λ
  have hετ₀ : A.ε (w₀ * z * w₀⁻¹) = s := by
    rw [A.eps_conj hw₀ hzX, hw₀u, hzb, hsdef]
  have hconj : ∀ x ∈ memBar α h b ⊔ memBar α' h' b', s * x * s⁻¹ ∈ memBar α h b ⊔ memBar α' h' b' := by
    refine conj_mem_sup_of (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨m, hm, rfl⟩ := (TL4.Mdl117.mem_memBar_iff α h b x).1 hx
      obtain ⟨m', hm', he⟩ := hs1 m hm
      rw [he]
      exact Subgroup.mem_sup_right ((TL4.Mdl117.mem_memBar_iff α' h' b' _).2 ⟨m', hm', rfl⟩)
    · obtain ⟨m, hm, rfl⟩ := (TL4.Mdl117.mem_memBar_iff α' h' b' x).1 hx
      obtain ⟨m', hm', he⟩ := hs2 m hm
      rw [he]
      exact Subgroup.mem_sup_left ((TL4.Mdl117.mem_memBar_iff α h b _).2 ⟨m', hm', rfl⟩)
  have hnorm := T.norm_P Λ hconj
  obtain ⟨m', hm', hεm', hnormτ⟩ := T.lift_inv Λ hw₀ (by rw [hετ₀]; exact hnorm)
  have hετ : A.ε (m' * z * m'⁻¹) = s := hεm'.trans hετ₀
  have hτX : m' * z * m'⁻¹ ∈ layerX Ω c :=
    (layerX Ω c).mul_mem ((layerX Ω c).mul_mem hm' hzX) ((layerX Ω c).inv_mem hm')
  have hτ2 : (m' * z * m'⁻¹) * (m' * z * m'⁻¹) = 1 := by
    calc (m' * z * m'⁻¹) * (m' * z * m'⁻¹) = m' * (z * z) * m'⁻¹ := by group
      _ = 1 := by rw [Λ.hz2]; group
  have hsV : InV s := by
    rw [hsdef]
    exact (spec_zV h b).conj u
  have hszc : s * mkQ 5 (zW (α, b)) = mkQ 5 (zW (α, b)) * s := InV.comm hsV (spec_zV h b)
  have hτzc : (m' * z * m'⁻¹) * z * (m' * z * m'⁻¹)⁻¹ = z := by
    apply A.inj_P2 Λ ((hnormτ z hzP)) hzP
    rw [A.eps_conj hτX hzX, hετ, hzb]
    rw [mul_inv_eq_iff_eq_mul]
    exact hszc
  have hcomm : (m' * z * m'⁻¹) * z = z * (m' * z * m'⁻¹) := by
    calc (m' * z * m'⁻¹) * z = ((m' * z * m'⁻¹) * z * (m' * z * m'⁻¹)⁻¹) * (m' * z * m'⁻¹) := by group
      _ = z * (m' * z * m'⁻¹) := by rw [hτzc]
  have hne : m' * z * m'⁻¹ ≠ z := by
    intro he
    apply hsz
    rw [← hετ, he, hzb]
  have hS2 : ¬ ∃ y : G, y * z * y⁻¹ = (m' * z * m'⁻¹) * z := by
    rintro ⟨y, hy⟩
    have hb₁X : (m' * z * m'⁻¹) * z ∈ layerX Ω c := (layerX Ω c).mul_mem hτX hzX
    have hb₁C : y * z * y⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [hy]
      exact layerX_le_centralizer Ω c hb₁X
    obtain ⟨α₂, b₂⟩ := l
    have hα₂ : α₂ ∈ Certificates.AE5Sq.alphas := fst_mem_alphas hl
    have hα₂c : α₂.card = 4 := AE5Sq.card_of_mem_alphas α₂ hα₂
    have hw : mkQ 5 m4 ∈ memBar α₂ hα₂c b₂ := (TL4.Mdl117.mem_memBar_iff α₂ hα₂c b₂ _).2 ⟨m4, hm4, rfl⟩
    have hεb : A.ε ((m' * z * m'⁻¹) * z) = s * mkQ 5 (zW (α, b)) := by
      rw [A.mul _ hτX _ hzX, hετ, hzb]
    obtain ⟨h₁, hh₁C, hh₁⟩ := A.exc y hb₁C (A.ε ((m' * z * m'⁻¹) * z))
      (fun y' hy' => by rw [hy]; exact A.eps_conj hb₁X hy') α₂ hα₂c b₂ _ hw hm41 hm42
      (by rw [hεb, mul_inv_eq_iff_eq_mul]; exact hm4c)
    obtain ⟨x', hx'⟩ := A.act h₁ hh₁C
    have h2 := hx' z hzX
    rw [hh₁, hy, hεb, hzb] at h2
    exact hM3 x' h2.symm
  refine ⟨m' * z * m'⁻¹, ⟨m', hm', rfl⟩, hcomm, hne, hτ2, hτX, hnormτ, ?_, ?_⟩
  · rw [hετ]
    exact hsV
  · intro m hm hma
    have hha : m' * c = c * m' :=
      Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω c hm')
    have haK : c ∈ trivialOnQuot K := P25S.trivialOnQuot_of_centralizes Λ.hyp Λ.hc2 Λ.hcR
    have haK' : c ∈ trivialOnQuot K' := P25S.trivialOnQuot_of_centralizes' Λ.hyp Λ.hc2 Λ.hcR'
    have hzc : z * (m' * z * m'⁻¹) * z⁻¹ = (m' * z * m'⁻¹) := by
      calc z * (m' * z * m'⁻¹) * z⁻¹ = ((m' * z * m'⁻¹) * z) * z⁻¹ := by rw [← hcomm]
        _ = (m' * z * m'⁻¹) := by group
    exact P25S.not_swap_in_both Λ.hyp haK haK' (Ne.symm hne) hzc hS2 rfl hha hm hma

end TwinLab

end Swap

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
