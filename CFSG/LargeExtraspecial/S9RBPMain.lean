module

public import CFSG.LargeExtraspecial.S9RBPCaseF
public import CFSG.LargeExtraspecial.S9PG
public import CFSG.LargeExtraspecial.S9RBMain
public import CFSG.LargeExtraspecial.S9RBPCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

namespace Step5Data

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} (D : Step5Data H C ht ht1 hVQ)
include D

theorem false_of_isConjCent (hNo : NoA2 S g)
    (hR : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) {τ : S.O}
    (hτ : IsConjCent S t τ) : False := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hττ := hτ.mul_self H ht
  have htr := D.transitive
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  have hbQ := conj_mem_QG' S h.2 haQ
  set A := S.Lbar g ⊓ Nbar S g t with hA
  set B := S.Lbar ((h : G) * g) ⊓ Nbar S g t with hB
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, Commute a a' := fun a ha a' ha' => Lbar_comm S haQ ha.1 ha'.1
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, Commute b b' := fun b hb b' hb' => Lbar_comm S hbQ hb.1 hb'.1
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => mul_self_of_mem_Lbar S haQ ha.1
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => mul_self_of_mem_Lbar S hbQ hb.1
  have htA : t ∈ A := ⟨ht, self_mem_Nbar H ht⟩
  have htB : t ∈ B := ⟨hth, self_mem_Nbar H ht⟩
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ zpowers t := by
    intro a ha b hbB
    have hbN := Nbar_le_normalizer haQ H.conj_ne (Lbar_mem_Dset ht) hbB.2
    have haN := Nbar_le_normalizer haQ H.conj_ne (Lbar_mul_mem_Dset hth) ha.2
    refine mem_zpowers_of_mem_Lbar_inf H C ht ht1 hVQ hh hb ?_ ?_
    · have h1 : b * a⁻¹ * b⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hbN _).mp (inv_mem ha.1)
      have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [e]
      exact mul_mem ha.1 h1
    · have h1 : a * b * a⁻¹ ∈ S.Lbar ((h : G) * g) := (mem_normalizer_iff.mp haN _).mp hbB.1
      exact mul_mem h1 (inv_mem hbB.1)
  have hBA := prod_comm_of htA hAB
  set N := prodSub A B hBA with hN
  have hτM := hτ.mem_Mbar ht
  obtain ⟨kτ, hkτ⟩ := MonoidHom.mem_range.mp hτM
  have hkτt : S.ρ kτ * t = t * S.ρ kτ := by rw [hkτ]; exact hτ.comm
  have hτV := hτ.fix_Vt H C ht ht1 hVQ htr hR
  have hτLa : τ ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) haQ H.conj_ne hτM
      (by simpa using hτV _ (cl_a_mem_Vt ht))
    simpa using this
  have hτLb : τ ∈ normalizer (S.Lbar ((h : G) * g) : Set S.O) :=
    mem_normalizer_of_fix haQ H.conj_ne hτM (hτV _ (cl_mem_Vt hth))
  have hτNb : ∀ x ∈ Nbar S g t, τ * x * τ⁻¹ ∈ Nbar S g t := fun x hx => by
    have := conj_mem_Nbar haQ hkτt hx
    rwa [hkτ] at this
  have hτN : ∀ n ∈ N, τ * n * τ⁻¹ ∈ N := fun n hn =>
    conj_mem_prodSub hBA (fun a ha => ⟨(mem_normalizer_iff.mp hτLa a).mp ha.1, hτNb a ha.2⟩)
      (fun b hb => ⟨(mem_normalizer_iff.mp hτLb b).mp hb.1, hτNb b hb.2⟩) hn
  have hnc : ∀ n ∈ N, n * τ * n⁻¹ ≠ τ * t := by
    intro n _ e
    obtain ⟨y, -, hyτ⟩ := hτ.conj
    have hinf := hτ.inf_eq_bot H C ht ht1 hVQ htr hR
    subst hyτ
    exact not_conj_mul_t_of_inf_eq_bot H C ht ht1 hVQ hinf hτV e
  have hNM : N ≤ S.Mbar := prodSub_le hBA (fun a ha => Rbar_le_Mbar (Nbar_le_Rbar ha.2))
    (fun b hb => Rbar_le_Mbar (Nbar_le_Rbar hb.2))
  have htri : ∀ ρ₁ ∈ nOrbit N τ, ∀ ρ₂ ∈ nOrbit N τ, Commute τ ρ₁ → Commute τ ρ₂ →
      Commute ρ₁ ρ₂ → ρ₁ ≠ τ → ρ₂ ≠ τ → ρ₁ ≠ ρ₂ → τ * ρ₁ * ρ₂ ∉ nOrbit N τ := by
    intro ρ₁ hρ₁ ρ₂ hρ₂ c₁ c₂ _ n₁ n₂ n₁₂ hmem
    obtain ⟨y, hy, hyτ⟩ := hτ.conj
    have hconj : ∀ ρ ∈ nOrbit N τ, ∃ m ∈ S.Mbar, m * τ * m⁻¹ = ρ :=
      fun ρ ⟨n, hn, e⟩ => ⟨n, hNM hn, e⟩
    have k₁ := isConjCent_conj_inv hy hyτ (hconj ρ₁ hρ₁) c₁.eq n₁
    have k₂ := isConjCent_conj_inv hy hyτ (hconj ρ₂ hρ₂) c₂.eq n₂
    have hρ₁2 : ρ₁ * ρ₁ = 1 := by
      obtain ⟨n, -, rfl⟩ := hρ₁
      calc n * τ * n⁻¹ * (n * τ * n⁻¹) = n * (τ * τ) * n⁻¹ := by group
        _ = 1 := by rw [hττ, mul_one, mul_inv_cancel]
    have hne3 : τ * ρ₁ * ρ₂ ≠ τ := by
      intro e
      rw [mul_assoc] at e
      have e' : ρ₁ * ρ₂ = 1 := mul_eq_left.mp e
      apply n₁₂
      calc ρ₁ = ρ₁ * (ρ₁ * ρ₂) := by rw [e', mul_one]
        _ = (ρ₁ * ρ₁) * ρ₂ := by group
        _ = ρ₂ := by rw [hρ₁2, one_mul]
    have hc3 : τ * (τ * ρ₁ * ρ₂) = τ * ρ₁ * ρ₂ * τ :=
      (((Commute.refl τ).mul_right c₁).mul_right c₂).eq
    have k₃ := isConjCent_conj_inv hy hyτ (hconj _ hmem) hc3 hne3
    have e3 : y⁻¹ * (τ * ρ₁ * ρ₂) * y = t * (y⁻¹ * ρ₁ * y) * (y⁻¹ * ρ₂ * y) := by
      rw [← hyτ]; group
    rw [e3] at k₃
    exact (TriHyp.mk D hR k₁ k₂ k₃).false hNo
  exact false_of_lambda htt hττ (show Commute t τ from hτ.comm.symm)
    (fun n hn => commute_t_of_mem_prodSub hAc hBc htA htB hBA hn)
    (fun n hn m hm => comm_mem_zpowers_of_mem_prodSub hAc hBc htA htB hAB hBA hn hm)
    (fun n hn => mul_self_mem_zpowers_of_mem_prodSub hAc hBc htA htB hAB hA2 hB2 hBA hn)
    hτN hnc htri
    (D.four_lt_card_nOrbit hR hτ hh hb (le_prodSub_left hBA)
      (le_prodSub_right hBA))

end Step5Data

end CFSG.LargeExtraspecial.S9.RB

namespace CFSG.LargeExtraspecial.S9

open Subgroup CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem pgl25Step5Residual : PGL25Step5Residual.{u} := by
  intro G _ _ S g _ _ H hNo C t ht ht1 hVQ hP _ hR x hxM hτt hβ w _
  exfalso
  refine (RB.step5Data_pgl25 H C ht ht1 hVQ hP).false_of_isConjCent hNo hR (τ := x * t * x⁻¹)
    ⟨⟨x, hxM, rfl⟩, hτt, fun e => ?_⟩
  apply hβ 1 (by rw [map_one]; exact one_mem _)
  rw [e]
  simp only [OneMemClass.coe_one, one_mul]
  exact ⟨ht, self_mem_Nbar H ht⟩

theorem pgl25TypeIIResidual : PGL25TypeIIResidual.{u} :=
  pgl25TypeIIResidual_of_step5Residual pgl25Step5Residual

end CFSG.LargeExtraspecial.S9
