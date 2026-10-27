module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusAct
public import CFSG.ClassicalInvolution.AschTight.S19MSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

section Core

variable {G : Type} [Group G] [Finite G]

abbrev fusE (K C : Subgroup G) : Type :=
  ↥(conjGen (secL K C)) ⧸ classicalInvolutionOddCore ↥(conjGen (secL K C))

abbrev fusΦ (K C : Subgroup G) : Set (Subgroup (fusE K C)) :=
  oddQuotientFamily (restrictFamily (conjFamily (secL K C)) (conjGen (secL K C)))

variable {K : Subgroup G} {z : G} {C : Subgroup G}

namespace FusSec3

variable (h : FusSec3 K z C)

include h

theorem fusion_of_inner (hsimple : IsSimpleGroup (fusE K C))
    (hM2 : ∀ x : fusE K C, x * x = 1 → x ≠ 1 → ∃ X ∈ fusΦ K C, IsUniqueInvolution X x)
    (hInner : ∀ s₁ : ↥C, s₁ * s₁ = 1 → (∃ g : G, (s₁ : G) = g * z * g⁻¹) →
      (s₁ : G) * z = z * (s₁ : G) → (s₁ : G) ≠ z →
        ∃ ē : fusE K C, secAct (conjGen (secL K C)) s₁ = MulAut.conj ē)
    (s : ↥C) (hs : ∃ g : G, (s : G) = g * z * g⁻¹) :
    ∃ c : ↥C, s = c * (⟨z, h.zC⟩ : C) * c⁻¹ := by
  have hI := h.isUniqueInvolution
  have hs2 : s * s = 1 := by
    obtain ⟨g, hg⟩ := hs
    apply Subtype.ext
    rw [Subgroup.coe_mul, hg, Subgroup.coe_one]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hcen : Subgroup.center (fusE K C) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (fusE K C)) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨x, -, y, -, hxy⟩ := h.exists_noncomm_secImg
      exact hxy (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top y) x)
  obtain ⟨X, hX, hXφ⟩ := S19M.exists_map_eq_of_dEdgeless (G := ↥C)
    (Ω := conjFamily (secL K C))
    (fun M hM g => conjInvariant_conjFamily (secL K C) g M hM)
    ⟨secL K C, ⟨1, conjSub_one _⟩⟩ h.edgelessC (MulAut.conj s)
    (by rw [← map_mul, hs2, map_one]) (fun M hM => conjInvariant_conjFamily _ s M hM)
  obtain ⟨c, rfl⟩ := hX
  have hc : (secImg (conjGen (secL K C)) (conjSub c (secL K C))).map
      (secAct (conjGen (secL K C)) s).toMonoidHom =
        secImg (conjGen (secL K C)) (conjSub c (secL K C)) := by
    rw [secAct_secImg _ s (le_conjGen ⟨c, rfl⟩)]
    exact congrArg _ hXφ
  obtain ⟨v, -, hv⟩ := h.exists_conj_comm_of_secAct hs2 hc
  set d := v * c with hd'
  set s₁ := d⁻¹ * s * d with hs₁
  suffices h₁ : ∃ c₁ : ↥C, s₁ = c₁ * (⟨z, h.zC⟩ : C) * c₁⁻¹ by
    obtain ⟨c₁, hc₁⟩ := h₁
    refine ⟨d * c₁, ?_⟩
    calc s = d * s₁ * d⁻¹ := by rw [hs₁]; group
      _ = d * c₁ * (⟨z, h.zC⟩ : C) * (d * c₁)⁻¹ := by rw [hc₁]; group
  have hs₁g : ∃ g : G, (s₁ : G) = g * z * g⁻¹ := by
    obtain ⟨g, hg⟩ := hs
    refine ⟨(d : G)⁻¹ * g, ?_⟩
    rw [hs₁, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
    group
  have hs₁z : (s₁ : G) * z = z * (s₁ : G) := congrArg Subtype.val hv
  have hs₁2 : s₁ * s₁ = 1 := by
    rw [hs₁]
    calc d⁻¹ * s * d * (d⁻¹ * s * d) = d⁻¹ * (s * s) * d := by group
      _ = 1 := by rw [hs2]; group
  by_cases hs₁e : (s₁ : G) = z
  · exact ⟨1, Subtype.ext (by rw [hs₁e]; simp)⟩
  have hφ2 : secAct (conjGen (secL K C)) s₁ * secAct (conjGen (secL K C)) s₁ = 1 := by
    rw [← map_mul, hs₁2, map_one]
  obtain ⟨ē, hē⟩ := hInner s₁ hs₁2 hs₁g hs₁z hs₁e
  have hē2 : ē * ē = 1 := by
    have h1 : MulAut.conj (ē * ē) = 1 := by rw [map_mul, ← hē, hφ2]
    have h2 : ē * ē ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut _ => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * (ē * ē) = ē * ē * g * (ē * ē)⁻¹ * (ē * ē) := by rw [this]
        _ = ē * ē * g := by group
    rw [hcen, Subgroup.mem_bot] at h2
    exact h2
  by_cases hē1 : ē = 1
  · exfalso
    rw [hē1, map_one] at hē
    exact hs₁e (h.eq_of_secAct_fixes hs₁g hs₁z hs₁2 (fun x _ => by rw [hē]; rfl))
  obtain ⟨X', hX', hX'u⟩ := hM2 ē hē2 hē1
  obtain ⟨c', rfl⟩ := (mem_secFamily_iff _ X').mp hX'
  have hē' := (h.isUniqueInvolution_secImg c').eq hX'u
  have huY : c' * (⟨z, h.zC⟩ : C) * c'⁻¹ ∈ conjGen (secL K C) :=
    le_conjGen ⟨c', rfl⟩ (h.isUniqueInvolution_conj_sec c').mem
  refine h.exists_conj_eq_of_secAct_eq hs₁g hs₁2 (c' := c') ?_
  rw [hē, ← hē', secAct_of_mem _ huY]
  rfl

end FusSec3

end Core

end CFSG.ClassicalInvolution.Q3.Q3T6
