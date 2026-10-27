module

public import CFSG.ClassicalInvolution.Asc77.AscS22C
public import CFSG.ClassicalInvolution.Asc77.AscT7BSylow

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem comm_gen (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
  have hc12 : Commute u₁ u₂ := h.comm₁₂
  have hc13 : Commute u₁ u₃ := T7J.comm₁₃ h
  have hc23 : Commute u₂ u₃ := h.comm₂₃
  have hcu₁₂ : Commute (u₁ * u₂) z :=
    Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)
  have hcu₂₃ : Commute (u₂ * u₃) z :=
    Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)
  have hmix : Commute (u₁ * u₂) (u₂ * u₃) :=
    Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hcu₁₂.eq
  · exact hmix.eq
  · exact hcu₁₂.symm.eq
  · rfl
  · exact hcu₂₃.symm.eq
  · exact hmix.symm.eq
  · exact hcu₂₃.eq
  · rfl

theorem B_le_centralizer (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)).eq

theorem isElemAbelian2_closure_23 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₂ * u₃, z} : Set G)) 2 :=
  isElemAbelian2_closure (rotate h)

theorem closure_23_le (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_thd
  · exact T7B.mem_closure_snd

theorem closure_12_le (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_fst
  · exact T7B.mem_closure_snd

theorem closure_13_le (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h.mem_B_13
  · exact T7B.mem_closure_snd

theorem isElemAbelian2_closure_13 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₃, z} : Set G)) 2 := by
  have h' := isElemAbelian2_closure (rotate (rotate h))
  rwa [← T7J.comm₁₃ h] at h'

theorem natCard_B (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    Nat.card ↥(Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) = 8 := by
  have := h.hB.1
  norm_num at this
  exact this

theorem exists_replace_third (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {M : Subgroup G}
    (hM : M ∈ twinSet Ω K) (hMK : M ≠ K) (hMK' : M ≠ K') :
    ∃ w : G, Hyp22Setting p f Ω K K' M z u₁ u₂ w := by
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet h.hz hM
  obtain ⟨R, R', -, hR, hR', -, h₁, h₂, -, c₁₂, -, -⟩ := T7J.exists_sylow_triple h
  obtain ⟨R_M, hRM, c₁, c₂⟩ := T7B.exists_third_sylow hp hq hΩ h.stand.mem h.hK'.1 hM.1
    h.hz h.hzK' hzM hMK hMK' hR hR' c₁₂
  obtain ⟨w, hw, o₃⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hM.1 hRM)
  exact ⟨w, hyp22Setting_of_sylows h.stand h.hz h.hK' h.hne h.perp hM hMK hMK' hR hR' hRM c₁₂
    c₁ c₂ h₁ h₂ hw h.hu₁.2 h.hu₂.2 o₃⟩

theorem conj (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {g : G} (hg : g * z * g⁻¹ = z) :
    Hyp22Setting p f Ω (conjSub g K) (conjSub g K') (conjSub g K₃) z (g * u₁ * g⁻¹)
      (g * u₂ * g⁻¹) (g * u₃ * g⁻¹) := by
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hK : K ∈ Ω := h.stand.mem
  have hcK : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hzc : IsUniqueInvolution (conjSub g K) z := by
    have := h.hz.conj g
    rwa [hg] at this
  have hmem : conjSub g K ∈ twinSet Ω K := ⟨hcK, z, h.hz, hzc⟩
  have hperp : KPerp Ω (conjSub g K) = KPerp Ω K :=
    ((l6_3 p f hp hq G Ω hΩ K hK _ hmem).1).symm
  have htw : twinSet Ω (conjSub g K) = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz hmem
  have hB : Subgroup.closure ({(g * u₁ * g⁻¹) * (g * u₂ * g⁻¹), z,
        (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹)} : Set G) =
      conjSub g (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    rw [T7B.conjSub_closure_three, hg]
    have e1 : (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) = g * (u₁ * u₂) * g⁻¹ := by group
    have e2 : (g * u₂ * g⁻¹) * (g * u₃ * g⁻¹) = g * (u₂ * u₃) * g⁻¹ := by group
    rw [e1, e2]
  refine
    { stand := h.stand.of_mem hcK
      hz := hzc
      hK' := twinSet_conj hΩ.conjInvariant h.hK' g
      hne := fun e => h.hne (conjSub_injective g e)
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := twinSet_conj hΩ.conjInvariant h.hK₃ g
      hK₃K := fun e => h.hK₃K (conjSub_injective g e)
      hK₃K' := fun e => h.hK₃K' (conjSub_injective g e)
      hu₁ := ⟨conj_mem_conjSub h.hu₁.1, by rw [T7B.orderOf_conj']; exact h.hu₁.2⟩
      hu₂ := ⟨conj_mem_conjSub h.hu₂.1, by rw [T7B.orderOf_conj']; exact h.hu₂.2⟩
      hu₃ := ⟨conj_mem_conjSub h.hu₃.1, by rw [T7B.orderOf_conj']; exact h.hu₃.2⟩
      hB := ?_ }
  rw [hB]
  refine ⟨by rw [natCard_conjSub]; exact h.hB.1, fun x hx => ?_⟩
  have hx' := mem_conjSub_iff.mp hx
  have := h.hB.2 _ hx'
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

end Setting

end S22

end CFSG.ClassicalInvolution.Asc77
