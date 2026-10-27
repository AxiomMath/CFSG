module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step6

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure Step6 (z : G) (L S : Subgroup G) where
  z₁ : G
  hz₁L : z₁ ∈ L
  hz₁S : z₁ ∈ S
  hz₁ : orderOf z₁ = 2
  hz₁Z : (QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L)
  hT : IsSylowOf 2 (S ⊓ centralizer {z₁}) (centralizer {z} ⊓ centralizer {z₁})
  J₁ : Subgroup G
  J₂ : Subgroup G
  J₃ : Subgroup G
  hJ₁ : IsTwoComponentIn J₁ (centralizer {z} ⊓ centralizer {z₁})
  hJ₂ : IsTwoComponentIn J₂ (centralizer {z} ⊓ centralizer {z₁})
  hJ₃ : IsTwoComponentIn J₃ (centralizer {z} ⊓ centralizer {z₁})
  hJ₁L : J₁ ≤ L
  hJ₂L : J₂ ≤ L
  hJ₃L : J₃ ≤ L
  hzJ₁ : z ∈ J₁
  hz₁J₂ : z₁ ∈ J₂
  hzz₁J₃ : z * z₁ ∈ J₃
  uniq₁ : ∀ K : Subgroup G, IsTwoComponentIn K (centralizer {z} ⊓ centralizer {z₁}) → z ∈ K →
    K = J₁
  uniq₂ : ∀ K : Subgroup G, IsTwoComponentIn K (centralizer {z} ⊓ centralizer {z₁}) → z₁ ∈ K →
    K = J₂
  uniq₃ : ∀ K : Subgroup G, IsTwoComponentIn K (centralizer {z} ⊓ centralizer {z₁}) →
    z * z₁ ∈ K → K = J₃
  b : G
  hbz : b * z * b⁻¹ = z * z₁
  hbz₁ : b * z₁ * b⁻¹ = z₁

variable {z : G} {L : Subgroup G} {p f : ℕ}

section Certified


theorem C3Config.exists_step6 (hI : C3Inputs) (h : C3Config G z L p f) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) : Nonempty (Step6 z L S) := by
  have := h.simple
  obtain ⟨z₁, hz₁L, hz₁S, hz₁, hz₁Z, hT⟩ := h.exists_z₁ hI hS
  obtain ⟨J₁, J₂, J₃, ⟨hJ₁, hJ₁L, -, -, hzJ₁⟩, ⟨hJ₂, hJ₂L, -, -, hz₁J₂⟩,
    ⟨hJ₃, hJ₃L, -, -, hzz₁J₃⟩⟩ := spinSeven_lift_three h.h5 h.hL h.hzL h.hz h.hcov hz₁L hz₁ hz₁Z
  have hz₁z : z₁ ∈ centralizer ({z} : Set G) := h.hL.1 hz₁L
  have hc : z * z₁ = z₁ * z := (mem_centralizer_singleton_iff.mp hz₁z).symm
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hne : z₁ ≠ z := fun he => hz₁Z (by
    have h1 : (⟨z₁, hz₁L⟩ : ↥L) = ⟨z, h.hzL⟩ := Subtype.ext he
    rw [h1]
    exact mk_mem_center_of_mem_center hzc)
  have hzz₁ : orderOf (z * z₁) = 2 := orderOf_mul_of_commute h.hz hz₁ hc hne
  have hzz₁L : z * z₁ ∈ L := mul_mem h.hzL hz₁L
  have hzz₁Z : (QuotientGroup.mk (⟨z * z₁, hzz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L) := by
    intro hcen
    apply hz₁Z
    have h1 : (QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L) =
        (QuotientGroup.mk ⟨z, h.hzL⟩)⁻¹ * QuotientGroup.mk ⟨z * z₁, hzz₁L⟩ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp
    rw [h1]
    exact mul_mem (inv_mem (mk_mem_center_of_mem_center hzc)) hcen
  have hCzz₁ : centralizer ({z} : Set G) ⊓ centralizer {z * z₁} =
      centralizer {z} ⊓ centralizer {z₁} := T23.centralizer_inf_mul
  obtain ⟨g₁, hg₁⟩ := h.exists_conj hI hz₁L hz₁
  have h₁ : C3Config G z₁ (L.map (MulAut.conj g₁).toMonoidHom) p f := hg₁ ▸ h.conj g₁
  have hzz₁' : z ∈ centralizer ({z₁} : Set G) := mem_centralizer_comm hz₁z
  have hzL₁ : z ∈ L.map (MulAut.conj g₁).toMonoidHom :=
    ((h₁.conj_iff hI hzz₁').mp ⟨g₁⁻¹, by rw [← hg₁]; group⟩).1
  have hzZ₁ : (QuotientGroup.mk (⟨z, hzL₁⟩ : ↥(L.map (MulAut.conj g₁).toMonoidHom)) :
      Bar (L.map (MulAut.conj g₁).toMonoidHom)) ∉
        center (Bar (L.map (MulAut.conj g₁).toMonoidHom)) :=
    fun hcen => hne (h₁.eq_of_mk_mem_center hzL₁ h.hz hcen).symm
  have hzz₁C : z * z₁ ∈ centralizer ({z₁} : Set G) :=
    mul_mem hzz₁' (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨g₂, hg₂⟩ := h.exists_conj hI hzz₁L hzz₁
  have hzz₁L₁ : z * z₁ ∈ L.map (MulAut.conj g₁).toMonoidHom :=
    ((h₁.conj_iff hI hzz₁C).mp ⟨g₂ * g₁⁻¹, by rw [← hg₂, ← hg₁]; group⟩).1
  have hzz₁Z₁ : (QuotientGroup.mk (⟨z * z₁, hzz₁L₁⟩ : ↥(L.map (MulAut.conj g₁).toMonoidHom)) :
      Bar (L.map (MulAut.conj g₁).toMonoidHom)) ∉
        center (Bar (L.map (MulAut.conj g₁).toMonoidHom)) := fun hcen => by
    have h1 := h₁.eq_of_mk_mem_center hzz₁L₁ hzz₁ hcen
    have h2 : z = 1 := by
      calc z = z * z₁ * z₁⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    have h3 := h.hz
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨b, hbL₁, hb⟩ := spinSeven_conj_of_involution h₁.h5 h₁.hcov hzL₁ hzz₁L₁ h.hz hzz₁ hzZ₁
    hzz₁Z₁
  have hbz₁ : b * z₁ * b⁻¹ = z₁ := by
    rw [mem_centralizer_singleton_iff.mp (h₁.hL.1 hbL₁), mul_inv_cancel_right]
  refine ⟨⟨z₁, hz₁L, hz₁S, hz₁, hz₁Z, hT, J₁, J₂, J₃, hJ₁, hJ₂, hJ₃, hJ₁L, hJ₂L, hJ₃L, hzJ₁,
    hz₁J₂, hzz₁J₃, ?_, ?_, ?_, b, hb, hbz₁⟩⟩
  · intro K hK hzK
    exact h₁.eq_of_mem_twoComponent hI hzL₁ h.hz hzZ₁
      (inf_comm (centralizer {z}) (centralizer {z₁}) ▸ hK)
      (inf_comm (centralizer {z}) (centralizer {z₁}) ▸ hJ₁) hzK hzJ₁
  · intro K hK hz₁K
    exact h.eq_of_mem_twoComponent hI hz₁L hz₁ hz₁Z hK hJ₂ hz₁K hz₁J₂
  · intro K hK hzz₁K
    exact h.eq_of_mem_twoComponent hI hzz₁L hzz₁ hzz₁Z (hCzz₁ ▸ hK) (hCzz₁ ▸ hJ₃) hzz₁K hzz₁J₃

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
