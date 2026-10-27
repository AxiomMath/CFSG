module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step6

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure Step6Three (z : G) (L S : Subgroup G) where
  z₁ : G
  hz₁L : z₁ ∈ L
  hz₁S : z₁ ∈ S
  hz₁ : orderOf z₁ = 2
  hz₁Z : (QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L)
  hT : IsSylowOf 2 (S ⊓ centralizer {z₁}) (centralizer {z} ⊓ centralizer {z₁})
  J₁ : Subgroup G
  J₂ : Subgroup G
  J₃ : Subgroup G
  hJ₁ : IsSolvableTwoComponentIn J₁ (centralizer {z} ⊓ centralizer {z₁})
  hJ₂ : IsSolvableTwoComponentIn J₂ (centralizer {z} ⊓ centralizer {z₁})
  hJ₃ : IsSolvableTwoComponentIn J₃ (centralizer {z} ⊓ centralizer {z₁})
  hJ₁L : J₁ ≤ L ⊔ (pPrimeCore 2 ↥(centralizer {z} ⊓ centralizer {z₁})).map
    (centralizer {z} ⊓ centralizer {z₁}).subtype
  hJ₂L : J₂ ≤ L ⊔ (pPrimeCore 2 ↥(centralizer {z} ⊓ centralizer {z₁})).map
    (centralizer {z} ⊓ centralizer {z₁}).subtype
  hJ₃L : J₃ ≤ L ⊔ (pPrimeCore 2 ↥(centralizer {z} ⊓ centralizer {z₁})).map
    (centralizer {z} ⊓ centralizer {z₁}).subtype
  hzJ₁ : z ∈ J₁
  hz₁J₂ : z₁ ∈ J₂
  hzz₁J₃ : z * z₁ ∈ J₃
  uniq₁ : ∀ K : Subgroup G, IsSolvableTwoComponentIn K (centralizer {z} ⊓ centralizer {z₁}) →
    z ∈ K → K = J₁
  uniq₂ : ∀ K : Subgroup G, IsSolvableTwoComponentIn K (centralizer {z} ⊓ centralizer {z₁}) →
    z₁ ∈ K → K = J₂
  uniq₃ : ∀ K : Subgroup G, IsSolvableTwoComponentIn K (centralizer {z} ⊓ centralizer {z₁}) →
    z * z₁ ∈ K → K = J₃
  hcover : ∀ Y : Subgroup (Bar L),
    IsSolvableTwoComponentIn Y (centralizer {(QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L)}) →
    ∀ y ∈ Y, ∃ w : ↥L, ((w : G) ∈ J₁ ∨ (w : G) ∈ J₂ ∨ (w : G) ∈ J₃) ∧
      (QuotientGroup.mk w : Bar L) = y
  b : G
  hbz : b * z * b⁻¹ = z * z₁
  hbz₁ : b * z₁ * b⁻¹ = z₁

variable {z : G} {L : Subgroup G}

section Certified


theorem S7Config.exists_step6 (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) : Nonempty (Step6Three z L S) := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₁, hz₁L, hz₁S, hz₁, hz₁Z, hT⟩ := h.exists_z₁ hI hS
  have hz₁z : z₁ ∈ centralizer ({z} : Set G) := h.hL.1 hz₁L
  have hc : z * z₁ = z₁ * z := (mem_centralizer_singleton_iff.mp hz₁z).symm
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hne : z₁ ≠ z := fun he => hz₁Z (by
    have h1 : (⟨z₁, hz₁L⟩ : ↥L) = ⟨z, h.hzL⟩ := Subtype.ext he
    rw [h1]
    exact mk_mem_center_of_mem_center hzc)
  have hzz₁ : orderOf (z * z₁) = 2 := F3.orderOf_mul_of_commute h.hz hz₁ hc hne
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
  have hOodd := odd_card_pPrimeCore_two ↥L
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  have hz₁' : orderOf (⟨z₁, hz₁L⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hz₁
  have hz₁sq : (⟨z₁, hz₁L⟩ : ↥L) * ⟨z₁, hz₁L⟩ = 1 := by rw [← sq, ← hz₁', pow_orderOf_eq_one]
  obtain ⟨-, hc1, hc2, hc3⟩ := lemma410c_three (by norm_num) h.hcov
    (mk_mem_center_of_mem_center hzc) (mk_ne_one_of_orderOf_two hz')
    (orderOf_mk_eq_two hOodd hz₁') hz₁Z
  have lift : ∀ e : ↥L, (QuotientGroup.mk e : Bar L) ∈ ({QuotientGroup.mk ⟨z, h.hzL⟩,
      QuotientGroup.mk ⟨z₁, hz₁L⟩, QuotientGroup.mk ⟨z, h.hzL⟩ * QuotientGroup.mk ⟨z₁, hz₁L⟩} :
        Set (Bar L)) → e ∈ centralizer {(⟨z₁, hz₁L⟩ : ↥L)} →
      ∃ (Y : Subgroup (Bar L)) (J : Subgroup G),
        IsSolvableTwoComponentIn Y
          (centralizer {(QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L)}) ∧
        (QuotientGroup.mk e : Bar L) ∈ Y ∧
        IsSolvableTwoComponentIn J (centralizer {z} ⊓ centralizer {z₁}) ∧
        J ≤ L ⊔ (pPrimeCore 2 ↥(centralizer {z} ⊓ centralizer {z₁})).map
          (centralizer {z} ⊓ centralizer {z₁}).subtype ∧ (e : G) ∈ J ∧
        ∀ w : ↥L, w ∈ centralizer {(⟨z₁, hz₁L⟩ : ↥L)} →
          (QuotientGroup.mk w : Bar L) ∈ Y → (w : G) ∈ J := by
    intro e he hec
    obtain ⟨Y, hY, -, heY⟩ := hc3 _ he
    have hslY := (hc1 Y hY).1
    rw [pow_one] at hslY
    obtain ⟨eY⟩ := F3S7.nonempty_equiv_sl23 hslY
    obtain ⟨J, hJ, -, hJL, hmem⟩ := F3S7.exists_lift_solvable h.hL hz₁L hz₁ hY eY
    exact ⟨Y, J, hY, heY, hJ, hJL, hmem e hec heY, hmem⟩
  have hzC : (⟨z, h.hzL⟩ : ↥L) ∈ centralizer {(⟨z₁, hz₁L⟩ : ↥L)} :=
    mem_centralizer_singleton_iff.mpr (Subtype.ext hc)
  have hz₁C : (⟨z₁, hz₁L⟩ : ↥L) ∈ centralizer {(⟨z₁, hz₁L⟩ : ↥L)} :=
    mem_centralizer_singleton_iff.mpr rfl
  have hzz₁C : (⟨z * z₁, hzz₁L⟩ : ↥L) ∈ centralizer {(⟨z₁, hz₁L⟩ : ↥L)} := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    change z * z₁ * z₁ = z₁ * (z * z₁)
    calc z * z₁ * z₁ = z₁ * z * z₁ := by rw [hc]
      _ = z₁ * (z * z₁) := mul_assoc z₁ z z₁
  obtain ⟨Y₁, J₁, hY₁, hzY₁, hJ₁, hJ₁L, hzJ₁, hmem₁⟩ := lift _ (Or.inl rfl) hzC
  obtain ⟨Y₂, J₂, hY₂, hz₁Y₂, hJ₂, hJ₂L, hz₁J₂, hmem₂⟩ := lift _ (Or.inr (Or.inl rfl)) hz₁C
  obtain ⟨Y₃, J₃, hY₃, hzz₁Y₃, hJ₃, hJ₃L, hzz₁J₃, hmem₃⟩ :=
    lift _ (Or.inr (Or.inr rfl)) hzz₁C
  have hcover : ∀ Y : Subgroup (Bar L),
      IsSolvableTwoComponentIn Y (centralizer {(QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L)}) →
      ∀ y ∈ Y, ∃ w : ↥L, ((w : G) ∈ J₁ ∨ (w : G) ∈ J₂ ∨ (w : G) ∈ J₃) ∧
        (QuotientGroup.mk w : Bar L) = y := by
    intro Y hY y hy
    have hyC := hY.1 hy
    have hCt : (centralizer ({⟨z₁, hz₁L⟩} : Set ↥L)).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) =
        centralizer {(QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L)} :=
      map_centralizer_eq hOodd hz₁sq
    rw [← hCt] at hyC
    obtain ⟨w, hw, rfl⟩ := hyC
    refine ⟨w, ?_, rfl⟩
    rcases (hc1 Y hY).2 with hzY | hz₁Y | hzz₁Y
    · have hYeq := hc2 Y Y₁ hY hY₁ _ (Or.inl rfl) hzY hzY₁
      exact .inl (hmem₁ w hw (hYeq ▸ hy))
    · have hYeq := hc2 Y Y₂ hY hY₂ _ (Or.inr (Or.inl rfl)) hz₁Y hz₁Y₂
      exact .inr (.inl (hmem₂ w hw (hYeq ▸ hy)))
    · have hYeq := hc2 Y Y₃ hY hY₃ _ (Or.inr (Or.inr rfl)) hzz₁Y hzz₁Y₃
      exact .inr (.inr (hmem₃ w hw (hYeq ▸ hy)))
  obtain ⟨g₁, hg₁⟩ := h.exists_conj hI hz₁L hz₁
  have h₁ : S7Config G z₁ (L.map (MulAut.conj g₁).toMonoidHom) := hg₁ ▸ h.conj g₁
  have hzz₁' : z ∈ centralizer ({z₁} : Set G) := mem_centralizer_comm hz₁z
  have hzL₁ : z ∈ L.map (MulAut.conj g₁).toMonoidHom :=
    ((h₁.conj_iff hI hzz₁').mp ⟨g₁⁻¹, by rw [← hg₁]; group⟩).1
  have hzZ₁ : (QuotientGroup.mk (⟨z, hzL₁⟩ : ↥(L.map (MulAut.conj g₁).toMonoidHom)) :
      Bar (L.map (MulAut.conj g₁).toMonoidHom)) ∉
        center (Bar (L.map (MulAut.conj g₁).toMonoidHom)) :=
    fun hcen => hne (h₁.eq_of_mk_mem_center hzL₁ h.hz hcen).symm
  have hzz₁C' : z * z₁ ∈ centralizer ({z₁} : Set G) :=
    mul_mem hzz₁' (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨g₂, hg₂⟩ := h.exists_conj hI hzz₁L hzz₁
  have hzz₁L₁ : z * z₁ ∈ L.map (MulAut.conj g₁).toMonoidHom :=
    ((h₁.conj_iff hI hzz₁C').mp ⟨g₂ * g₁⁻¹, by rw [← hg₂, ← hg₁]; group⟩).1
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
  obtain ⟨b, hbL₁, hb⟩ := F3S7.spinSeven_conj_of_involution_three h₁.hcov hzL₁ hzz₁L₁ h.hz hzz₁
    hzZ₁ hzz₁Z₁
  have hbz₁ : b * z₁ * b⁻¹ = z₁ := by
    rw [mem_centralizer_singleton_iff.mp (h₁.hL.1 hbL₁), mul_inv_cancel_right]
  refine ⟨⟨z₁, hz₁L, hz₁S, hz₁, hz₁Z, hT, J₁, J₂, J₃, hJ₁, hJ₂, hJ₃, hJ₁L, hJ₂L, hJ₃L, hzJ₁,
    hz₁J₂, hzz₁J₃, ?_, ?_, ?_, hcover, b, hb, hbz₁⟩⟩
  · intro K hK hzK
    exact h₁.eq_of_isSolvableTwoComponentIn hI hzL₁ h.hz hzZ₁
      (inf_comm (centralizer {z}) (centralizer {z₁}) ▸ hK)
      (inf_comm (centralizer {z}) (centralizer {z₁}) ▸ hJ₁) hzK hzJ₁
  · intro K hK hz₁K
    exact h.eq_of_isSolvableTwoComponentIn hI hz₁L hz₁ hz₁Z hK hJ₂ hz₁K hz₁J₂
  · intro K hK hzz₁K
    exact h.eq_of_isSolvableTwoComponentIn hI hzz₁L hzz₁ hzz₁Z (hCzz₁ ▸ hK) (hCzz₁ ▸ hJ₃)
      hzz₁K hzz₁J₃

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
