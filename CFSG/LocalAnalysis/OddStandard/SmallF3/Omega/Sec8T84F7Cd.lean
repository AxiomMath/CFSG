module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3E0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

private lemma local_mem_sup_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hconj : ∀ a ∈ H, ∀ b ∈ K, a * b * a⁻¹ ∈ K :=
    Subgroup.le_normalizer_iff.mp hHK
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, a * b = x}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
          exact ⟨a * c, H.mul_mem ha hc, (c⁻¹ * b * c) * d,
            K.mul_mem (by simpa using hconj c⁻¹ (H.inv_mem hc) b hb) hd, by group⟩
        inv_mem' := by
          rintro x ⟨a, ha, b, hb, rfl⟩
          exact ⟨a⁻¹, H.inv_mem ha, a * b⁻¹ * a⁻¹, hconj a ha b⁻¹ (K.inv_mem hb),
            by group⟩ }
    have hHP : H ≤ P := fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩
    have hKP : K ≤ P := fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩
    exact SetLike.le_def.mp (sup_le hHP hKP) hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

private lemma local_isElemAbelian_of_le {E H : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hH : H ≤ E) : CFSG.Open.IsElemAbelian 2 H := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    simpa using isMulCommutative_iff.mp hE.1 ⟨a, hH a.2⟩ ⟨b, hH b.2⟩
  · intro x hx
    exact hE.2 x (hH hx)

private lemma local_F2_le_T2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F2 ≤ T2 := by
  rw [D.F2_eq]
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨f, hf, rfl⟩ := hx
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using D.swap1 f (D.mod1.F_le hf)

private lemma local_F1_le_normalizer_F2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    F1 ≤ Subgroup.normalizer (F2 : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha b hb
  rw [D.comm a (D.mod1.F_le ha) b (local_F2_le_T2 D hb), mul_assoc, mul_inv_cancel, mul_one]
  exact hb

theorem sec8t84_E0_cent_card_le (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    Nat.card ↥((F1 ⊔ F2) ⊓ centralizer ({t} : Set G)) ≤ 16 := by
  have hE0 : CFSG.Open.IsElemAbelian 2 (F1 ⊔ F2) := (sec8t84_E0_isElemAb2 D).1
  have hR_le_E0 : (F1 ⊔ F2) ⊓ centralizer ({t} : Set G) ≤ F1 ⊔ F2 := inf_le_left
  have hR_elem : CFSG.Open.IsElemAbelian 2 ((F1 ⊔ F2) ⊓ centralizer ({t} : Set G)) :=
    local_isElemAbelian_of_le hE0 hR_le_E0
  have hR_le_T0 : (F1 ⊔ F2) ⊓ centralizer ({t} : Set G) ≤
      (T1 ⊔ T2) ⊓ centralizer ({t} : Set G) :=
    le_inf (hR_le_E0.trans (sup_le (D.mod1.F_le.trans le_sup_left)
      ((local_F2_le_T2 D).trans le_sup_right))) inf_le_right
  obtain ⟨R1, hR1_le, -, hR1_card, hdiag, hdiag_mem⟩ :=
    sec8t84_wr_elem_cent D.wr hR_le_T0 hR_elem
  have hR1_le_F1 : R1 ≤ F1 := by
    intro a ha
    have hda : a * (t * a * t⁻¹) ∈ (F1 ⊔ F2) ⊓ centralizer ({t} : Set G) := hdiag_mem a ha
    have hmem : a * (t * a * t⁻¹) ∈ F1 ⊔ F2 := hR_le_E0 hda
    obtain ⟨f1, hf1, f2, hf2, hprod⟩ :=
      (local_mem_sup_of_le_normalizer (local_F1_le_normalizer_F2 D)).mp hmem
    have haT1 : a ∈ T1 := hR1_le ha
    have htaT2 : t * a * t⁻¹ ∈ T2 := D.swap1 a haT1
    have hf2T2 : f2 ∈ T2 := local_F2_le_T2 D hf2
    have huniq := sec8t84_wr_unique D.wr haT1 (D.mod1.F_le hf1) htaT2 hf2T2 hprod.symm
    rw [huniq.1]
    exact hf1
  calc Nat.card ↥((F1 ⊔ F2) ⊓ centralizer ({t} : Set G))
      = Nat.card R1 := hR1_card.symm
    _ ≤ Nat.card F1 := Subgroup.card_le_of_le hR1_le_F1
    _ = 16 := by rw [D.mod1.F_e16.2]; norm_num

end TData

end CFSG.OddStandard.SmallF3.Omega
