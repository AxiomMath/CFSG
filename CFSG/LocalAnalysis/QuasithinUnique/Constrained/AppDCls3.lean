module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDCls2

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC

variable {G : Type} [Group G] [Finite G]

namespace GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem V_inf_D : conjR (C.U) x ⊓ blockD S L = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  have hyU := m.V_inf_Q_le_U C hy.1 (C.D_le_Q hy.2)
  have : y ∈ C.U ⊓ blockD S L := ⟨hyU, hy.2⟩
  rwa [C.U_inf_D] at this

theorem mem_B_of_pf {a : G} (haS : a ∈ S) (hπ : C.P.pf a ∈ Eset) : a ∈ baum S := by
  obtain ⟨v, hv, u, hu, d, hd, rfl, -⟩ := m.exists_vud C haS hπ
  exact mul_mem (mul_mem (m.V_le_B C hv) (C.U_le_baum hu)) (m.D_le_B C hd)

theorem card_VD : Nat.card ↥(conjR (C.U) x ⊔ blockD S L) = 16 * Nat.card ↥(blockD S L) := by
  have h := B2F.card_sup_mul_card_inf_of_commute (A := conjR (C.U) x) (B := blockD S L)
    (fun v hv d hd => (m.D_comm_V C hd hv).symm)
  rw [m.V_inf_D C, Subgroup.card_bot, card_V (x := x) C] at h
  omega

theorem eq_VD_of_type_E {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g ∈ Eset) : A = conjR (C.U) x ⊔ blockD S L := by
  have hAN : A ≤ S := hA.1
  have hVN : conjR (C.U) x ≤ S := (m.V_le_S C)
  have hD := m.D_le_of_isMax C hA
  have hex : ∀ g ∈ Eset, ∃ v ∈ conjR (C.U) x, ∃ u ∈ C.U,
      v * u ∈ A ∧ C.P.pf v = g := by
    intro g hg
    have hgA : g ∈ C.P.im A := (hty g).2 hg
    obtain ⟨a, haA, hpa⟩ := (C.P.mem_im_pf hAN).1 hgA
    obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := m.exists_vud C (hA.1 haA) (by rw [hpa]; exact hg)
    refine ⟨v, hv, u, hu, ?_, by rw [hpv, hpa]⟩
    have := mul_mem haA (inv_mem (hD hd))
    rw [hadec] at this
    simpa [mul_assoc] using this
  have hfixu : ∀ v ∈ conjR (C.U) x, ∀ u ∈ C.U, v * u ∈ A →
      vact (C.P.pf v) (C.P.bf u) = C.P.bf u := by
    intro v hv u hu hvu
    have hcom := comm_of_sq (hA.2.1.2 _ hvu) (V_sq (x := x) C hv) (C.hU.2 u hu)
    exact (C.P.comm_iff (hVN hv) hu).1 hcom
  obtain ⟨v₁, hv₁, u₁, hu₁, h₁A, hp₁⟩ := hex (swap 0 1) t1_mem_Eset
  obtain ⟨v₂, hv₂, u₂, hu₂, h₂A, hp₂⟩ := hex (swap 2 3) t2_mem_Eset
  have hf₁ := hfixu v₁ hv₁ u₁ hu₁ h₁A
  have hf₂ := hfixu v₂ hv₂ u₂ hu₂ h₂A
  rw [hp₁] at hf₁
  rw [hp₂] at hf₂
  have hcomm12 : (v₁ * u₁) * (v₂ * u₂) = (v₂ * u₂) * (v₁ * u₁) :=
    B2F.isElemAbelian_comm hA.2.1 h₁A h₂A
  have hrel := (C.P.comm_vu (hVN hv₁) (hVN hv₂) hu₁ hu₂ (V_comm (x := x) C hv₁ hv₂)).1 hcomm12
  rw [hp₁, hp₂, Equiv.swap_inv, Equiv.swap_inv] at hrel
  have hrel' : pact (swap 2 3) (C.P.bf u₁).1 + (C.P.bf u₂).1 =
      pact (swap 0 1) (C.P.bf u₂).1 + (C.P.bf u₁).1 := congrArg Subtype.val hrel
  obtain ⟨hF1, hF2⟩ := E_comm _ _ hrel'
  have hF1' : ∀ σ ∈ Eset, vact σ (C.P.bf u₁) = C.P.bf u₁ := fun σ hσ =>
    Subtype.ext (fixE_of _ (congrArg Subtype.val hf₁) hF1 σ hσ)
  have hF2' : ∀ σ ∈ Eset, vact σ (C.P.bf u₂) = C.P.bf u₂ := fun σ hσ =>
    Subtype.ext (fixE_of _ hF2 (congrArg Subtype.val hf₂) σ hσ)
  have hle : A ≤ conjR (C.U) x ⊔ blockD S L := by
    intro a ha
    have hpa : C.P.pf a ∈ Eset := (hty _).1 ((C.P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩)
    obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := m.exists_vud C (hA.1 ha) hpa
    have hvu : v * u ∈ A := by
      have := mul_mem ha (inv_mem (hD hd))
      rw [hadec] at this
      simpa [mul_assoc] using this
    have hpvE : C.P.pf v ∈ Eset := by rw [hpv]; exact hpa
    have hinvE : (C.P.pf v)⁻¹ ∈ Eset := by
      have := Eset_inv _ hpvE
      exact this
    have hfix1 : vact (swap 0 1) (C.P.bf u) = C.P.bf u := by
      have hcom : (v * u) * (v₁ * u₁) = (v₁ * u₁) * (v * u) :=
        B2F.isElemAbelian_comm hA.2.1 hvu h₁A
      have h := (C.P.comm_vu (hVN hv) (hVN hv₁) hu hu₁ (V_comm (x := x) C hv hv₁)).1 hcom
      rw [hp₁, Equiv.swap_inv, hF1' _ hinvE] at h
      rw [add_comm (C.P.bf u₁) (C.P.bf u)] at h
      exact add_right_cancel h
    have hfix2 : vact (swap 2 3) (C.P.bf u) = C.P.bf u := by
      have hcom : (v * u) * (v₂ * u₂) = (v₂ * u₂) * (v * u) :=
        B2F.isElemAbelian_comm hA.2.1 hvu h₂A
      have h := (C.P.comm_vu (hVN hv) (hVN hv₂) hu hu₂ (V_comm (x := x) C hv hv₂)).1 hcom
      rw [hp₂, Equiv.swap_inv, hF2' _ hinvE] at h
      rw [add_comm (C.P.bf u₂) (C.P.bf u)] at h
      exact add_right_cancel h
    have hallE : ∀ σ ∈ Eset, vact σ (C.P.bf u) = C.P.bf u := fun σ hσ =>
      Subtype.ext (fixE_of _ (congrArg Subtype.val hfix1) (congrArg Subtype.val hfix2) σ hσ)
    have huC : u ∈ Subgroup.centralizer (conjR (C.U) x : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
      have hwE : C.P.pf w ∈ Eset := by
        have : C.P.pf w ∈ C.P.im (conjR C.U x) := (C.P.mem_im_pf hVN).2 ⟨w, hw, rfl⟩
        rw [m.im_V C] at this
        exact (mem_Estd _).1 this
      exact (C.P.comm_iff (hVN hw) hu).2 (hallE _ hwE)
    have huV : u ∈ conjR (C.U) x := by
      have : u ∈ C.U ⊓ Subgroup.centralizer (conjR (C.U) x : Set G) := ⟨hu, huC⟩
      rw [(m.cent_U_V C).1] at this
      exact this.2
    rw [hadec]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hv huV)) (Subgroup.mem_sup_right hd)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [m.card_VD C, ← C.card_Q, ← m.card_eq_Q C hA]

theorem Qx_type_E : ∀ g, g ∈ C.P.im (conjR (pCoreOf 2 H) x) ↔ g ∈ Eset := by
  have hQx := m.Qx_isMax C
  have hVle : conjR (C.U) x ≤ conjR (pCoreOf 2 H) x := C5.conjSubgroup_mono C.hUQ x
  have hmem : ∀ g ∈ Eset, g ∈ C.P.im (conjR (pCoreOf 2 H) x) := by
    intro g hg
    have : g ∈ C.P.im (conjR C.U x) := by rw [m.im_V C]; exact (mem_Estd g).2 hg
    exact C.P.im_mono hVle this
  have ht1 := hmem _ t1_mem_Eset
  have ht2 := hmem _ t2_mem_Eset
  rcases m.type_cases C hQx with h | h | h | h
  · exact absurd ((h _).1 ht1) (by decide)
  · rcases (h _).1 ht2 with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · rcases (h _).1 ht1 with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · exact h

theorem Qx_eq : conjR (pCoreOf 2 H) x = conjR (C.U) x ⊔ blockD S L :=
  m.eq_VD_of_type_E C (m.Qx_isMax C) (m.Qx_type_E C)

end GMate

end CFSG.QuasithinUnique.AppD
