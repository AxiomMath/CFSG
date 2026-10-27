module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusSchur
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusOddCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.S8
  CFSG.Yardstones.M3aba7dc4b8a8 Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G]

@[expose] def WidthFourOmegaMinusCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ S : Setting G, S.width = 4 → S11.NoA2All S → ¬ S.IsReducible →
    ∀ g : G, ∀ (H : Hyp4 S g) (C : Cons311 S g), ¬ Nonempty (S5.SwapData S g) →
      ∀ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ → finrank (ZMod 2) (Vt S g t) = 4 → ¬ PlusAt H C →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t⁻¹ ∈ Obar S

theorem widthFourOmegaMinus_of_central
    (hsw : WidthFourSwapFalse) (hc : WidthFourOmegaMinusCentral) : WidthFourOmegaMinus := by
  intro G _ _ _ hnab hchar hK S hw hno hirr g H C t ht ht1 hVQ hΩ h4 hP
  have hcomm : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t⁻¹ ∈ Obar S :=
    hc G hnab hchar hK S hw hno hirr g H C (hsw G hnab hchar hK S hw hno hirr g H C) t ht ht1 hVQ
      hΩ h4 hP
  have hCE : CentralExtInput.{0} := S4.centralExtInput
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have hnc : ∃ x ∈ S.Mbar, x * t * x⁻¹ ≠ t := S7.exists_conj_ne H ht ht1
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  have hOne : timmesfeldOddCore S.Mbar ≠ ⊥ := by
    intro hO
    obtain ⟨x, hx, hxt⟩ := hnc
    have hmem : x * t * x⁻¹ * t⁻¹ ∈ Obar S := hcomm x hx
    have hbot : Obar S = ⊥ := by
      rw [S7.Obar, hO, Subgroup.map_bot]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hxt (mul_inv_eq_one.mp hmem)
  have h3O := W4Minus.card_oddCore_dvd_three_not_plus H hNo C hP hw
  have hOcard : Nat.card (Obar S) = 3 := by
    rw [S7.card_Obar]
    rcases (Nat.dvd_prime Nat.prime_three).mp h3O with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hOne
    · exact h
  have hprod : Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × Cbar S t) :=
    S7.nonempty_mulEquiv_sigma_prod (X := S.O) (M := S.Mbar) (D := Obar S) (t := t)
      S7.Obar_le_Mbar hOcard (fun x hx y hy => S7.conj_mem_Obar hx hy)
      (S.Lbar_le_Mbar g ht) htt ht1 hcomm hnc
  have hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t :=
    (S4.commSpace_t_eq H C ht ht1 hVQ).1
  have hinj : Function.Injective (S7.resC S g hV) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcV : ∀ v ∈ Vt S g t, ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
      (restrictHom_eq_one_iff _ _ _ c).mp hc
    have hcM : (c : S.O) ∈ S.Mbar := S7.Cbar_le_Mbar c.2
    have hct : (c : S.O) * t = t * (c : S.O) := S7.comm_of_mem_Cbar c.2
    rcases W4Minus.eq_one_or_t_of_fix_Vt hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hcM hct hcV with
      h1 | ht_eq
    · exact Subtype.ext h1
    ·
      have htC : t ∈ Cbar S t := by
        have := c.2
        rw [ht_eq] at this
        exact this
      have htc : ∀ y ∈ Obar S, t * y = y * t := fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp htC).2 y
          (Subgroup.mem_sup_left hy)).symm
      obtain ⟨y, hy, hyt⟩ := S7.exists_not_comm_t (X := S.O) (M := S.Mbar) (D := Obar S) (t := t)
        hOcard htt hcomm hnc
      exact (hyt (htc y hy)).elim
  have hRmodN_le : RmodN S g t ≤ (S7.resC S g hV).range := by
    intro e he
    rw [← range_resV H.conj_mem t] at he
    obtain ⟨⟨r, hr⟩, rfl⟩ := he
    have htV : ∀ v ∈ Vt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
      (S6.self_mem_Nbar H ht).2 v hv
    rcases S7.mem_cent_of_comm_t (X := S.O) (M := S.Mbar) (D := Obar S) (t := t)
      S7.Obar_le_Mbar hOcard (fun x hx y hy => S7.conj_mem_Obar hx hy)
      (S.Lbar_le_Mbar g ht) htt ht1 hcomm hnc (Rbar_le_Mbar hr)
      (commute_of_mem_Rbar H.conj_mem hr) with hc | hc
    · exact ⟨⟨r, hc⟩, LinearEquiv.ext fun v => Subtype.ext rfl⟩
    · refine ⟨⟨t * r, hc⟩, LinearEquiv.ext fun v => Subtype.ext ?_⟩
      change ((t * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v
      rw [coe_mul_apply, htV _ (apply_mem_Vt_of_mem_Rbar H.conj_mem hr v.2)]
  obtain ⟨Q, hQ, -, hX, -, hsing⟩ := hΩ.exists_form
  have hleOrth : (S7.resC S g hV).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    S7.range_resC_le_orthogonalGroup H hNo C ht ht1 hVQ hΩ hV hsing
  have hrange : (S7.resC S g hV).range = omegaGroup Q hQ ∨
      (S7.resC S g hV).range = TauCeti.QuadraticMap.orthogonalGroup Q := by
    have : Nontrivial (Vt S g t) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    have h1 : omegaGroup Q hQ ≤ (S7.resC S g hV).range := hX ▸ hRmodN_le
    have h2 : (S7.resC S g hV).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hleOrth
    have h3 := relIndex_omegaGroup Q hQ
    have h4 := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
    rw [h3] at h4
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ h4) with h5 | h5
    · left
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h5) h1
    · right
      rw [h5] at h4
      exact le_antisymm h2 (Subgroup.relIndex_eq_one.mp (by omega))
  obtain ⟨q, hqnd, -, ⟨eΩ⟩, ⟨eO⟩⟩ := Bridge.exists_fin_form Q h4
  have hQnd : ∀ u, (∀ v, QuadraticMap.polar Q u v = 0) → u = 0 :=
    (Bridge.polarBilin_nondegenerate_iff Q).mp hQ
  obtain ⟨eM⟩ := hprod
  let eC : Cbar S t ≃* (S7.resC S g hV).range := MonoidHom.ofInjective hinj
  refine ⟨q, hqnd hQnd, ?_⟩
  rcases hrange with hrange | hrange
  · left
    have eCΩQ : Cbar S t ≃* timmesfeldOmega (Q : Vt S g t → ZMod 2) :=
      (eC.trans (MulEquiv.subgroupCongr hrange)).trans
        ((MulEquiv.subgroupCongr (S7.timmesfeldOmega_eq Q hQ)).symm)
    have eCΩ : Cbar S t ≃* timmesfeldOmega (q : (Fin 4 → ZMod 2) → ZMod 2) := eCΩQ.trans eΩ
    exact ⟨eM.trans (MulEquiv.prodCongr (MulEquiv.refl _) eCΩ)⟩
  · right
    have eCOQ : Cbar S t ≃* timmesfeldIsometries (Q : Vt S g t → ZMod 2) :=
      (eC.trans (MulEquiv.subgroupCongr hrange)).trans
        ((MulEquiv.subgroupCongr (S7.timmesfeldIsometries_eq Q)).symm)
    have eCO : Cbar S t ≃* timmesfeldIsometries (q : (Fin 4 → ZMod 2) → ZMod 2) := eCOQ.trans eO
    exact ⟨eM.trans (MulEquiv.prodCongr (MulEquiv.refl _) eCO)⟩

end CFSG.GF2Type.Smith1979
