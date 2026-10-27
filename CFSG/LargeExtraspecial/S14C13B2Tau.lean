module

public import CFSG.LargeExtraspecial.S14C13B2A2
public import CFSG.LargeExtraspecial.S10Conj
public import CFSG.LargeExtraspecial.S6SevenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S10
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_conj_mem_Lbar_not_mem_Nbar [IsSimpleGroup G] (h83 : S8_3Stmt) {t : S.O}
    (hSt : Stage S g t) (hocc : Config.omegaPlus8b.Occurs S g t) :
    ∃ k : S.M, S.ρ k ∈ normalizer (S.Lbar g : Set S.O) ∧
      S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ∧ S.ρ k * t * (S.ρ k)⁻¹ ∉ Nbar S g t := by
  have haQ := hSt.hyp4.conj_mem
  have hw : S.width = 16 := hocc.2.1
  rcases h83 G S g t hSt (Or.inr (Or.inr hocc.1)) with ⟨x, hxM, hxL, hxN⟩ | ⟨-, -, h⟩ |
    ⟨-, -, h⟩
  · obtain ⟨n, hnM, hnN, hn⟩ := S5.exists_mem_normalizer_conj hSt.hyp4 hSt.cons hxM
      (fun l hl => Lbar_comm S haQ hSt.mem hl) (fun l hl => Lbar_comm S haQ hxL hl)
    obtain ⟨k, rfl⟩ := hnM
    exact ⟨k, hnN, hn ▸ hxL, hn ▸ hxN⟩
  · omega
  · omega

variable {t : S.O}

theorem exists_eichler_of_conj (hCE : CentralExtInput.{0}) (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) (D : B2Data S g hSt.mem) {k : S.M}
    (hτL : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g) (hτN : S.ρ k * t * (S.ρ k)⁻¹ ∉ Nbar S g t) :
    ∃ u : Vt S g t, polar D.Q (aV hSt.mem) u = 0 ∧ D.Q u = 0 ∧
      LinearIndependent (ZMod 2) ![aV hSt.mem, u] ∧
      (resV hSt.hyp4.conj_mem t ⟨_, Lbar_le_Rbar hSt.mem hτL⟩ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
        eichler D.Q (aV hSt.mem) u := by
  have H := hSt.hyp4
  have ht := hSt.mem
  have hA := isTypeA_resV_of_conj hCE hSt hocc D hτL hτN (k := S.ρ k) rfl
  set x := resV H.conj_mem t ⟨_, Lbar_le_Rbar ht hτL⟩
  have hxL : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical D.Q (aV ht) := by
    rw [← D.hE]; exact ⟨_, hτL, fun v => rfl⟩
  obtain ⟨u, hau, hxu⟩ := (mem_pointRadical_iff D.hQ (aV_ne_zero H ht) (D.Q_aV H)).mp hxL
  have hli : LinearIndependent (ZMod 2) ![aV ht, u] := by
    rw [linearIndependent_pair_iff]
    refine ⟨aV_ne_zero H ht, fun hu => hA.2.1 ?_, fun hu => hA.2.1 ?_⟩
    · rw [hxu, hu, CFSG.ClassicalGroups.Orthogonal.eichler_zero_right]
    · rw [hxu, ← hu]
      exact (eichler_eq_one_iff D.hQ (aV_ne_zero H ht) (D.Q_aV H)
        (polar_self_eq_zero D.Q _)).mpr (Submodule.mem_span_singleton_self _)
  refine ⟨u, hau, hA.2.2.2.2 u ?_, hli, hxu⟩
  rw [hxu, commSpace_eichler D.hQ (D.Q_aV H) hau hli]
  exact Submodule.subset_span (by simp)

theorem exists_b_of_conj (hCE : CentralExtInput.{0}) (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) (D : B2Data S g hSt.mem) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O))
    (hτL : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g) (hτN : S.ρ k * t * (S.ρ k)⁻¹ ∉ Nbar S g t) :
    ∃ (h₁ : S.M) (_ : S.ρ h₁ ∈ Rbar S g t) (hth₁ : t ∈ S.Lbar ((h₁ : G) * g)),
      S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar (((k * h₁ : S.M) : G) * g) ∧
      t ∈ S.Lbar (((k * h₁ : S.M) : G) * g) ∧
      S.cl (((k * h₁ : S.M) : G) * g * S.z * (((k * h₁ : S.M) : G) * g)⁻¹) ∈ Vt S g t ∧
      polar D.Q (aV hSt.mem) (bV hth₁) = 0 ∧ bV hth₁ ≠ aV hSt.mem := by
  have H := hSt.hyp4
  have haQ := H.conj_mem
  have ht := hSt.mem
  obtain ⟨u, hau, hQu, hli, hxu⟩ := exists_eichler_of_conj hCE hSt hocc D hτL hτN
  have hli' := linearIndependent_pair_iff.mp hli
  set y : S.O := S.ρ k with hy
  have hya : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    fix_cl_of_mem_normalizer H hk
  have hyia : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    conv_lhs => rw [← hya]
    exact inv_apply_apply_O y _
  have h67 : orbit S g t = {v | v ∈ Vt S g t ∧ ∃ x ∈ S.Mbar,
      v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} := by
    rcases S6.timmesfeld_6_7 hCE H (noA2_of_stage hSt) hSt.cons ht hSt.ne_one with h | ⟨-, -, h4⟩
    · exact h
    · rw [D.hdim] at h4; omega
  have hcomm : commSpace ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    have e : ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (y : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := rfl
    rw [e, commSpace_conj, commSpace_t_eq_Vt H hSt.cons ht hSt.ne_one D.hVQ]
  have hpull : ∀ w : Vt S g t, w ∈ Submodule.span (ZMod 2) {aV ht, u} →
      ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Vt S g t := by
    intro w hw
    rw [← commSpace_eichler D.hQ (D.Q_aV H) hau hli, ← hxu] at hw
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
    have hmem : (((resV haQ t ⟨_, Lbar_le_Rbar ht hτL⟩ :
        Vt S g t ≃ₗ[ZMod 2] Vt S g t) v - v : Vt S g t) : S.Qt) ∈
        commSpace ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      ⟨v, by simp [coe_resV_apply]⟩
    rw [hcomm] at hmem
    obtain ⟨v', hv', e⟩ := hmem
    rw [← e]
    simpa using (show ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v') ∈
      Vt S g t by rw [inv_apply_apply_O]; exact hv')
  have horb : ∀ w : Vt S g t, w ∈ Submodule.span (ZMod 2) {aV ht, u} → w ≠ 0 → D.Q w = 0 →
      ∃ r ∈ Rbar S g t, ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    intro w hw hw0 hQw
    have h1 := (mem_orbitOf_RmodN_iff haQ ht).mp ((D.horb w hw0).mp hQw)
    obtain ⟨r, hr, hre⟩ := h1
    have h2 : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ orbit S g t := by
      rw [h67]
      refine ⟨hpull w hw, y⁻¹ * r, mul_mem (inv_mem ⟨k, rfl⟩) (Rbar_le_Mbar hr), ?_⟩
      rw [hre, coe_mul_apply]
    exact h2
  have huspan : u ∈ Submodule.span (ZMod 2) {aV ht, u} := Submodule.subset_span (by simp)
  obtain ⟨r₁, hr₁, hr₁e⟩ := horb u huspan hli'.2.1 hQu
  obtain ⟨h₁, rfl⟩ : ∃ h₁ : S.M, S.ρ h₁ = r₁ := Rbar_le_Mbar hr₁
  have hth₁ := mem_Lbar_mul_of_mem_Rbar H ht hr₁
  have hb : (bV hth₁ : S.Qt) = ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by
    rw [coe_bV, hr₁e, ρ_cl_conj_z S h₁ haQ]
  have hbne : bV hth₁ ≠ aV ht := by
    intro h
    apply hli'.2.2
    apply Subtype.ext
    have := congrArg Subtype.val h
    rw [hb] at this
    have := congrArg ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt → S.Qt) this
    rw [show (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u by
      rw [← coe_mul_apply, mul_inv_cancel]; rfl] at this
    rw [this]
    exact hya.symm
  have hQb : D.Q (bV hth₁) = 0 :=
    (D.horb _ (bV_ne_zero H _)).mpr ((mem_orbitOf_RmodN_iff haQ ht).mpr
      ⟨S.ρ h₁, hr₁, by rw [coe_bV, ρ_cl_conj_z S h₁ haQ]⟩)
  have hneg : ∀ w : Vt S g t, -w = w := fun w => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hau0 : aV ht + u ≠ 0 := fun h => hli'.2.2
    (sub_eq_zero.mp (by rw [sub_eq_add_neg, hneg, h]))
  have hQau : D.Q (aV ht + u) = 0 := by
    rw [QuadraticMap.map_add D.Q (aV ht) u, D.Q_aV H, hQu, hau, add_zero, add_zero]
  obtain ⟨r₂, hr₂, hr₂e⟩ := horb (aV ht + u)
    (Submodule.add_mem _ (Submodule.subset_span (by simp)) huspan) hau0 hQau
  have hQab : D.Q (aV ht + bV hth₁) = 0 := by
    have hne : aV ht + bV hth₁ ≠ 0 := fun h => hbne
      (sub_eq_zero.mp (by rw [sub_eq_add_neg, hneg, add_comm, h]))
    refine (D.horb _ hne).mpr ((mem_orbitOf_RmodN_iff haQ ht).mpr ⟨r₂, hr₂, ?_⟩)
    rw [← hr₂e]
    change S.cl (g * S.z * g⁻¹) + (bV hth₁ : S.Qt) = _
    rw [hb, Submodule.coe_add, map_add,
      show ((aV ht : Vt S g t) : S.Qt) = S.cl (g * S.z * g⁻¹) from rfl, hyia]
  have e : S.cl (((k * h₁ : S.M) : G) * g * S.z * (((k * h₁ : S.M) : G) * g)⁻¹) =
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (bV hth₁ : S.Qt) := by
    rw [← ρ_cl_conj_z S (k * h₁) haQ, coe_bV, ← ρ_cl_conj_z S h₁ haQ, hy, ← coe_mul_apply,
      ← map_mul]
  have hcu : S.cl (((k * h₁ : S.M) : G) * g * S.z * (((k * h₁ : S.M) : G) * g)⁻¹) = u := by
    rw [e, hb, ← coe_mul_apply, mul_inv_cancel]
    rfl
  refine ⟨h₁, hr₁, hth₁, ?_, ?_, hcu ▸ u.2, ?_, hbne⟩
  · rw [← Lbar_mul_map_cK k h₁]
    exact ⟨t, hth₁, rfl⟩
  ·
    obtain ⟨r, hr, hre⟩ := (mem_orbitOf_RmodN_iff haQ ht).mp ((D.horb u hli'.2.1).mp hQu)
    obtain ⟨h₂, rfl⟩ : ∃ h₂ : S.M, S.ρ h₂ = r := Rbar_le_Mbar hr
    have hth₂ := mem_Lbar_mul_of_mem_Rbar H ht hr
    have hQ2 : (h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹ ∈ S.QG := by
      have := S.conj_mem_QG h₂.2 haQ
      simpa [mul_assoc] using this
    have hne2 : (h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹ ≠ S.z := by
      intro h
      apply H.conj_ne
      have e1 : g * S.z * g⁻¹ =
          (h₂ : G)⁻¹ * ((h₂ : G) * g * S.z * ((h₂ : G) * g)⁻¹) * (h₂ : G) := by group
      rw [e1, h, mul_assoc, ← S.mem_M_iff.mp h₂.2, inv_mul_cancel_left]
    have hQ3 : ((k * h₁ : S.M) : G) * g * S.z * (((k * h₁ : S.M) : G) * g)⁻¹ ∈ S.QG := by
      have := S.conj_mem_QG (k * h₁).2 haQ
      simpa [mul_assoc] using this
    have hL := Lbar_eq_of_cl_eq S hQ2 hne2 hQ3 (by
      rw [hcu, hre, ρ_cl_conj_z S h₂ haQ])
    rw [hL]
    exact hth₂
  · have e := QuadraticMap.map_add D.Q (aV ht) (bV hth₁)
    rw [hQab, D.Q_aV H, hQb, zero_add, zero_add] at e
    exact e.symm

end CFSG.LargeExtraspecial.S14
