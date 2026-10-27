module

public import CFSG.GH74.GLS.IVK.Lifted.OuterStruct

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510

open Subgroup CFSG CFSG.GorensteinWalter CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

section L2Level

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem l510_mul_self_of_orderOf_two {X : Type} [Group X] {a : X} (h : orderOf a = 2) : a * a = 1 := by
  have := pow_orderOf_eq_one a
  rwa [h, sq] at this

theorem l2_exists_Rm
    (h : L2Field F) (e : K ≃* L2 F) (M : Subgroup (MulAut K)) (hM : IsPGroup 2 ↥M) (P₀ : Sylow 2 K)
    (hP₀ : (P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤ M) :
    ∃ (e' : K ≃* L2 F) (Rm : Subgroup (MulAut K)), Rm ≤ M ∧ Rm ≤ fieldAutSub e' ∧
      (P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K) ⊓ Rm = ⊥ ∧
      ((P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K) ⊔ Rm).relIndex M ≤ 2 ∧
      ∀ x₀ ∈ M, orderOf x₀ = 2 → fieldProj e x₀ ≠ 1 →
        ∃ r₁ ∈ Rm, orderOf r₁ = 2 ∧ ∀ x ∈ M, orderOf x = 2 → fieldProj e x ≠ 1 →
          ∃ d ∈ (P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K), x = d * r₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hMT⟩ := hM.exists_le_sylow
  obtain ⟨e', N, hNT⟩ := ivk_1_2a_exists F h K e T
  have hTN : (N.T : Subgroup (MulAut K)) = (T : Subgroup (MulAut K)) := by rw [hNT]
  have hMT' : M ≤ (N.T : Subgroup (MulAut K)) := by rw [hTN]; exact hMT
  set D : Subgroup (MulAut K) := (P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K) with hDdef
  have hDP : D = N.P := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact le_inf (hP₀.trans hMT') (Subgroup.map_le_range _ _)
    · rw [card_P_eq e' N, hDdef, Subgroup.card_map_of_injective (conj_injective_of_L2 e),
        Sylow.card_eq_multiplicity P₀]
  have hPM : N.P ≤ M := by rw [← hDP]; exact hP₀
  have hPinn : N.P ≤ innAut K := inf_le_right
  have hRF : N.R ≤ fieldAutSub e' := inf_le_right
  have hRT : N.R ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hPtT : N.Pt ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hPtd : N.Pt ≤ innDiagSub e' := inf_le_right
  have hPPt : N.P ≤ N.Pt := P_le_Pt N
  have hPtR : N.Pt ⊓ N.R = ⊥ := (ivk_1_2f F h K e' N).1
  have hstruct := ivk_1_2a_struct F h K e' N
  have hRcomm : ∀ r₁ ∈ N.R, ∀ r₂ ∈ N.R, r₁ * r₂ = r₂ * r₁ := by
    intro r₁ h₁ r₂ h₂
    have : IsCyclic ↥(fieldAutSub e') := hstruct.2.1
    let := IsCyclic.commGroup (α := ↥(fieldAutSub e'))
    have := mul_comm (⟨r₁, hRF h₁⟩ : ↥(fieldAutSub e')) ⟨r₂, hRF h₂⟩
    simpa using congrArg Subtype.val this
  have hcommP : ∀ r ∈ N.R, ∀ d ∈ N.Pt, ⁅r, d⁆ ∈ N.P := by
    intro r hr d hd
    have hdIn : d ∈ innAut K ⊔ zpowers N.t := by
      have h1 : d ∈ N.P ⊔ zpowers N.t := by rw [P_sup_zpowers_eq_Pt e' h N]; exact hd
      exact (sup_le_sup_right hPinn _) h1
    have hc : ⁅r, d⁆ ∈ innAut K := hstruct.2.2.2 r (hRF hr) d hdIn
    have hcT : ⁅r, d⁆ ∈ (N.T : Subgroup (MulAut K)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hRT hr) (hPtT hd)) (inv_mem (hRT hr))) (inv_mem (hPtT hd))
    exact ⟨hcT, hc⟩
  have hidx : (N.P.subgroupOf N.Pt).index = 2 := P_index_two h N
  have hPtCov : ∀ x ∈ N.Pt, ∀ y ∈ N.Pt, x ∉ N.P → y ∉ N.P → x * y⁻¹ ∈ N.P := by
    intro x hx y hy hxP hyP
    have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : N.Pt))
      (b := (⟨y⁻¹, N.Pt.inv_mem hy⟩ : N.Pt))
    have h1 : (⟨x, hx⟩ : N.Pt) ∉ N.P.subgroupOf N.Pt := hxP
    have h2 : (⟨y⁻¹, N.Pt.inv_mem hy⟩ : N.Pt) ∉ N.P.subgroupOf N.Pt := fun hh =>
      hyP (by simpa using N.P.inv_mem (Subgroup.mem_subgroupOf.1 hh))
    have h3 : (⟨x, hx⟩ : N.Pt) * ⟨y⁻¹, N.Pt.inv_mem hy⟩ ∈ N.P.subgroupOf N.Pt :=
      key.2 (iff_of_false h1 h2)
    exact Subgroup.mem_subgroupOf.1 h3
  set Rm : Subgroup (MulAut K) := M ⊓ N.R with hRmdef
  have hRmM : Rm ≤ M := inf_le_left
  have hRmR : Rm ≤ N.R := inf_le_right
  have hdec : ∀ m ∈ M, ∃ d ∈ N.Pt, ∃ r ∈ N.R, m = d * r := fun m hm => T_decomp N m (hMT' hm)
  have hrM : ∀ m ∈ M, ∀ d ∈ N.P, ∀ r : MulAut K, m = d * r → r ∈ M := by
    intro m hm d hd r hmdr
    have : r = d⁻¹ * m := by rw [hmdr]; group
    rw [this]
    exact M.mul_mem (M.inv_mem (hPM hd)) hm
  have hindex : (N.P ⊔ Rm).relIndex M ≤ 2 := by
    by_cases hall : M ≤ N.P ⊔ Rm
    · rw [Subgroup.relIndex_eq_one.2 hall]
      norm_num
    · obtain ⟨a, haM, haP'⟩ : ∃ a ∈ M, a ∉ N.P ⊔ Rm := by
        by_contra hcon
        push Not at hcon
        exact hall fun m hm => hcon m hm
      obtain ⟨da, hda, ra, hra, haeq⟩ := hdec a haM
      have hdaP : da ∉ N.P := by
        intro hdaP
        apply haP'
        have hra' : ra ∈ Rm := ⟨hrM a haM da hdaP ra haeq, hra⟩
        rw [haeq]
        exact mul_mem_sup hdaP hra'
      have haT : a ∈ (N.T : Subgroup (MulAut K)) := hMT' haM
      refine relIndex_le_two_of_cover (P := N.P ⊔ Rm) haM ?_ ?_
      · intro b hb
        obtain ⟨db, hdb, rb, hrb, hbeq⟩ := hdec b hb
        by_cases hdbP : db ∈ N.P
        · left
          have hrb' : rb ∈ Rm := ⟨hrM b hb db hdbP rb hbeq, hrb⟩
          rw [hbeq]
          exact mul_mem_sup hdbP hrb'
        · right
          have hu : rb * ra⁻¹ ∈ N.R := N.R.mul_mem hrb (N.R.inv_mem hra)
          have hcab : ⁅da, rb * ra⁻¹⁆ ∈ N.P := by
            have := N.P.inv_mem (hcommP (rb * ra⁻¹) hu da hda)
            rwa [commutatorElement_inv] at this
          have hp₀ : (db * da⁻¹) * ⁅da, rb * ra⁻¹⁆ ∈ N.P :=
            N.P.mul_mem (hPtCov db hdb da hda hdbP hdaP) hcab
          have hbaeq : b * a⁻¹ = ((db * da⁻¹) * ⁅da, rb * ra⁻¹⁆) * (rb * ra⁻¹) := by
            rw [hbeq, haeq]
            simp only [commutatorElement_def]
            group
          have huM : rb * ra⁻¹ ∈ M := by
            have e1 : rb * ra⁻¹ = ((db * da⁻¹) * ⁅da, rb * ra⁻¹⁆)⁻¹ * (b * a⁻¹) := by
              rw [hbaeq]
              group
            rw [e1]
            exact M.mul_mem (M.inv_mem (hPM hp₀)) (M.mul_mem hb (M.inv_mem haM))
          refine ⟨((db * da⁻¹) * ⁅da, rb * ra⁻¹⁆) * (rb * ra⁻¹),
            mul_mem_sup hp₀ (⟨huM, hu⟩ : rb * ra⁻¹ ∈ Rm), ?_⟩
          calc b = (b * a⁻¹) * a := by group
            _ = _ := by rw [hbaeq]
      · intro p hp
        have hle : N.P ⊔ Rm ≤ (N.P ⊔ Rm).comap (MulAut.conj a⁻¹).toMonoidHom := by
          refine sup_le (fun p hp => ?_) (fun r hr => ?_)
          · have h1 : a⁻¹ * p * a⁻¹⁻¹ ∈ N.P := conj_mem_P N ((N.T : Subgroup (MulAut K)).inv_mem haT) hp
            exact mem_sup_left (by simpa [MulAut.conj_apply] using h1)
          · have hr' : r ∈ N.R := hRmR hr
            have hc : ⁅da⁻¹, r⁆ ∈ N.P := by
              have := N.P.inv_mem (hcommP r hr' da⁻¹ (N.Pt.inv_mem hda))
              rwa [commutatorElement_inv] at this
            have hra' : ra⁻¹ * r * ra = r := by
              have := hRcomm ra hra r hr'
              calc ra⁻¹ * r * ra = ra⁻¹ * (r * ra) := by group
                _ = ra⁻¹ * (ra * r) := by rw [this]
                _ = r := by group
            have e1 : a⁻¹ * r * a = (ra⁻¹ * ⁅da⁻¹, r⁆ * ra) * r := by
              calc a⁻¹ * r * a = ra⁻¹ * (da⁻¹ * r * da) * ra := by rw [haeq]; group
                _ = ra⁻¹ * (⁅da⁻¹, r⁆ * r) * ra := by simp only [commutatorElement_def]; group
                _ = (ra⁻¹ * ⁅da⁻¹, r⁆ * ra) * (ra⁻¹ * r * ra) := by group
                _ = (ra⁻¹ * ⁅da⁻¹, r⁆ * ra) * r := by rw [hra']
            have hc' : ra⁻¹ * ⁅da⁻¹, r⁆ * ra ∈ N.P := by
              have := conj_mem_P N ((N.T : Subgroup (MulAut K)).inv_mem (hRT hra)) hc
              simpa using this
            show (MulAut.conj a⁻¹) r ∈ N.P ⊔ Rm
            rw [MulAut.conj_apply, inv_inv, e1]
            exact mul_mem_sup hc' hr
        have := hle hp
        simpa [MulAut.conj_apply] using this
  have hinv : ∀ x ∈ M, orderOf x = 2 → fieldProj e x ≠ 1 →
      ∃ p ∈ N.P, ∃ r ∈ Rm, orderOf r = 2 ∧ x = p * r := by
    intro x hxM hx2 hxf
    obtain ⟨d, hd, r, hr, hxeq⟩ := hdec x hxM
    have hxx : x * x = 1 := l510_mul_self_of_orderOf_two hx2
    have hfp : fieldProj e' x = fieldProj e' r := by
      rw [hxeq, map_mul, (mem_innDiagSub_iff e' d).1 (hPtd hd), one_mul]
    have hr1 : r ≠ 1 := by
      intro h1
      apply hxf
      rw [← fieldProj_indep e e' x, hfp, h1, map_one]
    have hrr : r * r = 1 := by
      have hc : ⁅r, d⁆ ∈ N.P := hcommP r hr d hd
      have e1 : x * x = (d * ⁅r, d⁆ * d) * (r * r) := by
        rw [hxeq]
        simp only [commutatorElement_def]
        group
      have e2 : r * r = (d * ⁅r, d⁆ * d)⁻¹ := by
        rw [e1] at hxx
        exact eq_inv_of_mul_eq_one_right hxx
      have hmem : r * r ∈ N.Pt := by
        rw [e2]
        exact N.Pt.inv_mem (N.Pt.mul_mem (N.Pt.mul_mem hd (hPPt hc)) hd)
      have : r * r ∈ N.Pt ⊓ N.R := ⟨hmem, N.R.mul_mem hr hr⟩
      rw [hPtR] at this
      exact this
    have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hrr) hr1
    have hxT : x ∈ (N.T : Subgroup (MulAut K)) := hMT' hxM
    rcases ivk_1_2i_c F h K e' N r hr hr2 x hxT hx2 with hxP | ⟨hxPt, -⟩ | ⟨p, hp, hxp⟩
    · exfalso
      apply hxf
      rw [← fieldProj_indep e e' x]
      exact (mem_innDiagSub_iff e' x).1 (hPtd (hPPt hxP))
    · exfalso
      apply hxf
      rw [← fieldProj_indep e e' x]
      exact (mem_innDiagSub_iff e' x).1 (hPtd hxPt)
    · refine ⟨p, hp, r, ⟨?_, hr⟩, hr2, hxp⟩
      have : r = p⁻¹ * x := by rw [hxp]; group
      rw [this]
      exact M.mul_mem (M.inv_mem (hPM hp)) hxM
  refine ⟨e', Rm, hRmM, hRmR.trans hRF, ?_, by rw [hDP]; exact hindex, ?_⟩
  · rw [hDP]
    apply le_bot_iff.1
    calc N.P ⊓ Rm ≤ N.Pt ⊓ N.R := inf_le_inf hPPt hRmR
      _ = ⊥ := hPtR
  · intro x₀ hx₀M hx₀2 hx₀f
    obtain ⟨p₀, hp₀, r₁, hr₁, hr₁2, hx₀eq⟩ := hinv x₀ hx₀M hx₀2 hx₀f
    refine ⟨r₁, hr₁, hr₁2, ?_⟩
    intro x hxM hx2 hxf
    obtain ⟨p, hp, r, hr, hr2, hxeq⟩ := hinv x hxM hx2 hxf
    have hr1 : r ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hr2; omega
    have hr₁1 : r₁ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hr₁2; omega
    have hrr : r = r₁ :=
      R_unique_involution N (hRmR hr) (hRmR hr₁) hr1 hr₁1 (l510_mul_self_of_orderOf_two hr2)
        (l510_mul_self_of_orderOf_two hr₁2)
    exact ⟨p, by rw [hDP]; exact hp, by rw [hxeq, hrr]⟩

end L2Level

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510
