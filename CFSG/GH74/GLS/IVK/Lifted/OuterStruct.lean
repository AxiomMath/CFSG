module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GorensteinWalter CFSG.GH74.GLS.IVK
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped commutatorElement

section Indep

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem fieldProj_indep (e e' : K ≃* L2 F) (x : MulAut K) : fieldProj e' x = fieldProj e x := by
  have : IsCyclic (F ≃+* F) := ringAut_isCyclic F
  have hcomm : ∀ a b : F ≃+* F, a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := F ≃+* F)).is_comm.comm a b
  let β : MulAut (PSL2 F) := (toPSL e').symm.trans (toPSL e)
  have h1 : MulAut.congr (toPSL e) x = β * MulAut.congr (toPSL e') x * β⁻¹ := by
    ext y
    simp [β, MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_apply]
  have h2 : thetaAut e x = (semilinearEquivAut F).symm β * thetaAut e' x *
      ((semilinearEquivAut F).symm β)⁻¹ := by
    show (semilinearEquivAut F).symm (MulAut.congr (toPSL e) x) = _
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  rw [fieldProj_apply, fieldProj_apply, h2]
  set γ : PGammaL2 F := (semilinearEquivAut F).symm β with hγ
  show SemidirectProduct.rightHom (thetaAut e' x) =
    SemidirectProduct.rightHom (γ * thetaAut e' x * γ⁻¹)
  rw [map_mul, map_mul, map_inv, hcomm (SemidirectProduct.rightHom γ), mul_inv_cancel_right]

end Indep

section Index

theorem relIndex_le_two_of_cover {X : Type} [Group X] {P M : Subgroup X} {a : X} (ha : a ∈ M)
    (hcov : ∀ b ∈ M, b ∈ P ∨ ∃ p ∈ P, b = p * a) (hN : ∀ p ∈ P, a⁻¹ * p * a ∈ P) :
    P.relIndex M ≤ 2 := by
  let π : Fin 2 → (↥M ⧸ P.subgroupOf M) := fun i =>
    if i = 0 then QuotientGroup.mk 1 else QuotientGroup.mk ⟨a, ha⟩
  have hsurj : Function.Surjective π := by
    intro q
    induction q using QuotientGroup.induction_on with | H b => ?_
    rcases hcov b b.2 with h | ⟨p, hp, hbp⟩
    · refine ⟨0, ?_⟩
      show (QuotientGroup.mk 1 : ↥M ⧸ P.subgroupOf M) = QuotientGroup.mk b
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h
    · refine ⟨1, ?_⟩
      show (QuotientGroup.mk ⟨a, ha⟩ : ↥M ⧸ P.subgroupOf M) = QuotientGroup.mk b
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show a⁻¹ * (b : X) ∈ P
      rw [hbp]
      have : a⁻¹ * (p * a) = a⁻¹ * p * a := by group
      rw [this]
      exact hN p hp
  unfold Subgroup.relIndex Subgroup.index
  calc Nat.card (↥M ⧸ P.subgroupOf M) ≤ Nat.card (Fin 2) := Nat.card_le_card_of_surjective π hsurj
    _ = 2 := by simp

end Index

section Structure

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem outer_structure
    (h : L2Field F) (e : K ≃* L2 F) (M : Subgroup (MulAut K))
    (hM : IsPGroup 2 ↥M) (P₀ : Sylow 2 K)
    (hP₀ : (P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤ M)
    (hf : ∀ φ ∈ M, orderOf φ = 2 → fieldProj e φ = 1) :
    ((P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K)).relIndex M ≤ 2 ∧
      ((∃ n, IVK.IsDihedralTwoGroup ↥M n) ∨ ∃ n, IVK.IsSemidihedralTwoGroup ↥M n) := by
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
  have hPT : N.P ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hPinn : N.P ≤ innAut K := inf_le_right
  have hRF : N.R ≤ fieldAutSub e' := inf_le_right
  have hRT : N.R ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hPtT : N.Pt ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hMR : ∀ r ∈ M, r ∈ N.R → r = 1 := by
    intro r hrM hrR
    by_contra hr1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hM) ⟨r, hrM⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hr1 (orderOf_eq_one_iff.1 (by simpa using hk))
    set r₀ : MulAut K := r ^ (2 ^ (k - 1)) with hr₀
    have hr₀2 : r₀ * r₀ = 1 := by
      rw [hr₀, ← pow_add]
      have : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      rw [this, ← hk]
      exact pow_orderOf_eq_one r
    have hr₀1 : r₀ ≠ 1 := by
      intro h1
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hk] at h2
      have h3 := Nat.le_of_dvd (by positivity) h2
      have h4 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hr₀ord : orderOf r₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr₀2) hr₀1
    have hr₀M : r₀ ∈ M := M.pow_mem hrM _
    have hr₀F : r₀ ∈ fieldAutSub e' := (fieldAutSub e').pow_mem (hRF hrR) _
    have hfp : fieldProj e' r₀ = 1 := (fieldProj_indep e e' r₀).trans (hf r₀ hr₀M hr₀ord)
    obtain ⟨σ, hσ⟩ := hr₀F
    have hσ1 : σ = 1 := by
      have := fieldProj_fieldAutHom e' σ
      rw [hσ, hfp] at this
      exact this.symm
    apply hr₀1
    rw [← hσ, hσ1, map_one]
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
  have hPtM : ∀ x ∈ M, x ∈ N.Pt → x ∉ N.P → N.Pt ≤ M := by
    intro x hxM hxPt hxP y hy
    by_cases hyP : y ∈ N.P
    · exact hPM hyP
    · have h1 := hPtCov y hy x hxPt hyP hxP
      have : y = (y * x⁻¹) * x := by group
      rw [this]
      exact M.mul_mem (hPM h1) hxM
  have hsq : ∀ m ∈ M, ∃ d ∈ N.Pt, ∃ r ∈ N.R, m = d * r ∧ r * r = 1 := by
    intro m hm
    obtain ⟨d, hd, r, hr, hmdr⟩ := T_decomp N m (hMT' hm)
    refine ⟨d, hd, r, hr, hmdr, ?_⟩
    have hdIn : d ∈ innAut K ⊔ zpowers N.t := by
      have h1 : d ∈ N.P ⊔ zpowers N.t := by rw [P_sup_zpowers_eq_Pt e' h N]; exact hd
      exact (sup_le_sup_right hPinn _) h1
    have hc : ⁅r, d⁆ ∈ innAut K := (ivk_1_2a_struct F h K e' N).2.2.2 r (hRF hr) d hdIn
    have hrT : r ∈ (N.T : Subgroup (MulAut K)) := hRT hr
    have hdT : d ∈ (N.T : Subgroup (MulAut K)) := hPtT hd
    have hcT : ⁅r, d⁆ ∈ (N.T : Subgroup (MulAut K)) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hrT hdT) (inv_mem hrT)) (inv_mem hdT)
    have hcP : ⁅r, d⁆ ∈ N.P := ⟨hcT, hc⟩
    have hdcP : d * ⁅r, d⁆ * d⁻¹ ∈ N.P := conj_mem_P N hdT hcP
    have hdd : d * d ∈ N.P := by
      have : (N.P.subgroupOf N.Pt).Normal := Subgroup.normal_of_index_eq_two hidx
      have h1 := Subgroup.pow_index_mem (N.P.subgroupOf N.Pt) (⟨d, hd⟩ : N.Pt)
      rw [hidx] at h1
      have h2 := Subgroup.mem_subgroupOf.1 h1
      simpa [pow_two] using h2
    have hp : (d * ⁅r, d⁆ * d⁻¹) * (d * d) ∈ N.P := N.P.mul_mem hdcP hdd
    have hmm : m * m = ((d * ⁅r, d⁆ * d⁻¹) * (d * d)) * (r * r) := by
      rw [hmdr]
      simp only [commutatorElement_def]
      group
    have hrr : r * r = ((d * ⁅r, d⁆ * d⁻¹) * (d * d))⁻¹ * (m * m) := by
      rw [hmm]; group
    have hrrM : r * r ∈ M := by
      rw [hrr]
      exact M.mul_mem (M.inv_mem (hPM hp)) (M.mul_mem hm hm)
    exact hMR (r * r) hrrM (N.R.mul_mem hr hr)
  have hD2 : D.relIndex M ≤ 2 ∧
      ((∃ n, IVK.IsDihedralTwoGroup ↥M n) ∨ ∃ n, IVK.IsSemidihedralTwoGroup ↥M n) := by
    rw [hDP]
    by_cases hall : ∀ m ∈ M, fieldProj e' m = 1
    ·
      have hMPt : M ≤ N.Pt := fun m hm => ⟨hMT' hm, (mem_innDiagSub_iff e' m).2 (hall m hm)⟩
      have hcase : M = N.P ∨ M = N.Pt := by
        by_cases hMP : M ≤ N.P
        · exact Or.inl (le_antisymm hMP hPM)
        · right
          have hex : ∃ m ∈ M, m ∉ N.P := by
            by_contra hcon
            push Not at hcon
            exact hMP fun m hm => hcon m hm
          obtain ⟨m, hmM, hmP⟩ := hex
          exact le_antisymm hMPt (hPtM m hmM (hMPt hmM) hmP)
      rcases hcase with hM1 | hM1
      · rw [hM1]
        refine ⟨by simp, Or.inl ?_⟩
        exact ivk_1_2c F h K e' N
      · rw [hM1]
        refine ⟨le_of_eq hidx, Or.inl ?_⟩
        exact (ivk_1_2d F h K e' N).2.2.2
    · push Not at hall
      obtain ⟨m₀, hm₀M, hm₀⟩ := hall
      obtain ⟨d₀, hd₀, f, hfR, hm₀eq, hff⟩ := hsq m₀ hm₀M
      have hproj : fieldProj e' m₀ = fieldProj e' f := by
        rw [hm₀eq, map_mul, (mem_innDiagSub_iff e' d₀).1 hd₀.2, one_mul]
      have hf1 : f ≠ 1 := by
        intro h1
        apply hm₀
        rw [hproj, h1, map_one]
      have hf2 : orderOf f = 2 := orderOf_eq_prime (by rw [pow_two]; exact hff) hf1
      have hfT : f ∈ (N.T : Subgroup (MulAut K)) := hRT hfR
      have hf0 : f = d₀⁻¹ * m₀ := by rw [hm₀eq]; group
      have hMPt' : ∀ x ∈ M, x ∈ N.Pt → x ∈ N.P := by
        intro x hxM hxPt
        by_contra hxP
        have hPtM' := hPtM x hxM hxPt hxP
        have hfM : f ∈ M := by
          rw [hf0]
          exact M.mul_mem (M.inv_mem (hPtM' hd₀)) hm₀M
        exact hf1 (hMR f hfM hfR)
      have hd₀P : d₀ ∉ N.P := by
        intro hdP
        have hfM : f ∈ M := by
          rw [hf0]
          exact M.mul_mem (M.inv_mem (hPM hdP)) hm₀M
        exact hf1 (hMR f hfM hfR)
      have htPt : N.t ∈ N.Pt := ⟨N.t_mem, N.t_mem_diag⟩
      have htP : N.t ∉ N.P := fun ht => N.t_not_mem_inn (hPinn ht)
      have hpP : d₀ * N.t⁻¹ ∈ N.P := hPtCov d₀ hd₀ N.t htPt hd₀P htP
      have htt : N.t * N.t = 1 := by
        have := pow_orderOf_eq_one N.t
        rwa [N.t_order, pow_two] at this
      have htinv : N.t⁻¹ = N.t := inv_eq_of_mul_eq_one_right htt
      have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
      have htfM : N.t * f ∈ M := by
        have h1 : N.t * f = (d₀ * N.t⁻¹)⁻¹ * m₀ := by
          rw [hm₀eq]
          group
        rw [h1]
        exact M.mul_mem (M.inv_mem (hPM hpP)) hm₀M
      have hftM : f * N.t ∈ M := by
        have : f * N.t = (N.t * f)⁻¹ := by
          rw [mul_inv_rev, htinv, hfinv]
        rw [this]
        exact M.inv_mem htfM
      have hu_inv : (f * N.t)⁻¹ = N.t * f := by rw [mul_inv_rev, htinv, hfinv]
      have hm₀' : m₀ = (d₀ * N.t⁻¹) * (f * N.t)⁻¹ := by
        rw [hu_inv, hm₀eq]
        group
      have hMeq : M = N.P ⊔ zpowers (f * N.t) := by
        apply le_antisymm
        · intro m hm
          obtain ⟨d, hd, r, hr, hmdr, hrr⟩ := hsq m hm
          by_cases hr1 : r = 1
          · rw [hmdr, hr1, mul_one]
            have hdM : d ∈ M := by rw [← mul_one d, ← hr1, ← hmdr]; exact hm
            exact Subgroup.mem_sup_left (hMPt' d hdM hd)
          · have hrf : r = f := R_unique_involution N hr hfR hr1 hf1 hrr hff
            have h1 : m = (d * d₀⁻¹) * m₀ := by
              rw [hmdr, hrf, hm₀eq]
              group
            have hdd₀ : d * d₀⁻¹ ∈ N.P := by
              apply hMPt'
              · have hdM : d * f ∈ M := by rw [← hrf, ← hmdr]; exact hm
                have : d * d₀⁻¹ = (d * f) * m₀⁻¹ := by
                  rw [hm₀eq]; group
                rw [this]
                exact M.mul_mem hdM (M.inv_mem hm₀M)
              · exact N.Pt.mul_mem hd (N.Pt.inv_mem hd₀)
            rw [h1, hm₀']
            refine mul_mem (Subgroup.mem_sup_left hdd₀) (mul_mem (Subgroup.mem_sup_left hpP) ?_)
            exact inv_mem (Subgroup.mem_sup_right (mem_zpowers _))
        · exact sup_le hPM ((zpowers_le).2 hftM)
      have hcov : ∀ b ∈ M, b ∈ N.P ∨ ∃ p ∈ N.P, b = p * m₀ := by
        intro b hb
        obtain ⟨d, hd, r, hr, hbdr, hrr⟩ := hsq b hb
        by_cases hr1 : r = 1
        · left
          have hdM : d ∈ M := by rw [← mul_one d, ← hr1, ← hbdr]; exact hb
          rw [hbdr, hr1, mul_one]
          exact hMPt' d hdM hd
        · right
          have hrf : r = f := R_unique_involution N hr hfR hr1 hf1 hrr hff
          refine ⟨d * d₀⁻¹, ?_, ?_⟩
          · apply hMPt'
            · have hdM : d * f ∈ M := by rw [← hrf, ← hbdr]; exact hb
              have : d * d₀⁻¹ = (d * f) * m₀⁻¹ := by
                rw [hm₀eq]; group
              rw [this]
              exact M.mul_mem hdM (M.inv_mem hm₀M)
            · exact N.Pt.mul_mem hd (N.Pt.inv_mem hd₀)
          · rw [hbdr, hrf, hm₀eq]
            group
      have hm₀N : ∀ p ∈ N.P, m₀⁻¹ * p * m₀ ∈ N.P := by
        intro p hp
        have hm₀T : m₀ ∈ (N.T : Subgroup (MulAut K)) := hMT' hm₀M
        have := conj_mem_P N ((N.T : Subgroup (MulAut K)).inv_mem hm₀T) hp
        simpa using this
      refine ⟨relIndex_le_two_of_cover hm₀M hcov hm₀N, Or.inr ?_⟩
      rw [hMeq]
      exact ivk_1_2i_b F h K e' N f hfR hf2
  exact hD2

theorem dihedral_overgroup_field (h : L2Field F) (e : K ≃* L2 F) (M : Subgroup (MulAut K))
    (hM : IsPGroup 2 ↥M) (P₀ : Sylow 2 K)
    (hP₀ : (P₀ : Subgroup K).map (MulAut.conj : K →* MulAut K) ≤ M)
    (hdih : ∃ n, IVK.IsDihedralTwoGroup ↥M n) : ∀ φ ∈ M, fieldProj e φ = 1 := by
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
  have hdiag : ∀ φ ∈ N.Pt, fieldProj e φ = 1 := fun φ hφ =>
    (fieldProj_indep e e' φ).symm.trans ((mem_innDiagSub_iff e' φ).1 (Pt_le_innDiagSub N hφ))
  intro φ hφ
  rcases ivk_1_2j F h K e' N M hMT' hPM hdih with hM1 | hM1
  · exact hdiag φ (P_le_Pt N (hM1 ▸ hφ))
  · have hφ' : φ ∈ N.P ⊔ zpowers N.t := hM1 ▸ hφ
    rw [P_sup_zpowers_eq_Pt e' h N] at hφ'
    exact hdiag φ hφ'

end Structure

end CFSG.GH74.GLS.IVK.Lifted
