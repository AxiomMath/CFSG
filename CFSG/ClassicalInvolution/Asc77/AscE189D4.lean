module

public import CFSG.ClassicalInvolution.Asc77.AscE189D4Sign
public import CFSG.ClassicalInvolution.Asc77.AscE189OrthMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem e189_orth_projective (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) (𝓕 : Set (Subgroup (spinGroup Q)))
    (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R) (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕)
    (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q)
    {N : Subgroup (spinGroup Q)} {F₁ : Subgroup (spinGroup Q)} (hF₁ : F₁ ∈ 𝓕)
    {z₁ : spinGroup Q} (hz₁ : IsUniqueInvolution F₁ z₁) {g : spinGroup Q}
    (h1 : ⁅z₁, g * z₁ * g⁻¹⁆ ∈ N)
    (h3 : conjSub (g * z₁ * g⁻¹) F₁ ≠ F₁)
    (hB1 : spinAction Q z₁ * spinAction Q (g * z₁ * g⁻¹) * spinAction Q z₁ =
      LinearEquiv.neg K * spinAction Q (g * z₁ * g⁻¹)) :
    ∃ x : spinGroup Q, ∃ M₂ ∈ 𝓕, M₂ ≠ conjSub x F₁ ∧ Commutes (conjSub x F₁) M₂ ∧
      (∃ y, M₂ = conjSub y F₁) ∧
      ∃ z₂, IsUniqueInvolution M₂ z₂ ∧ (x * z₁ * x⁻¹)⁻¹ * z₂ ∈ N ∧
        ∀ w ∈ conjSub x F₁ ⊔ M₂, ⁅w, z₁ * (g * z₁ * g⁻¹)⁆ ∈ N := by
  set π := spinAction Q with hπ
  set t₁ : spinGroup Q := g * z₁ * g⁻¹ with ht₁
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hker : π.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  obtain ⟨i₁', fr₁, hL₁, hi₁'⟩ := hcorr F₁ hF₁
  have hπz₁ : π z₁ = fr₁.La (-1) :=
    spinAction_involution_eq hodd hL₁ hz₁ (spinAction_ne_one_of_moved hz₁ h3)
  have hi₂ : π t₁ * π t₁ = 1 := by rw [← map_mul, (hz₁.conj g).sq, map_one]
  set bar : V ≃ₗ[K] V := π z₁ * π t₁ with hbar
  have hbarO : bar ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.mul_mem _ (spinAction_mem_orthogonalGroup z₁) (spinAction_mem_orthogonalGroup t₁)
  have hbar2 : ∀ v, bar (bar v) = -v := by
    intro v
    have e : bar * bar = LinearEquiv.neg K := by
      calc bar * bar = π z₁ * π t₁ * (π z₁ * π t₁) := rfl
        _ = (π z₁ * π t₁ * π z₁) * π t₁ := by group
        _ = (LinearEquiv.neg K * π t₁) * π t₁ := by rw [hB1]
        _ = LinearEquiv.neg K * (π t₁ * π t₁) := by group
        _ = LinearEquiv.neg K := by rw [hi₂, mul_one]
    have := LinearEquiv.congr_fun e v
    simpa using this
  have hmap : ∀ x ∈ fr₁.span, bar x ∈ fr₁.perp := by
    intro x hx
    have hx' : π z₁ x = -x := by
      rw [hπz₁]
      exact (Frame.mem_span_iff_inv fr₁ h2).mp hx
    have e := LinearEquiv.congr_fun hB1 x
    simp only [LinearEquiv.mul_apply, hx', map_neg, LinearEquiv.neg_apply] at e
    have e' : π z₁ (π t₁ x) = π t₁ x := neg_injective e
    rw [Frame.mem_perp_iff_fix fr₁ h2, ← hπz₁]
    show π z₁ (π z₁ (π t₁ x)) = π z₁ (π t₁ x)
    rw [e']
    exact e'
  have hCx : CxStr fr₁ bar :=
    ⟨hbarO, hbar2, fun X Y => by
      rw [polar_comm]
      exact (Frame.mem_perp_iff_forall_incl fr₁).mp (hmap (fr₁.incl Y) ⟨Y, rfl⟩) X⟩
  set frP : Frame Q := diagFrame hCx h2 1 (by norm_num) with hfrP
  set frM : Frame Q := diagFrame hCx h2 (-1) (by norm_num) with hfrM
  have hD : DiagData frP frM bar :=
    ⟨hbarO, diagFrame_orth hCx h2, fun Y => diagFrame_bar_incl hCx h2 _ Y,
      fun Y => diagFrame_bar_incl hCx h2 _ Y⟩
  have hJ : (-cxJ : Matrix (Fin 2) (Fin 2) K) * cxJ = 1 := by
    rw [neg_mul, cxJ_mul_cxJ, neg_neg]
  have hcomm_a : ∀ A : SL(2, K), bar * frP.La A = frP.La A * bar ∧
      bar * frM.La A = frM.La A * bar := fun A =>
    ⟨commute_La_of_incl_mul hbarO hJ hD.bar₀ A, commute_La_of_incl_mul hbarO hJ hD.bar₁ A⟩
  have hperp4 : 2 ≤ Module.finrank K fr₁.perp := by
    have := finrank_perp_add_four fr₁
    omega
  obtain ⟨y₀, hy₀⟩ := exists_spin_conj hodd hQ fr₁ frP hperp4
  obtain ⟨y₁, hy₁⟩ := exists_spin_conj hodd hQ fr₁ frM hperp4
  have hM₁mem : conjSub y₀ F₁ ∈ 𝓕 := hconj F₁ hF₁ y₀
  have hM₂mem : conjSub y₁ F₁ ∈ 𝓕 := hconj F₁ hF₁ y₁
  have hM₁perf : ⁅conjSub y₀ F₁, conjSub y₀ F₁⁆ = conjSub y₀ F₁ := hperf _ hM₁mem
  have hM₂perf : ⁅conjSub y₁ F₁, conjSub y₁ F₁⁆ = conjSub y₁ F₁ := hperf _ hM₂mem
  have hM₁img : (conjSub y₀ F₁).map π = frP.La.range := by
    have h6 : (conjSub y₀ F₁).map π = (F₁.map π).map (MulAut.conj (π y₀)).toMonoidHom :=
      map_conj_map π y₀ F₁
    rw [h6, hL₁, ← La_range_eq_map_conj hy₀]
  have hM₂img : (conjSub y₁ F₁).map π = frM.La.range := by
    have h6 : (conjSub y₁ F₁).map π = (F₁.map π).map (MulAut.conj (π y₁)).toMonoidHom :=
      map_conj_map π y₁ F₁
    rw [h6, hL₁, ← La_range_eq_map_conj hy₁]
  set zP : spinGroup Q := y₀ * z₁ * y₀⁻¹ with hzP
  set zM : spinGroup Q := y₁ * z₁ * y₁⁻¹ with hzM
  have hzPu : IsUniqueInvolution (conjSub y₀ F₁) zP := hz₁.conj y₀
  have hzMu : IsUniqueInvolution (conjSub y₁ F₁) zM := hz₁.conj y₁
  have hπzP : π zP = frP.La (-1) := by
    rw [hzP, map_mul, map_mul, map_inv, hπz₁, ← hy₀ (-1)]
  have hπzM : π zM = frM.La (-1) := by
    rw [hzM, map_mul, map_mul, map_inv, hπz₁, ← hy₁ (-1)]
  have hPperf : Group.IsPerfect ↥(conjSub y₀ F₁ ⊔ conjSub y₁ F₁) := by
    apply isPerfect_of_le_commutator
    exact sup_le (hM₁perf.ge.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
      (hM₂perf.ge.trans (Subgroup.commutator_mono le_sup_right le_sup_right))
  have hcomm12 : Commutes (conjSub y₀ F₁) (conjSub y₁ F₁) := by
    refine RouteD.commutes_of_commutes_map π hker
      (isPerfect_of_le_commutator hM₁perf.ge) ?_
    rw [hM₁img, hM₂img]
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact Frame.La_comm_of_orth hD.orth A B
  set a : spinGroup Q := z₁ * t₁ with ha
  have hπa : π a = bar := map_mul π z₁ t₁
  have hPcomm : Commutes ((conjSub y₀ F₁ ⊔ conjSub y₁ F₁).map π)
      ((Subgroup.zpowers a).map π) := by
    rw [Subgroup.map_sup, hM₁img, hM₂img, MonoidHom.map_zpowers, hπa]
    have hle : frP.La.range ⊔ frM.La.range ≤
        Subgroup.centralizer ((Subgroup.zpowers bar : Subgroup (V ≃ₗ[K] V)) : Set _) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hC : Commute bar (frP.La A) := (hcomm_a A).1
        exact (hC.zpow_left k).eq
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hC : Commute bar (frM.La A) := (hcomm_a A).2
        exact (hC.zpow_left k).eq
    intro u hu v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hle hu)) v hv).symm
  have hPc := RouteD.commutes_of_commutes_map π hker hPperf hPcomm
  have hac : ∀ w ∈ conjSub y₀ F₁ ⊔ conjSub y₁ F₁, w * a = a * w := fun w hw =>
    hPc w hw a (Subgroup.mem_zpowers a)
  have hsign : a * a * (zP * zM) = 1 :=
    sign_relation hodd hQ hdim hD hM₁img hM₂img hzPu hzMu hπzP hπzM hcomm12 hπa
      (fun w hw => hac w (Subgroup.mem_sup_left hw)) (fun w hw => hac w (Subgroup.mem_sup_right hw))
  have hzinvP : zP⁻¹ = zP := inv_eq_of_mul_eq_one_right hzPu.sq
  have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁.sq
  have ht₁sq : t₁ * t₁ = 1 := (hz₁.conj g).sq
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁sq
  have haa : a * a = ⁅z₁, t₁⁆ := by
    rw [commutatorElement_def, hz₁inv, ht₁inv, ha]
    group
  have haaN : a * a ∈ N := haa ▸ h1
  have hzz : zP * zM = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right hsign
  have hne : conjSub y₁ F₁ ≠ conjSub y₀ F₁ := by
    intro h
    have hzeq : zM = zP := hzMu.eq (h ▸ hzPu)
    rw [hzeq, hzPu.sq, mul_one] at hsign
    have h0 : (π a) * (π a) = 1 := by rw [← map_mul, hsign, map_one]
    rw [hπa] at h0
    have hbb : bar * bar = LinearEquiv.neg K := by
      ext v
      simp [LinearEquiv.mul_apply, hbar2 v]
    rw [hbb] at h0
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    have := LinearEquiv.congr_fun h0 v₀
    have h' : (2 : K) • v₀ = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← show -v₀ = v₀ by simpa using this]
      exact neg_add_cancel v₀
    exact hv₀ ((smul_eq_zero.mp h').resolve_left h2)
  refine ⟨y₀, conjSub y₁ F₁, hM₂mem, hne, hcomm12, ⟨y₁, rfl⟩, zM, hzMu, ?_, ?_⟩
  · rw [hzinvP]
    show zP * zM ∈ N
    rw [hzz]
    exact N.inv_mem haaN
  · intro w hw
    have : ⁅w, z₁ * t₁⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hac w hw)
    rw [this]
    exact N.one_mem

end CFSG.ClassicalInvolution.Asc77
