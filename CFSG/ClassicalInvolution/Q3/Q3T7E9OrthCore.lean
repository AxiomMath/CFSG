module

public import CFSG.ClassicalInvolution.Asc77.AscE189OrthMain
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.ClassicalInvolution.Asc77.AscE189D4Sign

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

section Kernel

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

open CliffordAlgebra in
theorem spinAction_ker_sq [Nontrivial V] (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) :
    ∀ x ∈ (spinAction Q).ker, x * x = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  intro x hx
  rcases (mem_ker_spinAction_iff Q hQnd x).mp hx with rfl | rfl
  · exact mul_one 1
  · exact spinGroup.negOne_mul_self Q hQnd.ne_zero

end Kernel

section Eq

variable {X Y : Type} [Group X] [Group Y]

theorem eq_of_map_eq_of_gen3_sq (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hk2 : ∀ x ∈ π.ker, x * x = 1) {A B : Subgroup X} (hA : Gen3 A) (hB : Gen3 B)
    (h : A.map π = B.map π) : A = B := by
  have key : ∀ {A B : Subgroup X}, Gen3 A → A.map π ≤ B.map π → A ≤ B := by
    intro A B hA hAB
    obtain ⟨S, hSA, hS3, hAS⟩ := hA
    refine hAS.trans ((Subgroup.closure_le _).2 fun s hs => ?_)
    obtain ⟨b, hb, hbs⟩ := hAB (Subgroup.mem_map_of_mem π (hSA hs))
    set c : X := b⁻¹ * s with hc
    have hcker : c ∈ π.ker := by
      rw [MonoidHom.mem_ker, hc, map_mul, map_inv, hbs, inv_mul_cancel]
    have hcc : ∀ y : X, y * c = c * y := fun y => Subgroup.mem_center_iff.mp (hker hcker) y
    have hsbc : s = b * c := by rw [hc]; group
    have hc2 := hk2 c hcker
    have hc3B : c ^ 3 ∈ B := by
      have h1 : b ^ 3 * c ^ 3 = 1 := by
        rw [← (Commute.mul_pow (show Commute b c from hcc b) 3), ← hsbc]
        exact hS3 s hs
      have : c ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact B.inv_mem (B.pow_mem hb 3)
    have hc3 : c ^ 3 = c := by
      calc c ^ 3 = (c * c) * c := by rw [pow_succ, pow_two]
        _ = c := by rw [hc2, one_mul]
    have hcB : c ∈ B := hc3 ▸ hc3B
    rw [hsbc]
    exact B.mul_mem hb hcB
  exact le_antisymm (key hA h.le) (key hB h.ge)

end Eq

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem e189_orth_commuting_three (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank K V)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hgen : ∀ R ∈ 𝓕, Gen3 R)
    (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕)
    (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q)
    {N : Subgroup (spinGroup Q)} {F₁ : Subgroup (spinGroup Q)} (hF₁ : F₁ ∈ 𝓕)
    {z₁ : spinGroup Q} (hz₁ : IsUniqueInvolution F₁ z₁) {g : spinGroup Q}
    (hN : N ≤ Subgroup.center (spinGroup Q)) (h1 : ⁅z₁, g * z₁ * g⁻¹⁆ ∈ N)
    (h3 : conjSub (g * z₁ * g⁻¹) F₁ ≠ F₁) (h4 : Commutes F₁ (conjSub (g * z₁ * g⁻¹) F₁))
    (hcom : spinAction Q z₁ * spinAction Q (g * z₁ * g⁻¹) =
      spinAction Q (g * z₁ * g⁻¹) * spinAction Q z₁) :
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
  have hk2 : ∀ x ∈ π.ker, x * x = 1 := spinAction_ker_sq h2 hQ
  have hk3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1 := fun x hx h3 =>
    eq_one_of_sq_eq_one_of_pow_three (hk2 x hx) h3
  obtain ⟨i₁', fr₁, hL₁, hi₁'⟩ := hcorr F₁ hF₁
  have hπz₁ : π z₁ = fr₁.La (-1) :=
    spinAction_involution_eq hodd hL₁ hz₁ (spinAction_ne_one_of_moved hz₁ h3)
  have hgO : π g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := spinAction_mem_orthogonalGroup g
  set fr₂ : Frame Q := fr₁.map hgO with hfr₂
  have hπt₁ : π t₁ = fr₂.La (-1) := by
    rw [hfr₂, Frame.map_La, ht₁, map_mul, map_mul, map_inv, hπz₁]
  have h₁' : IsFundamental Q fr₁.La.range (fr₁.La (-1)) := IsFundamental.of_frame fr₁
  have h₂' : IsFundamental Q fr₂.La.range (fr₂.La (-1)) := IsFundamental.of_frame fr₂
  have hcom' : fr₁.La (-1) * fr₂.La (-1) = fr₂.La (-1) * fr₁.La (-1) := by
    rw [← hπz₁, ← hπt₁]
    exact hcom
  have hgen₁ : Gen3 F₁ := hgen F₁ hF₁
  have hgen₂ : Gen3 (conjSub t₁ F₁) := hgen _ (hconj F₁ hF₁ t₁)
  have hnn : π t₁ ∉ Subgroup.normalizer (fr₁.La.range : Set (V ≃ₗ[K] V)) := by
    intro hn
    have h5 := conjSubgroup_eq_of_mem_normalizer hn
    apply h3
    refine eq_of_map_eq_of_gen3_sq π hker hk2 hgen₂ hgen₁ ?_
    have h6 : (conjSub t₁ F₁).map π = conjSubgroup (π t₁) (F₁.map π) := by
      rw [conjSubgroup_eq_map]
      exact map_conj_map π t₁ F₁
    rw [h6, hL₁, h5]
  have hodd' : Odd (Module.finrank K ↥(negSpace (π z₁) ⊓ negSpace (π t₁))) := by
    have hne : ¬ Even (Module.finrank K ↥(negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1)))) := by
      intro he
      exact hnn (by rw [hπt₁]; exact (mem_normalizer_iff_even hodd h₁' h₂' hcom').mpr he)
    rw [hπz₁, hπt₁]
    exact Nat.not_even_iff_odd.mp hne
  have ht₁sq : t₁ * t₁ = 1 := (hz₁.conj g).sq
  obtain ⟨fr₀, c, hc2, hfr₀⟩ := exists_frame_scalar_of_commuting hodd hQ hdim
    (i₁ := π z₁) (i₂ := π t₁) (spinAction_mem_orthogonalGroup z₁)
    (spinAction_mem_orthogonalGroup t₁) (by rw [← map_mul, hz₁.sq, map_one])
    (by rw [← map_mul, ht₁sq, map_one]) hcom
    (by rw [hπz₁]; exact finrank_negSpace_of_isFundamental hodd h₁')
    (by rw [hπt₁]; exact finrank_negSpace_of_isFundamental hodd h₂') hodd'
  have hperp : 2 ≤ Module.finrank K fr₁.perp := by
    have := finrank_perp_add_four fr₁
    omega
  obtain ⟨y, hy⟩ := exists_spin_conj hodd hQ fr₁ fr₀ hperp
  have hM₂mem : conjSub (y * t₁) F₁ ∈ 𝓕 := hconj F₁ hF₁ _
  have hM₂ne : conjSub (y * t₁) F₁ ≠ conjSub y F₁ := by
    intro h
    apply h3
    rw [conjSub_mul] at h
    have := congrArg (conjSub y⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hM₁gen : Gen3 (conjSub y F₁) := hgen _ (hconj F₁ hF₁ y)
  have hM₂gen : Gen3 (conjSub (y * t₁) F₁) := hgen _ hM₂mem
  have hM₁img : (conjSub y F₁).map π = fr₀.La.range := by
    have h6 : (conjSub y F₁).map π = (F₁.map π).map (MulAut.conj (π y)).toMonoidHom :=
      map_conj_map π y F₁
    rw [h6, hL₁, ← La_range_eq_map_conj hy]
  set z₂ : spinGroup Q := (y * t₁) * z₁ * (y * t₁)⁻¹ with hz₂def
  have hz₂ : IsUniqueInvolution (conjSub (y * t₁) F₁) z₂ := hz₁.conj (y * t₁)
  have hc3 : π t₁ * π z₁ * (π t₁)⁻¹ = π z₁ := by
    rw [← hcom]
    group
  have hπz₂ : π z₂ = fr₀.La (-1) := by
    have h6 : π z₂ = π y * (π t₁ * π z₁ * (π t₁)⁻¹) * (π y)⁻¹ := by
      rw [hz₂def]
      simp only [map_mul, map_inv]
      group
    rw [h6, hc3, hπz₁, ← hy (-1)]
  have hM₂img : (conjSub (y * t₁) F₁).map π = fr₀.swap.La.range := by
    obtain ⟨i', fr', hL', hi'⟩ := hcorr _ hM₂mem
    have hπz₂mem : π z₂ ∈ fr'.La.range := hL' ▸ Subgroup.mem_map_of_mem π hz₂.mem
    have hord : orderOf (π z₂) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, ← map_mul, hz₂.sq, map_one]
      · rw [hπz₂]
        exact (IsFundamental.of_frame fr₀).ne_one hodd
    have hπz₂' : π z₂ = fr'.La (-1) :=
      (IsFundamental.of_frame fr').eq_of_orderOf_eq_two hodd hπz₂mem hord
    have hinv : fr'.La (-1) = fr₀.La (-1) := hπz₂'.symm.trans hπz₂
    rcases Frame.La_range_eq_or_eq_swap h2 hinv with h | h
    · exfalso
      apply hM₂ne
      refine eq_of_map_eq_of_gen3_sq π hker hk2 hM₂gen hM₁gen ?_
      rw [hL', h, hM₁img]
    · rw [hL', h]
  set a : spinGroup Q := z₁ * t₁ with ha
  have hπa : π a = π z₁ * π t₁ := map_mul π z₁ t₁
  have hcomm_a : ∀ A : SL(2, K), π a * fr₀.La A = fr₀.La A * π a ∧
      π a * fr₀.swap.La A = fr₀.swap.La A * π a := by
    intro A
    refine commute_La_of_scalar_on_span h2 (spinAction_mem_orthogonalGroup a) hc2 (fun x hx => ?_) A
    rw [hπa, LinearEquiv.mul_apply]
    exact hfr₀ x hx
  have hcentM₁ : ∀ w ∈ conjSub y F₁, w * a = a * w := by
    refine commute_of_map_commute_of_gen3 π hker hk3 hM₁gen (b := a) (fun x hx => ?_)
    have hx' : π x ∈ fr₀.La.range := hM₁img ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨A, hA⟩ := hx'
    rw [← hA]
    exact (hcomm_a A).1.symm
  have hcentM₂ : ∀ w ∈ conjSub (y * t₁) F₁, w * a = a * w := by
    refine commute_of_map_commute_of_gen3 π hker hk3 hM₂gen (b := a) (fun x hx => ?_)
    have hx' : π x ∈ fr₀.swap.La.range := hM₂img ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨A, hA⟩ := hx'
    rw [← hA]
    exact (hcomm_a A).2.symm
  have hPc : ∀ w ∈ conjSub y F₁ ⊔ conjSub (y * t₁) F₁, w * a = a * w := by
    have hle : conjSub y F₁ ⊔ conjSub (y * t₁) F₁ ≤
        Subgroup.centralizer ({a} : Set (spinGroup Q)) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentM₁ w hw)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentM₂ w hw)
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hzinv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁.sq
  have hN₂ : (y * z₁ * y⁻¹)⁻¹ * z₂ ∈ N := by
    have e0 : z₁⁻¹ * t₁ * z₁ * t₁⁻¹ = ⁅z₁, t₁⁆ := by
      rw [commutatorElement_def, hzinv]
    have e1 : (y * z₁ * y⁻¹)⁻¹ * z₂ = y * (z₁⁻¹ * t₁ * z₁ * t₁⁻¹) * y⁻¹ := by
      rw [hz₂def]
      group
    rw [e0] at e1
    have e2 : y * ⁅z₁, t₁⁆ * y⁻¹ = ⁅z₁, t₁⁆ :=
      mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp (hN h1) y)
    rw [e1, e2]
    exact h1
  refine ⟨y, conjSub (y * t₁) F₁, hM₂mem, hM₂ne, ?_, ⟨y * t₁, rfl⟩, z₂, hz₂, hN₂, ?_⟩
  · rw [conjSub_mul]
    exact h4.conjSub y
  · intro w hw
    have hwa : w * a = a * w := hPc w hw
    have : ⁅w, z₁ * t₁⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hwa
    rw [this]
    exact N.one_mem

theorem e189AtFam_spin_of_ne8_three (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank K V)
    (hdim8 : Module.finrank K V ≠ 8) (hZ : CenterScalar Q) (𝓕 : Set (Subgroup (spinGroup Q)))
    (hgen : ∀ R ∈ 𝓕, Gen3 R) (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕)
    (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q) :
    E189AtFam (spinGroup Q) 𝓕 := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 _ h3 h4 _
  right
  exact e189_orth_commuting_three hodd hQ hdim 𝓕 hgen hconj hcorr hF₁ hz₁ hN h1 h3 h4
    (e189_commute_images hodd hQ hdim hdim8 hZ 𝓕 hcorr hN hF₁ hz₁ h1 h3)

theorem e189AtFam_spin_of_noOrth_three (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank K V) (hZ : CenterScalar Q)
    (hNoOrth : ∀ F₀ F₁ : Frame Q, F₁.span ≤ F₀.perp → False)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hgen : ∀ R ∈ 𝓕, Gen3 R)
    (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕)
    (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q) :
    E189AtFam (spinGroup Q) 𝓕 := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 _ h3 h4 _
  right
  rcases e189_commute_or_proj hodd hQ hdim hZ 𝓕 hcorr hN hF₁ hz₁ h1 h3 with hc | ⟨-, hB1⟩
  · exact e189_orth_commuting_three hodd hQ hdim 𝓕 hgen hconj hcorr hF₁ hz₁ hN h1 h3 h4 hc
  · exfalso
    have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
    obtain ⟨i₁', fr₁, hL₁, hi₁'⟩ := hcorr F₁ hF₁
    have hπz₁ : spinAction Q z₁ = fr₁.La (-1) :=
      spinAction_involution_eq hodd hL₁ hz₁ (spinAction_ne_one_of_moved hz₁ h3)
    have hO := spinAction_mem_orthogonalGroup (Q := Q) (g * z₁ * g⁻¹)
    refine hNoOrth fr₁ (fr₁.map hO) ?_
    rintro _ ⟨X, rfl⟩
    rw [Frame.map_incl, Frame.mem_perp_iff_fix fr₁ h2, ← hπz₁]
    have hx : fr₁.incl X ∈ fr₁.span := ⟨X, rfl⟩
    have e1 : spinAction Q z₁ (fr₁.incl X) = -(fr₁.incl X) := by
      rw [hπz₁]
      exact (Frame.mem_span_iff_inv fr₁ h2).mp hx
    have e2 := LinearEquiv.congr_fun hB1 (fr₁.incl X)
    simp only [LinearEquiv.mul_apply, e1, map_neg, LinearEquiv.neg_apply] at e2
    exact neg_injective e2

theorem e189_orth_projective_three (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 8)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hgen : ∀ R ∈ 𝓕, Gen3 R)
    (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕)
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
  have hk2 : ∀ x ∈ π.ker, x * x = 1 := spinAction_ker_sq h2 hQ
  have hk3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1 := fun x hx h3 =>
    eq_one_of_sq_eq_one_of_pow_three (hk2 x hx) h3
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
  have hM₁gen : Gen3 (conjSub y₀ F₁) := hgen _ hM₁mem
  have hM₂gen : Gen3 (conjSub y₁ F₁) := hgen _ hM₂mem
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
  have hcomm12 : Commutes (conjSub y₀ F₁) (conjSub y₁ F₁) := by
    intro x hx b hb
    refine commute_of_map_commute_of_gen3 π hker hk3 hM₁gen (b := b) (fun a' ha' => ?_) x hx
    have hA' : π a' ∈ frP.La.range := hM₁img ▸ Subgroup.mem_map_of_mem π ha'
    have hB' : π b ∈ frM.La.range := hM₂img ▸ Subgroup.mem_map_of_mem π hb
    obtain ⟨A, hA⟩ := hA'
    obtain ⟨B, hB⟩ := hB'
    rw [← hA, ← hB]
    exact Frame.La_comm_of_orth hD.orth A B
  set a : spinGroup Q := z₁ * t₁ with ha
  have hπa : π a = bar := map_mul π z₁ t₁
  have hcentP : ∀ w ∈ conjSub y₀ F₁, w * a = a * w := by
    refine commute_of_map_commute_of_gen3 π hker hk3 hM₁gen (b := a) (fun x hx => ?_)
    have hx' : π x ∈ frP.La.range := hM₁img ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨A, hA⟩ := hx'
    rw [← hA, hπa]
    exact (hcomm_a A).1.symm
  have hcentM : ∀ w ∈ conjSub y₁ F₁, w * a = a * w := by
    refine commute_of_map_commute_of_gen3 π hker hk3 hM₂gen (b := a) (fun x hx => ?_)
    have hx' : π x ∈ frM.La.range := hM₂img ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨A, hA⟩ := hx'
    rw [← hA, hπa]
    exact (hcomm_a A).2.symm
  have hac : ∀ w ∈ conjSub y₀ F₁ ⊔ conjSub y₁ F₁, w * a = a * w := by
    have hle : conjSub y₀ F₁ ⊔ conjSub y₁ F₁ ≤ Subgroup.centralizer ({a} : Set (spinGroup Q)) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentP w hw)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentM w hw)
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
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

theorem e189AtFam_spin_of_eight_three (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 8) (hZ : CenterScalar Q)
    (𝓕 : Set (Subgroup (spinGroup Q))) (hgen : ∀ R ∈ 𝓕, Gen3 R)
    (hconj : ∀ R ∈ 𝓕, ∀ g, conjSub g R ∈ 𝓕)
    (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q) :
    E189AtFam (spinGroup Q) 𝓕 := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 _ h3 h4 _
  right
  rcases e189_commute_or_proj hodd hQ (by omega) hZ 𝓕 hcorr hN hF₁ hz₁ h1 h3 with hc | ⟨-, hB1⟩
  · exact e189_orth_commuting_three hodd hQ (by omega) 𝓕 hgen hconj hcorr hF₁ hz₁ hN h1 h3 h4 hc
  · exact e189_orth_projective_three hodd hQ hdim 𝓕 hgen hconj hcorr hF₁ hz₁ h1 h3 hB1

end CFSG.ClassicalInvolution.Q3.Q3T7E9
