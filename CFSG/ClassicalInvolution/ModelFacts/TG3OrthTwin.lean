module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.ModelFacts.TG3Lift
public import CFSG.ClassicalInvolution.ModelFacts.CF3A
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthCore

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.Transfer
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

section Basic

variable {K : Type*} [Group K] {E : Type*} [Group E]

theorem le_of_map_le_of_gen3 (θ : K →* E) (hker : θ.ker ≤ Subgroup.center K)
    (hker2 : ∀ x ∈ θ.ker, x * x = 1) {R R' : Subgroup K} (hR : Gen3 R)
    (h : R.map θ ≤ R'.map θ) : R ≤ R' := by
  obtain ⟨S, hSR, hS3, hRS⟩ := hR
  refine hRS.trans ((Subgroup.closure_le _).2 fun s hs => ?_)
  obtain ⟨y, hy, hys⟩ := h (Subgroup.mem_map_of_mem θ (hSR hs))
  set ε : K := s⁻¹ * y with hε
  have hεk : ε ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hε, map_mul, map_inv, hys, inv_mul_cancel]
  have hεc : Commute s ε := (Subgroup.mem_center_iff.mp (hker hεk) s)
  have hε2 : ε * ε = 1 := hker2 ε hεk
  have hy' : y = s * ε := by rw [hε]; group
  have hs3 : s ^ 3 = 1 := hS3 s hs
  have h4 : y ^ 4 = s := by
    rw [hy', hεc.mul_pow]
    have e1 : s ^ 4 = s := by rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ, hs3, one_mul]
    have e2 : ε ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_two ε, hε2, one_pow]
    rw [e1, e2, mul_one]
  rw [SetLike.mem_coe, ← h4]
  exact R'.pow_mem hy 4

end Basic

section Ctx

variable {ι : Type} [Fintype ι]

structure SpinCtx3 (Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)) (𝓕 : Set (Subgroup (spinGroup Q))) : Prop where
  hQ : (polarBilin Q).Nondegenerate
  hrange : (spinAction Q).range = elementaryGroup Q
  hZ : CenterScalar Q
  hdim : 7 ≤ Module.finrank 𝔽₃ (ι → 𝔽₃)
  hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1
  hframe : ∀ R ∈ 𝓕, ∃ fr : OFrame Q, R.map (spinAction Q) = fr.La.range
  hG3 : ∀ R ∈ 𝓕, Gen3 R
  hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, 𝔽₃))

variable {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)}

omit [Fintype ι] in
theorem theta_sl2Inv [Finite (spinGroup Q)] {R : Subgroup (spinGroup Q)}
    (e : R ≃* SL(2, 𝔽₃)) {fr : OFrame Q} (hR : R.map (spinAction Q) = fr.La.range) :
    spinAction Q (sl2Inv e) = fr.La (-1) := by
  have hodd := odd_natCard_galoisField_three
  have hcard : Nat.card R = Nat.card (R.map (spinAction Q)) := by
    rw [hR, Nat.card_congr e.toEquiv]
    exact (Nat.card_congr (MonoidHom.ofInjective fr.La_injective).toEquiv)
  have hinj := injOn_of_natCard_map3 (spinAction Q) hcard
  have hmem : spinAction Q (sl2Inv e) ∈ fr.La.range :=
    hR ▸ Subgroup.mem_map_of_mem _ (sl2Inv_mem e)
  have hsq : spinAction Q (sl2Inv e) * spinAction Q (sl2Inv e) = 1 := by
    rw [← map_mul, sl2Inv_mul_self hodd e, map_one]
  have hne : spinAction Q (sl2Inv e) ≠ 1 := fun h =>
    sl2Inv_ne_one hodd e (hinj _ (sl2Inv_mem e) 1 R.one_mem (h.trans (map_one _).symm))
  have hord : orderOf (spinAction Q (sl2Inv e)) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hne
  exact (IsFundamental.of_frame fr).eq_of_orderOf_eq_two hodd hmem hord

end Ctx


section Frames

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem La_fix_perp (fr : OFrame Q) (A : SL(2, F)) {x : V} (hx : x ∈ fr.perp) : fr.La A x = x :=
  Frame.La_apply_of_coords_eq_zero fr A ((Frame.mem_perp_iff fr).mp hx)

theorem La_swap_fix_perp (fr : OFrame Q) (B : SL(2, F)) {x : V} (hx : x ∈ fr.perp) :
    fr.swap.La B x = x := by
  apply Frame.La_apply_of_coords_eq_zero fr.swap B
  rw [← Frame.mem_perp_iff, Frame.perp_swap]
  exact hx

theorem La_maps_span (fr : OFrame Q) (A : SL(2, F)) {x : V} (hx : x ∈ fr.span) :
    fr.La A x ∈ fr.span := by
  obtain ⟨X, rfl⟩ := hx
  rw [Frame.La_apply_incl]
  exact ⟨_, rfl⟩

theorem La_swap_maps_span (fr : OFrame Q) (B : SL(2, F)) {x : V} (hx : x ∈ fr.span) :
    fr.swap.La B x ∈ fr.span := by
  rw [← Frame.span_eq_swap_span] at hx ⊢
  exact La_maps_span fr.swap B hx

end Frames

section Main

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)} {𝓕 : Set (Subgroup (spinGroup Q))}

theorem twin_generation_orth_ord [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    {X : Type} [Group X] (ψ : spinGroup Q →* X) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    {R₁ R₂ : Subgroup (spinGroup Q)} (hR₁ : R₁ ∈ 𝓕) (hR₂ : R₂ ∈ 𝓕)
    (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃))
    (hord : spinAction Q (sl2Inv e₁) = spinAction Q (sl2Inv e₂))
    (h24₁ : Nat.card (R₁.map ψ) = 24)
    (hne : R₁.map ψ ≠ R₂.map ψ) (hcomm : Commutes (R₁.map ψ) (R₂.map ψ)) {z : X}
    (hz₁ : IsUniqueInvolution (R₁.map ψ) z)
    {A : Subgroup X} (hA : IsElemAbelian2 A 2) (hAle : A ≤ R₁.map ψ ⊔ R₂.map ψ) (hzA : z ∈ A) :
    ψ.range ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ ψ.range := by
  classical
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hkerC : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  obtain ⟨u₁, -⟩ := uniqueInvolution_map3 ψ e₁ h24₁
  have hψz₁ : ψ (sl2Inv e₁) = z := u₁.eq hz₁
  obtain ⟨fr₁, hfr₁⟩ := c.hframe R₁ hR₁
  obtain ⟨fr₂, hfr₂⟩ := c.hframe R₂ hR₂
  have hθz₁ := theta_sl2Inv e₁ hfr₁
  have hθz₂ := theta_sl2Inv e₂ hfr₂
  have hι : fr₂.La (-1) = fr₁.La (-1) := by rw [← hθz₂, ← hθz₁, hord]
  rcases Frame.La_range_eq_or_eq_swap h2 hι with hsame | hswap
  · exfalso
    apply hne
    have h12 : R₂.map (spinAction Q) = R₁.map (spinAction Q) := by rw [hfr₂, hfr₁, hsame]
    have hle₁ : R₁ ≤ R₂ := le_of_map_le_of_gen3 _ hkerC c.hker2 (c.hG3 R₁ hR₁) h12.ge
    have hle₂ : R₂ ≤ R₁ := le_of_map_le_of_gen3 _ hkerC c.hker2 (c.hG3 R₂ hR₂) h12.le
    rw [le_antisymm hle₁ hle₂]
  have hfr₂' : R₂.map (spinAction Q) = fr₁.swap.La.range := hfr₂.trans hswap
  obtain ⟨w, hwA, hw1, hwz⟩ := exists_mem_ne_of_card_four (z := z) hA
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commutes hcomm (hAle hwA)
  obtain ⟨r₁, hr₁, rfl⟩ := ha
  obtain ⟨r₂, hr₂, rfl⟩ := hb
  have hψw : ψ (r₁ * r₂) = w := by rw [map_mul, hab]
  have hw2 : w * w = 1 := hA.2 w hwA
  have hθr₁ : spinAction Q r₁ ∈ fr₁.La.range := hfr₁ ▸ Subgroup.mem_map_of_mem _ hr₁
  have hθr₂ : spinAction Q r₂ ∈ fr₁.swap.La.range := hfr₂' ▸ Subgroup.mem_map_of_mem _ hr₂
  obtain ⟨A₀, hA₀⟩ := hθr₁
  obtain ⟨B₀, hB₀⟩ := hθr₂
  have hg_apply : ∀ x, spinAction Q (r₁ * r₂) x = fr₁.La A₀ (fr₁.swap.La B₀ x) := by
    intro x
    rw [map_mul, ← hA₀, ← hB₀]
    rfl
  have hgfix : ∀ x ∈ fr₁.perp, spinAction Q (r₁ * r₂) x = x := fun x hx => by
    rw [hg_apply, La_swap_fix_perp fr₁ B₀ hx, La_fix_perp fr₁ A₀ hx]
  have hgW : ∀ x ∈ fr₁.span, spinAction Q (r₁ * r₂) x ∈ fr₁.span := fun x hx => by
    rw [hg_apply]
    exact La_maps_span fr₁ A₀ (La_swap_maps_span fr₁ B₀ hx)
  have hperpdim : 3 ≤ Module.finrank 𝔽₃ fr₁.perp := by
    have h4 := finrank_perp_add_four fr₁
    have h7 := c.hdim
    omega
  have hperp_ne : fr₁.perp ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hperpdim
    omega
  obtain ⟨v, hvperp, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp_ne
  have hsqker : r₁ * r₂ * (r₁ * r₂) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hψw, hw2]
  obtain ⟨μ', hμ'⟩ := exists_smul_of_central c.hrange c.hZ (hψ hsqker)
  have hμ'1 : μ' = 1 := by
    have h1 : μ' • v = v := by
      rw [← hμ' v, map_mul, LinearEquiv.mul_apply, hgfix v hvperp, hgfix v hvperp]
    have h4 : (μ' - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hv0)
  have hg2 : ∀ x, spinAction Q (r₁ * r₂) (spinAction Q (r₁ * r₂) x) = x := fun x => by
    have h1 := hμ' x
    rw [hμ'1, one_smul, map_mul, LinearEquiv.mul_apply] at h1
    exact h1
  have hgE : spinAction Q (r₁ * r₂) ∈ elementaryGroup Q := by
    rw [← c.hrange]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hg'E : spinAction Q (sl2Inv e₁ * (r₁ * r₂)) ∈ elementaryGroup Q := by
    rw [← c.hrange]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hgO := elementaryGroup_le_orthogonalGroup Q hgE
  have hg'O := elementaryGroup_le_orthogonalGroup Q hg'E
  have hg'A : ∀ x ∈ fr₁.perp, spinAction Q (sl2Inv e₁ * (r₁ * r₂)) x = x := fun x hx => by
    rw [map_mul, hθz₁, LinearEquiv.mul_apply, hgfix x hx, La_fix_perp fr₁ (-1) hx]
  have hg' : ∀ x ∈ fr₁.span, spinAction Q (r₁ * r₂) x = -x →
      spinAction Q (sl2Inv e₁ * (r₁ * r₂)) x = x := fun x hx hgx => by
    rw [map_mul, hθz₁, LinearEquiv.mul_apply, hgx, map_neg, La_neg_one_of_mem_span fr₁ hx,
      neg_neg]
  obtain ⟨S₂, S₁, hle, h₂, h₁⟩ := exists_subspaces_of_involution hodd c.hQ
    (polarNondegOn_perp c.hQ fr₁) hperpdim fr₁.isCompl_span_perp
    (fun x hx y hy => polar_perp_of_mem_span fr₁ hx hy) hg2 hgfix hgW hg'A hg'
  have hl₂ : elemOn Q S₂ ≤
      (Subgroup.centralizer ({r₁ * r₂} : Set (spinGroup Q))).map (spinAction Q) :=
    elemOn_le_map_centralizer h2 (spinAction Q) c.hrange hkerC c.hker2
      (elemOn_le_centralizer_of_fix hgO h₂)
  have hl₁ : elemOn Q S₁ ≤
      (Subgroup.centralizer ({sl2Inv e₁ * (r₁ * r₂)} : Set (spinGroup Q))).map (spinAction Q) :=
    elemOn_le_map_centralizer h2 (spinAction Q) c.hrange hkerC c.hker2
      (elemOn_le_centralizer_of_fix hg'O h₁)
  have key := range_le_sup_of_lifts (spinAction Q) ψ hkerC hl₂ hl₁ (by rw [c.hrange]; exact hle)
  have hψzw : ψ (sl2Inv e₁ * (r₁ * r₂)) = z * w := by rw [map_mul, hψz₁, hψw]
  rw [hψw, hψzw] at key
  have hzw : z * w ≠ 1 := by
    intro h
    apply hwz
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hz₁.sq]
  refine key.trans (sup_le ?_ ?_)
  · exact le_iSup₂_of_le w hwA (le_iSup_of_le hw1 le_rfl)
  · exact le_iSup₂_of_le (z * w) (A.mul_mem hzA hwA) (le_iSup_of_le hzw le_rfl)


theorem twin_generation_orth [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False)
    {X : Type} [Group X] (ψ : spinGroup Q →* X) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    {R₁ R₂ : Subgroup (spinGroup Q)} (hR₁ : R₁ ∈ 𝓕) (hR₂ : R₂ ∈ 𝓕)
    (h24₁ : Nat.card (R₁.map ψ) = 24) (h24₂ : Nat.card (R₂.map ψ) = 24)
    (hne : R₁.map ψ ≠ R₂.map ψ) (hcomm : Commutes (R₁.map ψ) (R₂.map ψ)) {z : X}
    (hz₁ : IsUniqueInvolution (R₁.map ψ) z) (hz₂ : IsUniqueInvolution (R₂.map ψ) z)
    {A : Subgroup X} (hA : IsElemAbelian2 A 2) (hAle : A ≤ R₁.map ψ ⊔ R₂.map ψ) (hzA : z ∈ A) :
    ψ.range ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set X) ⊓ ψ.range := by
  classical
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hkerC : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  obtain ⟨e₁⟩ := c.hsl2 R₁ hR₁
  obtain ⟨e₂⟩ := c.hsl2 R₂ hR₂
  obtain ⟨u₁, -⟩ := uniqueInvolution_map3 ψ e₁ h24₁
  obtain ⟨u₂, -⟩ := uniqueInvolution_map3 ψ e₂ h24₂
  have hψz₁ : ψ (sl2Inv e₁) = z := u₁.eq hz₁
  have hψz₂ : ψ (sl2Inv e₂) = z := u₂.eq hz₂
  obtain ⟨fr₁, hfr₁⟩ := c.hframe R₁ hR₁
  obtain ⟨fr₂, hfr₂⟩ := c.hframe R₂ hR₂
  have hθz₁ := theta_sl2Inv e₁ hfr₁
  have hθz₂ := theta_sl2Inv e₂ hfr₂
  have hk : sl2Inv e₁ * (sl2Inv e₂)⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψz₁, hψz₂, mul_inv_cancel]
  obtain ⟨μ, hμ⟩ := exists_smul_of_central c.hrange c.hZ (hψ hk)
  have hι₁ : fr₁.La (-1) * fr₁.La (-1) = 1 := fr₁.La_neg_one_mul_self
  have hι₂ : fr₂.La (-1) * fr₂.La (-1) = 1 := fr₂.La_neg_one_mul_self
  have hμ' : ∀ v, fr₁.La (-1) (fr₂.La (-1) v) = μ • v := by
    intro v
    have := hμ v
    rw [map_mul, map_inv, hθz₁, hθz₂, inv_eq_of_mul_eq_one_right hι₂, LinearEquiv.mul_apply] at this
    exact this
  have e1 : ∀ v, fr₂.La (-1) v = μ • fr₁.La (-1) v := by
    intro v
    have h1 := congrArg (fun x => fr₁.La (-1) x) (hμ' v)
    simp only [map_smul] at h1
    have h2' : fr₁.La (-1) (fr₁.La (-1) (fr₂.La (-1) v)) = fr₂.La (-1) v := by
      have := congrArg (fun φ : (ι → 𝔽₃) ≃ₗ[𝔽₃] (ι → 𝔽₃) => φ (fr₂.La (-1) v)) hι₁
      simpa using this
    rw [h2'] at h1
    exact h1
  have hι : fr₂.La (-1) = fr₁.La (-1) := by
    obtain ⟨v, hv0⟩ : ∃ v : ι → 𝔽₃, v ≠ 0 := by
      have : 0 < Module.finrank 𝔽₃ (ι → 𝔽₃) := by have := c.hdim; omega
      exact Module.finrank_pos_iff_exists_ne_zero.mp this
    have hμ2 : μ * μ = 1 := by
      have h1 : fr₂.La (-1) (fr₂.La (-1) v) = v := by
        have := congrArg (fun φ : (ι → 𝔽₃) ≃ₗ[𝔽₃] (ι → 𝔽₃) => φ v) hι₂
        simpa using this
      rw [e1 v, map_smul, e1 (fr₁.La (-1) v), smul_smul] at h1
      have h3 : fr₁.La (-1) (fr₁.La (-1) v) = v := by
        have := congrArg (fun φ : (ι → 𝔽₃) ≃ₗ[𝔽₃] (ι → 𝔽₃) => φ v) hι₁
        simpa using this
      rw [h3] at h1
      have h4 : (μ * μ - 1) • v = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hv0)
    rcases mul_self_eq_one_iff.mp hμ2 with hμ1 | hμ1
    · refine LinearEquiv.ext fun x => ?_
      rw [e1 x, hμ1, one_smul]
    · exfalso
      refine hproj fr₁ fr₂ (LinearEquiv.ext fun x => ?_)
      rw [e1 x, hμ1, LinearEquiv.mul_apply, LinearEquiv.neg_apply, neg_smul, one_smul]
  exact twin_generation_orth_ord c ψ hψ hR₁ hR₂ e₁ e₂ (by rw [hθz₁, hθz₂, hι]) h24₁ hne hcomm hz₁
    hA hAle hzA

end Main

end CFSG.ClassicalInvolution.ModelFacts.TG3
