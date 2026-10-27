module

public import CFSG.ClassicalInvolution.Q3.Q3Y2Twin
public import CFSG.ClassicalInvolution.ModelFacts.TG3Models
public import CFSG.ClassicalInvolution.ModelFacts.TG3D4Tri

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y2

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

section Main

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)} {𝓕 : Set (Subgroup (spinGroup Q))}

theorem twinStrong3_ord [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕) {R₁ R₂ : Subgroup (spinGroup Q)}
    (hR₁ : R₁ ∈ 𝓕) (hR₂ : R₂ ∈ 𝓕) (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃)) (hne : R₁ ≠ R₂)
    (hcomm : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a)
    (hcen : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hord : spinAction Q (sl2Inv e₁) = spinAction Q (sl2Inv e₂)) {r₁ r₂ : spinGroup Q}
    (hr₁ : r₁ ∈ R₁) (hr₂ : r₂ ∈ R₂) (hr₁sq : r₁ * r₁ = sl2Inv e₁) (hr₂sq : r₂ * r₂ = sl2Inv e₂) :
    (⊤ : Subgroup (spinGroup Q)) ≤ Subgroup.centralizer ({sl2Inv e₁} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({r₁ * r₂} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({sl2Inv e₁ * (r₁ * r₂)} : Set (spinGroup Q)) := by
  classical
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hkerC : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
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
    have h4 := ModelFacts.finrank_perp_add_four fr₁
    have h7 := c.hdim
    omega
  have hperp_ne : fr₁.perp ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hperpdim
    omega
  obtain ⟨v, hvperp, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp_ne
  have hi₁R : sl2Inv e₁ ∈ R₁ := sl2Inv_mem e₁
  have hi₂R : sl2Inv e₂ ∈ R₂ := sl2Inv_mem e₂
  have hsqc : r₁ * r₂ * (r₁ * r₂) ∈ Subgroup.center (spinGroup Q) := by
    have h1 : r₂ * r₁ = r₁ * r₂ := (hcomm r₁ hr₁ r₂ hr₂).symm
    have e : r₁ * r₂ * (r₁ * r₂) = sl2Inv e₂ * sl2Inv e₁ := by
      calc r₁ * r₂ * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
        _ = r₁ * (r₁ * r₂) * r₂ := by rw [h1]
        _ = (r₁ * r₁) * (r₂ * r₂) := by group
        _ = sl2Inv e₁ * sl2Inv e₂ := by rw [hr₁sq, hr₂sq]
        _ = sl2Inv e₂ * sl2Inv e₁ := (hcomm _ hi₁R _ hi₂R)
    have hi₁inv : (sl2Inv e₁)⁻¹ = sl2Inv e₁ :=
      inv_eq_of_mul_eq_one_right (sl2Inv_mul_self hodd e₁)
    rw [e]
    simpa [hi₁inv] using hcen
  obtain ⟨μ', hμ'⟩ := exists_smul_of_central c.hrange c.hZ hsqc
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
    (ModelFacts.polarNondegOn_perp c.hQ fr₁) hperpdim fr₁.isCompl_span_perp
    (fun x hx y hy => polar_perp_of_mem_span fr₁ hx hy) hg2 hgfix hgW hg'A hg'
  have hl₂ : elemOn Q S₂ ≤
      (Subgroup.centralizer ({r₁ * r₂} : Set (spinGroup Q))).map (spinAction Q) :=
    elemOn_le_map_centralizer h2 (spinAction Q) c.hrange hkerC c.hker2
      (elemOn_le_centralizer_of_fix hgO h₂)
  have hl₁ : elemOn Q S₁ ≤
      (Subgroup.centralizer ({sl2Inv e₁ * (r₁ * r₂)} : Set (spinGroup Q))).map (spinAction Q) :=
    elemOn_le_map_centralizer h2 (spinAction Q) c.hrange hkerC c.hker2
      (elemOn_le_centralizer_of_fix hg'O h₁)
  have key := range_le_sup_of_lifts (spinAction Q) (MonoidHom.id (spinGroup Q)) hkerC hl₂ hl₁
    (by rw [c.hrange]; exact hle)
  have hsub : (Subgroup.centralizer ({(MonoidHom.id (spinGroup Q)) (r₁ * r₂)} : Set (spinGroup Q)) ⊓
        (MonoidHom.id (spinGroup Q)).range) ⊔
      (Subgroup.centralizer ({(MonoidHom.id (spinGroup Q)) (sl2Inv e₁ * (r₁ * r₂))} :
        Set (spinGroup Q)) ⊓ (MonoidHom.id (spinGroup Q)).range) ≤
      Subgroup.centralizer ({sl2Inv e₁} : Set (spinGroup Q)) ⊔
        Subgroup.centralizer ({r₁ * r₂} : Set (spinGroup Q)) ⊔
        Subgroup.centralizer ({sl2Inv e₁ * (r₁ * r₂)} : Set (spinGroup Q)) :=
    sup_le (inf_le_left.trans (le_sup_of_le_left le_sup_right)) (inf_le_left.trans le_sup_right)
  intro x _
  exact hsub (key (MonoidHom.mem_range.mpr ⟨x, rfl⟩))


theorem twinStrong3_of_ctx [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False) :
    TwinStrong3 𝓕 := by
  classical
  intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hcomm hcen _ r₁ hr₁ r₂ hr₂ hr₁sq hr₂sq
  have hodd := odd_natCard_galoisField_three
  have hk : sl2Inv e₁ * (sl2Inv e₂)⁻¹ ∈ Subgroup.center (spinGroup Q) := by
    have := Subgroup.inv_mem _ hcen
    simpa [mul_inv_rev] using this
  obtain ⟨fr₁, hfr₁⟩ := c.hframe R₁ hR₁
  obtain ⟨fr₂, hfr₂⟩ := c.hframe R₂ hR₂
  have hθz₁ := theta_sl2Inv e₁ hfr₁
  have hθz₂ := theta_sl2Inv e₂ hfr₂
  obtain ⟨μ, hμ⟩ := exists_smul_of_central c.hrange c.hZ hk
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
  exact twinStrong3_ord c hR₁ hR₂ e₁ e₂ hne hcomm hcen (by rw [hθz₁, hθz₂, hι]) hr₁ hr₂ hr₁sq
    hr₂sq

theorem twinStrong3_of_ctx_aut [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (haut : ∀ {c₀ : spinGroup Q}, c₀ ∈ Subgroup.center (spinGroup Q) → c₀ * c₀ = 1 →
      ∃ σ : spinGroup Q ≃* spinGroup Q, (∀ R ∈ 𝓕, R.map σ.toMonoidHom ∈ 𝓕) ∧
        spinAction Q (σ c₀) = 1) :
    TwinStrong3 𝓕 := by
  classical
  intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hcomm hcen _ r₁ hr₁ r₂ hr₂ hr₁sq hr₂sq
  have hodd := odd_natCard_galoisField_three
  have hsq₁ := sl2Inv_mul_self hodd e₁
  have hsq₂ := sl2Inv_mul_self hodd e₂
  have hinv : (sl2Inv e₁)⁻¹ = sl2Inv e₁ := inv_eq_of_mul_eq_one_right hsq₁
  have hcomm₁₂ : sl2Inv e₁ * sl2Inv e₂ = sl2Inv e₂ * sl2Inv e₁ :=
    hcomm _ (sl2Inv_mem e₁) _ (sl2Inv_mem e₂)
  have hc2 : (sl2Inv e₂ * (sl2Inv e₁)⁻¹) * (sl2Inv e₂ * (sl2Inv e₁)⁻¹) = 1 := by
    rw [hinv]
    calc sl2Inv e₂ * sl2Inv e₁ * (sl2Inv e₂ * sl2Inv e₁)
        = sl2Inv e₂ * (sl2Inv e₁ * sl2Inv e₂) * sl2Inv e₁ := by group
      _ = sl2Inv e₂ * (sl2Inv e₂ * sl2Inv e₁) * sl2Inv e₁ := by rw [hcomm₁₂]
      _ = (sl2Inv e₂ * sl2Inv e₂) * (sl2Inv e₁ * sl2Inv e₁) := by group
      _ = 1 := by rw [hsq₁, hsq₂, mul_one]
  obtain ⟨σ, hσ𝓕, hθσ⟩ := haut hcen hc2
  let e₁' : ↥(R₁.map σ.toMonoidHom) ≃* SL(2, 𝔽₃) := (σ.subgroupMap R₁).symm.trans e₁
  let e₂' : ↥(R₂.map σ.toMonoidHom) ≃* SL(2, 𝔽₃) := (σ.subgroupMap R₂).symm.trans e₂
  have hs₁ : sl2Inv e₁' = σ (sl2Inv e₁) := rfl
  have hs₂ : sl2Inv e₂' = σ (sl2Inv e₂) := rfl
  have hord : spinAction Q (sl2Inv e₁') = spinAction Q (sl2Inv e₂') := by
    have h1 : sl2Inv e₂ = (sl2Inv e₂ * (sl2Inv e₁)⁻¹) * sl2Inv e₁ := by group
    rw [hs₁, hs₂, h1, map_mul, map_mul, hθσ, one_mul]
  have hne' : R₁.map σ.toMonoidHom ≠ R₂.map σ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective σ.injective h)
  have hcomm' : ∀ a ∈ R₁.map σ.toMonoidHom, ∀ b ∈ R₂.map σ.toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show σ a * σ b = σ b * σ a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hcen' : sl2Inv e₂' * (sl2Inv e₁')⁻¹ ∈ Subgroup.center (spinGroup Q) := by
    rw [hs₁, hs₂, ← map_inv, ← map_mul]
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    have := Subgroup.mem_center_iff.mp hcen (σ.symm y)
    simpa using congrArg σ this
  have key := twinStrong3_ord c (hσ𝓕 R₁ hR₁) (hσ𝓕 R₂ hR₂) e₁' e₂' hne' hcomm' hcen' hord
    (r₁ := σ r₁) (r₂ := σ r₂) (Subgroup.mem_map_of_mem _ hr₁) (Subgroup.mem_map_of_mem _ hr₂)
    (by rw [hs₁, ← map_mul, hr₁sq]) (by rw [hs₂, ← map_mul, hr₂sq])
  have hmapC : ∀ y : spinGroup Q, (Subgroup.centralizer ({σ y} : Set (spinGroup Q))).map
      σ.symm.toMonoidHom ≤ Subgroup.centralizer ({y} : Set (spinGroup Q)) := by
    rintro y _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have := congrArg σ.symm (Subgroup.mem_centralizer_singleton_iff.mp hw)
    simpa using this
  have e2 : σ r₁ * σ r₂ = σ (r₁ * r₂) := (map_mul σ r₁ r₂).symm
  have e3 : σ (sl2Inv e₁) * σ (r₁ * r₂) = σ (sl2Inv e₁ * (r₁ * r₂)) := (map_mul σ _ _).symm
  rw [hs₁, e2, e3] at key
  intro x _
  have hx := key (Subgroup.mem_top (σ x))
  have hx' : σ.symm (σ x) ∈ ((Subgroup.centralizer ({σ (sl2Inv e₁)} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({σ (r₁ * r₂)} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({σ (sl2Inv e₁ * (r₁ * r₂))} : Set (spinGroup Q))).map
        σ.symm.toMonoidHom) := ⟨σ x, hx, rfl⟩
  rw [Subgroup.map_sup, Subgroup.map_sup] at hx'
  rw [MulEquiv.symm_apply_apply] at hx'
  exact (sup_le_sup (sup_le_sup (hmapC _) (hmapC _)) (hmapC _)) hx'

end Main

section Models

theorem twinStrong3_pOmegaOdd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    TwinStrong3 (Generic.fundamentalSubgroups .POmegaOdd
      (Generic.modelUniv .POmegaOdd n 3 1 Nat.prime_three).D) := by
  show TwinStrong3 (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D)
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaOdd n 3 1 Nat.prime_three =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ := rfl
  have hsingle : Generic.FundamentalSingleClass .POmegaOdd
      (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaOdd n 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D, Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaOdd) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D.rank, k.val + 1 < n →
      Generic.IsLongestRoot (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaOdd n 3 1 Nat.prime_three trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D, Nonempty (R ≃* SL(2, GaloisField 3 1)) :=
    fun R hR => nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaOdd) trivial hadm
      (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K :=
    finite_modelUniv (t := .POmegaOdd) hp2 Nat.prime_three trivial hadm
  generalize modelUniv .POmegaOdd n 3 1 Nat.prime_three = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have hn0 : 0 < n := by omega
  have : Finite (spinGroup (quadOdd n (GaloisField 3 1))) := hfin
  exact twinStrong3_of_ctx (spinCtx3_odd hn3 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 1 < n; omega)) hG3 hsl2) hproj_odd

theorem twinStrong3_pOmegaMinus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    TwinStrong3 (Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus n 3 1 Nat.prime_three).D) := by
  show TwinStrong3
    (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D)
  have hn4 : 4 ≤ n := hadm.2.2
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaMinus n 3 1 Nat.prime_three =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum n (minusCoeffs_irr 3 1)⟩ := rfl
  have hsingle : Generic.FundamentalSingleClass .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaMinus n 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D, Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaMinus) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D.rank, k.val + 2 < n →
      Generic.IsLongestRoot (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaMinus n 3 1 Nat.prime_three trivial hadm k hk
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaMinus) trivial hadm
      (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K :=
    finite_modelUniv (t := .POmegaMinus) hp2 Nat.prime_three trivial hadm
  generalize modelUniv .POmegaMinus n 3 1 Nat.prime_three = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have hn0 : 0 < n - 1 := by omega
  have : Finite (spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)) := hfin
  exact twinStrong3_of_ctx (spinCtx3_minus (minusCoeffs_irr 3 1) hn4 ⟨0, hn0⟩ rfl hsingle
    (hlong ⟨0, hn0⟩ (by show 0 + 2 < n; omega)) hG3 hsl2)
    (fun F₁ F₂ h => hproj_minus (minusCoeffs_irr 3 1) hn4 F₁ F₂ h)

theorem twinStrong3_pOmegaPlus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    (hn5 : 5 ≤ n) :
    TwinStrong3 (Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus n 3 1 Nat.prime_three).D) := by
  show TwinStrong3
    (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D)
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaPlus n 3 1 Nat.prime_three =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) hn3⟩ :=
    modelUniv_POmegaPlus hn3
  have hsingle : Generic.FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaPlus n 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D, Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D.rank,
      Generic.IsLongestRoot (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus n 3 1 Nat.prime_three trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaPlus) trivial hadm
      (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K :=
    finite_modelUniv (t := .POmegaPlus) hp2 Nat.prime_three trivial hadm
  generalize modelUniv .POmegaPlus n 3 1 Nat.prime_three = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have : Finite (spinGroup (quadPlus n (GaloisField 3 1))) := hfin
  exact twinStrong3_of_ctx (spinCtx3_plus hn3 hn4 hsingle hlong hG3 hsl2) (hproj_plus hn5)

theorem twinStrong3_pOmegaPlus_four (hadm : StatedLieAdmissible .POmegaPlus 4 3 1) :
    TwinStrong3 (Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D) := by
  show TwinStrong3
    (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D)
  have hn3 : 3 ≤ 4 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : modelUniv .POmegaPlus 4 3 1 Nat.prime_three =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    modelUniv_POmegaPlus hn3
  have hsingle : Generic.FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaPlus 4 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D, Gen3 R := fun R hR =>
    gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide) (by decide)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D.rank,
      Generic.IsLongestRoot (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus 4 3 1 Nat.prime_three trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaPlus) trivial hadm
      (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K :=
    finite_modelUniv (t := .POmegaPlus) hp2 Nat.prime_three trivial hadm
  generalize modelUniv .POmegaPlus 4 3 1 Nat.prime_three = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have : Finite (spinGroup (quadPlus 4 (GaloisField 3 1))) := hfin
  exact twinStrong3_of_ctx_aut (spinCtx3_plus hn3 le_rfl hsingle hlong hG3 hsl2)
    (fun {c₀} hc hc2 => exists_aut_ordinary3 hadm hc hc2)

end Models

end CFSG.ClassicalInvolution.Q3.Q3Y2
