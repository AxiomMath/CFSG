module

public import CFSG.ClassicalGroups.Orthogonal.SiegelSLBasic
public import CFSG.ClassicalGroups.SpecialLinear.TransvectionPencils

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelSL

open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 CFSG.CGT.Timmesfeld75
open CFSG.CGT.T75E QuadraticMap Module Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m : ℕ} {Qf : QuadraticForm K V} {ρ : SL(m, K) →* (V ≃ₗ[K] V)}

omit [CharP K 2] [Finite K] in
private theorem tvSL_smul_mem_inf {c α : Fin m → K} (μ : K) (h : (μ • α) ⬝ᵥ c = 0)
    (h0 : α ⬝ᵥ c = 0) : tvSL c (μ • α) h ∈ tvCenterSL c ⊓ tvAxisSL α := by
  refine Subgroup.mem_inf.mpr ⟨⟨μ • α, h, rfl⟩, ⟨μ • c, ?_, ?_⟩⟩
  · rw [dotProduct_smul, smul_eq_mul, h0, mul_zero]
  · rw [coe_tvSL, smul_vecMulVec, vecMulVec_smul]

omit [CharP K 2] [Finite K] in
private theorem tvSL_ne_one_of_ne_zero {c a : Fin m → K} (h : a ⬝ᵥ c = 0) (hc : c ≠ 0)
    (ha : a ≠ 0) : tvSL c a h ≠ 1 :=
  (isTransvection_of_coe hc ha h rfl).1

omit [CharP K 2] [Finite K] in
private theorem tvSL_zero_smul_eq_one {c α : Fin m → K} (h : ((0 : K) • α) ⬝ᵥ c = 0) :
    tvSL c ((0 : K) • α) h = 1 :=
  Subtype.ext (by simp [coe_tvSL])

omit [Finite K] in
private theorem SLSetting.exists_axes_pair (hs : SLSetting Qf ρ) {c α : Fin m → K} (hc : c ≠ 0)
    (hα : α ≠ 0) (h : α ⬝ᵥ c = 0) :
    ∃ A₁ ∈ axes ((tvCenterSL c).map ρ), ∃ A₂ ∈ axes ((tvAxisSL α).map ρ),
      A₁ ⊓ A₂ = ⊥ ∧ ¬ ∀ x ∈ A₁, ∀ y ∈ A₂, polar Qf x y = 0 := by
  obtain ⟨d, hαd, hd⟩ := exists_dot_eq_zero_not_smul hs.three_le c α
  obtain ⟨β, hβc, hβd⟩ := exists_dot_of_not_smul hd
  obtain ⟨hnc, hinf, hno⟩ := hs.not_commute_of_dot hβc hαd h (by rw [hβd]; exact one_ne_zero)
    hc hα
  have h1 : ρ (tvSL c β hβc) ≠ 1 := fun h1 => hnc (by rw [h1, one_mul, mul_one])
  have h2 : ρ (tvSL d α hαd) ≠ 1 := fun h2 => hnc (by rw [h2, one_mul, mul_one])
  exact ⟨_, ⟨_, Subgroup.mem_map_of_mem ρ ⟨β, hβc, rfl⟩, h1, rfl⟩, _,
    ⟨_, Subgroup.mem_map_of_mem ρ ⟨d, hαd, rfl⟩, h2, rfl⟩, hinf, hno⟩

omit [Finite K] [FiniteDimensional K V] in
private theorem SLSetting.isLongRootElement_of_mem_inf (hs : SLSetting Qf ρ) {c α : Fin m → K}
    {x : SL(m, K)} (hx : x ∈ tvCenterSL c ⊓ tvAxisSL α) (hx1 : x ≠ 1) :
    IsLongRootElement Qf (ρ x) ∧ movedSpace (ρ x) ∈ axes ((tvCenterSL c).map ρ) ∧
      movedSpace (ρ x) ∈ axes ((tvAxisSL α).map ρ) := by
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
  have h1 : ρ x ≠ 1 := fun h => hx1 (hs.injOn_center c x hx₁ 1 (one_mem _) (by rw [h, map_one]))
  exact ⟨(hs.isSiegelGroup_center c).siegel _ (Subgroup.mem_map_of_mem ρ hx₁) h1,
    ⟨ρ x, Subgroup.mem_map_of_mem ρ hx₁, h1, rfl⟩, ⟨ρ x, Subgroup.mem_map_of_mem ρ hx₂, h1, rfl⟩⟩

omit [Finite K] in
theorem SLSetting.not_le_of_dot_eq_zero (hs : SLSetting Qf ρ) {c α : Fin m → K} (hc : c ≠ 0)
    (hα : α ≠ 0) (h : α ⬝ᵥ c = 0) :
    ¬ commutatorSpace ((tvCenterSL c).map ρ) ≤ commutatorSpace ((tvAxisSL α).map ρ) ∧
      ¬ commutatorSpace ((tvAxisSL α).map ρ) ≤ commutatorSpace ((tvCenterSL c).map ρ) := by
  obtain ⟨A₁, hA₁, A₂, hA₂, -, hno⟩ := hs.exists_axes_pair hc hα h
  have hsing₁ := (hs.isSiegelGroup_center c).qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  have hsing₂ := (hs.isSiegelGroup_axis α).qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  have l₁ := le_commutatorSpace_of_mem_axes hA₁
  have l₂ := le_commutatorSpace_of_mem_axes hA₂
  exact ⟨fun hle => hno fun x hx y hy =>
      polar_eq_zero_of_totallySingular hsing₂ (hle (l₁ hx)) (l₂ hy),
    fun hle => hno fun x hx y hy =>
      polar_eq_zero_of_totallySingular hsing₁ (l₁ hx) (hle (l₂ hy))⟩

theorem SLSetting.axisInf_center_of_isStar (hs : SLSetting Qf ρ) {c : Fin m → K} (hc : c ≠ 0)
    (hst : IsStar ((tvCenterSL c).map ρ)) :
    finrank K (axisInf ((tvCenterSL c).map ρ)) = 1 ∧
      ∀ A ∈ axes ((tvCenterSL c).map ρ), axisInf ((tvCenterSL c).map ρ) ≤ A := by
  refine ⟨?_, fun A hA => axisInf_le hA⟩
  obtain ⟨P, hP1, hP⟩ := hst
  have hcard : Nat.card K < Nat.card ((tvCenterSL c).map ρ) := by
    rw [hs.card_map_center hc]
    have hq : 1 < Nat.card K := Finite.one_lt_card
    calc Nat.card K = Nat.card K ^ 1 := (pow_one _).symm
      _ < Nat.card K ^ (m - 1) := Nat.pow_lt_pow_right hq (by have := hs.three_le; omega)
  obtain ⟨A₁, hA₁, A₂, hA₂, hne⟩ := (hs.isSiegelGroup_center c).exists_ne_axes hs.nondeg hcard
  exact ((hs.isSiegelGroup_center c).eq_axisInf hs.nondeg hP1 hP hA₁ hA₂ hne).2

theorem SLSetting.axisInf_axis_of_isStar (hs : SLSetting Qf ρ) {α : Fin m → K} (hα : α ≠ 0)
    (hst : IsStar ((tvAxisSL α).map ρ)) :
    finrank K (axisInf ((tvAxisSL α).map ρ)) = 1 ∧
      ∀ A ∈ axes ((tvAxisSL α).map ρ), axisInf ((tvAxisSL α).map ρ) ≤ A := by
  refine ⟨?_, fun A hA => axisInf_le hA⟩
  obtain ⟨P, hP1, hP⟩ := hst
  have hcard : Nat.card K < Nat.card ((tvAxisSL α).map ρ) := by
    rw [hs.card_map_axis hα]
    have hq : 1 < Nat.card K := Finite.one_lt_card
    calc Nat.card K = Nat.card K ^ 1 := (pow_one _).symm
      _ < Nat.card K ^ (m - 1) := Nat.pow_lt_pow_right hq (by have := hs.three_le; omega)
  obtain ⟨A₁, hA₁, A₂, hA₂, hne⟩ := (hs.isSiegelGroup_axis α).exists_ne_axes hs.nondeg hcard
  exact ((hs.isSiegelGroup_axis α).eq_axisInf hs.nondeg hP1 hP hA₁ hA₂ hne).2

omit [Finite K] in
theorem SLSetting.axisInf_center_inf_axisInf_axis (hs : SLSetting Qf ρ) {c α : Fin m → K}
    (hc : c ≠ 0) (hα : α ≠ 0) (h : α ⬝ᵥ c = 0) :
    axisInf ((tvCenterSL c).map ρ) ⊓ axisInf ((tvAxisSL α).map ρ) = ⊥ := by
  obtain ⟨A₁, hA₁, A₂, hA₂, hbot, -⟩ := hs.exists_axes_pair hc hα h
  exact eq_bot_iff.mpr ((inf_le_inf (axisInf_le hA₁) (axisInf_le hA₂)).trans hbot.le)

omit [Finite K] in
theorem SLSetting.movedSpace_eq_inf_of_not_isStar_center (hs : SLSetting Qf ρ)
    {c α : Fin m → K} (hc : c ≠ 0) (hα : α ≠ 0) (h : α ⬝ᵥ c = 0)
    (hst : ¬ IsStar ((tvCenterSL c).map ρ)) {x : SL(m, K)}
    (hx : x ∈ tvCenterSL c ⊓ tvAxisSL α) (hx1 : x ≠ 1) :
    movedSpace (ρ x) =
      commutatorSpace ((tvCenterSL c).map ρ) ⊓ commutatorSpace ((tvAxisSL α).map ρ) := by
  obtain ⟨hsx, hA₁, hA₂⟩ := hs.isLongRootElement_of_mem_inf hx hx1
  have h3 := (hs.isSiegelGroup_center c).finrank_commutatorSpace_eq_three hs.nondeg ⟨_, hA₁⟩ hst
  have hlt : commutatorSpace ((tvCenterSL c).map ρ) ⊓ commutatorSpace ((tvAxisSL α).map ρ) <
      commutatorSpace ((tvCenterSL c).map ρ) :=
    inf_lt_left.mpr (hs.not_le_of_dot_eq_zero hc hα h).1
  have h4 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := hsx.finrank_movedSpace hs.nondeg
  exact Submodule.eq_of_le_of_finrank_le
    (le_inf (le_commutatorSpace_of_mem_axes hA₁) (le_commutatorSpace_of_mem_axes hA₂)) (by omega)

omit [Finite K] in
theorem SLSetting.movedSpace_eq_inf_of_not_isStar_axis (hs : SLSetting Qf ρ)
    {c α : Fin m → K} (hc : c ≠ 0) (hα : α ≠ 0) (h : α ⬝ᵥ c = 0)
    (hst : ¬ IsStar ((tvAxisSL α).map ρ)) {x : SL(m, K)}
    (hx : x ∈ tvCenterSL c ⊓ tvAxisSL α) (hx1 : x ≠ 1) :
    movedSpace (ρ x) =
      commutatorSpace ((tvCenterSL c).map ρ) ⊓ commutatorSpace ((tvAxisSL α).map ρ) := by
  obtain ⟨hsx, hA₁, hA₂⟩ := hs.isLongRootElement_of_mem_inf hx hx1
  have h3 := (hs.isSiegelGroup_axis α).finrank_commutatorSpace_eq_three hs.nondeg ⟨_, hA₂⟩ hst
  have hlt : commutatorSpace ((tvCenterSL c).map ρ) ⊓ commutatorSpace ((tvAxisSL α).map ρ) <
      commutatorSpace ((tvAxisSL α).map ρ) :=
    inf_lt_right.mpr (hs.not_le_of_dot_eq_zero hc hα h).2
  have h4 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := hsx.finrank_movedSpace hs.nondeg
  exact Submodule.eq_of_le_of_finrank_le
    (le_inf (le_commutatorSpace_of_mem_axes hA₁) (le_commutatorSpace_of_mem_axes hA₂)) (by omega)

theorem SLSetting.movedSpace_eq_sup_of_isStar (hs : SLSetting Qf ρ) {c α : Fin m → K}
    (hc : c ≠ 0) (hα : α ≠ 0) (h : α ⬝ᵥ c = 0) (hst₁ : IsStar ((tvCenterSL c).map ρ))
    (hst₂ : IsStar ((tvAxisSL α).map ρ)) {x : SL(m, K)}
    (hx : x ∈ tvCenterSL c ⊓ tvAxisSL α) (hx1 : x ≠ 1) :
    movedSpace (ρ x) = axisInf ((tvCenterSL c).map ρ) ⊔ axisInf ((tvAxisSL α).map ρ) := by
  obtain ⟨hsx, hA₁, hA₂⟩ := hs.isLongRootElement_of_mem_inf hx hx1
  obtain ⟨hf₁, hle₁⟩ := hs.axisInf_center_of_isStar hc hst₁
  obtain ⟨hf₂, hle₂⟩ := hs.axisInf_axis_of_isStar hα hst₂
  have hdisj := hs.axisInf_center_inf_axisInf_axis hc hα h
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (axisInf ((tvCenterSL c).map ρ))
    (axisInf ((tvAxisSL α).map ρ))
  rw [hdisj, finrank_bot, hf₁, hf₂] at h1
  have h2 := hsx.finrank_movedSpace hs.nondeg
  exact (Submodule.eq_of_le_of_finrank_le (sup_le (hle₁ _ hA₁) (hle₂ _ hA₂)) (by omega)).symm

theorem SLSetting.movedSpace_tvSL_smul_eq (hs : SLSetting Qf ρ) {c α : Fin m → K} (hc : c ≠ 0)
    (hα : α ≠ 0) (h : α ⬝ᵥ c = 0) {μ : K} (hμ : μ ≠ 0) :
    movedSpace (ρ (tvSL c (μ • α) (by rw [smul_dotProduct, h, smul_zero]))) =
      movedSpace (ρ (tvSL c α h)) := by
  have h' : (μ • α) ⬝ᵥ c = 0 := by rw [smul_dotProduct, h, smul_zero]
  have hx₁ := tvSL_smul_mem_inf μ h' h
  have hx₂ : tvSL c α h ∈ tvCenterSL c ⊓ tvAxisSL α :=
    Subgroup.mem_inf.mpr ⟨⟨α, h, rfl⟩, ⟨c, h, rfl⟩⟩
  have h₁ := tvSL_ne_one_of_ne_zero h' hc (smul_ne_zero hμ hα)
  have h₂ := tvSL_ne_one_of_ne_zero h hc hα
  by_cases hst₁ : IsStar ((tvCenterSL c).map ρ)
  · by_cases hst₂ : IsStar ((tvAxisSL α).map ρ)
    · rw [hs.movedSpace_eq_sup_of_isStar hc hα h hst₁ hst₂ hx₁ h₁,
        hs.movedSpace_eq_sup_of_isStar hc hα h hst₁ hst₂ hx₂ h₂]
    · rw [hs.movedSpace_eq_inf_of_not_isStar_axis hc hα h hst₂ hx₁ h₁,
        hs.movedSpace_eq_inf_of_not_isStar_axis hc hα h hst₂ hx₂ h₂]
  · rw [hs.movedSpace_eq_inf_of_not_isStar_center hc hα h hst₁ hx₁ h₁,
      hs.movedSpace_eq_inf_of_not_isStar_center hc hα h hst₁ hx₂ h₂]

theorem SLSetting.exists_eq_tvSL_of_movedSpace_eq (hs : SLSetting Qf ρ) {c α : Fin m → K}
    (hc : c ≠ 0) (hα : α ≠ 0) (h : α ⬝ᵥ c = 0) {s : V ≃ₗ[K] V} (hs' : IsLongRootElement Qf s)
    (hst : movedSpace s = movedSpace (ρ (tvSL c α h))) :
    ∃ (μ : K) (h' : (μ • α) ⬝ᵥ c = 0), μ ≠ 0 ∧ s = ρ (tvSL c (μ • α) h') := by
  set A := movedSpace (ρ (tvSL c α h)) with hAdef
  have hsα : IsLongRootElement Qf (ρ (tvSL c α h)) := hs.siegel c α h hc hα
  have hAfin : finrank K A = 2 := hsα.finrank_movedSpace hs.nondeg
  have hAsing : ∀ w ∈ A, Qf w = 0 := fun w hw => hsα.qf_eq_zero_of_mem_movedSpace hw
  have hAbot : A ≠ ⊥ := fun hb => by rw [hb, finrank_bot] at hAfin; omega
  obtain ⟨p, hpA, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAbot
  set P := Submodule.span K ({p} : Set V) with hPdef
  have hP1 : finrank K P = 1 := finrank_span_singleton hp0
  have hPA : P ≤ A := (Submodule.span_singleton_le_iff_mem p A).mpr hpA
  have hmem : ∀ (μ : K) (h' : (μ • α) ⬝ᵥ c = 0), ρ (tvSL c (μ • α) h') ∈ piGroup Qf P A := by
    intro μ h'
    by_cases hμ : μ = 0
    · subst hμ
      rw [tvSL_zero_smul_eq_one h', map_one]
      exact one_mem _
    · have hmv := hs.movedSpace_tvSL_smul_eq hc hα h hμ
      exact isLongRootElement_mem_piGroup (hs.siegel c (μ • α) h' hc (smul_ne_zero hμ hα))
        (hPA.trans hmv.ge) hmv.le
  have hμc : ∀ μ : K, (μ • α) ⬝ᵥ c = 0 := fun μ => by rw [smul_dotProduct, h, smul_zero]
  let f : K → piGroup Qf P A := fun μ => ⟨ρ (tvSL c (μ • α) (hμc μ)), hmem μ _⟩
  have hinj : Function.Injective f := by
    intro μ μ' hμμ'
    have h2 := hs.injOn_center c _ ⟨μ • α, hμc μ, rfl⟩ _ ⟨μ' • α, hμc μ', rfl⟩
      (congrArg Subtype.val hμμ')
    have h3 : (1 : Matrix (Fin m) (Fin m) K) + vecMulVec c (μ • α) =
        1 + vecMulVec c (μ' • α) := congrArg Subtype.val h2
    exact smul_left_injective K hα (vecMulVec_left_cancel hc (add_left_cancel h3))
  have hcard : Nat.card (piGroup Qf P A) = Nat.card K := by
    rw [natCard_piGroup hs.nondeg hAsing hP1 hPA, hAfin]
    simp
  have hfin : Finite (piGroup Qf P A) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcard.le
  have hs1 : s ≠ 1 := fun h1 => not_isLongRootElement_one hs.nondeg (h1 ▸ hs')
  have hsmem : s ∈ piGroup Qf P A :=
    (mem_piGroup_iff_of_ne_one hs.nondeg hAsing hP1 hPA hs1).mpr ⟨hs', hPA.trans hst.ge, hst.le⟩
  obtain ⟨μ, hμ⟩ := hbij.2 ⟨s, hsmem⟩
  have hμs : ρ (tvSL c (μ • α) (hμc μ)) = s := congrArg Subtype.val hμ
  refine ⟨μ, hμc μ, fun hμ0 => hs1 ?_, hμs.symm⟩
  rw [← hμs]
  subst hμ0
  rw [tvSL_zero_smul_eq_one, map_one]

theorem SLSetting.exists_isTransvection_eq (hs : SLSetting Qf ρ) {t : SL(m, K)}
    (ht : IsTransvection t) {s : V ≃ₗ[K] V} (hs' : IsLongRootElement Qf s)
    (hst : movedSpace s = movedSpace (ρ t)) :
    ∃ g : SL(m, K), IsTransvection g ∧ g * t = t * g ∧ ρ g = s := by
  have h3 := hs.three_le
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin m → K, c₀ ≠ 0 :=
    ⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, by omega⟩)⟩
  obtain ⟨α₀, hα₀, hα₀c, -⟩ := exists_ne_zero_dot_eq_zero_pair h3 c₀ c₀
  have ht₀ : IsTransvection (tvSL c₀ α₀ hα₀c) := isTransvection_of_coe hc₀ hα₀ hα₀c rfl
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection ht₀ ht
  obtain ⟨w, hw⟩ : ∃ w : V ≃ₗ[K] V, ρ W = w := ⟨_, rfl⟩
  have hhh : ∀ v, Qf (w⁻¹ v) = Qf v := fun v => by rw [← hw, ← map_inv]; exact hs.iso _ v
  have hρt : ρ t = w * ρ (tvSL c₀ α₀ hα₀c) * w⁻¹ := by
    rw [← hW, map_mul, map_mul, map_inv, hw]
  have hρt₀ : ρ (tvSL c₀ α₀ hα₀c) = w⁻¹ * ρ t * (w⁻¹)⁻¹ := by
    rw [hρt]; group
  have hmv : movedSpace (w⁻¹ * s * (w⁻¹)⁻¹) = movedSpace (ρ (tvSL c₀ α₀ hα₀c)) := by
    rw [hρt₀, movedSpace_conj, movedSpace_conj, hst]
  obtain ⟨μ, h', hμ, hseq⟩ := hs.exists_eq_tvSL_of_movedSpace_eq hc₀ hα₀ hα₀c
    ((isLongRootElement_conj_iff hhh).mpr hs') hmv
  refine ⟨W * tvSL c₀ (μ • α₀) h' * W⁻¹, ?_, ?_, ?_⟩
  · refine isTransvection_of_coe (mulVec_ne_zero' W hc₀)
      (vecMul_ne_zero' W⁻¹ (smul_ne_zero hμ hα₀)) ?_ (coe_conj_of_coe W (coe_tvSL h'))
    rw [← dotProduct_mulVec, inv_mulVec_mulVec', h']
  · have hx := tvCenterSL_comm (c := c₀) (tvSL c₀ (μ • α₀) h') ⟨μ • α₀, h', rfl⟩
      (tvSL c₀ α₀ hα₀c) ⟨α₀, hα₀c, rfl⟩
    calc _ = W * (tvSL c₀ (μ • α₀) h' * tvSL c₀ α₀ hα₀c) * W⁻¹ := by rw [← hW]; group
      _ = W * (tvSL c₀ α₀ hα₀c * tvSL c₀ (μ • α₀) h') * W⁻¹ := by rw [hx]
      _ = _ := by rw [← hW]; group
  · rw [map_mul, map_mul, map_inv, hw, ← hseq]
    group

end CFSG.ClassicalGroups.Orthogonal.SiegelSL
