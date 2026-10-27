module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard

public section

namespace CFSG.ABGTheoremB

open scoped commutatorElement

universe u

section Helpers

variable {X : Type*} [Group X]

private theorem commutatorElement_mul_mul_of_mem_center {a b z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at hz hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (b * w * z) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hz (b * w)]; group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hw a⁻¹]; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem map_commutator_eq_top_psl2 {F : Type} [Field F] [Finite F] (h3 : 3 < Nat.card F)
    (φ : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ) :
    (commutator X).map φ = ⊤ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hφ, ← commutator_def,
    (CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three F h3).commutator_eq_top]

private theorem commutator_inf_ker_eq_bot_psl2 [Finite X] {F : Type} [Field F] [Finite F]
    (hFodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (φ : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card φ.ker)) :
    commutator X ⊓ φ.ker = ⊥ := by
  have hEmap := map_commutator_eq_top_psl2 h3 φ hφ
  have hdecomp : ∀ x : X, ∃ e ∈ commutator X, e⁻¹ * x ∈ φ.ker := by
    intro x
    have hx : φ x ∈ (commutator X).map φ := hEmap ▸ Subgroup.mem_top _
    obtain ⟨e, he, hex⟩ := hx
    refine ⟨e, he, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hex, inv_mul_cancel]
  have hperf : ⁅commutator X, commutator X⁆ = commutator X := by
    refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
    conv_lhs => rw [commutator_def]
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨e₁, he₁, hk₁⟩ := hdecomp a
    obtain ⟨e₂, he₂, hk₂⟩ := hdecomp b
    have ha : a = e₁ * (e₁⁻¹ * a) := by group
    have hb : b = e₂ * (e₂⁻¹ * b) := by group
    rw [ha, hb, commutatorElement_mul_mul_of_mem_center (hcen hk₁) (hcen hk₂)]
    exact Subgroup.commutator_mem_commutator he₁ he₂
  have : Group.IsPerfect (commutator X) := Subgroup.isPerfect_iff.mpr hperf
  let ρ : commutator X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    φ.comp (commutator X).subtype
  have hρ : Function.Surjective ρ := by
    intro y
    have hy : y ∈ (commutator X).map φ := hEmap ▸ Subgroup.mem_top y
    obtain ⟨e, he, rfl⟩ := hy
    exact ⟨⟨e, he⟩, rfl⟩
  have hρker : ρ.ker ≤ Subgroup.center (commutator X) := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro e'
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcen he)) (e' : X))
  have hρodd : Odd (Nat.card ρ.ker) := by
    have hdvd : Nat.card ρ.ker ∣ Nat.card φ.ker := by
      have h := Subgroup.card_comap_dvd_of_injective φ.ker (commutator X).subtype
        (commutator X).subtype_injective
      rwa [MonoidHom.comap_ker] at h
    exact hodd.of_dvd_nat hdvd
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  have hF : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hp2 : ringChar F ≠ 2 := by
    intro h2
    rw [hF, h2] at hFodd
    exact (Nat.not_even_iff_odd.mpr hFodd) ((Nat.even_pow' n.ne_zero).mpr even_two)
  have hbot := (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel hp2 hF ρ hρ hρker
    hρodd).1 (hF ▸ h9)
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : commutator X) ∈ ρ.ker := hx.2
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

end Helpers

theorem psl2_odd_central_section {G : Type u} [Group G] [Finite G] :
    ∀ (M Z W : Subgroup G) (F : Type) [Field F] [Finite F], Z ≤ M → W ≤ Z →
      M ≤ Subgroup.normalizer (W : Set G) → Odd (Nat.card Z) → ⁅Z, M⁆ ≤ W →
      Odd (Nat.card F) → 3 < Nat.card F → Nat.card F ≠ 9 →
      (∃ ψ : M →* CFSG.GorensteinWalter.PSL2 F, Function.Surjective ψ ∧
        ψ.ker = Z.subgroupOf M) →
        ⁅M, M⁆ ⊓ Z ≤ W ∧ ⁅M, M⁆ ⊔ Z = M := by
  intro M Z W F _ _ hZM hWZ hMW hZodd hZW hFodd hF3 hF9 ⟨ψ, hψ, hψker⟩
  have hMM : ⁅M, M⁆ = (commutator M).map M.subtype := (Subgroup.map_subtype_commutator M).symm
  have hMtop := map_commutator_eq_top_psl2 hF3 ψ hψ
  refine ⟨?_, ?_⟩
  ·
    have hWM : W ≤ M := hWZ.trans hZM
    have : (W.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWM).mpr hMW
    have hWker : W.subgroupOf M ≤ ψ.ker := by
      rw [hψker]
      exact fun w hw => hWZ hw
    let φ : M ⧸ W.subgroupOf M →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      QuotientGroup.lift _ ψ hWker
    have hφ : Function.Surjective φ := by
      intro s
      obtain ⟨m, rfl⟩ := hψ s
      exact ⟨(m : M ⧸ W.subgroupOf M), rfl⟩
    have hφker : φ.ker = (Z.subgroupOf M).map (QuotientGroup.mk' (W.subgroupOf M)) := by
      rw [QuotientGroup.ker_lift, hψker]
    have hcen : φ.ker ≤ Subgroup.center (M ⧸ W.subgroupOf M) := by
      rw [hφker]
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
      have hc : ⁅(z : G), (m : G)⁆ ∈ W := hZW (Subgroup.commutator_mem_commutator hz m.2)
      have hc' : ⁅z, m⁆ ∈ W.subgroupOf M := by
        rw [Subgroup.mem_subgroupOf]
        simpa [commutatorElement_def] using hc
      have h1 : QuotientGroup.mk' (W.subgroupOf M) ⁅z, m⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hc'
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hodd : Odd (Nat.card φ.ker) := by
      rw [hφker]
      refine hZodd.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans ?_)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv]
    have hbot := commutator_inf_ker_eq_bot_psl2 hFodd hF3 hF9 φ hφ hcen hodd
    have hle : (commutator M).map (QuotientGroup.mk' (W.subgroupOf M)) ≤
        commutator (M ⧸ W.subgroupOf M) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    intro g hg
    have hg1 := hg.1
    rw [hMM] at hg1
    obtain ⟨m, hm, rfl⟩ := hg1
    have h3 : (m : M ⧸ W.subgroupOf M) ∈ commutator (M ⧸ W.subgroupOf M) ⊓ φ.ker := by
      refine ⟨hle ⟨m, hm, rfl⟩, ?_⟩
      rw [hφker]
      exact ⟨m, hg.2, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h3
    exact h3
  ·
    refine le_antisymm (sup_le ?_ hZM) fun m hm => ?_
    · rw [hMM]
      exact Subgroup.map_subtype_le _
    · have hx : ψ ⟨m, hm⟩ ∈ (commutator M).map ψ := hMtop ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hcm⟩ := hx
      have hk : c⁻¹ * ⟨m, hm⟩ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcm, inv_mul_cancel]
      rw [hψker, Subgroup.mem_subgroupOf] at hk
      have hcM : (c : G) ∈ ⁅M, M⁆ := by
        rw [hMM]
        exact ⟨c, hc, rfl⟩
      have : m = (c : G) * ((c⁻¹ * ⟨m, hm⟩ : M) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [this]
      exact Subgroup.mul_mem_sup hcM hk

end CFSG.ABGTheoremB
