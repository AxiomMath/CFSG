module

public import CFSG.LargeExtraspecial.S2Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

omit [FiniteDimensional (ZMod 2) M] in
theorem mem_fixOf_of_comm {ψ : M →ₗ[ZMod 2] M} (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v))
    {X : Set (V ≃ₗ[ZMod 2] V)} {v : M} (hv : v ∈ fixOf ρ X) : ψ v ∈ fixOf ρ X :=
  fun g hg => by rw [← hψ, hv g hg]

omit [FiniteDimensional (ZMod 2) M] in
theorem radDecomp_range {p p₁ : V}
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    {ψ : M →ₗ[ZMod 2] M} (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) :
    OmegaInvariant ρ ⊥ (LinearMap.range ψ) ∧ RadDecomp ρ ⊥ (LinearMap.range ψ) p p₁ := by
  refine ⟨fun g _ v hv => ?_, ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := hv
    exact ⟨ρ g w, hψ g w⟩
  · rw [radFix_bot, radFix_bot]
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) ⊔
        fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)) := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    exact Submodule.add_mem_sup ⟨⟨w₀, rfl⟩, mem_fixOf_of_comm ρ hψ hw₀⟩
      ⟨⟨w₁, rfl⟩, mem_fixOf_of_comm ρ hψ hw₁⟩
  · rw [radFix_bot, radFix_bot, eq_bot_iff]
    rintro v ⟨⟨-, hv₀⟩, -, hv₁⟩
    rw [← hc.inf_eq_bot]
    exact ⟨hv₀, hv₁⟩

theorem dvd_finrank_range {m : ℕ} (hm : 1 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    {ψ : M →ₗ[ZMod 2] M} (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) :
    2 ^ (m - 1) ∣ finrank (ZMod 2) (LinearMap.range ψ) := by
  have hperp : ∀ y : V, y ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun y => by
    rw [perp_bot]; exact Submodule.mem_top
  obtain ⟨hN, hD⟩ := radDecomp_range ρ hc hψ
  exact timmesfeld_2_1_b_dvd ρ m (bot_inf_eq _) hm (by rw [perp_bot, finrank_top]; exact hdim)
    hN (hperp p) (hperp p₁) hp0 hp hp₁ hpp₁ hD

omit [FiniteDimensional (ZMod 2) M] in
theorem range_pow_succ_eq {ψ : M →ₗ[ZMod 2] M}
    (h : LinearMap.range (ψ * ψ) = LinearMap.range ψ) (k : ℕ) :
    LinearMap.range (ψ ^ (k + 1)) = LinearMap.range ψ := by
  induction k with
  | zero => rw [zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp, ih, ← LinearMap.range_comp,
      ← Module.End.mul_eq_comp, h]

theorem sq_eq_zero_of_nilpotent {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hdimM : finrank (ZMod 2) M = 2 ^ m) {p p₁ : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    {ψ : M →ₗ[ZMod 2] M} (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) (hnil : ∃ k, ψ ^ k = 0)
    (hψ0 : ψ ≠ 0) :
    ψ * ψ = 0 ∧ LinearMap.range ψ = LinearMap.ker ψ ∧
      finrank (ZMod 2) (LinearMap.range ψ) = 2 ^ (m - 1) := by
  obtain ⟨k, hk⟩ := hnil
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [show m = (m - 1) + 1 by omega, pow_succ, mul_comm]; simp
  have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) _
  have h1 : LinearMap.range ψ ≠ ⊥ := fun h => hψ0 (LinearMap.range_eq_bot.mp h)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      rw [pow_zero] at hk
      have : (⊤ : Submodule (ZMod 2) M) = ⊥ := by
        rw [eq_bot_iff]; intro v _
        have := congrArg (fun f : M →ₗ[ZMod 2] M => f v) hk
        simpa using this
      have h0 : finrank (ZMod 2) (⊤ : Submodule (ZMod 2) M) = 0 := by rw [this, finrank_bot]
      rw [finrank_top, hdimM] at h0
      exact absurd h0 (pow_ne_zero _ (by norm_num))
    · exact h
  have hnot : LinearMap.range (ψ * ψ) ≠ LinearMap.range ψ := by
    intro h
    have := range_pow_succ_eq h (k - 1)
    rw [show k - 1 + 1 = k by omega, hk, LinearMap.range_zero] at this
    exact h1 this.symm
  have hd1 := dvd_finrank_range ρ (by omega) hdim hp0 hp hp₁ hpp₁ hc hψ
  have hψψ : ∀ g v, (ψ * ψ) (ρ g v) = ρ g ((ψ * ψ) v) := fun g v => by
    simp only [Module.End.mul_apply, hψ]
  have hd2 := dvd_finrank_range ρ (by omega) hdim hp0 hp hp₁ hpp₁ hc hψψ
  have hle : LinearMap.range (ψ * ψ) ≤ LinearMap.range ψ := by
    rw [Module.End.mul_eq_comp]; exact LinearMap.range_comp_le_range _ _
  have hlt : finrank (ZMod 2) (LinearMap.range ψ) < 2 ^ m := by
    rw [← hdimM]
    refine Submodule.finrank_lt (fun htop => ?_)
    have : LinearMap.range (ψ * ψ) = LinearMap.range ψ := by
      rw [Module.End.mul_eq_comp, LinearMap.range_comp, htop, Submodule.map_top]
      exact htop
    exact hnot this
  have hr1 : finrank (ZMod 2) (LinearMap.range ψ) = 2 ^ (m - 1) := by
    obtain ⟨c, hc'⟩ := hd1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero, Submodule.finrank_eq_zero] at hc'
      exact h1 hc'
    have : c < 2 := by
      by_contra h
      have : 2 ^ (m - 1) * 2 ≤ 2 ^ (m - 1) * c := Nat.mul_le_mul_left _ (by omega)
      omega
    obtain rfl : c = 1 := by omega
    rw [hc', mul_one]
  have hsq : ψ * ψ = 0 := by
    obtain ⟨c, hc'⟩ := hd2
    have hle' := Submodule.finrank_mono hle
    rw [hr1] at hle'
    rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · rw [mul_zero, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hc'
      exact hc'
    · exfalso
      apply hnot
      refine Submodule.eq_of_le_of_finrank_le hle ?_
      rw [hr1, hc']
      exact Nat.le_mul_of_pos_right _ hcpos
  have hrk : LinearMap.range ψ ≤ LinearMap.ker ψ := by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, hsq, LinearMap.zero_apply]
  have hker := LinearMap.finrank_range_add_finrank_ker ψ
  refine ⟨hsq, Submodule.eq_of_le_of_finrank_le hrk (by omega), hr1⟩

theorem eq_of_nilpotent {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hdimM : finrank (ZMod 2) M = 2 ^ m) {p p₁ : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    {ψ ψ' : M →ₗ[ZMod 2] M} (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v))
    (hψ' : ∀ g v, ψ' (ρ g v) = ρ g (ψ' v)) (hnil : ∃ k, ψ ^ k = 0) (hnil' : ∃ k, ψ' ^ k = 0)
    (hψ0 : ψ ≠ 0) (hψ'0 : ψ' ≠ 0) (hcomm : ψ * ψ' = ψ' * ψ) : ψ = ψ' := by
  obtain ⟨-, hrk, hr⟩ := sq_eq_zero_of_nilpotent ρ hm hdim hdimM hp0 hp hp₁ hpp₁ hc hψ hnil hψ0
  obtain ⟨hsq', hrk', hr'⟩ :=
    sq_eq_zero_of_nilpotent ρ hm hdim hdimM hp0 hp hp₁ hpp₁ hc hψ' hnil' hψ'0
  obtain ⟨hUinv, hUD⟩ := radDecomp_range ρ hc hψ
  have hperp : ∀ y : V, y ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun y => by
    rw [perp_bot]; exact Submodule.mem_top
  have hdimF : finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) = 2 * m := by
    rw [perp_bot, finrank_top]; exact hdim
  have hU' : ∀ v ∈ LinearMap.range ψ, ψ' v ∈ LinearMap.range ψ := by
    rintro _ ⟨w, rfl⟩
    exact ⟨ψ' w, by rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply]⟩
  obtain ⟨c, hcU⟩ := timmesfeld_2_6_1_omega ρ m (bot_inf_eq _) hm hdimF hUinv (hperp p)
    (hperp p₁) hp0 hp hp₁ hpp₁ hUD hr ψ' hU' (fun g _ v _ => hψ' g v)
  have hUne : LinearMap.range ψ ≠ ⊥ := fun h => hψ0 (LinearMap.range_eq_bot.mp h)
  have hc0 : c = 0 := by
    rcases zmod2_eq_zero_or_eq_one c with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
      have h1 : ψ' u = u := by rw [hcU u hu, h, one_smul]
      have h2 : ψ' (ψ' u) = 0 := by rw [← Module.End.mul_apply, hsq', LinearMap.zero_apply]
      rw [h1, h1] at h2
      exact hu0 h2
  have hUle : LinearMap.range ψ ≤ LinearMap.range ψ' := by
    intro u hu
    rw [hrk', LinearMap.mem_ker, hcU u hu, hc0, zero_smul]
  have hUeq : LinearMap.range ψ = LinearMap.range ψ' :=
    Submodule.eq_of_le_of_finrank_le hUle (by rw [hr, hr'])
  have hker : LinearMap.ker ψ ≤ LinearMap.ker ψ' := by rw [← hrk, ← hrk', hUeq]
  set χ₀ : ↥(LinearMap.range ψ) →ₗ[ZMod 2] M :=
    ((LinearMap.ker ψ).liftQ ψ' hker).comp ψ.quotKerEquivRange.symm.toLinearMap with hχ₀def
  have hχ₀ : ∀ w, χ₀ ⟨ψ w, ⟨w, rfl⟩⟩ = ψ' w := fun w => by
    rw [hχ₀def, LinearMap.comp_apply, LinearEquiv.coe_coe]
    erw [LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  obtain ⟨χ, hχ⟩ := LinearMap.exists_extend χ₀
  have hχψ : ∀ w, χ (ψ w) = ψ' w := fun w => by
    have := congrArg (fun f : ↥(LinearMap.range ψ) →ₗ[ZMod 2] M => f ⟨ψ w, ⟨w, rfl⟩⟩) hχ
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hχ₀]
  have hχU : ∀ v ∈ LinearMap.range ψ, χ v ∈ LinearMap.range ψ := by
    rintro _ ⟨w, rfl⟩
    rw [hχψ, hUeq]
    exact ⟨w, rfl⟩
  have hχc : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup ⊥ →
      ∀ v ∈ LinearMap.range ψ, χ (ρ g v) = ρ g (χ v) := by
    rintro g - _ ⟨w, rfl⟩
    rw [← hψ, hχψ, hχψ, hψ']
  obtain ⟨c', hc'⟩ := timmesfeld_2_6_1_omega ρ m (bot_inf_eq _) hm hdimF hUinv (hperp p)
    (hperp p₁) hp0 hp hp₁ hpp₁ hUD hr χ hχU hχc
  have hψc : ∀ w, ψ' w = c' • ψ w := fun w => by rw [← hχψ, hc' _ ⟨w, rfl⟩]
  rcases zmod2_eq_zero_or_eq_one c' with h | h
  · exfalso
    apply hψ'0
    ext w
    rw [hψc, h, zero_smul, LinearMap.zero_apply]
  · ext w
    rw [hψc, h, one_smul]

end CFSG.LargeExtraspecial.S14
