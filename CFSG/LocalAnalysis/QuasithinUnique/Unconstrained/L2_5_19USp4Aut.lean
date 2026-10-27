module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Syl
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public section

namespace CFSG.QuasithinUnique.Id2519.USp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Basic

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def pointwiseStab (Kb : Subgroup (StatedProj (StatedSp 2 F))) :
    Subgroup (MulAut (StatedProj (StatedSp 2 F))) where
  carrier := {β | ∀ k ∈ Kb, β k = k}
  mul_mem' := fun {a b} ha hb k hk => by
    rw [MulAut.mul_apply, hb k hk, ha k hk]
  one_mem' := fun k _ => rfl
  inv_mem' := fun {a} ha k hk => by
    have h := ha k hk
    calc a⁻¹ k = a⁻¹ (a k) := by rw [h]
      _ = k := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

omit [Finite F] [CharP F 2] in
theorem mem_pointwiseStab {Kb : Subgroup (StatedProj (StatedSp 2 F))}
    {β : MulAut (StatedProj (StatedSp 2 F))} :
    β ∈ pointwiseStab Kb ↔ ∀ k ∈ Kb, β k = k := Iff.rfl

omit [Finite F] in
theorem eq_one_of_central {p : StatedProj (StatedSp 2 F)} (hp : ∀ q, p * q = q * p) : p = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
  have h1 : spInner 2 F g = 1 := by
    rw [spInner_eq_conj]
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply]
    simp [hp x]
  have h2 : spInner 2 F g = spInner 2 F 1 := by rw [h1, map_one]
  rw [spInner_injective h2, map_one]

omit [Finite F] in
theorem eq_one_of_commute_proj_aS_bS {q : StatedProj (StatedSp 2 F)}
    (ha : q * proj 2 F aS = proj 2 F aS * q) (hb : q * proj 2 F bS = proj 2 F bS * q) : q = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) q
  rw [← map_mul, ← map_mul] at ha hb
  have h := eq_one_of_commute_aS_bS (UnitaryHigher.proj_bijective_of_charTwo.1 ha)
    (UnitaryHigher.proj_bijective_of_charTwo.1 hb)
  rw [h, map_one]

end Basic

section AutFacts

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem aut_facts (hF : Nat.card F = 4) :
    (∀ α : MulAut (StatedProj (StatedSp 2 F)), orderOf α = 2 → α ∈ spSemilinearAutGroup 2 F) ∧
    (spSemilinearAutGroup 2 F).index = 2 ∧ exceptionalAut F ∉ spSemilinearAutGroup 2 F := by
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hrest⟩ :=
    even_symplectic_two_exterior_square_automorphism (f := 2) (by norm_num) hF'
  obtain ⟨-, -, hγE, -, -, -, -, -, -, -, hev, -⟩ := hrest γ hγ
  have hγeq : γ = exceptionalAut F := eq_exceptionalAut hγ
  rw [hγeq] at hγE
  refine ⟨hev (by norm_num), ?_, hγE⟩
  obtain ⟨-, -, -, hEi⟩ := CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation
    (K := F)
  have h0 : (spSemilinearAutGroup 2 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (spSemilinearAutGroup 2 F).index ≠ 1 := by
    intro h
    apply hγE
    rw [Subgroup.index_eq_one.mp h]
    exact Subgroup.mem_top _
  omega

@[expose] noncomputable def t₀ (F : Type) [Field F] : StatedSp 2 F :=
  upperUnipotentSp 2 F (transpose_single_zero_zero (K := F))

theorem not_fixes_of_not_mem_E (hF : Nat.card F = 4)
    {β : MulAut (StatedProj (StatedSp 2 F))} (hβ : β ∉ spSemilinearAutGroup 2 F) :
    β (proj 2 F (t₀ F)) ≠ proj 2 F (t₀ F) := by
  obtain ⟨-, hEidx, hγ⟩ := aut_facts hF
  intro hfix
  have h1 : β * (exceptionalAut F)⁻¹ ∈ spSemilinearAutGroup 2 F := by
    rw [Subgroup.mul_mem_iff_of_index_two hEidx]
    exact ⟨fun h => absurd h hβ, fun h => absurd (by simpa using inv_mem h) hγ⟩
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut (inv_mem h1)
  have hinvfix : β⁻¹ (proj 2 F (t₀ F)) = proj 2 F (t₀ F) := by
    calc β⁻¹ (proj 2 F (t₀ F)) = β⁻¹ (β (proj 2 F (t₀ F))) := by rw [hfix]
      _ = proj 2 F (t₀ F) := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have h3 : (β * (exceptionalAut F)⁻¹)⁻¹ (proj 2 F (t₀ F)) =
      exceptionalAut F (proj 2 F (t₀ F)) := by
    rw [_root_.mul_inv_rev, inv_inv, MulAut.mul_apply, hinvfix]
  rw [hgφ, spInner_mul_fieldAut_proj, t₀, exceptionalAut_proj, exceptionalSpAut_upperUnipotent] at h3
  have h4 := UnitaryHigher.proj_bijective_of_charTwo.1 h3
  have h5 := displacementInLine_conj g (upperUnipotentSp 2 F (transpose_single_zero_zero (K := F))) φ
    displacementInLine_upperUnipotent
  rw [h4] at h5
  exact not_displacementInLine_upperUnipotent_swap h5

@[expose] def fixedSub {M : Type*} [Group M] (α : MulAut M) : Subgroup M where
  carrier := {p | α p = p}
  mul_mem' := fun {a b} ha hb => by
    change α (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' := fun {a} ha => by
    change α a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixedSub {M : Type*} [Group M] {α : MulAut M} {p : M} : p ∈ fixedSub α ↔ α p = p :=
  Iff.rfl

theorem card_fixedSub_fieldAut (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) :
    Nat.card (fixedSub (fieldAut 2 F σ)) = 720 := by
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  obtain ⟨-, -, hk⟩ := ringEquiv_involution_facts (f := 2) (by norm_num) hF' hσσ hσ1
  set k := descentField σ with hkdef
  have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
  let Φ : StatedSp 2 k →* StatedProj (StatedSp 2 F) := (proj 2 F).comp (subfieldSpHom 2 k)
  have hΦinj : Function.Injective Φ :=
    UnitaryHigher.proj_bijective_of_charTwo.1.comp (subfieldSpHom_injective k)
  have hrange : fixedSub (fieldAut 2 F σ) = Φ.range := by
    ext p
    constructor
    · intro hp
      obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
      rw [mem_fixedSub, fieldAut_proj] at hp
      have hg : fieldSp 2 F σ g = g := UnitaryHigher.proj_bijective_of_charTwo.1 hp
      obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq hg
      refine ⟨g₀, ?_⟩
      change proj 2 F (subfieldSpHom 2 (descentField σ) g₀) = proj 2 F g
      rw [hg₀]
    · rintro ⟨g₀, rfl⟩
      rw [mem_fixedSub]
      simp only [Φ, MonoidHom.comp_apply]
      rw [fieldAut_proj, fieldSp_subfieldSpHom]
  rw [hrange, Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv.symm, SymplecticFlag.card_statedSp,
    hk2]
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

section IndexTwo

variable {M : Type*} [Group M] [Finite M] {N Kb : Subgroup M}

theorem index_subgroupOf_eq_two_of_card (hle : Kb ≤ N) (hK : Nat.card Kb * 2 = Nat.card N) :
    (Kb.subgroupOf N).index = 2 := by
  have h1 := Subgroup.card_mul_index (Kb.subgroupOf N)
  have h2 : Nat.card (Kb.subgroupOf N) = Nat.card Kb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hpos : 0 < Nat.card Kb := Nat.card_pos
  rw [h2] at h1
  have : Nat.card Kb * (Kb.subgroupOf N).index = Nat.card Kb * 2 := by rw [h1, hK]
  exact Nat.eq_of_mul_eq_mul_left hpos this

omit [Finite M] in
theorem mem_of_odd_pow_eq_one (hidx : (Kb.subgroupOf N).index = 2) {x : M}
    (hx : x ∈ N) {n : ℕ} (hn : x ^ (2 * n + 1) = 1) : x ∈ Kb := by
  have h1 := Subgroup.sq_mem_of_index_two hidx (⟨x ^ (n + 1), N.pow_mem hx _⟩ : N)
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (x ^ (n + 1)) ^ 2 = x := by
    calc (x ^ (n + 1)) ^ 2 = x ^ (2 * n + 1) * x := by rw [← pow_mul, ← pow_succ]; ring_nf
      _ = x := by rw [hn, one_mul]
  simpa [h2] using h1

omit [Finite M] in
theorem conj_mem_of_index_two (hle : Kb ≤ N) (hidx : (Kb.subgroupOf N).index = 2) {n : M}
    (hn : n ∈ N) {κ : M} (hκ : κ ∈ Kb) : n * κ * n⁻¹ ∈ Kb := by
  have : (Kb.subgroupOf N).Normal := Subgroup.normal_of_index_eq_two hidx
  have h1 := this.conj_mem ⟨κ, hle hκ⟩ (by simpa [Subgroup.mem_subgroupOf] using hκ) ⟨n, hn⟩
  simpa [Subgroup.mem_subgroupOf] using h1

end IndexTwo

omit [Finite F] in
theorem fieldSp_aS (φ : F ≃+* F) : fieldSp 2 F φ (aS : StatedSp 2 F) = aS :=
  Subtype.ext (Units.ext (by
    change (spMat (aS : StatedSp 2 F)).map φ = spMat (aS : StatedSp 2 F)
    exact map_aMat φ.toRingHom))

omit [Finite F] in
theorem fieldSp_bS (φ : F ≃+* F) : fieldSp 2 F φ (bS : StatedSp 2 F) = bS :=
  Subtype.ext (Units.ext (by
    change (spMat (bS : StatedSp 2 F)).map φ = spMat (bS : StatedSp 2 F)
    exact map_bMat φ.toRingHom))

omit [Finite F] [CharP F 2] in
theorem fieldSp_t₀ (φ : F ≃+* F) : fieldSp 2 F φ (t₀ F) = t₀ F := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change φ (spMat (t₀ F) i j) = spMat (t₀ F) i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [t₀, spMat, coe_upperUnipotentSp]

omit [Finite F] [CharP F 2] in
theorem card_ringEquiv_eq_two (hF : Nat.card F = 4) : Nat.card (F ≃+* F) = 2 := by
  obtain ⟨_, -, -, -, h, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two
    (n := 2) (by norm_num) (by rw [hF]; norm_num : Nat.card F = 2 ^ 2)
  exact h

omit [Finite F] [CharP F 2] in
theorem eq_one_or_eq_of_ne_one (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ : σ ≠ 1)
    (φ : F ≃+* F) : φ = 1 ∨ φ = σ := by
  obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp (card_ringEquiv_eq_two hF)
  by_cases hφ1 : φ = 1
  · exact Or.inl hφ1
  · exact Or.inr ((hyu φ hφ1).trans (hyu σ hσ).symm)

theorem pointwiseStab_subset_of_fix (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) {Kb : Subgroup (StatedProj (StatedSp 2 F))} (hKb : Nat.card Kb = 360)
    (hfix : ∀ k ∈ Kb, fieldAut 2 F σ k = k) :
    ∀ β ∈ pointwiseStab Kb, β = 1 ∨ β = fieldAut 2 F σ := by
  obtain ⟨hinvol, hEidx, -⟩ := aut_facts hF
  have hN : Nat.card (fixedSub (fieldAut 2 F σ)) = 720 := card_fixedSub_fieldAut hF hσ1 hσσ
  have hle : Kb ≤ fixedSub (fieldAut 2 F σ) := fun k hk => hfix k hk
  have hidx : (Kb.subgroupOf (fixedSub (fieldAut 2 F σ))).index = 2 :=
    index_subgroupOf_eq_two_of_card hle (by rw [hKb, hN])
  have haN : proj 2 F aS ∈ fixedSub (fieldAut 2 F σ) := by
    rw [mem_fixedSub, fieldAut_proj, fieldSp_aS]
  have hbN : proj 2 F bS ∈ fixedSub (fieldAut 2 F σ) := by
    rw [mem_fixedSub, fieldAut_proj, fieldSp_bS]
  have haK : proj 2 F aS ∈ Kb := by
    refine mem_of_odd_pow_eq_one hidx haN (n := 1) ?_
    rw [← map_pow, show 2 * 1 + 1 = 3 by norm_num, aS_pow_three, map_one]
  have hbK : proj 2 F bS ∈ Kb := by
    refine mem_of_odd_pow_eq_one hidx hbN (n := 2) ?_
    rw [← map_pow, show 2 * 2 + 1 = 5 by norm_num, bS_pow_five, map_one]
  have hC : ∀ q : StatedProj (StatedSp 2 F), (∀ k ∈ Kb, q * k = k * q) → q = 1 :=
    fun q hq => eq_one_of_commute_proj_aS_bS (hq _ haK) (hq _ hbK)
  have hφ : ∀ φ : F ≃+* F, φ = 1 ∨ φ = σ := eq_one_or_eq_of_ne_one hF hσ1
  have hE : ∀ β ∈ pointwiseStab Kb, β ∈ spSemilinearAutGroup 2 F → β = 1 ∨ β = fieldAut 2 F σ := by
    intro β hβ hβE
    obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hβE
    have h1 : g * aS * g⁻¹ = aS := by
      have := hβ _ haK
      rw [spInner_mul_fieldAut_proj, fieldSp_aS] at this
      exact UnitaryHigher.proj_bijective_of_charTwo.1 this
    have h2 : g * bS * g⁻¹ = bS := by
      have := hβ _ hbK
      rw [spInner_mul_fieldAut_proj, fieldSp_bS] at this
      exact UnitaryHigher.proj_bijective_of_charTwo.1 this
    have hg : g = 1 := by
      refine eq_one_of_commute_aS_bS ?_ ?_
      · calc g * aS = (g * aS * g⁻¹) * g := by group
          _ = aS * g := by rw [h1]
      · calc g * bS = (g * bS * g⁻¹) * g := by group
          _ = bS * g := by rw [h2]
    subst hg
    rw [map_one, one_mul]
    rcases hφ φ with rfl | rfl
    · left
      rw [map_one]
    · right
      rfl
  intro β hβ
  by_cases hβE : β ∈ spSemilinearAutGroup 2 F
  · exact hE β hβ hβE
  · exfalso
    have hβ2E : β ^ 2 ∈ spSemilinearAutGroup 2 F := Subgroup.sq_mem_of_index_two hEidx β
    have hβ2 : β ^ 2 ∈ pointwiseStab Kb := pow_mem hβ 2
    rcases hE (β ^ 2) hβ2 hβ2E with h2 | h2
    · have hne1 : β ≠ 1 := fun h => hβE (h ▸ one_mem _)
      have hord : orderOf β = 2 := orderOf_eq_prime h2 hne1
      exact hβE (hinvol β hord)
    · have hcomm : β * fieldAut 2 F σ = fieldAut 2 F σ * β := by
        rw [← h2]
        group
      have hfixN : ∀ n ∈ fixedSub (fieldAut 2 F σ), β n = n := by
        intro n hn
        have hβn : β n ∈ fixedSub (fieldAut 2 F σ) := by
          rw [mem_fixedSub]
          have h3 : (fieldAut 2 F σ * β) n = (β * fieldAut 2 F σ) n := by rw [hcomm]
          rw [MulAut.mul_apply, MulAut.mul_apply, mem_fixedSub.mp hn] at h3
          exact h3
        have hq : n⁻¹ * β n = 1 := by
          refine hC _ fun κ hκ => ?_
          have h4 : β (n * κ * n⁻¹) = n * κ * n⁻¹ := hβ _ (conj_mem_of_index_two hle hidx hn hκ)
          rw [map_mul, map_mul, map_inv, hβ κ hκ] at h4
          calc n⁻¹ * β n * κ = n⁻¹ * (β n * κ * (β n)⁻¹) * β n := by group
            _ = n⁻¹ * (n * κ * n⁻¹) * β n := by rw [h4]
            _ = κ * (n⁻¹ * β n) := by group
        calc β n = n * (n⁻¹ * β n) := by group
          _ = n := by rw [hq, mul_one]
      have h0 : proj 2 F (t₀ F) ∈ fixedSub (fieldAut 2 F σ) := by
        rw [mem_fixedSub, fieldAut_proj, fieldSp_t₀]
      exact not_fixes_of_not_mem_E hF hβE (hfixN _ h0)

theorem card_pointwiseStab_le_two_of_fix (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) {Kb : Subgroup (StatedProj (StatedSp 2 F))} (hKb : Nat.card Kb = 360)
    (hfix : ∀ k ∈ Kb, fieldAut 2 F σ k = k) : Nat.card (pointwiseStab Kb) ≤ 2 := by
  have h := pointwiseStab_subset_of_fix hF hσ1 hσσ hKb hfix
  have hsub : (pointwiseStab Kb : Set (MulAut (StatedProj (StatedSp 2 F)))) ⊆
      {1, fieldAut 2 F σ} := fun β hβ => by
    rcases h β hβ with rfl | rfl <;> simp
  calc Nat.card (pointwiseStab Kb)
      = (pointwiseStab Kb : Set (MulAut (StatedProj (StatedSp 2 F)))).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, fieldAut 2 F σ} : Set (MulAut (StatedProj (StatedSp 2 F)))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]

theorem not_mem_inner_of_fix (hF : Nat.card F = 4) {Kb : Subgroup (StatedProj (StatedSp 2 F))}
    (h9 : 9 ∣ Nat.card Kb) {τ : MulAut (StatedProj (StatedSp 2 F))}
    (hτ : ∀ k ∈ Kb, τ k = k) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) : τ ∉ inner (StatedProj (StatedSp 2 F)) := by
  rintro ⟨s, rfl⟩
  apply hτ1
  have hs2 : s ^ 2 = 1 := by
    refine eq_one_of_central fun q => ?_
    have h1 : MulAut.conj (s ^ 2) = 1 := by rw [map_pow, sq]; exact hτ2
    have h2 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 F)) => α q) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc s ^ 2 * q = (s ^ 2 * q * (s ^ 2)⁻¹) * s ^ 2 := by group
      _ = q * s ^ 2 := by rw [h2]
  have hcomm : ∀ k ∈ Kb, s * k = k * s := by
    intro k hk
    have h1 := hτ k hk
    simp only [MulAut.conj_apply] at h1
    calc s * k = (s * k * s⁻¹) * s := by group
      _ = k * s := by rw [h1]
  have hs1 : s = 1 := eq_one_of_centralizes_of_nine_dvd hF h9 hs2 hcomm
  rw [hs1, map_one]

theorem exists_conj_fieldAut (hF : Nat.card F = 4) {τ : MulAut (StatedProj (StatedSp 2 F))}
    (hτ2 : τ * τ = 1) (hτ : τ ∉ inner (StatedProj (StatedSp 2 F)))
    (hE : τ ∈ spSemilinearAutGroup 2 F) :
    ∃ (σ : F ≃+* F) (h : StatedSp 2 F), σ ≠ 1 ∧ σ * σ = 1 ∧
      τ = spInner 2 F h * fieldAut 2 F σ * (spInner 2 F h)⁻¹ := by
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut hE
  have hφ : φ ≠ 1 := by
    rintro rfl
    apply hτ
    rw [hgφ, map_one, mul_one]
    exact spInner_mem_inner g
  have hφφ : φ * φ = 1 := by
    have h1 := hτ2
    rw [hgφ, spInner_mul_fieldAut_mul, show (1 : MulAut (StatedProj (StatedSp 2 F))) =
      spInner 2 F 1 * fieldAut 2 F 1 by rw [map_one, map_one, one_mul]] at h1
    exact (spInner_mul_fieldAut_inj h1).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, hh⟩ :=
    even_symplectic_quadratic_involution_descent (r := 2) (f := 2) (by norm_num) (by norm_num) hF'
      hτ2 g φ hgφ hφ
  exact ⟨φ, h, hφ, hφφ, hh⟩

theorem card_pointwiseStab_le_two (hF : Nat.card F = 4)
    {Kb : Subgroup (StatedProj (StatedSp 2 F))} (hKb : Nat.card Kb = 360)
    {τ : MulAut (StatedProj (StatedSp 2 F))} (hτ : τ ∈ pointwiseStab Kb) (hτ2 : τ * τ = 1)
    (hτ1 : τ ≠ 1) : Nat.card (pointwiseStab Kb) ≤ 2 := by
  obtain ⟨hinvol, -, -⟩ := aut_facts hF
  have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  have hnot := not_mem_inner_of_fix hF (by rw [hKb]; norm_num) hτ hτ2 hτ1
  obtain ⟨σ, h, hσ1, hσσ, hτh⟩ := exists_conj_fieldAut hF hτ2 hnot (hinvol τ hord)
  set c := spInner 2 F h with hc
  let Kb₀ : Subgroup (StatedProj (StatedSp 2 F)) := Kb.map (c⁻¹ : MulAut _).toMonoidHom
  have hKb₀ : Nat.card Kb₀ = 360 := by
    rw [← hKb]
    exact Subgroup.card_map_of_injective (c⁻¹ : MulAut _).injective
  have hfix₀ : ∀ k ∈ Kb₀, fieldAut 2 F σ k = k := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : fieldAut 2 F σ = c⁻¹ * τ * c := by rw [hτh]; group
    have h2 : (fieldAut 2 F σ) ((c⁻¹ : MulAut _) k) = (c⁻¹ : MulAut _) k := by
      rw [h1, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hτ k hk]
    exact h2
  have hle := card_pointwiseStab_le_two_of_fix hF hσ1 hσσ hKb₀ hfix₀
  have hmem : ∀ β : pointwiseStab Kb, c⁻¹ * (β : MulAut _) * c ∈ pointwiseStab Kb₀ := by
    intro β
    rintro _ ⟨k, hk, rfl⟩
    have h3 : (c⁻¹ * (β : MulAut (StatedProj (StatedSp 2 F))) * c :
        MulAut (StatedProj (StatedSp 2 F))) ((c⁻¹ : MulAut (StatedProj (StatedSp 2 F))) k) =
        (c⁻¹ : MulAut (StatedProj (StatedSp 2 F))) k := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, β.2 k hk]
    exact h3
  refine le_trans (Nat.card_le_card_of_injective
    (fun β : pointwiseStab Kb => (⟨c⁻¹ * (β : MulAut _) * c, hmem β⟩ : pointwiseStab Kb₀)) ?_) hle
  intro β β' hββ'
  have h4 : c⁻¹ * (β : MulAut _) * c = c⁻¹ * (β' : MulAut _) * c := congrArg Subtype.val hββ'
  apply Subtype.ext
  have h5 := congrArg (fun x => c * x * c⁻¹) h4
  simpa [mul_assoc] using h5

end AutFacts

end CFSG.QuasithinUnique.Id2519.USp4
