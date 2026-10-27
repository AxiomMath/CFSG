module

public import CFSG.LargeExtraspecial.OrthoF2Pairs
public import CFSG.LargeExtraspecial.OrthoF2Alt
public import CFSG.LargeExtraspecial.OrthoF2Radical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace OrthoF2

theorem mem_orthogonal_commSpace_iff (hq : q.polarBilin.Nondegenerate) {β : V ≃ₗ[ZMod 2] V}
    (hβO : β ∈ orthogonalGroup q) {x : V} :
    x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) ↔ β x = x := by
  rw [← fixSpace_eq_orthogonal_commSpace_of_mem hq hβO, mem_fixSpace]

theorem mem_orthogonal_iff_polar {U : Submodule (ZMod 2) V} {x : V} :
    x ∈ LinearMap.BilinForm.orthogonal q.polarBilin U ↔ ∀ u ∈ U, polar q x u = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun u _ => ?_
  rw [polarBilin_apply_apply, polar_comm]

theorem eq_of_commSpace_eq [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2)
    (h : commSpace α = commSpace β) : α = β := by
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  obtain ⟨t, -, huniq⟩ := existsUnique_of_totallySingular_finrank_two hq hα.2.2.2.2 hα.2.2.2.1
  have hfixα : ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace α), α x = x :=
    fun x hx => (mem_orthogonal_commSpace_iff hq hαO).mp hx
  have hfixβ : ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace α), β x = x :=
    fun x hx => (mem_orthogonal_commSpace_iff hq hβO).mp (h ▸ hx)
  exact (huniq α ⟨hαO, hα.2.1, le_rfl, hfixα⟩).trans
    (huniq β ⟨hβO, hβ.2.1, h.symm.le, hfixβ⟩).symm

theorem mul_sq_eq_one_iff {G : Type*} [Group G] {α β : G} (hαα : α * α = 1)
    (hββ : β * β = 1) : (α * β) ^ 2 = 1 ↔ α * β = β * α := by
  have hα : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hβ : β⁻¹ = β := inv_eq_of_mul_eq_one_right hββ
  rw [pow_two, mul_eq_one_iff_eq_inv, mul_inv_rev, hα, hβ]

theorem inf_orthogonal_eq_bot_of_scalar_one (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hβO : β ∈ orthogonalGroup q)
    (h1 : ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) =
      (α : V →ₗ[ZMod 2] V) - 1) :
    commSpace α ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨haA, haB⟩ := Submodule.mem_inf.mp ha
  obtain ⟨w, rfl⟩ := mem_commSpace.mp haA
  have hfix : β (α w - w) = α w - w := (mem_orthogonal_commSpace_iff hq hβO).mp haB
  have h := LinearMap.congr_fun h1 w
  simp only [Module.End.mul_apply, sub_one_apply] at h
  simp only [hfix, sub_self, map_zero] at h
  rw [Submodule.mem_bot, ← h]

theorem inf_orthogonal_ne_bot_of_scalar_zero [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβO : β ∈ orthogonalGroup q)
    (h2 : ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) =
      0) :
    commSpace α ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) ≠ ⊥ := by
  intro hbot
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hφψ : ∀ w, α (β w - w) = β w - w := by
    intro w
    have hmem : α (β w - w) - (β w - w) ∈
        commSpace α ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) := by
      refine Submodule.mem_inf.mpr ⟨sub_mem_commSpace α _, ?_⟩
      rw [mem_orthogonal_commSpace_iff hq hβO]
      have h := LinearMap.congr_fun h2 w
      simp only [Module.End.mul_apply, sub_one_apply, LinearMap.zero_apply] at h
      exact sub_eq_zero.mp h
    rw [hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hA : commSpace α ≤
      commSpace α ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) := by
    intro a ha
    refine Submodule.mem_inf.mpr ⟨ha, mem_orthogonal_iff_polar.mpr fun b hb => ?_⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hb
    have hb' := mem_orthogonal_iff_polar.mp ((mem_orthogonal_commSpace_iff hq hαO).mpr (hφψ w))
    rw [polar_comm]
    exact hb' a ha
  rw [hbot, le_bot_iff] at hA
  have h2' := hα.2.2.2.1
  rw [hA, finrank_bot] at h2'
  exact absurd h2' (by norm_num)

theorem commute_of_inf_ne_bot [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2)
    (h : commSpace α ⊓ commSpace β ≠ ⊥) : α * β = β * α := by
  by_cases hne : commSpace α = commSpace β
  · rw [eq_of_commSpace_eq hq hα hβ hne]
  · obtain ⟨p, x, y, -, -, -, -, -, -, -, hpx, hpy, -, -, rfl, rfl⟩ :=
      exists_eichler_of_isTypeA_pair hq hα hβ hne h
    rw [eichler_mul hpx hpy, eichler_mul hpy hpx, add_comm]

theorem commute_of_orthogonal [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hαO : α ∈ orthogonalGroup q) (hβO : β ∈ orthogonalGroup q)
    (horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0) : α * β = β * α := by
  have horth' : ∀ b ∈ commSpace β, ∀ a ∈ commSpace α, polar q b a = 0 := fun b hb a ha => by
    rw [polar_comm]
    exact horth a ha b hb
  refine LinearEquiv.ext fun v => ?_
  have h1 := sub_one_apply_sub_one_apply_eq_zero hq hαO horth v
  have h2 := sub_one_apply_sub_one_apply_eq_zero hq hβO horth' v
  rw [map_sub, sub_eq_zero, sub_eq_iff_eq_add] at h1 h2
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2]
  abel

theorem orthogonal_of_commute_of_inf_eq_bot [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hαO : α ∈ orthogonalGroup q)
    (hc : α * β = β * α) (hbot : commSpace α ⊓ commSpace β = ⊥) :
    ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0 := by
  intro a ha b hb
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hb
  have hmem : α (β w - w) - (β w - w) ∈ commSpace α ⊓ commSpace β := by
    refine Submodule.mem_inf.mpr ⟨sub_mem_commSpace α _, ?_⟩
    have e : α (β w - w) - (β w - w) = β (α w - w) - (α w - w) := by
      have hcw : α (β w) = β (α w) := LinearEquiv.congr_fun hc w
      rw [map_sub, map_sub, hcw]
      abel
    rw [e]
    exact sub_mem_commSpace β _
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
  have hb' := mem_orthogonal_iff_polar.mp ((mem_orthogonal_commSpace_iff hq hαO).mpr hmem)
  rw [polar_comm]
  exact hb' a ha

theorem fixSpace_inf_fixSpace_eq [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hαO : α ∈ orthogonalGroup q) (hβO : β ∈ orthogonalGroup q) :
    fixSpace α ⊓ fixSpace β =
      LinearMap.BilinForm.orthogonal q.polarBilin (commSpace α ⊔ commSpace β) := by
  rw [fixSpace_eq_orthogonal_commSpace_of_mem hq hαO,
    fixSpace_eq_orthogonal_commSpace_of_mem hq hβO, orthogonal_sup]

theorem commSpace_inf_fixSpace_eq_bot_of_pow_three {g : V ≃ₗ[ZMod 2] V} (h3 : g ^ 3 = 1) :
    commSpace g ⊓ fixSpace g = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxc, hxf⟩ := Submodule.mem_inf.mp hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hxc
  have hfix : g (g v - v) = g v - v := mem_fixSpace.mp hxf
  rw [map_sub] at hfix
  have hgg : g (g v) = v := by
    rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, vec_add_self, zero_sub, vec_neg] at hfix
    exact hfix
  have hv : g v = v := by
    have h := LinearEquiv.congr_fun h3 v
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgg] at h
    exact h
  rw [hv, sub_self]
  exact Submodule.zero_mem _

theorem commSpace_mul_of_inf_eq_bot [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hαO : α ∈ orthogonalGroup q)
    (hβO : β ∈ orthogonalGroup q) (hαα : α * α = 1) (hbot : commSpace α ⊓ commSpace β = ⊥) :
    fixSpace (α * β) = fixSpace α ⊓ fixSpace β ∧
      commSpace (α * β) = commSpace α ⊔ commSpace β := by
  have hfix : fixSpace (α * β) = fixSpace α ⊓ fixSpace β := by
    ext v
    rw [Submodule.mem_inf, mem_fixSpace, mem_fixSpace, mem_fixSpace, LinearEquiv.mul_apply]
    constructor
    · intro h
      have hβv : β v = α v := by
        have := congrArg α h
        rwa [apply_apply_of_mul_self hαα] at this
      have hmem : α v - v ∈ commSpace α ⊓ commSpace β :=
        Submodule.mem_inf.mpr ⟨sub_mem_commSpace α v, hβv ▸ sub_mem_commSpace β v⟩
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
      exact ⟨hmem, hβv.trans hmem⟩
    · rintro ⟨h1, h2⟩
      rw [h2, h1]
  refine ⟨hfix, ?_⟩
  have hle : commSpace (α * β) ≤ commSpace α ⊔ commSpace β := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    have e : (α * β) v - v = (α (β v) - β v) + (β v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [e]
    exact Submodule.add_mem_sup (sub_mem_commSpace α _) (sub_mem_commSpace β _)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 := finrank_commSpace_add_finrank_fixSpace (α * β)
  rw [hfix, fixSpace_inf_fixSpace_eq hq hαO hβO, LinearMap.BilinForm.finrank_orthogonal hq] at h1
  have h2 := Submodule.finrank_le (commSpace α ⊔ commSpace β)
  omega

end OrthoF2

theorem commute_iff_of_isTypeA [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2) :
    α * β = β * α ↔ commSpace α ⊓ commSpace β ≠ ⊥ ∨
      ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0 := by
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  constructor
  · intro hc
    by_cases h : commSpace α ⊓ commSpace β = ⊥
    · exact Or.inr (orthogonal_of_commute_of_inf_eq_bot hq hαO hc h)
    · exact Or.inl h
  · rintro (h | h)
    · exact commute_of_inf_ne_bot hq hα hβ h
    · exact commute_of_orthogonal hq hαO hβO h

theorem orderOf_mul_eq_one_iff_of_isTypeA [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) : orderOf (α * β) = 1 ↔ commSpace α = commSpace β := by
  rw [orderOf_eq_one_iff]
  constructor
  · intro h
    have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ.2.2.1
    rw [eq_inv_of_mul_eq_one_left h, hβinv]
  · intro h
    rw [eq_of_commSpace_eq hq hα hβ h]
    exact hβ.2.2.1

theorem orderOf_mul_dvd_two_iff_of_isTypeA [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) :
    orderOf (α * β) ∣ 2 ↔ commSpace α ⊓ commSpace β ≠ ⊥ ∨
      ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0 := by
  rw [orderOf_dvd_iff_pow_eq_one, mul_sq_eq_one_iff hα.2.2.1 hβ.2.2.1,
    commute_iff_of_isTypeA hq hα hβ]

theorem orderOf_mul_eq_three_iff_of_isTypeA [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) :
    orderOf (α * β) = 3 ↔
      commSpace α ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) = ⊥ := by
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  obtain ⟨d, h1, h2⟩ := exists_pair_scalar hq hα hβ
  rcases zmod2_eq_zero_or_eq_one d with rfl | rfl
  · rw [zero_smul] at h1 h2
    have h4 := mul_pow_four_eq_one_of_scalar_zero hα.2.2.1 hβ.2.2.1 h1 h2
    constructor
    · intro h3
      have := orderOf_dvd_of_pow_eq_one h4
      rw [h3] at this
      norm_num at this
    · intro hbot
      exact absurd hbot (inf_orthogonal_ne_bot_of_scalar_zero hq hα hβO h2)
  · rw [one_smul] at h1 h2
    have h3 := mul_pow_three_eq_one_of_scalar_one hα.2.2.1 hβ.2.2.1 h1 h2
    refine ⟨fun _ => inf_orthogonal_eq_bot_of_scalar_one hq hβO h1, fun hbot => ?_⟩
    have hne1 : orderOf (α * β) ≠ 1 := by
      rw [Ne, orderOf_mul_eq_one_iff_of_isTypeA hq hα hβ]
      intro heq
      rw [heq, inf_eq_left.mpr (le_orthogonal_of_totallySingular hβ.2.2.2.2)] at hbot
      have h2' := hβ.2.2.2.1
      rw [hbot, finrank_bot] at h2'
      exact absurd h2' (by norm_num)
    exact ((Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3)).resolve_left hne1

theorem orderOf_mul_eq_four_iff_of_isTypeA [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) :
    orderOf (α * β) = 4 ↔
      commSpace α ⊓ commSpace β = ⊥ ∧
        commSpace α ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) ≠ ⊥ ∧
        ∃ a ∈ commSpace α, ∃ b ∈ commSpace β, polar q a b ≠ 0 := by
  have h3 := orderOf_mul_eq_three_iff_of_isTypeA hq hα hβ
  have h2 := orderOf_mul_dvd_two_iff_of_isTypeA hq hα hβ
  constructor
  · intro h4
    have hn2 : ¬ orderOf (α * β) ∣ 2 := by rw [h4]; norm_num
    have hn3 : orderOf (α * β) ≠ 3 := by rw [h4]; norm_num
    rw [h2] at hn2
    rw [Ne, h3] at hn3
    obtain ⟨hb, hnot⟩ := not_or.mp hn2
    refine ⟨not_not.mp hb, hn3, ?_⟩
    by_contra hcon
    apply hnot
    intro a ha b hb
    by_contra hab
    exact hcon ⟨a, ha, b, hb, hab⟩
  · rintro ⟨hbot, hperp, a, ha, b, hb, hab⟩
    obtain ⟨hmem, -⟩ := aschbacher_3_7 hq hα hβ
    have hn3 : orderOf (α * β) ≠ 3 := fun h => hperp (h3.mp h)
    have hn2 : ¬ orderOf (α * β) ∣ 2 := fun h => by
      rcases h2.mp h with h' | h'
      · exact h' hbot
      · exact hab (h' a ha b hb)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> simp_all

theorem orderOf_mul_eq_two_iff_of_isTypeA [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) :
    orderOf (α * β) = 2 ↔ commSpace α ≠ commSpace β ∧ (commSpace α ⊓ commSpace β ≠ ⊥ ∨
      ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0) := by
  rw [← orderOf_mul_dvd_two_iff_of_isTypeA hq hα hβ, ne_eq,
    ← orderOf_mul_eq_one_iff_of_isTypeA hq hα hβ]
  constructor
  · intro h
    rw [h]
    norm_num
  · rintro ⟨h1, h2⟩
    have hpos : 0 < orderOf (α * β) := Nat.pos_of_dvd_of_pos h2 (by norm_num)
    have hle := Nat.le_of_dvd (by norm_num) h2
    omega

theorem finrank_fixSpace_inf_of_meet [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) (hne : commSpace α ≠ commSpace β)
    (hmeet : commSpace α ⊓ commSpace β ≠ ⊥) :
    finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) = 1 ∧
      finrank (ZMod 2) ↥(commSpace α ⊔ commSpace β) = 3 ∧
      finrank (ZMod 2) ↥(fixSpace α ⊓ fixSpace β) + 3 = finrank (ZMod 2) V := by
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  have hinf : finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) = 1 := by
    have h1 : 1 ≤ finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) :=
      Submodule.one_le_finrank_iff.mpr hmeet
    have h2 := Submodule.finrank_mono (inf_le_left : commSpace α ⊓ commSpace β ≤ commSpace α)
    rw [hα.2.2.2.1] at h2
    by_contra h3
    have h4 : finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) = 2 := by omega
    apply hne
    have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : commSpace α ⊓ commSpace β ≤ _)
      (by rw [h4, hα.2.2.2.1])
    have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : commSpace α ⊓ commSpace β ≤ _)
      (by rw [h4, hβ.2.2.2.1])
    rw [← e1, e2]
  have hsup : finrank (ZMod 2) ↥(commSpace α ⊔ commSpace β) = 3 := by
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
    rw [hinf, hα.2.2.2.1, hβ.2.2.2.1] at h2
    omega
  refine ⟨hinf, hsup, ?_⟩
  rw [fixSpace_inf_fixSpace_eq hq hαO hβO, LinearMap.BilinForm.finrank_orthogonal hq, hsup]
  have h3 := Submodule.finrank_le (commSpace α ⊔ commSpace β)
  omega

theorem isTypeA_mul_of_meet_of_orthogonal [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) (hne : commSpace α ≠ commSpace β) (hmeet : commSpace α ⊓ commSpace β ≠ ⊥)
    (horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0) :
    α * β = β * α ∧ IsTypeA q (α * β) 2 := by
  refine ⟨commute_of_inf_ne_bot hq hα hβ hmeet, ?_⟩
  obtain ⟨p, x, y, hp0, -, -, hxy, hqp, hqx, hqy, hpx, hpy, hspx, hspy, rfl, rfl⟩ :=
    exists_eichler_of_isTypeA_pair hq hα hβ hne hmeet
  have hxy0 : polar q x y = 0 :=
    horth x (by rw [hspx]; exact Submodule.subset_span (by simp)) y
      (by rw [hspy]; exact Submodule.subset_span (by simp))
  have hq1 : q (x + y) = 0 := by rw [map_add_eq, hqx, hqy, hxy0, add_zero, add_zero]
  have hpxy : polar q p (x + y) = 0 := by rw [polar_add_right, hpx, hpy, add_zero]
  rw [eichler_mul hpx hpy]
  exact (eichler_type_of_not_mem_span hq hp0 hqp hpxy hxy).2.1 hq1

theorem isTypeA_four_mul_of_inf_eq_bot [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) (hbot : commSpace α ⊓ commSpace β = ⊥)
    (horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0) :
    α * β = β * α ∧ IsTypeA q (α * β) 4 ∧ commSpace (α * β) = commSpace α ⊔ commSpace β := by
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  have hc := commute_of_orthogonal hq hαO hβO horth
  obtain ⟨-, hcomm⟩ := commSpace_mul_of_inf_eq_bot hq hαO hβO hα.2.2.1 hbot
  have hsup : finrank (ZMod 2) ↥(commSpace α ⊔ commSpace β) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
    rw [hbot, finrank_bot, hα.2.2.2.1, hβ.2.2.2.1] at h
    omega
  refine ⟨hc, ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (mul_mem hαO hβO) v,
    ?_, ?_, by rw [hcomm, hsup], ?_⟩, hcomm⟩
  · intro h1
    rw [h1, commSpace_one] at hcomm
    rw [← hcomm, finrank_bot] at hsup
    exact absurd hsup (by norm_num)
  · calc α * β * (α * β) = α * (β * α) * β := by simp only [mul_assoc]
      _ = α * (α * β) * β := by rw [hc]
      _ = 1 := by rw [← mul_assoc, hα.2.2.1, one_mul, hβ.2.2.1]
  · intro x hx
    rw [hcomm] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add_eq, hα.2.2.2.2 a ha, hβ.2.2.2.2 b hb, horth a ha b hb, add_zero, add_zero]

theorem commSpace_mul_of_orderOf_eq_three [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) (h3 : orderOf (α * β) = 3) :
    commSpace α ⊓ commSpace β = ⊥ ∧ commSpace (α * β) = commSpace α ⊔ commSpace β ∧
      finrank (ZMod 2) (commSpace (α * β)) = 4 ∧
      commSpace (α * β) ⊓
          LinearMap.BilinForm.orthogonal q.polarBilin (commSpace (α * β)) = ⊥ ∧
      fixSpace (α * β) = fixSpace α ⊓ fixSpace β := by
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  have hperp := (orderOf_mul_eq_three_iff_of_isTypeA hq hα hβ).mp h3
  have hbot : commSpace α ⊓ commSpace β = ⊥ := by
    rw [eq_bot_iff, ← hperp]
    exact inf_le_inf_left _ (le_orthogonal_of_totallySingular hβ.2.2.2.2)
  obtain ⟨hfix, hcomm⟩ := commSpace_mul_of_inf_eq_bot hq hαO hβO hα.2.2.1 hbot
  have hsup : finrank (ZMod 2) ↥(commSpace α ⊔ commSpace β) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
    rw [hbot, finrank_bot, hα.2.2.2.1, hβ.2.2.2.1] at h
    omega
  have hpow : (α * β) ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one _
  refine ⟨hbot, hcomm, by rw [hcomm, hsup], ?_, hfix⟩
  rw [← fixSpace_eq_orthogonal_commSpace_of_mem hq (mul_mem hαO hβO)]
  exact commSpace_inf_fixSpace_eq_bot_of_pow_three hpow

end CFSG.LargeExtraspecial
