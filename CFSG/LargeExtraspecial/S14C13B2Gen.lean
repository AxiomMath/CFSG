module

public import CFSG.LargeExtraspecial.S14C13B2Str
public import CFSG.LargeExtraspecial.S14C13B2Tv
public import CFSG.LargeExtraspecial.S14C13B2Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2 CFSG.LargeExtraspecial.S2

theorem exists_mem_comm_mem_of_lt {X : Type*} [Group X] [Finite X] {F N : Subgroup X}
    (hNF : N ≤ F) (hne : N ≠ F) (hN : ∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hF : IsPGroup 2 F) : ∃ α ∈ F, α ∉ N ∧ ∀ β ∈ F, α * β * α⁻¹ * β⁻¹ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α₀, hα₀F, hα₀N⟩ : ∃ α ∈ F, α ∉ N := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hNF h)
  have hN'n : (N.subgroupOf F).Normal := ⟨fun n hn c => by
    rw [mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hN c c.2 n hn⟩
  have hP : IsPGroup 2 (F ⧸ N.subgroupOf F) := hF.to_quotient _
  have hnt : Nontrivial (F ⧸ N.subgroupOf F) := ⟨⟨QuotientGroup.mk ⟨α₀, hα₀F⟩, 1, fun h =>
    hα₀N (by
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h
      exact h)⟩⟩
  have : Nontrivial (center (F ⧸ N.subgroupOf F)) := hP.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : center (F ⧸ N.subgroupOf F))
  obtain ⟨α, hα⟩ := QuotientGroup.mk_surjective (z : F ⧸ N.subgroupOf F)
  refine ⟨α, α.2, fun h => hz1 (Subtype.ext ?_), fun β hβ => ?_⟩
  · rw [← hα, OneMemClass.coe_one, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact h
  · have hzc := mem_center_iff.mp z.2 (QuotientGroup.mk ⟨β, hβ⟩)
    have h1 : (QuotientGroup.mk (α * ⟨β, hβ⟩ * α⁻¹ * (⟨β, hβ⟩ : F)⁻¹) :
        F ⧸ N.subgroupOf F) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hα, ← hzc]
      group
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1

section Psi

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

omit [FiniteDimensional (ZMod 2) M] in
theorem sub_one_comm_of_comm {f : Module.End (ZMod 2) M}
    (hf : ∀ g v, f (ρ g v) = ρ g (f v)) : ∀ g v, (f - 1) (ρ g v) = ρ g ((f - 1) v) := by
  intro g v
  rw [LinearMap.sub_apply, LinearMap.sub_apply, hf, Module.End.one_apply,
    Module.End.one_apply, map_sub]

omit [FiniteDimensional (ZMod 2) M] in
theorem sub_one_pow_eq_zero {f : Module.End (ZMod 2) M} {k : ℕ} (hf : f ^ (2 ^ k) = 1) :
    (f - 1) ^ (2 ^ k) = 0 := by
  rw [sub_one_pow_two_pow, hf, sub_self]

omit [FiniteDimensional (ZMod 2) M] in
theorem sub_one_mul_comm {f f' : Module.End (ZMod 2) M} (h : f * f' = f' * f) :
    (f - 1) * (f' - 1) = (f' - 1) * (f - 1) := by
  simp only [sub_mul, mul_sub, mul_one, one_mul]
  rw [h]
  abel

theorem psi_data {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hdimM : finrank (ZMod 2) M = 2 ^ m) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    {f : Module.End (ZMod 2) M} (hf : ∀ g v, f (ρ g v) = ρ g (f v)) {k : ℕ}
    (hfk : f ^ (2 ^ k) = 1) (hf1 : f ≠ 1) :
    (f - 1) * (f - 1) = 0 ∧ LinearMap.range (f - 1) = LinearMap.ker (f - 1) ∧
      finrank (ZMod 2) (LinearMap.range (f - 1)) = 2 ^ (m - 1) :=
  sq_eq_zero_of_nilpotent ρ hm hdim hdimM hp0 hp hp₁ hpp₁ hc (sub_one_comm_of_comm ρ hf)
    ⟨_, sub_one_pow_eq_zero hfk⟩ (fun h => hf1 (sub_eq_zero.mp h))

theorem psi_unique {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hdimM : finrank (ZMod 2) M = 2 ^ m) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    {f f' : Module.End (ZMod 2) M} (hf : ∀ g v, f (ρ g v) = ρ g (f v))
    (hf' : ∀ g v, f' (ρ g v) = ρ g (f' v)) {k k' : ℕ} (hfk : f ^ (2 ^ k) = 1)
    (hfk' : f' ^ (2 ^ k') = 1) (hf1 : f ≠ 1) (hf1' : f' ≠ 1) (hcomm : f * f' = f' * f) :
    f - 1 = f' - 1 :=
  eq_of_nilpotent ρ hm hdim hdimM hp0 hp hp₁ hpp₁ hc (sub_one_comm_of_comm ρ hf)
    (sub_one_comm_of_comm ρ hf') ⟨_, sub_one_pow_eq_zero hfk⟩ ⟨_, sub_one_pow_eq_zero hfk'⟩
    (fun h => hf1 (sub_eq_zero.mp h)) (fun h => hf1' (sub_eq_zero.mp h)) (sub_one_mul_comm hcomm)

omit [FiniteDimensional (ZMod 2) M] in
theorem psi_comm_of_conj {f u u' : Module.End (ZMod 2) M} (h1 : u * u' = 1) (h2 : u' * u = 1)
    (heq : f - 1 = u * f * u' - 1) : u * (f - 1) = (f - 1) * u := by
  have e : u * f * u' - 1 = u * (f - 1) * u' := by
    rw [mul_sub, sub_mul, mul_one, h1]
  calc u * (f - 1) = u * (f - 1) * (u' * u) := by rw [h2, mul_one]
    _ = (u * (f - 1) * u') * u := by simp only [mul_assoc]
    _ = (f - 1) * u := by rw [← e, ← heq]

end Psi

section Restrict

variable {G' : Type*} [Group G'] {X : Subgroup G'}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

@[expose] noncomputable def restrictRep (ρ : X →* (M ≃ₗ[ZMod 2] M))
    (U : Submodule (ZMod 2) M) (hU : ∀ x, ∀ v ∈ U, ρ x v ∈ U) : X →* (U ≃ₗ[ZMod 2] U) where
  toFun x := S2.restrictOfMapsTo (ρ x) U (hU x)
  map_one' := LinearEquiv.ext fun v => Subtype.ext (by
    rw [S2.restrictOfMapsTo_apply, map_one]
    rfl)
  map_mul' x y := LinearEquiv.ext fun v => Subtype.ext (by
    rw [S2.restrictOfMapsTo_apply, map_mul]
    rfl)

theorem mem_fixOf_restrictRep (ρ : X →* (M ≃ₗ[ZMod 2] M)) (U : Submodule (ZMod 2) M)
    (hU : ∀ x, ∀ v ∈ U, ρ x v ∈ U) {T : Set G'} (v : U) :
    v ∈ fixOf (restrictRep ρ U hU) T ↔ (v : M) ∈ fixOf ρ T := by
  rw [mem_fixOf, mem_fixOf]
  exact forall₂_congr fun x _ => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem isCompl_restrictRep (ρ : X →* (M ≃ₗ[ZMod 2] M)) (U : Submodule (ZMod 2) M)
    (hU : ∀ x, ∀ v ∈ U, ρ x v ∈ U) {T T₁ : Set G'}
    (h1 : U ⊓ fixOf ρ T ⊔ U ⊓ fixOf ρ T₁ = U)
    (h2 : U ⊓ fixOf ρ T ⊓ (U ⊓ fixOf ρ T₁) = ⊥) :
    IsCompl (fixOf (restrictRep ρ U hU) T) (fixOf (restrictRep ρ U hU) T₁) := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro v hv
    obtain ⟨hv₀, hv₁⟩ := Submodule.mem_inf.mp hv
    rw [mem_fixOf_restrictRep] at hv₀ hv₁
    have : (v : M) ∈ U ⊓ fixOf ρ T ⊓ (U ⊓ fixOf ρ T₁) := ⟨⟨v.2, hv₀⟩, v.2, hv₁⟩
    rw [h2, Submodule.mem_bot] at this
    exact (Submodule.mem_bot _).mpr (Subtype.ext this)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : (v : M) ∈ U ⊓ fixOf ρ T ⊔ U ⊓ fixOf ρ T₁ := by rw [h1]; exact v.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    have e : v = ⟨a, ha.1⟩ + ⟨b, hb.1⟩ := Subtype.ext hab.symm
    rw [e]
    exact Submodule.add_mem_sup ((mem_fixOf_restrictRep ρ U hU _).mpr ha.2)
      ((mem_fixOf_restrictRep ρ U hU _).mpr hb.2)

end Restrict

section Range

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) {ψ : Module.End (ZMod 2) M}

noncomputable abbrev rangeRep (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) :
    omegaGroup q hq →* (LinearMap.range ψ ≃ₗ[ZMod 2] LinearMap.range ψ) :=
  restrictRep ρ (LinearMap.range ψ) fun e v hv => by
    obtain ⟨w, rfl⟩ := hv
    exact ⟨ρ e w, hψ e w⟩

theorem isCompl_rangeRep {p p₁ : V}
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) :
    IsCompl (fixOf (rangeRep ρ hψ) (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf (rangeRep ρ hψ) (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))) := by
  obtain ⟨-, hD⟩ := radDecomp_range ρ hc hψ
  rw [RadDecomp, radFix_bot, radFix_bot] at hD
  exact isCompl_restrictRep _ _ _ hD.1 hD.2

theorem two_mul_finrank_fixOf_rangeRep {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) :
    2 * finrank (ZMod 2) (fixOf (rangeRep ρ hψ) (pointRadical q p : Set (V ≃ₗ[ZMod 2] V))) =
      finrank (ZMod 2) (LinearMap.range ψ) :=
  two_mul_finrank_fixOf_eq (rangeRep ρ hψ) hm hdim hp0 hp hp₁ hpp₁ (isCompl_rangeRep ρ hc hψ)

theorem rangeRep_faithful [IsSimpleGroup (omegaGroup q hq)] {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) (hr : 0 < finrank (ZMod 2) (LinearMap.range ψ))
    (e : omegaGroup q hq) (he : rangeRep ρ hψ e = 1) : e = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (rangeRep ρ hψ).ker with h | h
  · have : e ∈ (rangeRep ρ hψ).ker := he
    rw [h] at this
    exact this
  · exfalso
    have h2 := two_mul_finrank_fixOf_rangeRep ρ hm hdim hp0 hp hp₁ hpp₁ hc hψ
    have htop : fixOf (rangeRep ρ hψ) (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) = ⊤ := by
      rw [eq_top_iff]
      intro v _ x _
      have hx : x ∈ (rangeRep ρ hψ).ker := by rw [h]; exact mem_top x
      rw [MonoidHom.mem_ker] at hx
      rw [hx]
      rfl
    rw [htop, finrank_top] at h2
    omega

theorem rangeRep_trivial_of_rank_le_one [IsSimpleGroup (omegaGroup q hq)]
    (hdim : finrank (ZMod 2) V = 8) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) (hr : 5 ≤ finrank (ZMod 2) (LinearMap.range ψ))
    (e : omegaGroup q hq) (c : M)
    (h : ∀ w ∈ LinearMap.range ψ, ρ e w - w ∈ (ZMod 2) ∙ c) :
    ∀ w ∈ LinearMap.range ψ, ρ e w = w := by
  have hfaith := rangeRep_faithful ρ (m := 4) (by norm_num) (by rw [hdim]) hp0 hp hp₁ hpp₁ hc hψ
    (by omega)
  have hne1 := finrank_commSpace_ne_one (rangeRep ρ hψ) hdim hr hp0 hp hp₁ hpp₁
    (isCompl_rangeRep ρ hc hψ) hfaith e
  have hle : (commSpace (rangeRep ρ hψ e)).map (LinearMap.range ψ).subtype ≤ (ZMod 2) ∙ c := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
    exact h u u.2
  have hfin : finrank (ZMod 2) (commSpace (rangeRep ρ hψ e)) ≤ 1 := by
    rw [← Submodule.finrank_map_subtype_eq]
    refine (Submodule.finrank_mono hle).trans ?_
    by_cases hc0 : c = 0
    · rw [hc0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton hc0]
  have h0 : commSpace (rangeRep ρ hψ e) = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    omega
  intro w hw
  have hu := sub_mem_commSpace (rangeRep ρ hψ e) ⟨w, hw⟩
  rw [h0, Submodule.mem_bot, sub_eq_zero] at hu
  exact congrArg Subtype.val hu

theorem exists_mem_range_fixOf {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hψ : ∀ g v, ψ (ρ g v) = ρ g (ψ v)) (hr : 0 < finrank (ZMod 2) (LinearMap.range ψ)) :
    ∃ w ∈ LinearMap.range ψ, w ≠ 0 ∧
      w ∈ fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) := by
  have h2 := two_mul_finrank_fixOf_rangeRep ρ hm hdim hp0 hp hp₁ hpp₁ hc hψ
  have hne : fixOf (rangeRep ρ hψ) (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h2
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨u, u.2, fun h => hu0 (Subtype.ext h), (mem_fixOf_restrictRep _ _ _ u).mp hu⟩

end Range

end CFSG.LargeExtraspecial.S14
