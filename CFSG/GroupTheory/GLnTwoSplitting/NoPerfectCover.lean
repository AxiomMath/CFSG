module

public import CFSG.GroupTheory.GLnTwoSplitting.NoPerfectCoverForm
public import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear
public import CFSG.Monster.Schur.Defs

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Subgroup CFSG.Monster.Schur
open scoped commutatorElement

theorem exists_ne_one_of_card_ker_eq_two {C D : Type*} [Group C] [Group D] {p : C →* D}
    (hk : Nat.card p.ker = 2) :
    ∃ ζ ∈ p.ker, ζ ≠ 1 ∧ p.ker ≤ center C ∧ ∀ z ∈ p.ker, z * z = 1 := by
  obtain ⟨t, ht, huniq⟩ := (Nat.card_eq_two_iff' (1 : p.ker)).mp hk
  have hall : ∀ z ∈ p.ker, z = 1 ∨ z = t := fun z hz => by
    by_cases h : z = 1
    · exact Or.inl h
    · exact Or.inr (congrArg Subtype.val (huniq ⟨z, hz⟩ fun h' => h (congrArg Subtype.val h')))
  have ht1 : (t : C) ≠ 1 := fun h => ht (Subtype.ext h)
  refine ⟨t, t.2, ht1, fun z hz => mem_center_iff.2 fun g => ?_, fun z hz => ?_⟩
  · rcases hall z hz with rfl | rfl
    · rw [one_mul, mul_one]
    · rcases hall _ (p.normal_ker.conj_mem _ t.2 g) with h | h
      · exact absurd (by simpa using h) ht1
      · calc g * (t : C) = g * t * g⁻¹ * g := by group
          _ = t * g := by rw [h]
  · have h := pow_card_eq_one' (G := p.ker) (x := ⟨z, hz⟩)
    rw [hk, pow_two] at h
    exact congrArg Subtype.val h

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] (X : NatExt G E)
include X

theorem isPerfect_of_three_le (hE : 3 ≤ finrank (ZMod 2) E) : Group.IsPerfect G := by
  have := isPerfect_linearEquiv hE
  have hι : ∀ e, X.ι e ∈ commutator G := fun e => by
    obtain ⟨f, x, hfe, -, hfx⟩ := exists_dual_apply_eq_zero_of_three_le hE e e
    obtain ⟨g, hg⟩ := X.surjective (LinearEquiv.transvection hfe)
    have h1 : g * X.ι x * g⁻¹ = X.ι x * X.ι e := by
      rw [X.conj, hg, transvection_apply, hfx, one_smul, X.ι_add]
    have h2 : ⁅X.ι x, g⁆ = X.ι e := by
      calc ⁅X.ι x, g⁆ = X.ι x * (g * X.ι x * g⁻¹) := by
            rw [commutatorElement_def, X.ι_inv]
            group
        _ = X.ι e := by rw [h1, ← mul_assoc, X.ι_mul_self, one_mul]
    rw [← h2, _root_.commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  refine ⟨eq_top_iff.2 fun x _ => ?_⟩
  have hx : X.π x ∈ (commutator G).map X.π := by
    rw [_root_.commutator_def, Subgroup.map_commutator, map_top_of_surjective _ X.surjective,
      ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
    exact mem_top _
  obtain ⟨y, hy, hyx⟩ := mem_map.1 hx
  obtain ⟨e, rfl⟩ := X.exists_eq_mul_ι hyx
  exact mul_mem hy (hι e)

theorem noPerfectDoubleCover_of_five_le (hE : 5 ≤ finrank (ZMod 2) E) :
    NoPerfectDoubleCover G := by
  intro C _ p hp hperf hk
  obtain ⟨ζ, hζ, hζ1, hcen, hsq⟩ := exists_ne_one_of_card_ker_eq_two hk
  obtain ⟨W, hWn, hWV, hζW, hcov⟩ := X.exists_normal_complement (by omega) hp hcen hsq hζ hζ1
  let ψ : C ⧸ W →* (E ≃ₗ[ZMod 2] E) :=
    QuotientGroup.lift W (X.π.comp p) fun v hv => MonoidHom.mem_ker.2 (hWV v hv)
  have hψ : ∀ x : C, ψ x = X.π (p x) := fun _ => rfl
  have hψs : Function.Surjective ψ := fun γ => by
    obtain ⟨x, hx⟩ := (X.surjective.comp hp) γ
    exact ⟨x, hx⟩
  have hcenter : ∀ c ∈ center C, (c : C ⧸ W) ∈ center (C ⧸ W) := fun c hc =>
    mem_center_iff.2 fun y => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 hc y]
  have hψk : ψ.ker ≤ center (C ⧸ W) := fun y hy => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rcases hcov x (by rwa [MonoidHom.mem_ker, hψ] at hy) with h | h
    · rw [(QuotientGroup.eq_one_iff x).2 h]
      exact one_mem _
    · have e : ((x : C) : C ⧸ W) = ((x * ζ : C) : C ⧸ W) * ((ζ⁻¹ : C) : C ⧸ W) := by
        rw [← QuotientGroup.mk_mul, mul_inv_cancel_right]
      rw [e, (QuotientGroup.eq_one_iff _).2 h, one_mul]
      exact hcenter _ (hcen (inv_mem hζ))
  obtain ⟨t, ht⟩ := exists_section_of_ker_le_center hE hψs hψk
  have : Group.IsPerfect (C ⧸ W) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective W)
  have htop : ∀ y : C ⧸ W, y ∈ t.range := fun y => by
    have hy : y ∈ commutator (C ⧸ W) := Group.IsPerfect.mem_commutator
    rw [_root_.commutator_def] at hy
    refine (commutator_le.2 fun a _ b _ => ?_) hy
    refine MonoidHom.mem_range.2 ⟨⁅ψ a, ψ b⁆, ?_⟩
    rw [map_commutatorElement]
    exact commutatorElement_eq_of_map_eq hψk (ht (ψ a)).symm (ht (ψ b)).symm
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 (htop (ζ : C ⧸ W))
  have ha1 : a = 1 := by rw [← ht a, ha, hψ, MonoidHom.mem_ker.1 hζ, map_one]
  rw [ha1, map_one, eq_comm, QuotientGroup.eq_one_iff] at ha
  exact hζW ha

theorem noPerfectDoubleCover (hE : finrank (ZMod 2) E = 5) : NoPerfectDoubleCover G :=
  X.noPerfectDoubleCover_of_five_le hE.ge

theorem isPerfect (hE : finrank (ZMod 2) E = 5) : Group.IsPerfect G :=
  X.isPerfect_of_three_le (by omega)

end NatExt

end CFSG.GroupTheory.GLnTwoSplitting
