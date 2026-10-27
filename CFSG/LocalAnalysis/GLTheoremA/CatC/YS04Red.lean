module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom centerQuotientHom_injective)

@[expose] def KD26fSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ((∃ (n q : ℕ) (lin : Bool), IsLnEps S n q lin ∧
          p ∣ Nat.gcd n (qEps lin q) ∧ ¬ p ^ 2 ∣ Nat.gcd n (qEps lin q)) ∨
        (∃ (q : ℕ) (lin : Bool), IsE6Eps S q lin ∧ p = 3 ∧ 3 ∣ qEps lin q)) →
      ∀ D : Subgroup (MulAut S), IsElemAbelian p D →
        Nat.card D ≤ p * Nat.card ↥(D ⊓ inner S)

theorem kd26f_of_simple (h : KD26fSimple) : KD26f := by
  intro K _ _ hK p hp hp2 hhyp D hD
  have hperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1.1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  set φ : MulAut K →* MulAut (K ⧸ Subgroup.center K) := centerQuotientHom K with hφdef
  have hφ : Function.Injective φ := centerQuotientHom_injective K
  have hD' : IsElemAbelian p (D.map φ) := by
    haveI : IsMulCommutative ↥D := hD.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : MulAut (K ⧸ Subgroup.center K)) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥D) ⟨y, hy⟩)
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      rw [← map_pow, hD.2 x hx, map_one]
  have hinf : (D.map φ) ⊓ inner (K ⧸ Subgroup.center K) = (D ⊓ inner K).map φ := by
    ext z
    constructor
    · rintro ⟨hzD, hzi⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hzD
      exact Subgroup.mem_map.2 ⟨x, ⟨hx, mem_inner_of_centerQuotientHom_mem hzi⟩, rfl⟩
    · rintro hz
      obtain ⟨x, ⟨hxD, ⟨g, hg⟩⟩, rfl⟩ := Subgroup.mem_map.1 hz
      refine ⟨Subgroup.mem_map.2 ⟨x, hxD, rfl⟩, ⟨QuotientGroup.mk' (Subgroup.center K) g, ?_⟩⟩
      rw [← hg]
      exact (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj g).symm
  have h1 := h (K ⧸ Subgroup.center K) inferInstance hna p hp hp2 hhyp (D.map φ) hD'
  rw [hinf, Subgroup.card_map_of_injective hφ, Subgroup.card_map_of_injective hφ] at h1
  exact h1

@[expose] def KD26bcSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p = 3 ∧ IsLnEps S 3 8 false) →
      ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 → D ⊓ inner S = ⊥ →
        ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
          (∃ a b : ↥L, a * b ≠ b * a) ∧ p ∣ Nat.card L ∧
          ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L

theorem kd26bc_of_simple (h : KD26bcSimple) : KD26bc := by
  intro K _ _ hK p hp hp2 _ hU8 D hD hDcard hDinn
  have hperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1.1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  set φ : MulAut K →* MulAut (K ⧸ Subgroup.center K) := centerQuotientHom K with hφdef
  have hφ : Function.Injective φ := centerQuotientHom_injective K
  have hD' : IsElemAbelian p (D.map φ) := by
    haveI : IsMulCommutative ↥D := hD.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : MulAut (K ⧸ Subgroup.center K)) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥D) ⟨y, hy⟩)
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      rw [← map_pow, hD.2 x hx, map_one]
  have hDinn' : (D.map φ) ⊓ inner (K ⧸ Subgroup.center K) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzD, hzi⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hzD
    have : x ∈ D ⊓ inner K := ⟨hx, mem_inner_of_centerQuotientHom_mem hzi⟩
    rw [hDinn, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  obtain ⟨yb, hybD, hyb1, L, hLfix, hLs, hLna, hpL, hLnorm⟩ := h (K ⧸ Subgroup.center K) inferInstance
    hna hK.2 p hp hp2 hU8 (D.map φ) hD' (by rw [Subgroup.card_map_of_injective hφ]; exact hDcard)
    hDinn'
  obtain ⟨y, hyD, rfl⟩ := Subgroup.mem_map.1 hybD
  refine ⟨y, hyD, fun h1 => hyb1 (by rw [h1, map_one]), ?_⟩
  refine YS04Lift.glaPLayer_ne_bot_of_fixed_block hp hLs hLna (fun x hx => hLfix hx) hpL ?_
  intro g hg x hx
  have hgfix : QuotientGroup.mk' (Subgroup.center K) g ∈ fixSub (φ y) := by
    show φ y (QuotientGroup.mk' (Subgroup.center K) g) = QuotientGroup.mk' (Subgroup.center K) g
    rw [show φ y (QuotientGroup.mk' (Subgroup.center K) g) =
      QuotientGroup.mk' (Subgroup.center K) (y g) from
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk y g]
    exact congrArg _ (show y g = g from hg)
  exact hLnorm _ hgfix x hx

end CFSG.LocalAnalysis.GLTheoremA
