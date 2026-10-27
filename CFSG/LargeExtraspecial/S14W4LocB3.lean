module

public import CFSG.LargeExtraspecial.S14W4LocAct
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.LargeExtraspecial.GLRElimSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.RankThree.OrthogonalInvolutions

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {π : T.M →* (V ≃ₗ[ZMod 2] V)}

omit [Finite X] in
theorem mem_orthogonalGroup (A : Act T R π) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (k : T.M) : π k ∈ TauCeti.QuadraticMap.orthogonalGroup q := by
  refine O62.mem_orthogonalGroup_of_normalizes hV hq fun x hx => hR.le ?_
  have hx' : ∃ r : T.M, r ∈ R.subgroupOf T.M ∧ π r = x := Subgroup.mem_map.mp (hR.ge hx)
  obtain ⟨r, hr, hrx⟩ := hx'
  subst hrx
  have hmem : k * r * k⁻¹ ∈ R.subgroupOf T.M := A.conj_mem k r hr
  exact Subgroup.mem_map.mpr ⟨k * r * k⁻¹, hmem, by simp only [map_mul, map_inv]⟩

theorem factorization_card_le_of (hQ : Nat.card T.Q = 2 ^ 9)
    (hP : ∀ P : Subgroup T.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) :
    (Nat.card X).factorization 2 ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, -, hT₁⟩ := GLR.exists_isSylowIn_le (bot_le : ⊥ ≤ T.M) IsPGroup.of_bot
  have htop := GLR.Config.sylowIn_top hT₁
  have hfac := GLR.SylowIn.factorization_eq htop
  rw [Subgroup.card_top] at hfac
  rw [hfac]
  have h2 : IsPGroup 2 T₁ := GLR.SylowIn.isPGroup hT₁
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h2
  rw [ha, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  set T₁' := T₁.subgroupOf T.M
  have hT₁' : Nat.card T₁' = Nat.card T₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (GLR.SylowIn.le hT₁)).toEquiv
  set f := T.ρ.comp T₁'.subtype
  have hker : Nat.card f.ker ≤ 2 ^ 9 := by
    rw [← hQ]
    have hle : f.ker.map T₁'.subtype ≤ T.Q := by
      rintro _ ⟨x, hx, rfl⟩
      exact T.mem_Q_of_ρ_eq_one hx
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective T₁'.subtype_injective] at this
  have hrange : Nat.card f.range ≤ 2 ^ 7 := by
    have hle : f.range ≤ T.Mbar := by
      rintro _ ⟨x, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h1 : Nat.card (f.range.subgroupOf T.Mbar) = Nat.card f.range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have h2' : IsPGroup 2 T₁' :=
      h2.of_equiv (Subgroup.subgroupOfEquivOfLe (GLR.SylowIn.le hT₁)).symm
    have h3 : IsPGroup 2 (f.range.subgroupOf T.Mbar) :=
      (h2'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).of_equiv
        (Subgroup.subgroupOfEquivOfLe hle).symm
    rw [← h1]
    exact hP _ h3
  have hmul := Subgroup.card_ker_mul_card_range f
  have hle16 : 2 ^ a ≤ 2 ^ 16 := by
    rw [← ha, ← hT₁', ← hmul]
    calc Nat.card f.ker * Nat.card f.range ≤ 2 ^ 9 * 2 ^ 7 := Nat.mul_le_mul hker hrange
      _ = 2 ^ 16 := by norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle16

end CFSG.LargeExtraspecial.S14.W4Loc
