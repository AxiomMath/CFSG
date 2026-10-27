module

public import CFSG.ClassicalInvolution.Q3.Q3MTModel1
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTorus

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Asc77.T3CII (center_sl3_eq_bot center_su3_eq_bot)
open CFSG.ClassicalInvolution.Models (suMat)
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Linear

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem linear_pow_card_sub_one3 (hF : Nat.card F = 3) {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair F W U V) {x : X} (hxV : x ∈ V)
    (hxN : x ∈ Subgroup.normalizer (U : Set X)) : x ^ (Nat.card F - 1) = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    have := hker (MonoidHom.mem_ker.2 hc1)
    rwa [center_sl3_eq_bot hF, Subgroup.mem_bot] at this
  rw [← hV] at hxV
  obtain ⟨g, hg, rfl⟩ := hxV
  rw [← hU] at hxN
  have hgN' := mem_normalizer_of_map_injective' hinj hxN
  obtain ⟨M, rfl⟩ := hg
  have hb : WeakCT.blockSL F 3 2 0 (by omega) (WeakCT.rotSL) ∈ WeakCT.B12 F := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
  have h2 : WeakCT.blockSL F 3 2 0 (by omega) A' * WeakCT.blockSL F 3 2 1 (by omega) M =
      WeakCT.blockSL F 3 2 1 (by omega) M * WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL := by
    rw [hA']
    group
  have h3 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero, coe_blockSL_one] at h3
  obtain ⟨h01, h10⟩ := embPair_zero_conj_rot _ _ h3.symm
  obtain ⟨u, rfl⟩ := WeakCT.mem_diagTorus2_iff.mp (WeakCT.mem_diagTorus2_of_offDiag M h01 h10)
  have hu : u ^ (Nat.card F - 1) = 1 := by
    rw [← MuTab.natCard_units_eq' F]
    exact pow_card_eq_one'
  rw [← map_pow, ← map_pow, ← map_pow, hu, map_one, map_one, map_one]

end Linear

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem unitary_pow_card_add_one3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f = 3)
    {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V) {x : X} (hxV : x ∈ V)
    (hxN : x ∈ Subgroup.normalizer (U : Set X)) : x ^ (p ^ f + 1) = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    have := hker (MonoidHom.mem_ker.2 hc1)
    rwa [center_su3_eq_bot hK hq, Subgroup.mem_bot] at this
  rw [← hV] at hxV
  obtain ⟨g, hg, rfl⟩ := hxV
  rw [← hU] at hxN
  have hgN' := mem_normalizer_of_map_injective' hinj hxN
  obtain ⟨M, rfl⟩ := hg
  have hb : embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) ∈
      Phan.B12 K p f := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
  have h2 : embSUid (unitaryInvolution K p f) 2 A' * embSUid (unitaryInvolution K p f) 0 M =
      embSUid (unitaryInvolution K p f) 0 M *
        embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) := by
    rw [hA']
    group
  have h3 := congrArg suMat h2
  simp only [Models.suMat_mul] at h3
  obtain ⟨h01, h10⟩ := embPair_zero_conj_rot _ _ h3.symm
  have hM : M ∈ Phan.torus (unitaryInvolution K p f) 2 := by
    rw [Phan.mem_torus_iff]
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact h01
    · exact h10
    · exact absurd rfl hab
  obtain ⟨dd, rfl⟩ := hM
  have hdd : dd ^ (p ^ f + 1) = 1 := by
    refine Subtype.ext (funext fun a => ?_)
    show (dd.1 a) ^ (p ^ f + 1) = 1
    rw [← Phan.card_normOne (K := K) (p := p) (f := f) hK]
    exact pow_card_eq_one'
  rw [← map_pow, ← map_pow, ← map_pow, hdd, map_one, map_one, map_one]

end Unitary

end CFSG.ClassicalInvolution.Q3.Q3MT
