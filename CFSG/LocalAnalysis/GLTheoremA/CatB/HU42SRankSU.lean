module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SRankU6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SHopf

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S

open CFSG.Open CFSG.RankThree.PerfectCover

variable {K : Type} [Field K] [Finite K]

def projSU {S : Type} [Group S] (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) :
    ↥(StatedSU 6 (2 ^ 1) K) →* S :=
  f.symm.toMonoidHom.comp
    (QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K)))

theorem projSU_surjective {S : Type} [Group S] (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) :
    Function.Surjective (projSU f) := by
  intro s
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (f s)
  refine ⟨y, ?_⟩
  simp only [projSU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
  rw [hy, MulEquiv.symm_apply_apply]

theorem mem_ker_projSU_iff {S : Type} [Group S] (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K))
    (y : ↥(StatedSU 6 (2 ^ 1) K)) :
    y ∈ (projSU f).ker ↔ (y : GL (Fin 6) K) ∈ StatedScalars (Fin 6) K := by
  rw [MonoidHom.mem_ker, projSU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]

theorem ker_projSU_eq {S : Type} [Group S] (hK : Nat.card K = 4)
    (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) : (projSU f).ker = scalSub hK := by
  ext y
  rw [mem_ker_projSU_iff, mem_scalSub_iff]

theorem card_ker_projSU {S : Type} [Group S] (hK : Nat.card K = 4)
    (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) : Nat.card (projSU f).ker = 3 := by
  rw [ker_projSU_eq hK f, card_scalSub hK]

theorem ker_projSU_le_center {S : Type} [Group S] (hK : Nat.card K = 4)
    (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) :
    (projSU f).ker ≤ Subgroup.center (StatedSU 6 (2 ^ 1) K) := by
  rw [ker_projSU_eq hK f]
  exact scalSub_le_center hK

theorem finite_SU (K : Type) [Field K] [Finite K] : Finite ↥(StatedSU 6 (2 ^ 1) K) := by
  haveI := Fintype.ofFinite K
  infer_instance

theorem perfect_SU (hK : Nat.card K = 4) : Group.IsPerfect ↥(StatedSU 6 (2 ^ 1) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) (n := 6)
  · rw [hK]
    norm_num
  · norm_num
  · decide

theorem rank5_of_u6 {S Q : Type} [Group S] [Finite S] [Group.IsPerfect S] [Group Q] [Finite Q]
    [Group.IsPerfect Q] (hK : Nat.card K = 4) (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K))
    (hM : Nat.card (hopfMultiplier S) = 12) (p : Q →* S) (hp : Function.Surjective p)
    (hpc : p.ker ≤ Subgroup.center Q) (h3 : 3 ∣ Nat.card p.ker) :
    ∃ W : Subgroup Q, IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 5 := by
  haveI := finite_SU K
  haveI := perfect_SU (K := K) hK
  obtain ⟨π, hπs, hπk⟩ := exists_surj_kernel_not_three_dvd p hp hpc (projSU f) (projSU_surjective f)
    (ker_projSU_le_center hK f) hM (card_ker_projSU hK f) h3
  obtain ⟨W, hW, hcard⟩ := exists_elemAbelian_lift π hπs hπk (W6_isElemAbelian hK)
  exact ⟨W, hW, hcard.trans (card_W6 hK)⟩

theorem pow_three_T₁ (hK : Nat.card K = 4) (a : ↥(T₁ K)) : a ^ 3 = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_three_TT hK a.1

theorem rank4_of_u6 {S Q : Type} [Group S] [Finite S] [Group.IsPerfect S] [Group Q] [Finite Q]
    (hK : Nat.card K = 4) (f : S ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) (p : Q →* S)
    (hp : Function.Surjective p) (hker : ¬ 3 ∣ Nat.card p.ker) :
    ∃ W : Subgroup Q, IsElemAbelian 3 W ∧ Nat.card W = 3 ^ 4 := by
  let g : ↥(T₁ K) →* S := (projSU f).comp ((torusY hK).comp (T₁ K).subtype)
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : torusY hK ((T₁ K).subtype a) ∈ W4 hK := MonoidHom.mem_range.2 ⟨a, rfl⟩
    have hs : torusY hK ((T₁ K).subtype a) ∈ scalSub hK := by
      rw [← ker_projSU_eq hK f]
      exact ha
    have h1 := W4_inf_scalSub hK hmem hs
    have h2 : (T₁ K).subtype a = 1 := torusY_injective hK (by rw [h1, map_one])
    exact Subtype.ext h2
  have hE : CFSG.Open.IsElemAbelian 3 g.range :=
    isElemAbelian_range_of_cube g (fun a => pow_three_T₁ hK a)
  have hcard : Nat.card g.range = 3 ^ 4 := by
    rw [card_range_of_injective' g hginj, card_T₁ hK]
  obtain ⟨W, hW, hWc⟩ := exists_elemAbelian_lift p hp hker hE
  exact ⟨W, hW, hWc.trans hcard⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S
