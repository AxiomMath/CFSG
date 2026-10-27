module

public import CFSG.LieType.Chevalley.E6GraphLeviUnitary
public import CFSG.LieType.SeitzGeneration.FixPlaneGenUnitary

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration CFSG.Open
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {σ : K →+* K}

theorem conjTr_unitaryInvolution_gen (hσ : ∀ c, σ c = c ^ p ^ f)
    (M : Matrix (Fin 6) (Fin 6) K) :
    conjTr (unitaryInvolution K p f) M = (M.map σ).transpose := by
  rw [conjTr]
  congr 1
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply, hσ]

theorem map_toGL_unitarySL_gen (hσ : ∀ c, σ c = c ^ p ^ f) :
    (unitarySL σ).map Matrix.SpecialLinearGroup.toGL = SU (unitaryInvolution K p f) 6 := by
  ext g
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B.2, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, conjTr_unitaryInvolution_gen hσ]
    exact mem_unitarySL_iff.1 hB
  · rintro ⟨hdet, hiso⟩
    rw [conjTr_unitaryInvolution_gen hσ] at hiso
    exact ⟨⟨(g : Matrix (Fin 6) (Fin 6) K), hdet⟩, mem_unitarySL_iff.2 hiso, Units.ext rfl⟩

@[expose] def unitarySLEquiv_gen (hσ : ∀ c, σ c = c ^ p ^ f) :
    unitarySL σ ≃* SU (unitaryInvolution K p f) 6 :=
  ((unitarySL σ).equivMapOfInjective _ Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (map_toGL_unitarySL_gen hσ))

theorem isPerfect_unitarySL_gen (hK : Nat.card K = (p ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ p ^ f) :
    Group.IsPerfect (unitarySL σ) := by
  have : Group.IsPerfect (SU (unitaryInvolution K p f) 6) :=
    (isQuasisimple_SU hK (n := 6) (by norm_num) (by simp)).1
  exact Group.IsPerfect.ofSurjective (f := (unitarySLEquiv_gen hσ).symm.toMonoidHom)
    (unitarySLEquiv_gen hσ).symm.surjective

@[expose] def unitarySLEquivStated (hK : Nat.card K = (p ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ p ^ f) :
    unitarySL σ ≃* StatedSU 6 (p ^ f) K :=
  (unitarySLEquiv_gen hσ).trans (equivStatedSU hK 6)

theorem closure_centralizers_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (E : Subgroup G) :
    (Subgroup.closure {g : G | ∃ x ∈ E, x ≠ 1 ∧ Commute g x}).map e.toMonoidHom =
      Subgroup.closure {g : H | ∃ x ∈ E.map e.toMonoidHom, x ≠ 1 ∧ Commute g x} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨g₀, ⟨x, hx, hx1, hc⟩, rfl⟩
    exact ⟨e x, Subgroup.mem_map_of_mem _ hx, fun h1 => hx1 (e.map_eq_one_iff.1 h1), hc.map e⟩
  · intro hg
    obtain ⟨x', ⟨x, hx, rfl⟩, hx1, hc⟩ := hg
    refine ⟨e.symm g, ⟨x, hx, fun h1 => hx1 (by simp [h1]), ?_⟩, by simp⟩
    simpa using hc.map e.symm

theorem unitarySL_planeGen {q : ℕ} (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f)
    (hσ : ∀ c, σ c = c ^ p ^ f) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hq' : q ∣ p ^ f + 1 → p ^ f ≠ 2) (E : Subgroup (unitarySL σ)) (hE : IsElemAbelian q E)
    (hc : Nat.card E = q ^ 2) :
    Subgroup.closure {g : unitarySL σ | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} = ⊤ := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨(Fact.out : p.Prime), hf, by rw [hK]; ring⟩
  let e := unitarySLEquivStated hK hσ
  have hE' : IsElemAbelian q (E.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map q hE e.toMonoidHom
  have hcard' : Nat.card (E.map e.toMonoidHom) = q ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hc]
  have hcomm : ∀ x ∈ E.map e.toMonoidHom, ∀ y ∈ E.map e.toMonoidHom, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hE'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hgen : Subgroup.closure {g : StatedSU 6 (p ^ f) K |
      ∃ x ∈ E.map e.toMonoidHom, x ≠ 1 ∧ Commute g x} = ⊤ :=
    unitarySU_planeGen_of_ne hU hq hq2 hqp (by norm_num) hq' (E.map e.toMonoidHom) hcomm
      hE'.2 hcard'
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ (Subgroup.closure {g : unitarySL σ | ∃ x ∈ E, x ≠ 1 ∧ Commute g x}).map
      e.toMonoidHom := by
    rw [closure_centralizers_of_mulEquiv e E, hgen]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [e.injective hyx] at hy

end CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
