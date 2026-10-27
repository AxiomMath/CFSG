module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinCG
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGrp
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421TransProof

open K421CGProof K421GrpProof

section Centralizer

variable {L L' : Type} [Group L] [Group L']

theorem centralizer_map_singleton (φ : L ≃* L') (y : L) :
    (Subgroup.centralizer ({y} : Set L)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ y} : Set L') := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ Subgroup.centralizer ({y} : Set L) := hw
    rw [Subgroup.mem_centralizer_iff] at hw' ⊢
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    have h1 := hw' y rfl
    show φ y * φ w = φ w * φ y
    rw [← map_mul, ← map_mul, h1]
  · intro hz
    rw [Subgroup.mem_centralizer_iff] at hz
    refine ⟨φ.symm z, ?_, φ.apply_symm_apply z⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact hz (φ u) rfl

theorem card_centralizer_map (φ : L ≃* L') (y : L) :
    Nat.card (Subgroup.centralizer ({φ y} : Set L')) =
      Nat.card (Subgroup.centralizer ({y} : Set L)) := by
  rw [← centralizer_map_singleton φ y, Subgroup.card_map_of_injective φ.injective]

theorem card_centralizer_conj (n x : L) :
    Nat.card (Subgroup.centralizer ({n * x * n⁻¹} : Set L)) =
      Nat.card (Subgroup.centralizer ({x} : Set L)) :=
  card_centralizer_map (MulAut.conj n) x

theorem emb_conj {S : Type} [Group S] (φ : S →* L) (hφ : Function.Injective φ) {n x y : L}
    (hy : n * x * n⁻¹ = y) (hle : φ.range ≤ Subgroup.centralizer ({y} : Set L)) :
    ∃ ψ : S →* L, Function.Injective ψ ∧ ψ.range ≤ Subgroup.centralizer ({x} : Set L) := by
  refine ⟨(MulAut.conj n⁻¹).toMonoidHom.comp φ, (MulAut.conj n⁻¹).injective.comp hφ, ?_⟩
  rintro _ ⟨s, rfl⟩
  have h1 : (MulAut.conj n⁻¹) y = x := by
    rw [← hy]
    simp [MulAut.conj_apply, mul_assoc]
  have h2 := centralizer_map_singleton (MulAut.conj n⁻¹) y
  rw [h1] at h2
  rw [← h2]
  exact ⟨φ s, hle ⟨s, rfl⟩, rfl⟩

end Centralizer

theorem card_GL_two (n : ℕ) : Nat.card (GL (Fin n) (ZMod 2)) = glc 2 n := by
  rw [card_GL, Fintype.card_fin, ZMod.card]

theorem seven_dvd_glc : ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) → 7 ∣ glc 2 n := by
  rintro n (rfl | rfl | rfl)
  · rw [glc_two.2.2.2.1]; norm_num
  · rw [glc_two.2.2.2.2.1]; norm_num
  · rw [glc_two.2.2.2.2.2]; norm_num

theorem glc_ne_seven : ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) → glc 2 n ≠ 7 := by
  rintro n (rfl | rfl | rfl)
  · rw [glc_two.2.2.2.1]; norm_num
  · rw [glc_two.2.2.2.2.1]; norm_num
  · rw [glc_two.2.2.2.2.2]; norm_num

theorem caseA_of_emb {G : Type} [Group G] [Finite G]
    (hrank : CFSG.Open.pRank 7 (⊤ : Subgroup G) ≤ 2) {x : G} {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (φ : GL (Fin n) (ZMod 2) →* G) (hφ : Function.Injective φ)
    (hle : φ.range ≤ Subgroup.centralizer ({x} : Set G)) :
    2 ≤ CFSG.Open.pRank 7 (Subgroup.centralizer ({x} : Set G)) +
        (3 - CFSG.Open.pRank 7 (⊤ : Subgroup G)) ∧
      ¬ CFSG.HallHigman.IsPSolvable 7 ↥(Subgroup.centralizer ({x} : Set G)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hn3 : 3 ≤ n := by omega
  haveI := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two hn3
  have hdvd : 7 ∣ Nat.card (GL (Fin n) (ZMod 2)) := by
    rw [card_GL_two]
    exact seven_dvd_glc n hn
  have hne : Nat.card (GL (Fin n) (ZMod 2)) ≠ 7 := by
    rw [card_GL_two]
    exact glc_ne_seven n hn
  have h1 := rank_ge_one_of_embedding hdvd φ hφ hle
  refine ⟨by omega, ?_⟩
  exact not_isPSolvable_of_embedding inferInstance hdvd hne φ hφ hle

end K421TransProof

end CFSG.LocalAnalysis.RankThreeUC.S15
