module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open Subgroup Matrix
open scoped MatrixGroups

theorem card_GL32_gh : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem isSimpleGroup_GL32_gh : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

theorem eq_top_of_dvd_card_GL32 {R : Subgroup (GL (Fin 3) (ZMod 2))} (h : 56 ∣ Nat.card R) :
    R = ⊤ := by
  have hs := isSimpleGroup_GL32_gh
  have hd : Nat.card R ∣ 168 := card_GL32_gh ▸ Subgroup.card_subgroup_dvd_card R
  have hmul : Nat.card R * R.index = 168 := by rw [R.card_mul_index, card_GL32_gh]
  obtain ⟨k, hk⟩ := h
  have hk3 : k ∣ 3 := by
    rw [hk, show (168 : ℕ) = 56 * 3 by norm_num] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
  · exfalso
    have h3 : R.index = 3 := by rw [hk] at hmul; omega
    have hc := R.index_normalCore_le_factorial_index
    rcases hs.eq_bot_or_eq_top_of_normal R.normalCore with hb | ht
    · rw [hb, index_bot, card_GL32_gh, h3] at hc
      exact absurd hc (by decide)
    · have hR : R = ⊤ := top_le_iff.mp (ht ▸ R.normalCore_le)
      rw [hR, index_top] at h3
      exact absurd h3 (by decide)
  · exact eq_top_of_card_eq R (hk.trans card_GL32_gh.symm)

@[expose] def SL32EquivGL32 : SL(3, ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => by
      have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
        have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
          g.isUnit.map Matrix.detMonoidHom
        obtain ⟨u, hu⟩ := hu
        rw [← hu, Subsingleton.elim u 1, Units.val_one]
      exact ⟨⟨g, hdet⟩, Units.ext rfl⟩⟩

variable {G : Type*} [Group G]

theorem nonempty_mulAut_equiv_GL32 {V : Subgroup G} [Finite V] (hV : CFSG.Open.IsElemAbelian 2 V)
    (h8 : Nat.card V = 8) : Nonempty (MulAut ↥V ≃* GL (Fin 3) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥V) (p := 2)
    (n := 3) (fun a b => hV.1.is_comm.comm a b) (fun a => Subtype.ext (hV.2 a a.2))
    (by rw [h8]; norm_num)
  exact ⟨CFSG.SectionRank.Ccomm.elemAutEquivGL e⟩

theorem exists_GL32_of_dvd_index [Finite G] {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (h8 : Nat.card V = 8)
    (h56 : 56 ∣ ((centralizer (V : Set G)).subgroupOf (normalizer (V : Set G))).index) :
    ∃ θ : ↥(normalizer (V : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective θ ∧
      θ.ker = (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G)) := by
  obtain ⟨e⟩ := nonempty_mulAut_equiv_GL32 hV h8
  have hker := V.normalizerMonoidHom_ker
  have hR : V.normalizerMonoidHom.range.map e.toMonoidHom = ⊤ := by
    refine eq_top_of_dvd_card_GL32 ?_
    rw [card_map_of_injective e.injective, ← Subgroup.index_ker, hker]
    exact h56
  refine ⟨e.toMonoidHom.comp V.normalizerMonoidHom, fun g => ?_, ?_⟩
  · obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (hR ▸ mem_top g : g ∈ V.normalizerMonoidHom.range.map
      e.toMonoidHom)
    exact ⟨n, hn⟩
  · rw [← hker]
    ext n
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

end CFSG.ComponentClassification.GHarris
