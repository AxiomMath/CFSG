module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618One

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped MatrixGroups

private theorem oneCase_conj_injective {G : Type} [Group G]
    (hZ : ∀ a : G, (∀ g : G, a * g = g * a) → a = 1) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine hZ g fun x => ?_
  have h := DFunLike.congr_fun hg x
  rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h
  exact h

private theorem oneCase_mulAut_conj_conj {G : Type} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) :=
  MulEquiv.ext fun x => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

private theorem oneCase_normal_range_conj {G : Type} [Group G] :
    ((MulAut.conj : G →* MulAut G).range).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    exact ⟨α g, (oneCase_mulAut_conj_conj α g).symm⟩

private theorem oneCase_eq_one_of_commute_conj {G : Type} [Group G]
    (hZ : ∀ a : G, (∀ g : G, a * g = g * a) → a = 1) (φ : MulAut G)
    (h : ∀ g : G, φ * MulAut.conj g = MulAut.conj g * φ) : φ = 1 := by
  ext g
  have h1 : MulAut.conj (φ g) = MulAut.conj g := by
    rw [← oneCase_mulAut_conj_conj, h g, mul_assoc, mul_inv_cancel, mul_one]
  exact oneCase_conj_injective hZ h1

private theorem oneCase_eq_one_of_commute (a : PSL(3, ZMod 2))
    (h : ∀ g : PSL(3, ZMod 2), a * g = g * a) : a = 1 := by
  have := isSimpleGroup_psl_three_two
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center PSL(3, ZMod 2)) with hc | hc
  · exact Subgroup.mem_bot.mp (hc ▸ Subgroup.mem_center_iff.mpr fun g => (h g).symm)
  · exfalso
    let : CommGroup PSL(3, ZMod 2) := Group.commGroupOfCenterEqTop hc
    have hp := IsSimpleGroup.prime_card (α := PSL(3, ZMod 2))
    rw [card_psl_three_two] at hp
    exact absurd hp (by norm_num)

theorem exists_layer_of_caseOne {Y : Type} [Group Y] [Finite Y]
    (hcase : Nonempty (Y ≃* Multiplicative (ZMod 3) × PSL(3, ZMod 2)) ∨
      Nonempty (Y ≃* Multiplicative (ZMod 3) × MulAut PSL(3, ZMod 2)))
    {D : Subgroup Y} {R : Type} [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ∃ a b : R, a * b ≠ b * a) (h3 : 3 ∣ Nat.card R) (f : ↥D →* R)
    (hf : Function.Surjective f) :
    ∃ L : Subgroup Y, ∃ hLD : L ≤ D, Nonempty (↥L ≃* PSL(3, ZMod 2)) ∧
      Function.Bijective (f.comp (Subgroup.inclusion hLD)) ∧
      ∀ Q : Subgroup Y, Nat.Coprime 3 (Nat.card Q) →
        (∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) → Q = ⊥ := by
  rcases hcase with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact exists_layer_abstract (I := (⊤ : Subgroup PSL(3, ZMod 2))) e Subgroup.topEquiv
      (by rw [Subgroup.index_top]; decide)
      (fun a h => oneCase_eq_one_of_commute a fun g => h g (Subgroup.mem_top g)) hR h3 f hf
  · have : ((MulAut.conj : PSL(3, ZMod 2) →* MulAut PSL(3, ZMod 2)).range).Normal :=
      oneCase_normal_range_conj
    let eI : ↥(MulAut.conj : PSL(3, ZMod 2) →* MulAut PSL(3, ZMod 2)).range ≃* PSL(3, ZMod 2) :=
      (MonoidHom.ofInjective (oneCase_conj_injective oneCase_eq_one_of_commute)).symm
    exact exists_layer_abstract
      (I := (MulAut.conj : PSL(3, ZMod 2) →* MulAut PSL(3, ZMod 2)).range) e eI
      not_three_dvd_index_range_conj
      (fun a h => oneCase_eq_one_of_commute_conj oneCase_eq_one_of_commute a
        fun g => h _ ⟨g, rfl⟩) hR h3 f hf

end CFSG.LocalAnalysis.RankThreeTheoremC
