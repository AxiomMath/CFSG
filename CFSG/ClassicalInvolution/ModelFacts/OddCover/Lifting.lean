module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Cover

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open CFSG.LieType.Steinberg

universe v w

theorem lifting_of_noCover {X : Type v} [Group X] [Finite X] [Group.IsPerfect X] {W : Type w}
    [Group W] [Group.IsPerfect W] (hX : NoCover.{max v w} Odd X) {Z : Subgroup W} [Z.Normal]
    (hZc : Z ≤ Subgroup.center W) (hZ : Odd (Nat.card Z)) (θbar : X →* W ⧸ Z)
    (hθbar : Function.Surjective θbar) (hker : θbar.ker ≤ Subgroup.center X) :
    ∃ θ : X →* W, Function.Surjective θ ∧ θ.ker ≤ Subgroup.center X ∧
      ∀ x, (θ x : W ⧸ Z) = θbar x := by
  have : Finite Z := Nat.finite_of_card_ne_zero hZ.pos.ne'
  have : Finite (W ⧸ Z) := Finite.of_surjective θbar hθbar
  have : Finite W := Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := Z)).symm
  have hker' : (QuotientGroup.mk' Z).ker ≤ Subgroup.center W := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hQ : ∀ m n : ℕ, m ∣ n → Odd n → Odd m := fun m n hmn hn => hn.of_dvd_nat hmn
  have hodd : Odd (Nat.card (pullbackFst θbar (QuotientGroup.mk' Z)).ker) := by
    refine hQ _ _ (card_ker_pullbackFst_dvd θbar (QuotientGroup.mk' Z)) ?_
    rw [QuotientGroup.ker_mk']
    exact hZ
  obtain ⟨s, hs⟩ := exists_section_of_noCover hQ hX (pullbackFst θbar (QuotientGroup.mk' Z))
    (pullbackFst_surjective (QuotientGroup.mk'_surjective Z)) (ker_pullbackFst_le_center hker')
    hodd
  let θ : X →* W := (MonoidHom.snd X W).comp ((pullback θbar (QuotientGroup.mk' Z)).subtype.comp s)
  have hθ : ∀ x, (θ x : W ⧸ Z) = θbar x := fun x => by
    have h1 : ((s x : pullback θbar (QuotientGroup.mk' Z)) : X × W).1 = x := hs x
    have h2 := mem_pullback.1 (s x).2
    rw [h1] at h2
    exact h2.symm
  refine ⟨θ, ?_, fun x hx => hker ?_, hθ⟩
  · have htop : θ.range = ⊤ := by
      refine eq_top_of_perfect_of_central hZc (S := θ.range) (Z := Z) fun w => ?_
      obtain ⟨x, hx⟩ := hθbar (w : W ⧸ Z)
      refine ⟨θ x, ⟨x, rfl⟩, (θ x)⁻¹ * w, ?_, by group⟩
      rw [← QuotientGroup.eq, hθ, hx]
    exact MonoidHom.range_eq_top.1 htop
  · rw [MonoidHom.mem_ker, ← hθ, MonoidHom.mem_ker.1 hx, QuotientGroup.mk_one]

end CFSG.ClassicalInvolution.ModelFacts.OddCover
