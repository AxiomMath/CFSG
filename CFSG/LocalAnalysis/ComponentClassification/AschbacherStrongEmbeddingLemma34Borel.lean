module

public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.BenderSuzuki

theorem eq_normalizer_of_stronglyEmbedded {X : Type} [Group X] [Finite X]
    (hX : IsSimpleGroup X) {M : Subgroup X} (hM : fusionStronglyEmbedded M)
    (hr : CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo X) :
    ∃ T : Sylow 2 X, M = Subgroup.normalizer ((T : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hM.to_native
  have hL : involutionCore X = ⊤ := hn.involutionCore_eq_top_of_isSimple hX
  rcases theorem_SE M hn with hlow | hB
  · exact absurd (twoRankAtLeastTwo_involutionCore_iff.mpr hr) hlow
  obtain ⟨-, -, hborel⟩ := hB
  set L := involutionCore X with hLdef
  set O := twoPrimeCore L with hOdef
  let e : L ≃* X := (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv
  have he : ∀ l : L, e l = (l : X) := fun _ => rfl
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := L))
  have hXeven : Even (Nat.card X) :=
    hM.2.1.two_dvd.trans (Subgroup.card_subgroup_dvd_card M) |> (even_iff_two_dvd.mpr)
  have hObot : O = ⊥ := by
    have hN : (O.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map (inferInstance : O.Normal) e.toMonoidHom e.surjective
    rcases hX.eq_bot_or_eq_top_of_normal (O.map e.toMonoidHom) with h1 | h1
    · exact (Subgroup.map_eq_bot_iff_of_injective O e.injective).mp h1
    · exfalso
      have hcard : Nat.card O = Nat.card X := by
        rw [← Subgroup.card_map_of_injective
          (show Function.Injective e.toMonoidHom from e.injective), h1, Subgroup.card_top]
      rw [hcard] at hOodd
      exact (Nat.not_even_iff_odd.mpr hOodd) hXeven
  set π := QuotientGroup.mk' O with hπdef
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hObot
  let φ : L ≃* (L ⧸ O) := MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective O⟩
  let ψ : (L ⧸ O) ≃* X := φ.symm.trans e
  obtain ⟨-, S', hS'⟩ := hborel
  refine ⟨S'.mapSurjective (show Function.Surjective ψ.toMonoidHom from ψ.surjective), ?_⟩
  change M = Subgroup.normalizer (((S' : Subgroup (L ⧸ O)).map ψ.toMonoidHom : Subgroup X) :
    Set X)
  rw [← Subgroup.map_equiv_normalizer_eq, ← hS']
  have hxL : ∀ x : X, x ∈ L := fun x => by rw [hL]; exact Subgroup.mem_top x
  ext x
  constructor
  · intro hx
    refine ⟨π ⟨x, hxL x⟩, ⟨⟨x, hxL x⟩, ⟨hx, hxL x⟩, rfl⟩, ?_⟩
    change e (φ.symm (φ ⟨x, hxL x⟩)) = x
    rw [MulEquiv.symm_apply_apply]
    rfl
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    change e (φ.symm (φ l)) ∈ M
    rw [MulEquiv.symm_apply_apply, he]
    exact (Subgroup.mem_inf.mp hl).1

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
