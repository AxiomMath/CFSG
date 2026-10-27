module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmA2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPMerge
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.StandardType
open CFSG.RankThree.Classical2 (orthDerived)
open QuadraticMap (polarBilin)
open LinearMap (BilinForm)

private theorem exists_simple_centralizer_of_equiv {F V : Type} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (hF : 4 ≤ Nat.card F)
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate) {R : Type} [Group R]
    (e : R ≃* ↥(orthDerived Q)) {X : Subgroup R} (hX : IsElemAbelian 3 X)
    (hcard : Nat.card X = 3 ^ 3) {d : R} (hd : d ∈ X) :
    ∃ Y ≤ X, d ∈ Y ∧ Nat.card Y = 3 ^ 2 ∧ ∃ A : Subgroup R,
      A ≤ Subgroup.centralizer (Y : Set R) ∧ IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧
      3 ∣ Nat.card A := by
  set ι : R →* (V ≃ₗ[F] V) := (orthDerived Q).subtype.comp e.toMonoidHom with hι
  have hιinj : Function.Injective ι := (orthDerived Q).subtype_injective.comp e.injective
  have hιO : ∀ r, ι r ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun r =>
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (e r).2
  have hιr : orthDerived Q ≤ ι.range := fun v hv => ⟨e.symm ⟨v, hv⟩, by simp [hι]⟩
  have hXr : X.map ι ≤ ι.range := by
    rintro _ ⟨r, -, rfl⟩
    exact ⟨r, rfl⟩
  have hXO : X.map ι ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨r, -, rfl⟩
    exact hιO r
  obtain ⟨Y', hY'X, hdY', hY'c, U, t, htY', hU4, hUnd, htU, htfix, hYt⟩ :=
    SG.exists_merged_block hQ hXO (hX.map ι)
      (by rw [Subgroup.card_map_of_injective hιinj, hcard]) (Subgroup.mem_map_of_mem ι hd)
  obtain ⟨A', hA'Ω, hA's, hA'nc, hA'3, hA'c⟩ := SG.exists_sl2_commuting F V hF Q U hU4 hUnd t
    (hXO (hY'X htY')) ((hX.map ι).2 t (hY'X htY')) htU htfix
  let φ : ↥(A'.comap ι) ≃* ↥A' := (Subgroup.equivMapOfInjective _ ι hιinj).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (hA'Ω.trans hιr)))
  refine ⟨Y'.comap ι, fun r hr => ?_, hdY', ?_, A'.comap ι, fun a ha => ?_, φ.isSimpleGroup,
    ?_, ?_⟩
  · obtain ⟨x, hx, hxr⟩ := hY'X hr
    rwa [← hιinj hxr]
  · rw [← Subgroup.card_map_of_injective hιinj, Subgroup.map_comap_eq_self (hY'X.trans hXr),
      hY'c]
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk⟩ := hYt (ι y) hy
    exact hιinj (by rw [map_mul, map_mul]; exact (hA'c (ι y) (hιO y) k hk (ι a) ha).symm)
  · obtain ⟨a, b, hab⟩ := hA'nc
    exact ⟨φ.symm a, φ.symm b, fun h => hab (by simpa using congrArg φ h)⟩
  · rw [Nat.card_congr φ.toEquiv]
    exact hA'3

private theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem SG.exists_simple_centralizer_omPlus {K : Type} [Field K] [Finite K] {n m : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hm : 1 ≤ m) {X : Subgroup (OrthRest.RPlus K m)}
    (hX : IsElemAbelian 3 X) (hcard : Nat.card X = 3 ^ 3) {d : OrthRest.RPlus K m}
    (hd : d ∈ X) :
    ∃ Y ≤ X, d ∈ Y ∧ Nat.card Y = 3 ^ 2 ∧ ∃ A : Subgroup (OrthRest.RPlus K m),
      A ≤ Subgroup.centralizer (Y : Set (OrthRest.RPlus K m)) ∧ IsSimpleGroup A ∧
      (∃ a b : A, a * b ≠ b * a) ∧ 3 ∣ Nat.card A := by
  haveI := charP_two_of_card hK
  exact exists_simple_centralizer_of_equiv (hK ▸ four_le_two_pow hn)
    (TableBOrth.nondegenerate_qPlusForm m) (OrthTorus.rPlusEquiv K hm) hX hcard hd

theorem SG.exists_simple_centralizer_omMinus {K : Type} [Field K] [Finite K] {n m : ℕ}
    {b c : K} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {X : Subgroup (OrthRest.RMinus K m b c)} (hX : IsElemAbelian 3 X)
    (hcard : Nat.card X = 3 ^ 3) {d : OrthRest.RMinus K m b c} (hd : d ∈ X) :
    ∃ Y ≤ X, d ∈ Y ∧ Nat.card Y = 3 ^ 2 ∧ ∃ A : Subgroup (OrthRest.RMinus K m b c),
      A ≤ Subgroup.centralizer (Y : Set (OrthRest.RMinus K m b c)) ∧ IsSimpleGroup A ∧
      (∃ a b : A, a * b ≠ b * a) ∧ 3 ∣ Nat.card A := by
  haveI := charP_two_of_card hK
  exact exists_simple_centralizer_of_equiv (hK ▸ four_le_two_pow hn)
    (TableBOrth.nondegenerate_qMinusForm m hirr) (OrthTorus.rMinusEquiv K m b c) hX hcard hd

end CFSG.LocalAnalysis.GLTheoremA.S265

end
