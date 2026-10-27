module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphAltEight
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphProd
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphAltEightFinalGL
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

theorem exists_mulSingle_of_equiv {R : Type} [Group R] {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] (hG : ∀ i, Prod.ProdFactor (G i))
    (e : R ≃* ∀ i, G i) {X : Subgroup R} (hX : Sym.IsSymThree X) (hXs : IsSubnormal X ⊤) :
    ∃ i, Nonempty (G i ≃* Equiv.Perm (Fin 3)) ∧
      X.map e.toMonoidHom = (⊤ : Subgroup (G i)).map (MonoidHom.mulSingle G i) := by
  have hXs' : IsSubnormal (X.map e.toMonoidHom) ⊤ :=
    IsSubnormal.top_iff.2 ((IsSubnormal.top_iff.1 hXs).map e.surjective)
  have hX' : Sym.IsSymThree (X.map e.toMonoidHom) := by
    obtain ⟨eX⟩ := hX
    exact ⟨(X.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eX⟩
  exact Prod.exists_mulSingle_eq_of_subnormal_symThree hG hX' hXs'

theorem false_of_three_members {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hA8 : Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin 8)))
    (hP : IsParabolicTwo Y P)
    {X X' X₁ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hX : Sym.IsSymThree X)
    (hX' : Sym.IsSymThree X') (hXs : IsSubnormal X ⊤) (hXs' : IsSubnormal X' ⊤) (hne : X ≠ X')
    (hX₁s : IsSubnormal X₁ ⊤) (hX₁ : IsSymThreeOrSUThreeTwo ↥X₁ ∨ Open.IsQuasisimple ↥X₁)
    (h1 : X₁ ≠ X) (h2 : X₁ ≠ X') : False := by
  classical
  obtain ⟨K, _, _, a, hK, hsum, ⟨e⟩⟩ := exists_levi_equiv hY hO hA8 hP
  have ha4 : ∀ i, a i ≤ 4 := fun i =>
    (Finset.single_le_sum (f := a) (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans hsum
  have hG : ∀ i, Prod.ProdFactor (GL (Fin (a i)) K) := fun i => prodFactor_gl_fin hK (ha4 i)
  obtain ⟨i, ⟨ei⟩, hi⟩ := exists_mulSingle_of_equiv hG e hX hXs
  obtain ⟨j, ⟨ej⟩, hj⟩ := exists_mulSingle_of_equiv hG e hX' hXs'
  have hij : i ≠ j := by
    rintro rfl
    exact hne (Subgroup.map_injective e.injective (hi.trans hj.symm))
  have hai := two_le_of_mulEquiv_perm_three hK ei
  have haj := two_le_of_mulEquiv_perm_three hK ej
  have hk0 : ∀ k, k ≠ i → k ≠ j → a k = 0 := by
    intro k hki hkj
    have h3 := Finset.sum_le_sum_of_subset (f := a)
      (Finset.subset_univ ({i, j, k} : Finset (Fin 4)))
    rw [Finset.sum_insert (by simp [hij, Ne.symm hki]), Finset.sum_pair (Ne.symm hkj)] at h3
    omega
  have hcard : Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_eq_mul i j hij ?_
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
    · rw [SymThree.card_eq_six_of_mulEquiv ei, SymThree.card_eq_six_of_mulEquiv ej]
      norm_num
    · rintro k - ⟨hki, hkj⟩
      exact natCard_gl_fin_of_le_one hK (by have := hk0 k hki hkj; omega)
  haveI : Group.IsSolvable (↥P ⧸ CFSG.pCore 2 ↥P) := by
    haveI := Fintype.ofFinite (↥P ⧸ CFSG.pCore 2 ↥P)
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 2) (b := 2) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  rcases hX₁ with (he₁ | ⟨K', _, _, hK', ⟨f⟩⟩) | hq
  ·
    obtain ⟨k, ⟨ek⟩, hk⟩ := exists_mulSingle_of_equiv hG e (X := X₁) he₁ hX₁s
    have hki : k ≠ i := by
      rintro rfl
      exact h1 (Subgroup.map_injective e.injective (hk.trans hi.symm))
    have hkj : k ≠ j := by
      rintro rfl
      exact h2 (Subgroup.map_injective e.injective (hk.trans hj.symm))
    have := hk0 k hki hkj
    have := two_le_of_mulEquiv_perm_three hK ek
    omega
  ·
    have h216 : Nat.card ↥X₁ = 216 := by
      rw [Nat.card_congr f.toEquiv,
        CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq (q := 2)
          (by rw [hK']; norm_num)]
      norm_num
    have hd := Subgroup.card_subgroup_dvd_card X₁
    rw [h216, hcard] at hd
    omega
  ·
    obtain ⟨hperf, hsimple⟩ := hq
    haveI : Group.IsPerfect ↥X₁ := Group.isPerfect_def.mpr hperf
    haveI : Nontrivial ↥X₁ := (QuotientGroup.mk'_surjective (Subgroup.center ↥X₁)).nontrivial
    exact Group.IsPerfect.not_isSolvable (G := ↥X₁) inferInstance

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight
