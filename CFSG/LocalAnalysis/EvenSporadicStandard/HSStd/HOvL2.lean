module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvLie
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction

public section

namespace CFSG.EvenSporadicStandard.HSStd.HOv

open Equiv Subgroup CFSG.GorensteinWalter

theorem card_le_four_of_sq_eq_one_pgl2 (K : Type) [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) (E : Subgroup (PGL2 K)) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE x x.2)⟩
  obtain ⟨T, hET⟩ := hE2.exists_le_sylow
  obtain ⟨m, hm, ⟨φ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hodd T
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact CFSG.QuasithinUnique.card_le_four_of_dihedral T.isPGroup' h2m φ hET hE

theorem card_eq_mul_card_map {Γ Q : Type*} [Group Γ] [Group Q] [Finite Γ] (π : Γ →* Q)
    (A : Subgroup Γ) : Nat.card A = Nat.card ↥(A ⊓ π.ker) * Nat.card ↥(A.map π) := by
  let f : ↥A →* Q := π.comp A.subtype
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ π.ker) :=
    Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card f.range = Nat.card ↥(A.map π) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hker, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem card_le_eight_of_pGammaL2 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card K = p ^ 2) (hodd : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PGammaL2 K)) (hA : ∀ x ∈ A, x ^ 2 = 1) : Nat.card A ≤ 8 := by
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PGammaL2 K) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  rw [card_eq_mul_card_map (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) A]
  have h1 : Nat.card ↥(A ⊓ (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).ker) ≤ 4 := by
    have hmap : (A.comap (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)).map
        SemidirectProduct.inl =
        A ⊓ (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).ker := by
      rw [Subgroup.map_comap_eq, SemidirectProduct.range_inl_eq_ker_rightHom, inf_comm]
    rw [← hmap, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
    refine card_le_four_of_sq_eq_one_pgl2 K hodd _ (fun x hx => ?_)
    have : (SemidirectProduct.inl (x ^ 2) : PGammaL2 K) = 1 := by
      rw [map_pow]
      exact hA _ hx
    exact SemidirectProduct.inl_injective (this.trans (map_one _).symm)
  have h2 : Nat.card ↥(A.map (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K))) ≤ 2 :=
    (Subgroup.card_le_card_group _).trans
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hcard).1.le
  exact Nat.mul_le_mul h1 h2

theorem not_exists_elemAbelian_sixteen_of_psl_two_twentyfive {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {t : D} (ht : orderOf t = 2)
    (e : Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)))
    (hL : CFSG.Blueprint.LieModel ↥(commutator D) .PSL 2 5 2) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  rintro ⟨A, hA, hcardA⟩
  have hM := statedClassicalModel_of_lieModel (by norm_num) hL
  have hordS := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
    ↥(commutator D) 2 5 2 hM).1
  have hcardS : Nat.card ↥(commutator D) = 7800 := by rw [hordS]; decide
  have hC := centralizer_eq_bot_of_normal_of_card hZ ht e (commutator D)
    (by rw [hcardS]; norm_num) (by rw [hcardS]; norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e1⟩⟩ := hM
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK25 : Nat.card K = 5 ^ 2 := hK
  have hodd : IsOddPrimePower (Nat.card K) := ⟨5, 2, by norm_num, by decide, by norm_num, hK25⟩
  have h3 : 3 < Nat.card K := by rw [hK25]; norm_num
  let φ : ↥(commutator D) ≃* PSL2 K :=
    e1.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let Φ : PGammaL2 K ≃* MulAut (PSL2 K) := MulEquiv.ofBijective
    (pGammaL2ToMulAutPSL2 K hodd h3)
    ⟨pGammaL2ToMulAutPSL2_injective K hodd h3, pGammaL2ToMulAutPSL2_surjective K hK25 hodd h3⟩
  let ι : D →* PGammaL2 K := Φ.symm.toMonoidHom.comp (HL34.actionHom (commutator D) φ)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : HL34.actionHom (commutator D) φ d = 1 := by
      have : Φ.symm (HL34.actionHom (commutator D) φ d) = 1 := hd
      exact Φ.symm.injective (this.trans (map_one _).symm)
    have h2 := (HL34.actionHom_eq_one_iff (commutator D) φ d).1 h1
    rw [hC, mem_bot] at h2
    exact h2
  have hA' : ∀ x ∈ A.map ι, x ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  have := card_le_eight_of_pGammaL2 K (by norm_num : Nat.Prime 5) hK25 hodd (A.map ι) hA'
  rw [Subgroup.card_map_of_injective hι, hcardA] at this
  omega

end CFSG.EvenSporadicStandard.HSStd.HOv
