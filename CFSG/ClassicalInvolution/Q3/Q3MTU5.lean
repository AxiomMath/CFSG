module

public import CFSG.ClassicalInvolution.Q3.Q3MTKind
public import CFSG.ClassicalInvolution.Q3.Q3MTModel1
public import CFSG.ClassicalInvolution.Q3.Q3MTDatum
public import CFSG.ClassicalInvolution.Asc77.AscMuTabBigTenU

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open scoped MatrixGroups


section Orders

theorem u5_two_pow_factorization_eight_aux : (2 : ℕ) ^ (Nat.factorization 24) 2 = 8 := by
  have h : (Nat.factorization 24) 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have h1 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    have h0 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  rw [h]
  norm_num

theorem u5_two_pow_factorization_four_aux : (2 : ℕ) ^ (Nat.factorization 4) 2 = 4 := by
  have h : (Nat.factorization 4) 2 = 2 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have h1 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h1, padicValNat.prime_pow]
  rw [h]
  norm_num

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem natCard_sylow_member3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) {J R : Subgroup G} (hJ : J ∈ Ω)
    (hR : IsSylow2In R J) : Nat.card R = 8 := by
  obtain ⟨z, hz⟩ := hΩ.classical J hJ
  have hs : (MemberType.sl2 3 1).IsSolvableType := (by norm_num : (3 : ℕ) ^ 1 = 3)
  obtain ⟨eL⟩ := hz.nonempty_equiv_sl2Three hs
  rw [natCard_isSylow2In_eq hR, Nat.card_congr eL.toEquiv, natCard_sl2Three]
  exact u5_two_pow_factorization_eight_aux

theorem mem_USet3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) {J : Subgroup G} (hJ : J ∈ Ω) {x : G}
    (hx : x ∈ J) (hord : orderOf x = 4) : Subgroup.zpowers x ∈ USet Ω := by
  have hcardT : Nat.card (Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hord]
  have hT2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [hcardT]; norm_num)
  obtain ⟨R, -, hRJ, hTR⟩ := exists_mem_RSet_ge hJ hT2 (Subgroup.zpowers_le.mpr hx)
  exact mem_USet_of_natCard hJ hRJ hTR inferInstance
    (by rw [natCard_sylow_member3 hΩ hJ hRJ, hcardT])

end Orders

section Ten

theorem shapeBig10_psu5_3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}
    (M : Ih8Model 3 1 Ω .PSU 5 e) (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hne : Ω.Nonempty) :
    ShapeBig10 Ω := by
  have hG2 : (.PSU : StatedLieTag) ≠ .G2 := by decide
  have hD4 : (.PSU : StatedLieTag) ≠ .trialityD4 := by decide
  have hnpsl : ¬ ((.PSU : StatedLieTag) = .PSL ∧ (5 : ℕ) = 2) := by simp
  obtain rfl : e = 1 := M.exp_eq_f hD4
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have h2 : (2 : GaloisField 3 (2 * 1)) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 M.admissible
  obtain ⟨u₀, hu₀⟩ := exists_orderOf_two_part
    (normOne (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1))
  have hcardN : Nat.card (normOne (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1)) = 4 := by
    rw [Phan.card_normOne hK]
    norm_num
  have hord4 : 2 ^ (Nat.card (normOne (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1))
      ).factorization 2 = 4 := by
    rw [hcardN]
    exact u5_two_pow_factorization_four_aux
  let T : Fin 10 → Pair 5 := fun k =>
    ⟨{(pairs5 k).1, (pairs5 k).2}, Finset.card_pair (ne_of_lt (pairs5_lt k))⟩
  let R : Fin 10 → Subgroup (modelUniv .PSU 5 3 1 Fact.out).K := fun k =>
    (LcU (GaloisField 3 (2 * 1)) 3 1 (T k)).map φ.symm.toMonoidHom
  have hRmem : ∀ k, R k ∈ M.cls := by
    intro k
    refine M.fund_subset_cls hne hG2 hD4 ((hφ _).mpr ?_)
    rw [muTab_map_equiv_symm_map]
    exact LcU_mem_longRootSetU h2 _ (T k)
  let y : Fin 10 → Su (GaloisField 3 (2 * 1)) 3 1 5 := fun k =>
    diagSUHom (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 5
      ⟨pairDiag (pairs5 k).1 (pairs5 k).2 u₀, (mem_detKer (σ := unitaryInvolution
        (GaloisField 3 (2 * 1)) 3 1)).mpr (prod_pairDiag (ne_of_lt (pairs5_lt k)) u₀)⟩
  have hy_mem : ∀ k, y k ∈ LcU (GaloisField 3 (2 * 1)) 3 1 (T k) := fun k =>
    diagSU_pairDiag_mem_LcU (ne_of_lt (pairs5_lt k)) u₀
  have hy_ord : ∀ k, orderOf (y k) = 4 := fun k =>
    ((orderOf_diagSUHom_pairDiag (ne_of_lt (pairs5_lt k)) u₀).trans hu₀).trans hord4
  let Q₀ : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 5) :=
    (CommGroup.primaryComponent (detKer (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 5) 2).map
      (diagSUHom (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 5)
  have hQ₀ : IsPGroup 2 Q₀ := CommGroup.primaryComponent.isPGroup.map _
  have hy_Q : ∀ k, y k ∈ Q₀ := by
    intro k
    refine ⟨⟨pairDiag (pairs5 k).1 (pairs5 k).2 u₀, (mem_detKer (σ := unitaryInvolution
      (GaloisField 3 (2 * 1)) 3 1)).mpr (prod_pairDiag (ne_of_lt (pairs5_lt k)) u₀)⟩, ?_, rfl⟩
    refine ⟨(Nat.card (normOne (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1))).factorization 2,
      ?_⟩
    refine Subtype.ext ?_
    show (pairDiag (pairs5 k).1 (pairs5 k).2 u₀) ^ 2 ^ (Nat.card (normOne (unitaryInvolution
      (GaloisField 3 (2 * 1)) 3 1))).factorization 2 = 1
    rw [pairDiag_pow, ← hu₀, pow_orderOf_eq_one]
    funext l
    simp [pairDiag]
  refine ⟨fun k => (R k).map M.ψ, fun k => Subgroup.zpowers (M.ψ (φ.symm (y k))),
    (Q₀.map φ.symm.toMonoidHom).map M.ψ, ?_, (hQ₀.map _).map _,
    fun k => ⟨M.map_mem (hRmem k), ?_, ?_, ?_⟩⟩
  · intro k l h
    have h1 := map_inj3 M hG2 hD4 (hRmem k) (hRmem l) h
    have h3 := Subgroup.map_injective φ.symm.injective h1
    exact pairs5_inj k l (congrArg Subtype.val (LcU_injective hK hp2 (by omega) h3))
  · refine mem_USet3 hΩ (M.map_mem (hRmem k))
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (hy_mem k))) ?_
    have h := M.muTab_orderOf_map hnpsl (hRmem k) (Subgroup.mem_map_of_mem _ (hy_mem k))
    exact h.trans ((MulEquiv.orderOf_eq φ.symm (y k)).trans (hy_ord k))
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (hy_mem k)))
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (hy_Q k)))

end Ten

section Field

theorem psu5Shape3 : SmallShape3 .PSU 5 := by
  intro G _ _ _ Ω hΩ _ hne _ hL
  have hshape : KindShape Ω (muKind false .PSU 5) = ShapeBig10 Ω := by
    simp [muKind]
    rfl
  rw [hshape]
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  exact shapeBig10_psu5_3 M hΩ hne

end Field

end CFSG.ClassicalInvolution.Q3.Q3MT
