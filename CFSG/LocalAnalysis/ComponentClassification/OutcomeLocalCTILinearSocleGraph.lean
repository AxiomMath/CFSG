module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleField
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleSteps
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open FourGroupEvenCanonical UnitaryHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A}
  {n e : ℕ} {K : Type} [Field K]

theorem linear_socle_pure_graph_setup (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 3 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    {Aₘ : GL (Fin n) K} (hρa : ρ a = conjAut n K Aₘ * dualAut n K) :
    ∃ H C : GL (Fin n) K,
      (((C : Matrix (Fin n) (Fin n) K) = 1 ∧ Odd n) ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∧
      ρ a = conjAut n K H * (conjAut n K C * dualAut n K) * (conjAut n K H)⁻¹ ∧
      (centralizer {a}).map ρ = ρ.range ⊓ (centralizer {conjAut n K C * dualAut n K}).map
        (MulAut.conj (conjAut n K H)).toMonoidHom ∧
      (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓
        (centralizer {conjAut n K C * dualAut n K}).map
          (MulAut.conj (conjAut n K H)).toMonoidHom ∧
      (centralizer {conjAut n K C * dualAut n K} : Set (MulAut (projectiveSL n K))) =
        {α | ∃ g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K), ∃ (τ : K ≃+* K) (ε : ℕ),
          ε ≤ 1 ∧ α = conjAut n K g * fieldAut n K τ * (conjAut n K C * dualAut n K) ^ ε} ∧
      Function.Injective
        ((conjAut n K).comp (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).subtype) ∧
      CFSG.Assembly.IsComponentOf ((L.map ρ).map (MulAut.conj (conjAut n K H)⁻¹).toMonoidHom)
        ((conjAut n K).comp (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).subtype).range
        := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have hα2 : (conjAut n K Aₘ * dualAut n K) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨-, ⟨H, C, -, hconj, hCcase⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms he hK hn Aₘ hα2
  have hC' : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rcases hCcase with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, hr, hJ⟩
  obtain ⟨hinjO, hNinn, -, hCset, hNC, hNnormal, hcan⟩ :=
    even_linear_canonical_graph_symplectic_centralizers he hK hn C hC'
  set χ := conjAut n K H with hχ
  set β := conjAut n K C * dualAut n K with hβ
  have hρa' : ρ a = χ * β * χ⁻¹ := by rw [hρa, hconj]
  have hCa : centralizer {ρ a} = (centralizer {β}).map (MulAut.conj χ).toMonoidHom := by
    rw [hρa', map_conj_centralizer_singleton']
  have hW : W.map ρ = inner (projectiveSL n K) := map_eq_range_conj φ hρW
  have hWle : inner (projectiveSL n K) ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (inner (projectiveSL n K) ⊓ centralizer {ρ a}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCWimg] at this
  have hY : (inner (projectiveSL n K) ⊓ centralizer {ρ a}).map (MulAut.conj χ⁻¹).toMonoidHom =
      inner (projectiveSL n K) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀ (inner (projectiveSL n K) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have : Finite (MulAut (projectiveSL n K)) :=
    Finite.of_injective (fun χ : MulAut (projectiveSL n K) => (χ : projectiveSL n K → _))
      (fun χ₁ χ₂ h => MulEquiv.ext (congrFun h))
  have hrange : ((conjAut n K).comp (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).subtype
      ).range = (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hcase : ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ Odd n) ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rcases hC' with h1 | hJ
    · rcases Nat.even_or_odd n with ⟨r, hr⟩ | hodd
      · exfalso
        have hC1 : C = 1 := Units.ext h1
        have hβδ : β = dualAut n K := by rw [hβ, hC1, map_one, one_mul]
        rw [hβδ] at hL₀
        obtain ⟨-, -, -, -, -, -, -, -, -, hRinn, hRC, hRnormal, hCR, hRp, -⟩ :=
          even_linear_nonalternating_graph_radical he hK (show n = 2 * r by omega) (by omega)
            ⟨0, by omega⟩
        refine UnbalancingLocal.ComponentFree.no_component_of_two_radical
          (le_inf hRinn hRC) (fun x hx => mem_normalizer_of_normal_subgroupOf hRC hRnormal hx.2)
          (fun r hr => ?_) (fun x hx hxc => ?_) _
          ((isComponentOf_iff_isComponent_subgroupOf hL₀.1).mp hL₀)
        · obtain ⟨k, hk⟩ := hRp ⟨r, mem_sup_left hr⟩
          exact ⟨k, by simpa using congrArg Subtype.val hk⟩
        · have hxm : x ∈ centralizer {dualAut n K} ⊓ centralizer
              (((NonalternatingRadical.radicalGroup (K := K) (⟨0, by omega⟩ : Fin n)).map
                (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
                  Set (MulAut (projectiveSL n K))) := mem_inf.mpr ⟨hx.2, hxc⟩
          rw [hCR] at hxm
          obtain ⟨k, hk⟩ := hRp ⟨x, hxm⟩
          exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      · exact Or.inl ⟨h1, hodd⟩
    · exact Or.inr hJ
  have hcen := (hcan (by
    rcases hcase with ⟨h1, hodd⟩ | hJ
    · exact Or.inr ⟨h1, hodd⟩
    · exact Or.inl hJ)).1
  have hL₀N : CFSG.Assembly.IsComponentOf L₀
      ((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K)) := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x hx hxc y hy hyc
    have hx' : x ∈ centralizer {β} ⊓ centralizer (((matrixIsometryGroup (C : Matrix (Fin n)
        (Fin n) K)).map (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
          Set (MulAut (projectiveSL n K))) := mem_inf.mpr ⟨hx.2, hxc⟩
    have hy' : y ∈ centralizer {β} ⊓ centralizer (((matrixIsometryGroup (C : Matrix (Fin n)
        (Fin n) K)).map (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
          Set (MulAut (projectiveSL n K))) := mem_inf.mpr ⟨hy.2, hyc⟩
    rw [hcen] at hx' hy'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy'
    exact (Commute.zpow_zpow_self β i j).eq
  refine ⟨H, C, hcase, hρa', by rw [hCAimg, hCa], by rw [hCWimg, hCa], hCset, hinjO, ?_⟩
  rw [hrange]
  exact hL₀N

theorem isSolvable_matrixIsometryGroup_one_of_card_two {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {n : ℕ} (hn : n = 2 * 1 + 1) :
    Group.IsSolvable (matrixIsometryGroup ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
  have := Fintype.ofFinite k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hk])
  obtain ⟨eSL⟩ := exists_planeIsometryEquivSL _ (dotForm_restrict_isAlt (k := k) (n := n))
    (dotForm_restrict_nondegenerate hn) (by rw [finrank_dotForm_ker hn])
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) k) :=
    CatalogueBGeneralLinear.generalLinear_two_small_solvable k (Or.inl hk)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL.comp eSL.toMonoidHom).comp
      (oneRestrictEquiv (k := k) hn).toMonoidHom)
    ((Matrix.SpecialLinearGroup.toGL_injective.comp eSL.injective).comp
      (oneRestrictEquiv (k := k) hn).injective)

theorem ringEquiv_eq_one_of_card_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    (τ : k ≃+* k) : τ = 1 := by
  classical
  have := Fintype.ofFinite k
  have hk2 : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  have huniv : (Finset.univ : Finset k) = {0, 1} :=
    (Finset.eq_univ_of_card {0, 1} (by rw [Finset.card_pair zero_ne_one, hk2])).symm
  refine RingEquiv.ext fun x => ?_
  have hx : x ∈ ({0, 1} : Finset k) := huniv ▸ Finset.mem_univ x
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · rw [map_zero]
    rfl
  · rw [map_one]
    rfl

theorem linear_socle_pure_graph_case [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 3 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    (hWalt : ∀ m : ℕ, 5 ≤ m → IsEmpty (W ≃* alternatingGroup (Fin m)))
    {Aₘ : GL (Fin n) K} (hρa : ρ a = conjAut n K Aₘ * dualAut n K) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) :
    ∃ c : GL (Fin n) K,
      (let β := dualAut n K
       let O := matrixIsometryGroup ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
       let N := O.map (conjAut n K)
       let N' : Subgroup (MulAut (projectiveSL n K)) := ⁅N, N⁆
       let B := Matrix.toBilin' ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
       let dperp := LinearMap.ker (B fun _ => 1)
       ρ a = conjAut n K c * β * (conjAut n K c)⁻¹ ∧
       (centralizer {a}).map ρ = ρ.range ⊓
         (centralizer {β}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
       (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓
         (centralizer {β}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
       Function.Injective ((conjAut n K).comp O.subtype) ∧
       (∀ g : O, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun _ => 1) =
         fun _ => 1) ∧
       (∃ R : O ≃* isometryGroup (B.restrict dperp),
         ∀ g w, ((R g).1 w : Fin n → K) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) ∧
       ((n = 3 ∧ e = 2 ∧ p = 5 ∧ f = 1 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
           (centralizer {β} : Set (MulAut (projectiveSL n K))) =
             {α | ∃ g ∈ O, ∃ (τ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
               α = conjAut n K g * fieldAut n K τ * β ^ ε} ∧
           Nonempty (isometryGroup (B.restrict dperp) ≃* StatedSp 1 K) ∧
           Nonempty (isometryGroup (B.restrict dperp) ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
           L.map ρ = N.map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
           Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∨
         (n = 5 ∧ e = 1 ∧ p = 3 ∧ f = 2 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
           (centralizer {β} : Set (MulAut (projectiveSL n K))) =
             {α | ∃ g ∈ O, ∃ ε : ℕ, ε ≤ 1 ∧ α = conjAut n K g * β ^ ε} ∧
           Nonempty (isometryGroup (B.restrict dperp) ≃* StatedSp 2 K) ∧
           (∃ E : N ≃* PresentationLocal.sympFour, ∀ x : N,
             (x : MulAut (projectiveSL n K)) ∈ N' ↔
               PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
           Nonempty (N ≃* Equiv.Perm (Fin 6)) ∧ Nonempty (N' ≃* alternatingGroup (Fin 6)) ∧
           L.map ρ = N'.map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
           Nonempty (L ≃* alternatingGroup (Fin 6))))) ∧
      IsSimpleGroup L ∧ IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  obtain ⟨H, C, hcase, hρa', hCA, hCW, hCset, hinjO, hL₀⟩ :=
    linear_socle_pure_graph_setup ha hLCW hn he hK φ hinj hρW hρa
  have hLnab := exists_ne_commute_of_isQuasisimple hLCW.2.2
  set χ := conjAut n K H with hχ
  have eY : L ≃* (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom :=
    (L.equivMapOfInjective ρ hinj).trans
      ((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective)
  have hid : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  have hback : ∀ X : Subgroup (MulAut (projectiveSL n K)),
      (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom = X →
        L.map ρ = X.map (MulAut.conj χ).toMonoidHom := by
    intro X hX
    rw [← hX, Subgroup.map_map, hid, Subgroup.map_id]
  have : Finite (GL (Fin n) K) := Finite.of_injective Units.val Units.val_injective
  rcases hcase with ⟨hC1, ⟨r, hr⟩⟩ | ⟨r, hr, hCJ⟩
  ·
    have hC1' : C = 1 := Units.ext hC1
    subst hC1'
    have hβ : conjAut n K 1 * dualAut n K = dualAut n K := by rw [map_one, one_mul]
    rw [hβ] at hρa' hCA hCW hCset
    have hrange : ((conjAut n K).comp (matrixIsometryGroup ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)).subtype).range =
          (matrixIsometryGroup ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map
            (conjAut n K) := by
      rw [MonoidHom.range_comp, range_subtype]
    by_cases hq : n = 3 ∧ 2 ^ e = 2
    ·
      exfalso
      have he1 : e = 1 := Nat.pow_right_injective (le_refl 2) (hq.2.trans (pow_one 2).symm)
      have hsolv := isSolvable_matrixIsometryGroup_one_of_card_two (k := K)
        (by rw [hK, he1, pow_one]) (show n = 2 * 1 + 1 by omega)
      have : Group.IsSolvable ((conjAut n K).comp (matrixIsometryGroup ((1 : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)).subtype).range :=
        Group.isSolvable_of_isSolvable_injective
          (f := (MonoidHom.ofInjective hinjO).symm.toMonoidHom)
          (MonoidHom.ofInjective hinjO).symm.injective
      have hLq := hL₀.2.2
      have : Group.IsPerfect ((L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom) := ⟨hLq.1⟩
      have : IsSimpleGroup (((L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom) ⧸
          center ((L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom)) := hLq.2
      have : Nontrivial ((L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom) :=
        (QuotientGroup.mk'_surjective (center ((L.map ρ).map
          (MulAut.conj χ⁻¹).toMonoidHom))).nontrivial
      have : Group.IsSolvable ((L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hL₀.1)
          (Subgroup.inclusion_injective hL₀.1)
      exact Group.IsPerfect.not_isSolvable _ this
    obtain ⟨hrows, hYs, hPSL, hA7, -⟩ :=
      socle_rows_one (by rw [hK]) hr hn hq hinjO hL₀ eY hLnab hp2 hsrc
    refine ⟨H, ?_, hYs, hA7⟩
    rcases hrows with ⟨hn3, he2, hp5, hf1, hSp1, hSL, hXc, -, ⟨eSL⟩⟩ |
      ⟨hn5, he1, hp3, hf2, hSp2, hE, hP6, hA6, hXc, hY6⟩
    · rw [hrange] at hXc
      exact ⟨hρa', hCA, hCW, hinjO, mulVec_ones_of_mem_one,
        ⟨oneRestrictEquiv hr, oneRestrictEquiv_apply hr⟩, Or.inl ⟨hn3, he2, hp5, hf1, hPSL,
          hCset, hSp1, hSL, hback _ hXc, ⟨eSL⟩⟩⟩
    · have hfield : ∀ τ : K ≃+* K, fieldAut n K τ = 1 := fun τ => by
        rw [ringEquiv_eq_one_of_card_two (by rw [hK, he1, pow_one]) τ, map_one]
      have hCset' : (centralizer {dualAut n K} : Set (MulAut (projectiveSL n K))) =
          {α | ∃ g ∈ matrixIsometryGroup ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
            ∃ ε : ℕ, ε ≤ 1 ∧ α = conjAut n K g * dualAut n K ^ ε} := by
        rw [hCset]
        ext α
        simp only [Set.mem_ofPred_eq, hfield, mul_one]
        constructor
        · rintro ⟨g, hg, -, ε, hε, rfl⟩
          exact ⟨g, hg, ε, hε, rfl⟩
        · rintro ⟨g, hg, ε, hε, rfl⟩
          exact ⟨g, hg, 1, ε, hε, rfl⟩
      rw [hrange] at hE hP6 hA6 hXc
      exact ⟨hρa', hCA, hCW, hinjO, mulVec_ones_of_mem_one,
        ⟨oneRestrictEquiv hr, oneRestrictEquiv_apply hr⟩, Or.inr ⟨hn5, he1, hp3, hf2, hPSL,
          hCset', hSp2, hE, hP6, hA6, hback _ hXc, hY6⟩⟩
  ·
    exfalso
    obtain ⟨hn4, -, he1, -⟩ := socle_rows_blockSwap (by rw [hK]) hr hn hCJ hinjO hL₀ eY hLnab
      hp2 hsrc
    subst hn4
    have hmodel := statedClassicalModel_of_projectiveSL (n := 4) (by norm_num) le_rfl
      (by rw [hK, he1]) φ
    obtain ⟨e8⟩ := (SymmetricLocal.lie_model_linear_four_two_iff W).mp
      (Or.inl ⟨by decide, hmodel⟩)
    exact (hWalt 8 (by norm_num)).false e8

end CFSG.ComponentClassification.OutcomeLocal
