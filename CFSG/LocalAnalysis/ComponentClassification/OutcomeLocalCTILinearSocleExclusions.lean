module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityUnitary
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceUnitary
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalComponentFree
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A}
  {n e : ℕ} {K : Type} [Field K]

theorem linear_socle_inner_false (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 3 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    (hZ : center (projectiveSL n K) = ⊥) {Aₘ : GL (Fin n) K} (hρa : ρ a = conjAut n K Aₘ) :
    False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have h2 : conjAut n K Aₘ ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have h1 : conjAut n K Aₘ ≠ 1 := by
    rw [← hρa]
    intro h
    rw [← map_one ρ] at h
    rw [hinj h, orderOf_one] at ha
    omega
  obtain ⟨t, ht, hct⟩ := exists_involution_eq_conjAut hn Aₘ h2 h1
  have hW : W.map ρ = inner (projectiveSL n K) := map_eq_range_conj φ hρW
  have hWle : inner (projectiveSL n K) ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (inner (projectiveSL n K) ⊓ centralizer {MulAut.conj t}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCWimg, hρa, hct] at this
  have hconj := conj_injective_of_center_eq_bot hZ
  exact UnbalancingLocal.ComponentFree.no_component_of_mulEquiv
    (UnbalancingLocal.ComponentFree.centralizerRangeEquiv hconj t).symm
    (even_linear_involution_centralizers_component_free he (by omega) hK t ht) _
    ((isComponentOf_iff_isComponent_subgroupOf hL₁.1).mp hL₁)

theorem card_psu_three_two {K : Type} [Field K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ 1) K)) = 72 := by
  rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by norm_num) hK
    (by norm_num)]
  decide

theorem linear_socle_graph_field_false (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 3 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    {Aₘ : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut n K Aₘ * fieldAut n K σ * dualAut n K) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) : False := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα2 : (conjAut n K Aₘ * fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two he hK hn Aₘ σ hσ hα2
  have hg : 1 ≤ e / 2 := by obtain ⟨m, hm⟩ := heven; omega
  have hKe : Nat.card K = 2 ^ (2 * (e / 2)) := by
    rw [hK]
    congr 1
    obtain ⟨m, hm⟩ := heven
    omega
  have hud : UnitaryFieldData 2 (e / 2) K := ⟨Nat.prime_two, hg, hKe⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by rw [hσx, hud.bar_apply]
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_graph_field_full_centralizer_rigidity hud hn σ hσbar
  set χ := conjAut n K H with hχ
  set β := fieldAut n K σ * dualAut n K with hβ
  set N := (unitarySU 2 (e / 2) K n).map (conjAut n K) with hNdef
  have hρa' : ρ a = χ * β * χ⁻¹ := by rw [hρa, hH]
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
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have hK2 : Nat.card K = (2 ^ (e / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
  have eU : unitaryPSU hud n ≃* StatedProj (StatedSU n (2 ^ (e / 2)) K) :=
    unitaryPSUEquiv hud (by omega)
  by_cases h32 : n = 3 ∧ 2 ^ (e / 2) = 2
  ·
    obtain ⟨hn3, hq2⟩ := h32
    have he1 : e / 2 = 1 := by
      have := Nat.pow_right_injective (le_refl 2) (hq2.trans (pow_one 2).symm)
      exact this
    have hcard : Nat.card N = 72 := by
      rw [← Nat.card_congr ι.toEquiv, Nat.card_congr eU.toEquiv]
      subst hn3
      rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hg hK2
        (by norm_num), hq2]
      decide
    have hsolv : Group.IsSolvable N := isSolvable_of_card_primeFactors_le_two (by
      rw [hcard, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide)
    have hLq := hL₀N.2.2
    have : Group.IsPerfect L₀ := ⟨hLq.1⟩
    have : IsSimpleGroup (L₀ ⧸ center L₀) := hLq.2
    have : Nontrivial L₀ := (QuotientGroup.mk'_surjective (center L₀)).nontrivial
    have : Group.IsSolvable L₀ := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hL₀N.1) (Subgroup.inclusion_injective hL₀N.1)
    exact Group.IsPerfect.not_isSolvable L₀ this
  ·
    have hnq : (n, 2 ^ (e / 2)) ≠ (3, 2) := fun h => h32 ⟨congrArg Prod.fst h,
      congrArg Prod.snd h⟩
    have : IsSimpleGroup (StatedProj (StatedSU n (2 ^ (e / 2)) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 (e / 2) hK2 n hn hnq
    have : IsSimpleGroup (unitaryPSU hud n) := eU.isSimpleGroup
    have hNs : IsSimpleGroup N := ι.symm.isSimpleGroup
    have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNs hL₀N
    have hid : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom =
        MonoidHom.id _ :=
      MonoidHom.ext fun x => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
    have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
      rw [← hL₀eq, hL₀def, Subgroup.map_map, hid, Subgroup.map_id]
    have eL : L ≃* StatedProj (StatedSU n (2 ^ (e / 2)) K) :=
      ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
        ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans (ι.symm.trans eU)
    have hLsimple : IsSimpleGroup L := eL.isSimpleGroup
    have hLnab : ∃ x y : L, x * y ≠ y * x := exists_ne_commute_of_isQuasisimple hLCW.2.2
    have eZ : L ⧸ center L ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hLnab)).trans
        QuotientGroup.quotientBot
    have hX : StatedClassicalModel (L ⧸ center L) .PSU n 2 (e / 2) :=
      ⟨⟨Nat.prime_two, hg, hn, hnq⟩, K, inferInstance, inferInstance, hK2, ⟨eZ.trans eL⟩⟩
    obtain ⟨h1, h2, h3⟩ :=
      UnbalancingLocal.small_standard_source_even_unitary_model_exclusion_stated hX
    rcases hsrc with h | ⟨e7⟩ | h
    · exact h1 p f hp2 h
    · exact not_nonempty_iff.mpr h2 e7
    · exact h3 h

end CFSG.ComponentClassification.OutcomeLocal
