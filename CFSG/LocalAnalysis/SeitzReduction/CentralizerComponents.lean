module

public import CFSG.Foundations.Basic
import CFSG.ClassicalInvolution.LBalance.Main
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.SeitzReduction

open Subgroup

namespace CentralizerComponents

variable {X : Type*} [Group X]

theorem conj_conj_of_sq_eq_one {t : X} (ht : t ^ 2 = 1) (x : X) :
    MulAut.conj t (MulAut.conj t x) = x := by
  have htt : t * t = 1 := by rw [← sq]; exact ht
  simp only [MulAut.conj_apply]
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [htt]; group

theorem map_conj_map_conj {t : X} (ht : t ^ 2 = 1) (H : Subgroup X) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  have hid : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id X := by
    ext x
    exact conj_conj_of_sq_eq_one ht x
  rw [map_map, hid, map_id]

theorem map_conj_sSup_eq {t : X} (ht : t ^ 2 = 1) {S : Set (Subgroup X)}
    (hS : ∀ L ∈ S, L.map (MulAut.conj t).toMonoidHom ∈ S) :
    (sSup S).map (MulAut.conj t).toMonoidHom = sSup S := by
  have hle : (sSup S).map (MulAut.conj t).toMonoidHom ≤ sSup S :=
    map_le_iff_le_comap.mpr (sSup_le fun L hL => map_le_iff_le_comap.mp (le_sSup (hS L hL)))
  refine le_antisymm hle ?_
  calc sSup S = ((sSup S).map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
        (map_conj_map_conj ht _).symm
    _ ≤ (sSup S).map (MulAut.conj t).toMonoidHom := map_mono hle

theorem conj_eq_of_mem_centralizer {t d : X} (hd : d ∈ centralizer ({t} : Set X)) :
    MulAut.conj t d = d := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact (mem_centralizer_singleton_iff.mp hd).symm

theorem map_conj_eq_of_le_centralizer {t : X} {D : Subgroup X}
    (hDt : D ≤ centralizer ({t} : Set X)) : D.map (MulAut.conj t).toMonoidHom = D := by
  have hfix : ∀ d ∈ D, MulAut.conj t d = d := fun d hd => conj_eq_of_mem_centralizer (hDt hd)
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    change MulAut.conj t d ∈ D
    rw [hfix d hd]
    exact hd
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

theorem commutator_eq_self_of_isComponent_subgroupOf {D H : Subgroup X} (hDH : D ≤ H)
    (hD : IsComponent (D.subgroupOf H)) : ⁅D, D⁆ = D := by
  have h := congrArg (Subgroup.map H.subtype) (isPerfect_iff.mp hD.1.1)
  rwa [map_commutator, subgroupOf_map_subtype, inf_eq_left.mpr hDH] at h

theorem ne_bot_of_isComponent_subgroupOf {D H : Subgroup X} (hD : IsComponent (D.subgroupOf H)) :
    D ≠ ⊥ := by
  rintro rfl
  have := CFSG.LocalCores.isQuasisimple_nontrivial hD.1
  exact (nontrivial_iff_ne_bot _).mp this (bot_subgroupOf _)

theorem exists_isComponent_commutator_ne_bot {P : Subgroup X} (hP : P ≤ layer X)
    (hPP : ⁅P, P⁆ ≠ ⊥) : ∃ K : Subgroup X, IsComponent K ∧ ⁅P, K⁆ ≠ ⊥ := by
  by_contra h
  push Not at h
  apply hPP
  have hle : layer X ≤ centralizer (P : Set X) := sSup_le fun K hK => by
    have hPK := h K hK
    rw [commutator_comm] at hPK
    exact commutator_eq_bot_iff_le_centralizer.mp hPK
  exact commutator_eq_bot_iff_le_centralizer.mpr (hP.trans hle)

theorem isComponent_subgroupOf_inf_centralizer {t : X} {D M : Subgroup X}
    (hDt : D ≤ centralizer ({t} : Set X))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set X)))) (hDM : D ≤ M) :
    IsComponent (D.subgroupOf (M ⊓ centralizer ({t} : Set X))) := by
  have hDMC : D ≤ M ⊓ centralizer ({t} : Set X) := le_inf hDM hDt
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((subgroupOfEquivOfLe hDt).trans (subgroupOfEquivOfLe hDMC).symm) hD.1, ?_⟩
  exact hD.2.comap (inclusion inf_le_right)

variable [Finite X]

theorem isSubnormal_sSup_of_isComponent {S : Set (Subgroup X)} (hS : ∀ L ∈ S, IsComponent L) :
    (sSup S).IsSubnormal := by
  have hle : sSup S ≤ layer X := sSup_le fun L hL => CFSG.LocalCores.component_le_layer (hS L hL)
  have hnorm : layer X ≤ normalizer ((sSup S : Subgroup X) : Set X) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, sSup_eq_iSup', Subgroup.map_iSup]
    exact iSup_congr fun L => mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LocalCores.layer_le_normalizer (hS L.1 L.2) hg)
  have hEn : (layer X).Normal :=
    @Subgroup.normal_of_characteristic _ _ _ CFSG.LocalCores.layer_characteristic
  exact IsSubnormal.step _ (layer X) hle hEn.isSubnormal (normal_subgroupOf_of_le_normalizer hnorm)

theorem le_or_le_of_isComponent_centralizer {t : X} {D A B : Subgroup X}
    (hDt : D ≤ centralizer ({t} : Set X))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set X))))
    (hA : A.IsSubnormal) (hB : B.IsSubnormal) (hAB : ⁅A, B⁆ = ⊥)
    (hAt : A.map (MulAut.conj t).toMonoidHom = A) (hBt : B.map (MulAut.conj t).toMonoidHom = B)
    (hDAB : D ≤ A ⊔ B) : D ≤ A ∨ D ≤ B := by
  set C := centralizer ({t} : Set X) with hC
  have hfix : ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj t) = C := by
    ext x
    rw [hC, mem_centralizer_singleton_iff]
    change t * x * t⁻¹ = x ↔ x * t = t * x
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  have hD2 : D ≤ (A ⊓ C) ⊔ (B ⊓ C) := by
    have h := ComponentClassification.FixedCommutingProduct.derived_fixed A B hAB
      (MulAut.conj t) hAt hBt
    rw [hfix] at h
    calc D = ⁅D, D⁆ := (commutator_eq_self_of_isComponent_subgroupOf hDt hD).symm
      _ ≤ ⁅(A ⊔ B) ⊓ C, (A ⊔ B) ⊓ C⁆ := commutator_mono (le_inf hDAB hDt) (le_inf hDAB hDt)
      _ ≤ (A ⊓ C) ⊔ (B ⊓ C) := h
  have hD3 : D.subgroupOf C ≤ A.subgroupOf C ⊔ B.subgroupOf C := by
    rw [← map_le_map_iff_of_injective C.subtype_injective, Subgroup.map_sup, subgroupOf_map_subtype,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hDt]
    exact hD2
  rcases CFSG.LocalCores.component_subnormal_subgroup hD hA.subgroupOf with h1 | h1
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hDt h1)
  rcases CFSG.LocalCores.component_subnormal_subgroup hD hB.subgroupOf with h2 | h2
  · exact Or.inr (CFSG.LocalCores.le_of_subgroupOf_le hDt h2)
  exfalso
  rw [commutator_comm] at h1 h2
  have hcent : A.subgroupOf C ⊔ B.subgroupOf C ≤ centralizer (D.subgroupOf C : Set C) :=
    sup_le (commutator_eq_bot_iff_le_centralizer.mp h1)
      (commutator_eq_bot_iff_le_centralizer.mp h2)
  have hab : ⁅D.subgroupOf C, D.subgroupOf C⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hD3.trans hcent)
  have hne := CFSG.LocalCores.isQuasisimple_nontrivial hD.1
  rw [nontrivial_iff_ne_bot] at hne
  exact hne ((isPerfect_iff.mp hD.1.1).symm.trans hab)

theorem inf_le_center_of_map_conj_ne {t : X} {D K : Subgroup X}
    (hDt : D ≤ centralizer ({t} : Set X)) (hK : IsComponent K)
    (hne : K.map (MulAut.conj t).toMonoidHom ≠ K) :
    ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧ D ⊓ K ≤ (center K).map K.subtype := by
  have hK' : IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
  have hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left (Ne.symm hne)
  refine ⟨hcomm, ?_⟩
  rintro d ⟨hdD, hdK⟩
  have hdK' : d ∈ K.map (MulAut.conj t).toMonoidHom :=
    ⟨d, hdK, conj_eq_of_mem_centralizer (hDt hdD)⟩
  have hKc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  refine ⟨⟨d, hdK⟩, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
  exact (mem_centralizer_iff.mp (hKc g.2) d hdK').symm

theorem coe_eq_diagonal_of_commutator_eq_bot {t : X} (ht : t ^ 2 = 1) {D K : Subgroup X}
    (hK : IsQuasisimple K) (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hDle : D ≤ (K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set X))
    (hD : IsComponent (D.subgroupOf
      ((K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set X)))) :
    (D : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g} ∧
      Nonempty (D ⧸ center D ≃* K ⧸ center K) := by
  have htt : t * t = 1 := by rw [← sq]; exact ht
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconj : LocalAnalysis.ComponentInitial.conjSub t⁻¹ K =
      K.map (MulAut.conj t).toMonoidHom := by
    rw [ht']
  have hAB : ⁅K, LocalAnalysis.ComponentInitial.conjSub t⁻¹ K⁆ = ⊥ := by
    rw [hconj]
    exact hcomm
  have hA : CFSG.Assembly.IsQuasisimple K :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).2 hK
  have ht1 : t ≠ 1 := by
    rintro rfl
    have hK1 : K.map (MulAut.conj (1 : X)).toMonoidHom = K :=
      map_conj_eq_of_le_centralizer fun k _ => mem_centralizer_singleton_iff.mpr (by simp)
    rw [hK1, isPerfect_iff.mp hK.1] at hcomm
    have hne := CFSG.LocalCores.isQuasisimple_nontrivial hK
    rw [nontrivial_iff_ne_bot] at hne
    exact hne hcomm
  have hto : orderOf t = 2 := orderOf_eq_prime ht ht1
  obtain ⟨hset, -, -, -, -, -, -, -, -, hcompiff, -, hiso⟩ :=
    LocalAnalysis.ComponentInitial.swapped_quasisimple_fixed_central_product hto hA hAB
  have hD' : CFSG.Assembly.IsComponentOf D
      ((K ⊔ LocalAnalysis.ComponentInitial.conjSub t⁻¹ K) ⊓ centralizer ({t} : Set X)) := by
    rw [hconj]
    exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDle).2 hD
  obtain rfl := (hcompiff D).1 hD'
  refine ⟨?_, hiso⟩
  rw [hset, ht']

theorem le_sup_map_conj_of_commutator_ne_bot {t : X} (ht : t ^ 2 = 1) {D K : Subgroup X}
    (hDt : D ≤ centralizer ({t} : Set X))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set X)))) (hDE : D ≤ layer X)
    (hK : IsComponent K) (hDK : ⁅D, K⁆ ≠ ⊥) :
    D ≤ K ⊔ K.map (MulAut.conj t).toMonoidHom := by
  have hK' : IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
  let S : Set (Subgroup X) :=
    {L | IsComponent L ∧ L ≠ K ∧ L ≠ K.map (MulAut.conj t).toMonoidHom}
  have hSt : ∀ L ∈ S, L.map (MulAut.conj t).toMonoidHom ∈ S := by
    rintro L ⟨hL, hLK, hLK'⟩
    refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hL, fun h => hLK' ?_,
      fun h => hLK (map_injective (MulAut.conj t).injective h)⟩
    rw [← h, map_conj_map_conj ht]
  have hE₀t : (K ⊔ K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_sup, map_conj_map_conj ht, sup_comm]
  have hE₁t : (sSup S).map (MulAut.conj t).toMonoidHom = sSup S := map_conj_sSup_eq ht hSt
  have hE₀sub : (K ⊔ K.map (MulAut.conj t).toMonoidHom).IsSubnormal := by
    rw [← sSup_pair]
    refine isSubnormal_sSup_of_isComponent fun L hL => ?_
    rcases hL with rfl | hL
    · exact hK
    · rw [Set.mem_singleton_iff.mp hL]
      exact hK'
  have hE₁sub : (sSup S).IsSubnormal := isSubnormal_sSup_of_isComponent fun L hL => hL.1
  have hcomm : ⁅K ⊔ K.map (MulAut.conj t).toMonoidHom, sSup S⁆ = ⊥ := by
    have hS :
        sSup S ≤ centralizer ((K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X) := by
      refine sSup_le fun L hL => ?_
      rw [le_centralizer_iff]
      refine sup_le ?_ ?_
      · exact commutator_eq_bot_iff_le_centralizer.mp
          ((CFSG.LocalCores.distinct_components_commute hK hL.1).resolve_left (Ne.symm hL.2.1))
      · exact commutator_eq_bot_iff_le_centralizer.mp
          ((CFSG.LocalCores.distinct_components_commute hK' hL.1).resolve_left (Ne.symm hL.2.2))
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hS
  have hlayer : layer X ≤ (K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊔ sSup S := by
    refine sSup_le fun L hL => ?_
    by_cases h1 : L = K
    · rw [h1]
      exact le_sup_left.trans le_sup_left
    by_cases h2 : L = K.map (MulAut.conj t).toMonoidHom
    · rw [h2]
      exact le_sup_right.trans le_sup_left
    exact (le_sSup (show L ∈ S from ⟨hL, h1, h2⟩)).trans le_sup_right
  rcases le_or_le_of_isComponent_centralizer hDt hD hE₀sub hE₁sub hcomm hE₀t hE₁t
      (hDE.trans hlayer) with h | h
  · exact h
  · exfalso
    rw [commutator_comm] at hcomm
    exact hDK (le_bot_iff.mp ((commutator_mono h le_sup_left).trans hcomm.le))

end CentralizerComponents

open CentralizerComponents

theorem layer_centralizer_le_layer {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {A : Subgroup X} (hA : IsPGroup 2 A) :
    (layer (centralizer (A : Set X))).map (centralizer (A : Set X)).subtype ≤ layer X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (pPrimeCore 2 (centralizer (A : Set X))) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1 pPrimeCore_coprime_card)
  calc (layer (centralizer (A : Set X))).map (centralizer (A : Set X)).subtype
      ≤ (pLayer (centralizer (A : Set X)) 2).map (centralizer (A : Set X)).subtype :=
        map_mono (LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components 2
          Nat.prime_two hsolv).2.1
    _ ≤ pLayer X 2 := ClassicalInvolution.l2PrimeBalance X A hA
    _ = layer X := ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hO

theorem le_layer_of_isComponent_centralizer_of_isPGroup {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥) {A : Subgroup X} (hA : IsPGroup 2 A) {D : Subgroup X}
    (hDA : D ≤ centralizer (A : Set X))
    (hD : IsComponent (D.subgroupOf (centralizer (A : Set X)))) : D ≤ layer X := by
  have h : (D.subgroupOf (centralizer (A : Set X))).map (centralizer (A : Set X)).subtype ≤
      (layer (centralizer (A : Set X))).map (centralizer (A : Set X)).subtype :=
    map_mono (CFSG.LocalCores.component_le_layer hD)
  rw [subgroupOf_map_subtype, inf_eq_left.mpr hDA] at h
  exact h.trans (layer_centralizer_le_layer hO hA)

theorem isComponent_centralizer_le_layer {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥) {t : X} (ht : t ^ 2 = 1) {D : Subgroup X}
    (hDt : D ≤ centralizer ({t} : Set X))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set X)))) : D ≤ layer X := by
  have hA : IsPGroup 2 (zpowers t) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ht) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hCz : centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [← hCz] at hDt hD
  exact le_layer_of_isComponent_centralizer_of_isPGroup hO hA hDt hD

theorem exists_isComponent_orbit_of_le_layer {X : Type*} [Group X] [Finite X] {t : X}
    (ht : t ^ 2 = 1) {D : Subgroup X} (hDt : D ≤ centralizer ({t} : Set X))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set X)))) (hDE : D ≤ layer X) :
    ∃ K : Subgroup X, IsComponent K ∧ ⁅D, K⁆ ≠ ⊥ ∧
      D ≤ K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
      IsComponent (D.subgroupOf
        ((K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set X))) ∧
      (∀ L : Subgroup X, IsComponent L →
        (⁅D, L⁆ ≠ ⊥ ↔ L = K ∨ L = K.map (MulAut.conj t).toMonoidHom)) ∧
      (K.map (MulAut.conj t).toMonoidHom = K →
        D ≤ K ∧ IsComponent (D.subgroupOf (K ⊓ centralizer ({t} : Set X)))) ∧
      (K.map (MulAut.conj t).toMonoidHom ≠ K →
        ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧ D ⊓ K ≤ (center K).map K.subtype ∧
          (D : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g} ∧
          Nonempty (D ⧸ center D ≃* K ⧸ center K)) := by
  have hDperf := commutator_eq_self_of_isComponent_subgroupOf hDt hD
  have hDne := ne_bot_of_isComponent_subgroupOf hD
  obtain ⟨K, hK, hDK⟩ := exists_isComponent_commutator_ne_bot hDE (by rw [hDperf]; exact hDne)
  have hK' : IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
  have hle := le_sup_map_conj_of_commutator_ne_bot ht hDt hD hDE hK hDK
  have hDK' : ⁅D, K.map (MulAut.conj t).toMonoidHom⁆ ≠ ⊥ := by
    intro h
    apply hDK
    rw [← map_eq_bot_iff_of_injective _ (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective, map_commutator, map_conj_eq_of_le_centralizer hDt]
    exact h
  refine ⟨K, hK, hDK, hle, isComponent_subgroupOf_inf_centralizer hDt hD hle, ?_, ?_,
    fun hne => ?_⟩
  · intro L hL
    refine ⟨fun hDL => ?_, ?_⟩
    · by_contra hLK
      push Not at hLK
      apply hDL
      have hLc : K ⊔ K.map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set X) :=
        sup_le
          (commutator_eq_bot_iff_le_centralizer.mp
            ((CFSG.LocalCores.distinct_components_commute hK hL).resolve_left (Ne.symm hLK.1)))
          (commutator_eq_bot_iff_le_centralizer.mp
            ((CFSG.LocalCores.distinct_components_commute hK' hL).resolve_left (Ne.symm hLK.2)))
      exact commutator_eq_bot_iff_le_centralizer.mpr (hle.trans hLc)
    · rintro (rfl | rfl)
      · exact hDK
      · exact hDK'
  · intro hKt
    have hDK : D ≤ K := by
      have h := hle
      rwa [hKt, sup_idem] at h
    exact ⟨hDK, isComponent_subgroupOf_inf_centralizer hDt hD hDK⟩
  · obtain ⟨hcomm, hcen⟩ := inf_le_center_of_map_conj_ne hDt hK hne
    exact ⟨hcomm, hcen, coe_eq_diagonal_of_commutator_eq_bot ht hK.1 hcomm (le_inf hle hDt)
      (isComponent_subgroupOf_inf_centralizer hDt hD hle)⟩

theorem exists_isComponent_orbit_of_isComponent_centralizer {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥) {t : X} (ht : t ^ 2 = 1) {D : Subgroup X}
    (hDt : D ≤ centralizer ({t} : Set X))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set X)))) :
    D ≤ layer X ∧ ∃ K : Subgroup X, IsComponent K ∧ ⁅D, K⁆ ≠ ⊥ ∧
      D ≤ K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
      IsComponent (D.subgroupOf
        ((K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set X))) ∧
      (∀ L : Subgroup X, IsComponent L →
        (⁅D, L⁆ ≠ ⊥ ↔ L = K ∨ L = K.map (MulAut.conj t).toMonoidHom)) ∧
      (K.map (MulAut.conj t).toMonoidHom = K →
        D ≤ K ∧ IsComponent (D.subgroupOf (K ⊓ centralizer ({t} : Set X)))) ∧
      (K.map (MulAut.conj t).toMonoidHom ≠ K →
        ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧ D ⊓ K ≤ (center K).map K.subtype ∧
          (D : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g} ∧
          Nonempty (D ⧸ center D ≃* K ⧸ center K)) :=
  ⟨isComponent_centralizer_le_layer hO ht hDt hD,
    exists_isComponent_orbit_of_le_layer ht hDt hD (isComponent_centralizer_le_layer hO ht hDt hD)⟩

end CFSG.SeitzReduction
