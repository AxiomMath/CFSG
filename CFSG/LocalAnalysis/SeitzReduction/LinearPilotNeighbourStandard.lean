module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearSchreier
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type*} [Group G] {L : Subgroup G}

section Basic

variable {C : Type*} [Group C]

theorem mem_centralizer_map_symm (e : L ≃* C) (A : Subgroup C) {t : G}
    (htC : t ∈ centralizer (L : Set G)) :
    t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) :=
  centralizer_le (map_subtype_le _) htC

theorem map_symm_le_centralizer_singleton (e : L ≃* C) (B : Subgroup C) {t : G}
    (htC : t ∈ centralizer (L : Set G)) :
    (B.map e.symm.toMonoidHom).map L.subtype ≤ centralizer ({t} : Set G) :=
  (map_subtype_le _).trans (le_centralizer_of_mem_centralizer htC)

theorem map_symm_le_centralizer_map_symm (e : L ≃* C) {A B : Subgroup C}
    (hBA : B ≤ centralizer (A : Set C)) :
    (B.map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
  rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, mem_centralizer_iff.1 (hBA hb) x hx]

noncomputable def mapSymmMulEquiv (e : L ≃* C) (B : Subgroup C) :
    ((B.map e.symm.toMonoidHom).map L.subtype : Subgroup G) ≃* B :=
  (((B.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
    (B.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm)

theorem card_map_symm (e : L ≃* C) (A : Subgroup C) :
    Nat.card ((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) = Nat.card A :=
  Nat.card_congr (mapSymmMulEquiv e A).toEquiv

theorem isCyclic_map_symm (e : L ≃* C) {A : Subgroup C} (hA : IsCyclic A) :
    IsCyclic ((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  isCyclic_of_surjective (mapSymmMulEquiv e A).symm.toMonoidHom
    (mapSymmMulEquiv e A).symm.surjective

end Basic

section SpecialLinear

variable {K : Type*} [Field K] {D : Type*} [Group D] {m : ℕ}

theorem odd_natCard_sub_one [Finite K] [CharP K 2] : Odd (Nat.card K - 1) := by
  obtain ⟨k, hk⟩ := odd_natCard_add_one (K := K)
  have h1 := Finite.one_lt_card (α := K)
  exact ⟨k - 1, by omega⟩

noncomputable def quotientCenterEquivProjectiveSL
    (φ : D ≃* Matrix.SpecialLinearGroup (Fin m) K) :
    D ⧸ center D ≃* LinearFlag.projectiveSL m K :=
  (QuotientGroup.congr (center D) (center (Matrix.SpecialLinearGroup (Fin m) K)) φ
      (map_center_eq φ)).trans
    (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center m K).symm)

theorem odd_card_center_of_mulEquiv [Finite K] [CharP K 2] (hm : 1 ≤ m)
    (φ : D ≃* Matrix.SpecialLinearGroup (Fin m) K) : Odd (Nat.card (center D)) := by
  rw [Nat.card_congr (centerCongr φ).toEquiv, ← LinearFlag.scalars_eq_center]
  exact odd_natCard_sub_one.of_dvd_nat (LinearFlag.card_scalars_dvd hm)

theorem isSolvable_outer_quotient_center_of_mulEquiv [Finite K] (hm : 3 ≤ m)
    (φ : D ≃* Matrix.SpecialLinearGroup (Fin m) K) : Group.IsSolvable (Outer (D ⧸ center D)) := by
  have := (UnitaryHigher.linear_higher_schreier (K := K) hm).2
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
    (quotientCenterEquivProjectiveSL φ).symm

theorem isCyclic_levTorus [Finite K] {n : ℕ} (a : Fin n) : IsCyclic (levTorus (K := K) a) :=
  isCyclic_of_surjective ((LinearFlag.proj n K).comp (levTorusHom a)).rangeRestrict
    ((LinearFlag.proj n K).comp (levTorusHom a)).rangeRestrict_surjective

theorem odd_card_levTorus [Finite K] [CharP K 2] {n : ℕ} (a : Fin n) :
    Odd (Nat.card (levTorus (K := K) a)) := by
  have h : Nat.card (levTorus (K := K) a) ∣ Nat.card Kˣ := card_range_dvd _
  rw [Nat.card_units] at h
  exact odd_natCard_sub_one.of_dvd_nat h

end SpecialLinear

section TorusQ1

variable [Finite G] {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem neighbour_standard (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    (hX : (X.subgroupOf L).map e.toMonoidHom ≤ rootSL2 a b)
    (hXc : Nat.card ((X.subgroupOf L).map e.toMonoidHom) = Nat.card K + 1)
    {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  have hDq : CFSG.Open.IsQuasisimple D :=
    hDe ▸ isQuasisimple_open_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_torusQ1 e hn hab hX hXc hDe)

omit [Finite G] in
theorem neighbour_data_torusQ1 (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) {t : G} (htC : t ∈ centralizer (L : Set G))
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ (X.subgroupOf L).map e.toMonoidHom = X₀ ∧
      Nat.card X = Nat.card K + 1 ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧
      CFSG.Open.IsQuasisimple D ∧ Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin (n - 2)) K) ∧
      Odd (Nat.card (center D)) ∧ Group.IsSolvable (Outer (D ⧸ center D)) := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨φ⟩ := blockSL_mulEquiv (K := K) (I := ({a, b} : Finset (Fin n))ᶜ) (by omega)
  subst hX hDe
  set ψ := (mapSymmMulEquiv e _).trans (φ.trans (reindexSpecialLinear (finCongr hcard)))
  exact ⟨map_subtype_le _, mem_centralizer_map_symm e X₀ htC,
    F4Pilot.map_subgroupOf_map_symm e X₀, (card_map_symm e X₀).trans hX₀c,
    (layer_inf_centralizer_torusQ1 e hn hab hX₀ hX₀c).symm,
    le_inf (map_symm_le_centralizer_map_symm e (blockSL_compl_le_centralizer hX₀))
      (map_symm_le_centralizer_singleton e _ htC),
    isQuasisimple_open_map_blockSL e (by omega) (by omega) (Or.inl (by omega)), ⟨ψ⟩,
    odd_card_center_of_mulEquiv (by omega) ψ,
    isSolvable_outer_quotient_center_of_mulEquiv (by omega) ψ⟩

theorem neighbour_standard_torusQ1 (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨-, -, hXe, -, hD, -⟩ := neighbour_data_torusQ1 e hn hab htC hX₀ hX₀c hX hDe
  exact neighbour_standard hL htC ht hK e hn hab htX (hXe ▸ hX₀) (hXe ▸ hX₀c) hDe hD

theorem exists_neighbour_standard_torusQ1 (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    ∃ X₀ : Subgroup (LinearFlag.projectiveSL n K), X₀ ≤ rootSL2 a b ∧ IsCyclic X₀ ∧
      Nat.card X₀ = Nat.card K + 1 ∧
      ∀ {X D : Subgroup G}, X = (X₀.map e.symm.toMonoidHom).map L.subtype →
        D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype →
        ∃ htX : t ∈ centralizer (X : Set G),
          CFSG.Open.IsComponentOf
              ((D.subgroupOf (centralizer (X : Set G))).map
                (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
              (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
                Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
            (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
              IsPGroup 2 U →
              U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
                  (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
                Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
              Nat.card U ≤ 2) ∧
            standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨X₀, hX₀, hcyc, hX₀c⟩ := exists_torusQ1 (n := n) (K := K) hab
  refine ⟨X₀, hX₀, hcyc, hX₀c, fun {X D} hX hDe => ?_⟩
  have htX : t ∈ centralizer (X : Set G) := hX ▸ mem_centralizer_map_symm e X₀ htC
  exact ⟨htX, neighbour_standard_torusQ1 hL htC ht hK e hn hab hX₀ hX₀c hX htX hDe⟩

end TorusQ1

section Levi

variable [Finite G] {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem neighbour_standard_levi (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n) (a : Fin n)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hcard : (({a} : Finset (Fin n))ᶜ).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  have hDq : CFSG.Open.IsQuasisimple D :=
    hDe ▸ isQuasisimple_open_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_levi e hn a hDe)

omit [Finite G] in
theorem neighbour_data_levTorus (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n) (a : Fin n)
    (hc : ∃ c : Kˣ, c ^ n ≠ 1) {t : G} (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G} (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Odd (Nat.card X) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧
      CFSG.Open.IsQuasisimple D ∧ Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) K) ∧
      Odd (Nat.card (center D)) ∧ Group.IsSolvable (Outer (D ⧸ center D)) := by
  have hcard : (({a} : Finset (Fin n))ᶜ).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  obtain ⟨φ⟩ := blockSL_mulEquiv (K := K) (I := ({a} : Finset (Fin n))ᶜ) (by omega)
  subst hX hDe
  set ψ := (mapSymmMulEquiv e _).trans (φ.trans (reindexSpecialLinear (finCongr hcard)))
  exact ⟨map_subtype_le _, mem_centralizer_map_symm e _ htC,
    isCyclic_map_symm e (isCyclic_levTorus a),
    (card_map_symm e _).symm ▸ odd_card_levTorus a,
    (layer_inf_centralizer_levTorus e hn a hc).symm,
    le_inf (map_symm_le_centralizer_map_symm e (blockSL_compl_le_centralizer_levTorus a))
      (map_symm_le_centralizer_singleton e _ htC),
    isQuasisimple_open_map_blockSL e (by omega) (by omega) (Or.inl (by omega)), ⟨ψ⟩,
    odd_card_center_of_mulEquiv (by omega) ψ,
    isSolvable_outer_quotient_center_of_mulEquiv (by omega) ψ⟩

theorem neighbour_standard_levTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n) (a : Fin n) (hc : ∃ c : Kˣ, c ^ n ≠ 1)
    {X : Subgroup G} (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨-, -, -, -, hD, -⟩ := neighbour_data_levTorus e hn a hc htC hX hDe
  exact neighbour_standard_levi hL htC ht hK e hn a htX hDe hD

theorem neighbour_standard_levTorus_four (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* LinearFlag.projectiveSL 4 K) (hq : 4 ≤ Nat.card K) (a : Fin 4)
    {X : Subgroup G} (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  neighbour_standard_levTorus hL htC ht hK e le_rfl a (exists_pow_four_ne_one hq) hX htX hDe

end Levi

end CFSG.SeitzReduction.LinearPilot
