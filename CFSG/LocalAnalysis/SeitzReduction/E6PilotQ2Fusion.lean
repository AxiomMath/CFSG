module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvection

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

theorem map_conj_centralizer_singleton_q2 {G : Type*} [Group G] (n x : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * x * n⁻¹} : Set G) := by
  ext g
  rw [mem_map_equiv, MulAut.conj_symm_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * (n * x * n⁻¹) = n * (n⁻¹ * g * n * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * g * n)) * n⁻¹ := by rw [h]
      _ = n * x * n⁻¹ * g := by group
  · intro h
    calc n⁻¹ * g * n * x = n⁻¹ * (g * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * x * n⁻¹ * g) * n := by rw [h]
      _ = x * (n⁻¹ * g * n) := by group


variable {K : Type} [Field K]

theorem mem_range_conj_of_fix_posUnipotent_E6_two (hK : Nat.card K = 2)
    (β : MulAut (adjointGroup .E6 K))
    (hβ : ∀ u : adjointGroup .E6 K, (u : ModGL .E6 K) ∈ posUnipotent .E6 K → β u = u) :
    β ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact F4Pilot.mem_range_conj_of_mem_diagonalFieldActors_two hK
    (mem_diagonalFieldActors_E6_of_forall_posUnipotent β hβ)

theorem mem_range_conj_of_fix_sylow_E6_two (hK : Nat.card K = 2)
    (U : Sylow 2 (adjointGroup .E6 K)) (β : MulAut (adjointGroup .E6 K))
    (hβ : ∀ u ∈ (U : Subgroup (adjointGroup .E6 K)), β u = u) :
    β ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [pow_one]; exact hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL .E6 K) := finite_modGL
    infer_instance
  exact F4Pilot.mem_range_conj_of_fix_sylow_of_fix (E8Pilot.posUnipotentSylowE .E6 K)
    (fun β' hβ' => mem_range_conj_of_fix_posUnipotent_E6_two hK β' fun u hu =>
      hβ' u (E8Pilot.mem_posUnipotentSylowE.2 hu)) U β hβ

theorem mem_range_conj_of_fix_sylow_of_mulEquiv_E6_two {X : Type*} [Group X]
    (hK : Nat.card K = 2) (e : X ≃* adjointGroup .E6 K) (U : Sylow 2 X) (β : MulAut X)
    (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL .E6 K) := finite_modGL
    infer_instance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact F4Pilot.mem_range_conj_of_fix_sylow_of_mulEquiv_of_forall
    (mem_range_conj_of_fix_sylow_E6_two hK) e U β hβ

theorem commutator_centralizer_of_mem_centralizer_sylow_E6_two (hK : Nat.card K = 2)
    (U : Sylow 2 (adjointGroup .E6 K)) {w : adjointGroup .E6 K}
    (hw : w ∈ centralizer ((U : Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)))
    (hw1 : w ≠ 1) :
    ⁅centralizer ({w} : Set (adjointGroup .E6 K)), centralizer ({w} : Set (adjointGroup .E6 K))⁆ =
      centralizer ({w} : Set (adjointGroup .E6 K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [pow_one]; exact hK)
  obtain ⟨c, hc⟩ :=
    E8Pilot.exists_conj_eq_pinnedElt_highRoot_of_mem_centralizer_sylow (Or.inl rfl) U hw hw1
  have hwc : w = c⁻¹ * EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) * c⁻¹⁻¹ := by
    rw [← hc]
    group
  rw [hwc, ← map_conj_centralizer_singleton_q2, ← map_commutator,
    E8Pilot.commutator_centralizer_pinnedElt_highRoot_two (Or.inl rfl) hK]

theorem isSolvable_outer_of_mulEquiv_E6 {G : Type*} [Group G] {L : Subgroup G} [Finite K]
    (e : L ≃* adjointGroup .E6 K) : Group.IsSolvable (Outer L) :=
  ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).1⟩⟩

theorem not_forall_commute_sylow_conj_E6_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E6 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hwL hwU
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set w := g⁻¹ * t * g with hwdef
  set φ : adjointGroup .E6 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  set wC : adjointGroup .E6 K := e ⟨w, hwL⟩ with hwCdef
  have hφw : φ wC = w := by simp [hφdef, hwCdef]
  have hw1 : w ≠ 1 := by
    intro h
    have h1 : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [← hwdef, h]; group
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have hwC1 : wC ≠ 1 := by
    intro h
    apply hw1
    rw [← hφw, h, map_one]
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (adjointGroup .E6 K) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (adjointGroup .E6 K)) ↔ e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hwCU : wC ∈ centralizer ((UC : Subgroup (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K)) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h := hwU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφw]
    exact h
  have hPC := commutator_centralizer_of_mem_centralizer_sylow_E6_two hK UC hwCU hwC1
  set P := (centralizer ({wC} : Set (adjointGroup .E6 K))).map φ with hPdef
  have hPeq : P = L ⊓ centralizer ({w} : Set G) := by
    rw [hPdef, F4Pilot.map_centralizer_singleton hφ, hφr, hφw]
  have hP : ⁅P, P⁆ = P := by rw [hPdef, ← map_commutator, hPC]
  have hPL : P ≤ L := hPeq ▸ inf_le_left
  have hPw : P ≤ centralizer ({g⁻¹ * t * g} : Set G) := hPeq ▸ inf_le_right
  have hwP : g⁻¹ * t * g ∈ P := hPeq ▸ ⟨hwL, mem_centralizer_singleton_iff.2 rfl⟩
  exact LinearPilot.conj_not_mem_perfect hset (isSolvable_outer_of_mulEquiv_E6 e)
    (F4Pilot.center_eq_bot_congr e.symm center_adjointGroup_eq_bot) htC ht g hP hPL hPw hwP

theorem exists_conj_eq_mul_twoSided_E6_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  exact SeitzQ2.exists_conj_eq_mul_twoCentral_twoSided hset
    (SeitzQ2.card_outer_le_two_of_mulEquiv_E6_two hK e).2 ht hKt
    (not_forall_commute_sylow_conj_E6_two hset hK e htK.1 ht)
    (mem_range_conj_of_fix_sylow_of_mulEquiv_E6_two hK e)

theorem exists_conj_eq_mul_twoCentral_E6_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  obtain ⟨x, z, hz, hxz, hz1, hU, -, -⟩ := exists_conj_eq_mul_twoSided_E6_two hset hK e ht hKt
  exact ⟨x, z, hz.1, hxz, hz1, hU⟩

end CFSG.SeitzReduction.E6Pilot
