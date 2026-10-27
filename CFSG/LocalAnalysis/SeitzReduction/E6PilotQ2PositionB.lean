module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutPSL

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms


section F56

variable {K : Type} [Field K]

theorem centralizer_posJ_eq_a5Levi [Finite K] [CharP K 2] :
    centralizer (posJ K : Set (adjointGroup .E6 K)) = a5Levi K := by
  obtain ⟨A, hAJ, hcyc, hA⟩ := exists_nonsplit_le_subgroupOf_highRootSL2 (τ := .E6) (K := K)
  refine le_antisymm (fun g hg => ?_) a5Levi_le_centralizer_posJ
  have hgA : g ∈ centralizer (A : Set (adjointGroup .E6 K)) := Subgroup.centralizer_le hAJ hg
  obtain ⟨a, ha, d, hd, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit_E6 hAJ hA hcyc hgA
  have haJ : a ∈ centralizer (posJ K : Set (adjointGroup .E6 K)) := by
    have := mul_mem hg (inv_mem (a5Levi_le_centralizer_posJ hd))
    rwa [mul_inv_cancel_right] at this
  have haJ' : (a : ModGL .E6 K) ∈ EPilot.highRootSL2 .E6 K := mem_subgroupOf.1 (hAJ ha)
  rw [← range_rootSL2_highRoot] at haJ'
  obtain ⟨B, hB⟩ := haJ'
  have hBc : B ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [mem_center_iff]
    intro B'
    apply rootSL2_highRoot_injective (τ := .E6)
    have h := mem_centralizer_iff.1 haJ
      ⟨_, rootSL2_highRoot_mem_adjointGroup (τ := .E6) B'⟩
      (mem_subgroupOf.2 (rootSL2_highRoot_mem_highRootSL2 B'))
    have h' := congrArg (fun x : adjointGroup .E6 K => (x : ModGL .E6 K)) h
    simp only [Subgroup.coe_mul] at h'
    rw [map_mul, map_mul, hB]
    exact h'
  have ha1 : a = 1 := by
    apply Subtype.ext
    rw [← hB, eq_one_of_mem_center_SL2 hBc, map_one]
    rfl
  rw [ha1, one_mul]
  exact hd

theorem nonempty_centralizer_map_conj_posJ_mulEquiv_of_finite [Finite K] [CharP K 2]
    (c : adjointGroup .E6 K) :
    Nonempty (centralizer (((posJ K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) ≃* a5Levi K) := by
  obtain ⟨φ⟩ := nonempty_centralizer_map_conj_mulEquiv (posJ K) c
  exact ⟨φ.trans (MulEquiv.subgroupCongr centralizer_posJ_eq_a5Levi)⟩

theorem nonempty_centralizer_map_posJ_rootPerpLevi_mulEquiv [Finite K] [CharP K 2]
    (ι : EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) ≃*
      EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) :
    Nonempty (centralizer
      (((((posJ K).subgroupOf (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1))).map
        ι.toMonoidHom).map (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)).subtype :
          Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) ≃* a5Levi K) := by
  obtain ⟨m, -, hm⟩ := isAutConjIn_rootPerpLevi_highRootSL2 (K := K) ι
  have hm' : (((posJ K).subgroupOf (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1))).map
      ι.toMonoidHom).map (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)).subtype =
        (posJ K).map (MulAut.conj m).toMonoidHom := hm
  rw [hm']
  exact nonempty_centralizer_map_conj_posJ_mulEquiv_of_finite m

end F56

section F3

variable {K : Type} [Field K]

theorem commutator_centralizer_e6Rep_zero_two [CharP K 2] (hK : Nat.card K = 2) :
    ⁅centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K)),
        centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))⁆ =
      centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K)) := by
  obtain ⟨n, hn⟩ := E8Pilot.exists_conj_pinnedElt_highRoot_eq (K := K) (Or.inl rfl)
    (isRoot_single .E6 (0 : Fin 6))
  rw [EPilot.e6Rep_zero_eq_pinnedElt, ← hn, ← map_conj_centralizer_singleton_q2,
    ← map_commutator, E8Pilot.commutator_centralizer_pinnedElt_highRoot_two (Or.inl rfl) hK]

end F3

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_E6_two {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E6 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ P : Subgroup G,
      P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm (e6Rep K 0) : G)} : Set G) ∧
      Nonempty (P ≃* a5Levi K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [pow_one]; exact hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_E6 e
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  set φ : adjointGroup .E6 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hperf : ⁅centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K)),
      centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))⁆ =
        centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K)) :=
    commutator_centralizer_e6Rep_zero_two hK
  obtain ⟨U, hU⟩ := hzU
  set zC : adjointGroup .E6 K := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC1 : zC ≠ 1 := by
    intro h
    apply hz1
    rw [← hφz, h, map_one]
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
  have hzCU : zC ∈ centralizer ((UC : Subgroup (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K)) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h := hU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφz]
    exact h
  obtain ⟨c, hc⟩ := E8Pilot.exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ
    (isRoot_single .E6 (0 : Fin 6)) UC hzCU hzC1
  set y : G := φ (e6Rep K 0) with hydef
  have hyL : y ∈ L := hφr ▸ ⟨e6Rep K 0, rfl⟩
  have hy : y = φ c * z * (φ c)⁻¹ := by
    rw [hydef, EPilot.e6Rep_zero_eq_pinnedElt, ← hc, map_mul, map_mul, map_inv, hφz]
  have hcL : φ c ∈ L := hφr ▸ ⟨c, rfl⟩
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    have htc : φ c * t = t * φ c := mem_centralizer_singleton_iff.1 (hLt hcL)
    calc g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
      _ = φ c * t * z * (φ c)⁻¹ := by rw [hg, mul_assoc (φ c) t z]
      _ = t * (φ c * z * (φ c)⁻¹) := by rw [htc]; group
      _ = t * y := by rw [hy]
  set Λ := (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ with hΛdef
  have hΛeq : Λ = L ⊓ centralizer ({y} : Set G) := by
    rw [hΛdef, F4Pilot.map_centralizer_singleton hφ, hφr]
  have hΛperf : ⁅Λ, Λ⁆ = Λ := by rw [hΛdef, ← map_commutator, hperf]
  have hΛt : Λ ≤ centralizer ({t} : Set G) := hΛeq ▸ inf_le_left.trans hLt
  have hΛy : Λ ≤ centralizer ({y} : Set G) := hΛeq ▸ inf_le_right
  have hΛt' : Λ ≤ centralizer ({g₁⁻¹ * t * g₁} : Set G) := by
    rw [hg₁]
    exact fun x hx => F4Pilot.mem_centralizer_singleton_mul (hΛt hx) (hΛy hx)
  have hΛL' : Λ ≤ L ⊓ CFSG.conjugate L g₁ :=
    std_perfect_le_inf_conjugate hset hOut htC ht g₁ hΛperf hΛt hΛt'
  set φ'₀ : adjointGroup .E6 K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  have hyΛ : y ∈ Λ := hΛeq ▸ ⟨hyL, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨w, hw⟩ : y ∈ φ'₀.range := hφ'₀r ▸ (hΛL' hyΛ).2
  set W₁ := (UC : Subgroup (adjointGroup .E6 K)).map (MulAut.conj c).toMonoidHom with hW₁def
  have hW₁y : ∀ a ∈ W₁, a * e6Rep K 0 = e6Rep K 0 * a := by
    rintro _ ⟨u, hu, rfl⟩
    have h := mem_centralizer_iff.1 hzCU u hu
    rw [EPilot.e6Rep_zero_eq_pinnedElt, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * u * c⁻¹ * (c * zC * c⁻¹) = c * (u * zC) * c⁻¹ := by group
      _ = c * (zC * u) * c⁻¹ := by rw [h]
      _ = c * zC * c⁻¹ * (c * u * c⁻¹) := by group
  set U₀ := W₁.map φ with hU₀def
  have hU₀Λ : U₀ ≤ Λ := by
    rw [hΛeq]
    rintro _ ⟨a, ha, rfl⟩
    refine mem_inf.2 ⟨hφr ▸ ⟨a, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, hydef, ← map_mul, ← map_mul, hW₁y a ha]
  have hU₀L' : U₀ ≤ φ'₀.range := hφ'₀r ▸ hU₀Λ.trans (hΛL'.trans inf_le_right)
  set W := U₀.comap φ'₀ with hWdef
  have hWcard : Nat.card W = Nat.card (UC : Subgroup (adjointGroup .E6 K)) := by
    have h1 : W.map φ'₀ = U₀ := map_comap_eq_self hU₀L'
    rw [← card_map_of_injective hφ'₀, h1, hU₀def, card_map_of_injective hφ, hW₁def,
      card_map_of_injective (MulAut.conj c).injective]
  have hWp : IsPGroup 2 W := by
    obtain ⟨k, hk⟩ := UC.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hWcard.trans hk)
  have hWidx : ¬ 2 ∣ W.index := by
    have h1 := W.card_mul_index
    have h2 := (UC : Subgroup (adjointGroup .E6 K)).card_mul_index
    rw [hWcard] at h1
    have hpos : 0 < Nat.card (UC : Subgroup (adjointGroup .E6 K)) := Nat.card_pos
    have h3 : W.index = (UC : Subgroup (adjointGroup .E6 K)).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact UC.not_dvd_index
  set WS : Sylow 2 (adjointGroup .E6 K) := hWp.toSylow hWidx with hWS
  have hwW : w ∈ centralizer ((WS : Subgroup (adjointGroup .E6 K)) :
      Set (adjointGroup .E6 K)) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : φ'₀ a ∈ U₀ := ha
    have h := mem_centralizer_singleton_iff.1 (hΛy (hU₀Λ ha'))
    apply hφ'₀
    rw [map_mul, map_mul, hw]
    exact h
  have hw1 : w ≠ 1 := by
    intro h
    apply e6Rep_ne_one (K := K) 0
    apply hφ
    rw [map_one, ← hydef, ← hw, h, map_one]
  obtain ⟨c', hc'⟩ := E8Pilot.exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ
    (isRoot_single .E6 (0 : Fin 6)) WS hwW hw1
  set φ' : adjointGroup .E6 K →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'y : φ' (e6Rep K 0) = y := by
    rw [hφ'def, MonoidHom.comp_apply, EPilot.e6Rep_zero_eq_pinnedElt, ← hc', ← hw]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hΛ' : (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ =
      (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ' := by
    have hR : (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ' =
        CFSG.conjugate L g₁ ⊓ centralizer ({y} : Set G) := by
      rw [F4Pilot.map_centralizer_singleton hφ', hφ'r, hφ'y]
    rw [← hΛdef, hR]
    apply le_antisymm
    · exact le_inf (hΛL'.trans inf_le_right) hΛy
    · have hperf' : ⁅(centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ',
          (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ'⁆ =
          (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ' := by
        rw [← map_commutator, hperf]
      have ht' : (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))).map φ' ≤
          centralizer ({t} : Set G) := by
        rw [hR]
        intro x hx
        have h1 := F4Pilot.conjugate_le_centralizer htC g₁ hx.1
        rw [hg₁] at h1
        exact F4Pilot.mem_centralizer_singleton_of_mul h1 hx.2
      have hle := std_perfect_le hset hOut htC ht hperf' ht'
      rw [hR] at hle
      rw [hΛeq]
      exact fun x hx => ⟨hle hx, hx.2⟩
  obtain ⟨hQ, hQM, hQMb, hMN⟩ := EPilot.isTwoRadicalDecomp_e6Rep_zero (K := K)
  have hQMd : Disjoint (EPilot.rootRadical .E6 K (Pi.single (0 : Fin 6) 1))
      (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) := disjoint_iff.2 hQMb
  have hΛQM : (EPilot.rootRadical .E6 K (Pi.single (0 : Fin 6) 1) ⊔
      EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)).map φ =
      (EPilot.rootRadical .E6 K (Pi.single (0 : Fin 6) 1) ⊔
        EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)).map φ' := by
    rw [hQM]
    exact hΛ'
  have hJM : posJ K ≤ EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) :=
    EPilot.highRootSL2_subgroupOf_le_rootPerpLevi_e6Rep_zero
  have hXJ' : X ≤ (posJ K).map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨ι, -, P, hP, ⟨eP⟩⟩ := EPilot.exists_le_centralizer_mulEquiv_of_two_decompositions
    hφ hφ' hQ hQ forall_normal_isPGroup_eq_bot_rootPerpLevi_single_zero
    forall_normal_isPGroup_eq_bot_rootPerpLevi_single_zero hMN hMN hQMd hQMd hΛQM
    hJM hXJ' (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  obtain ⟨eD⟩ := nonempty_centralizer_map_posJ_rootPerpLevi_mulEquiv ι
  refine ⟨P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  have h := (hP.trans inf_le_left).trans (hφ'r ▸ F4Pilot.conjugate_le_centralizer htC g₁)
  rwa [hg₁] at h

end CFSG.SeitzReduction.E6Pilot
