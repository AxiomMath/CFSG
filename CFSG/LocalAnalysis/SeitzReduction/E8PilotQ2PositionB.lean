module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionF5

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms


section F56

variable {K : Type} [Field K]

theorem e7Levi_le_centralizer_posJE8_of_finite [Finite K] [CharP K 2] :
    e7Levi K ≤ centralizer (posJE8 K : Set (adjointGroup .E8 K)) :=
  centralizer_highRootSL2_subgroupOf_E8.symm.le

theorem nonempty_centralizer_map_conj_posJE8_mulEquiv_of_finite [Finite K] [CharP K 2]
    (c : adjointGroup .E8 K) :
    Nonempty (centralizer (((posJE8 K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) ≃* e7Levi K) := by
  have hcen : centralizer (((posJE8 K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) =
        (e7Levi K).map (MulAut.conj c).toMonoidHom := by
    rw [← F4Pilot.map_centralizer_mulEquiv (MulAut.conj c) (posJE8 K), posJE8,
      centralizer_highRootSL2_subgroupOf_E8]
  exact ⟨(MulEquiv.subgroupCongr hcen).trans
    ((e7Levi K).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

theorem factF56E8_of_factF5E8_of_finite [Finite K] [CharP K 2] (h : FactF5E8 K) :
    FactF56E8 K := by
  intro ι
  obtain ⟨c, hc⟩ := h ι
  rw [hc]
  exact nonempty_centralizer_map_conj_posJE8_mulEquiv_of_finite c

theorem factF56E8_of_one_le {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) : FactF56E8 K := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  exact factF56E8_of_factF5E8_of_finite (factF5E8 hf hK)

end F56

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_E8_of_one_le {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ P : Subgroup G,
      P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm (repXE8 K) : G)} : Set G) ∧
      Nonempty (P ≃* e7Levi K) := by
  classical
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_E8 e
  have hF56 : FactF56E8 K := factF56E8_of_one_le hf hK
  have hτ : Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 := Or.inr (Or.inr rfl)
  set φ : adjointGroup .E8 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hperf : ⁅centralizer ({repXE8 K} : Set (adjointGroup .E8 K)),
      centralizer ({repXE8 K} : Set (adjointGroup .E8 K))⁆ =
        centralizer ({repXE8 K} : Set (adjointGroup .E8 K)) :=
    commutator_centralizer_repXE8_of_one_le hf hK
  obtain ⟨U, hU⟩ := hzU
  set zC : adjointGroup .E8 K := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC1 : zC ≠ 1 := by
    intro h
    apply hz1
    rw [← hφz, h, map_one]
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (adjointGroup .E8 K) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (adjointGroup .E8 K)) ↔ e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hzCU : zC ∈ centralizer ((UC : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h := hU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφz]
    exact h
  obtain ⟨c, hc⟩ :=
    exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ isRoot_rootXE8 UC hzCU hzC1
  set y : G := φ (repXE8 K) with hydef
  have hyL : y ∈ L := hφr ▸ ⟨repXE8 K, rfl⟩
  have hy : y = φ c * z * (φ c)⁻¹ := by
    rw [hydef, repXE8, ← hc, map_mul, map_mul, map_inv, hφz]
  have hcL : φ c ∈ L := hφr ▸ ⟨c, rfl⟩
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    have htc : φ c * t = t * φ c := mem_centralizer_singleton_iff.1 (hLt hcL)
    calc g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
      _ = φ c * t * z * (φ c)⁻¹ := by rw [hg, mul_assoc (φ c) t z]
      _ = t * (φ c * z * (φ c)⁻¹) := by rw [htc]; group
      _ = t * y := by rw [hy]
  set Λ := (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ with hΛdef
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
  set φ'₀ : adjointGroup .E8 K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  have hyΛ : y ∈ Λ := hΛeq ▸ ⟨hyL, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨w, hw⟩ : y ∈ φ'₀.range := hφ'₀r ▸ (hΛL' hyΛ).2
  set W₁ := (UC : Subgroup (adjointGroup .E8 K)).map (MulAut.conj c).toMonoidHom with hW₁def
  have hW₁y : ∀ a ∈ W₁, a * repXE8 K = repXE8 K * a := by
    rintro _ ⟨u, hu, rfl⟩
    have h := mem_centralizer_iff.1 hzCU u hu
    rw [repXE8, ← hc]
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
  have hWcard : Nat.card W = Nat.card (UC : Subgroup (adjointGroup .E8 K)) := by
    have h1 : W.map φ'₀ = U₀ := map_comap_eq_self hU₀L'
    rw [← card_map_of_injective hφ'₀, h1, hU₀def, card_map_of_injective hφ, hW₁def,
      card_map_of_injective (MulAut.conj c).injective]
  have hWp : IsPGroup 2 W := by
    obtain ⟨k, hk⟩ := UC.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hWcard.trans hk)
  have hWidx : ¬ 2 ∣ W.index := by
    have h1 := W.card_mul_index
    have h2 := (UC : Subgroup (adjointGroup .E8 K)).card_mul_index
    rw [hWcard] at h1
    have hpos : 0 < Nat.card (UC : Subgroup (adjointGroup .E8 K)) := Nat.card_pos
    have h3 : W.index = (UC : Subgroup (adjointGroup .E8 K)).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact UC.not_dvd_index
  set WS : Sylow 2 (adjointGroup .E8 K) := hWp.toSylow hWidx with hWS
  have hwW : w ∈ centralizer ((WS : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : φ'₀ a ∈ U₀ := ha
    have h := mem_centralizer_singleton_iff.1 (hΛy (hU₀Λ ha'))
    apply hφ'₀
    rw [map_mul, map_mul, hw]
    exact h
  have hw1 : w ≠ 1 := by
    intro h
    apply repXE8_ne_one (K := K)
    apply hφ
    rw [map_one, ← hydef, ← hw, h, map_one]
  obtain ⟨c', hc'⟩ :=
    exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ isRoot_rootXE8 WS hwW hw1
  set φ' : adjointGroup .E8 K →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'y : φ' (repXE8 K) = y := by
    rw [hφ'def, MonoidHom.comp_apply, repXE8, ← hc', ← hw]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hΛ' : (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ =
      (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' := by
    have hR : (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' =
        CFSG.conjugate L g₁ ⊓ centralizer ({y} : Set G) := by
      rw [F4Pilot.map_centralizer_singleton hφ', hφ'r, hφ'y]
    rw [← hΛdef, hR]
    apply le_antisymm
    · exact le_inf (hΛL'.trans inf_le_right) hΛy
    · have hperf' : ⁅(centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ',
          (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ'⁆ =
          (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' := by
        rw [← map_commutator, hperf]
      have ht' : (centralizer ({repXE8 K} : Set (adjointGroup .E8 K))).map φ' ≤
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
  obtain ⟨hQ, hQM, hQMb, hMN⟩ := isTwoRadicalDecomp_repXE8 (K := K)
  have hQMd : Disjoint (xRadicalE8 K) (xLeviE8 K) := disjoint_iff.2 hQMb
  have hΛQM : (xRadicalE8 K ⊔ xLeviE8 K).map φ = (xRadicalE8 K ⊔ xLeviE8 K).map φ' := by
    rw [hQM]
    exact hΛ'
  have hXJ' : X ≤ (posJE8 K).map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨ι, -, P, hP, ⟨eP⟩⟩ := EPilot.exists_le_centralizer_mulEquiv_of_two_decompositions
    hφ hφ' hQ hQ (forall_normal_isPGroup_eq_bot_xLeviE8_of_one_le hf hK)
    (forall_normal_isPGroup_eq_bot_xLeviE8_of_one_le hf hK) hMN hMN hQMd hQMd hΛQM
    posJE8_le_xLeviE8 hXJ'
    (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  obtain ⟨eD⟩ := hF56 ι
  refine ⟨P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  have h := (hP.trans inf_le_left).trans (hφ'r ▸ F4Pilot.conjugate_le_centralizer htC g₁)
  rwa [hg₁] at h

end CFSG.SeitzReduction.E8Pilot
