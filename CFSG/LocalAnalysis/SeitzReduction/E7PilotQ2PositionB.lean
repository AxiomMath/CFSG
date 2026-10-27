module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFusion
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms


theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_E7_of_one_le {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ g₁ : G, g₁⁻¹ * t * g₁ = t * (e.symm (e7Rep K 0) : G) ∧ ∃ P : Subgroup G,
      P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm (e7Rep K 0) : G)} : Set G) ∧
      Nonempty (P ≃* EPilot.perpLevi .E7 K) := by
  classical
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_E7_of_finite e
  have hO2 : FactO2E7 K := factO2E7_of_finite
  have hF56 : FactF56E7 K := factF56E7_of_finite
  have hτ : Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inl rfl)
  set φ : adjointGroup .E7 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hperf : ⁅centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)),
      centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))⁆ =
        centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K)) :=
    commutator_centralizer_e7Rep_zero_of_one_le hf hK
  obtain ⟨U, hU⟩ := hzU
  set zC : adjointGroup .E7 K := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC1 : zC ≠ 1 := by
    intro h
    apply hz1
    rw [← hφz, h, map_one]
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (adjointGroup .E7 K) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (adjointGroup .E7 K)) ↔ e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hzCU : zC ∈ centralizer ((UC : Subgroup (adjointGroup .E7 K)) :
      Set (adjointGroup .E7 K)) := by
    rw [mem_centralizer_iff]
    intro c hc
    have h := hU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφz]
    exact h
  obtain ⟨c, hc⟩ :=
    E8Pilot.exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ isRoot_rootXE7 UC hzCU hzC1
  set y : G := φ (e7Rep K 0) with hydef
  have hyL : y ∈ L := hφr ▸ ⟨e7Rep K 0, rfl⟩
  have hy : y = φ c * z * (φ c)⁻¹ := by
    rw [hydef, e7Rep_zero_eq_pinnedElt_rootXE7, ← hc, map_mul, map_mul, map_inv, hφz]
  have hcL : φ c ∈ L := hφr ▸ ⟨c, rfl⟩
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    have htc : φ c * t = t * φ c := mem_centralizer_singleton_iff.1 (hLt hcL)
    calc g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
      _ = φ c * t * z * (φ c)⁻¹ := by rw [hg, mul_assoc (φ c) t z]
      _ = t * (φ c * z * (φ c)⁻¹) := by rw [htc]; group
      _ = t * y := by rw [hy]
  set Λ := (centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ with hΛdef
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
  set φ'₀ : adjointGroup .E7 K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  have hyΛ : y ∈ Λ := hΛeq ▸ ⟨hyL, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨w, hw⟩ : y ∈ φ'₀.range := hφ'₀r ▸ (hΛL' hyΛ).2
  set W₁ := (UC : Subgroup (adjointGroup .E7 K)).map (MulAut.conj c).toMonoidHom with hW₁def
  have hW₁y : ∀ a ∈ W₁, a * e7Rep K 0 = e7Rep K 0 * a := by
    rintro _ ⟨u, hu, rfl⟩
    have h := mem_centralizer_iff.1 hzCU u hu
    rw [e7Rep_zero_eq_pinnedElt_rootXE7, ← hc]
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
  have hWcard : Nat.card W = Nat.card (UC : Subgroup (adjointGroup .E7 K)) := by
    have h1 : W.map φ'₀ = U₀ := map_comap_eq_self hU₀L'
    rw [← card_map_of_injective hφ'₀, h1, hU₀def, card_map_of_injective hφ, hW₁def,
      card_map_of_injective (MulAut.conj c).injective]
  have hWp : IsPGroup 2 W := by
    obtain ⟨k, hk⟩ := UC.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hWcard.trans hk)
  have hWidx : ¬ 2 ∣ W.index := by
    have h1 := W.card_mul_index
    have h2 := (UC : Subgroup (adjointGroup .E7 K)).card_mul_index
    rw [hWcard] at h1
    have hpos : 0 < Nat.card (UC : Subgroup (adjointGroup .E7 K)) := Nat.card_pos
    have h3 : W.index = (UC : Subgroup (adjointGroup .E7 K)).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact UC.not_dvd_index
  set WS : Sylow 2 (adjointGroup .E7 K) := hWp.toSylow hWidx with hWS
  have hwW : w ∈ centralizer ((WS : Subgroup (adjointGroup .E7 K)) :
      Set (adjointGroup .E7 K)) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : φ'₀ a ∈ U₀ := ha
    have h := mem_centralizer_singleton_iff.1 (hΛy (hU₀Λ ha'))
    apply hφ'₀
    rw [map_mul, map_mul, hw]
    exact h
  have hw1 : w ≠ 1 := by
    intro h
    apply e7Rep_zero_ne_one (K := K)
    apply hφ
    rw [map_one, ← hydef, ← hw, h, map_one]
  obtain ⟨c', hc'⟩ :=
    E8Pilot.exists_conj_eq_pinnedElt_of_mem_centralizer_sylow hτ isRoot_rootXE7 WS hwW hw1
  set φ' : adjointGroup .E7 K →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'y : φ' (e7Rep K 0) = y := by
    rw [hφ'def, MonoidHom.comp_apply, e7Rep_zero_eq_pinnedElt_rootXE7, ← hc', ← hw]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hΛ' : (centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ =
      (centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ' := by
    have hR : (centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ' =
        CFSG.conjugate L g₁ ⊓ centralizer ({y} : Set G) := by
      rw [F4Pilot.map_centralizer_singleton hφ', hφ'r, hφ'y]
    rw [← hΛdef, hR]
    apply le_antisymm
    · exact le_inf (hΛL'.trans inf_le_right) hΛy
    · have hperf' : ⁅(centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ',
          (centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ'⁆ =
          (centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ' := by
        rw [← map_commutator, hperf]
      have ht' : (centralizer ({e7Rep K 0} : Set (adjointGroup .E7 K))).map φ' ≤
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
  obtain ⟨hQ, hQM, hQMb, hMN⟩ := isTwoRadicalDecomp_e7Rep_zero (K := K)
  have hQMd : Disjoint (xRadicalE7 K) (xLeviE7 K) := disjoint_iff.2 hQMb
  have hΛQM : (xRadicalE7 K ⊔ xLeviE7 K).map φ = (xRadicalE7 K ⊔ xLeviE7 K).map φ' := by
    rw [hQM]
    exact hΛ'
  have hXJ' : X ≤ (posJE7 K).map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨ι, -, P, hP, ⟨eP⟩⟩ := EPilot.exists_le_centralizer_mulEquiv_of_two_decompositions
    hφ hφ' hQ hQ hO2 hO2 hMN hMN hQMd hQMd hΛQM posJE7_le_xLeviE7 hXJ'
    (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  obtain ⟨eD⟩ := hF56 ι
  refine ⟨g₁, hg₁, P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  have h := (hP.trans inf_le_left).trans (hφ'r ▸ F4Pilot.conjugate_le_centralizer htC g₁)
  rwa [hg₁] at h

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_twoCentral_E7_of_one_le {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ g₁ : G, ∃ y ∈ ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype, y ≠ 1 ∧
      g₁⁻¹ * t * g₁ = t * y ∧ ∃ P : Subgroup G,
        P ≤ centralizer (X : Set G) ⊓ centralizer ({g₁⁻¹ * t * g₁} : Set G) ∧
          Nonempty (P ≃* EPilot.perpLevi .E7 K) := by
  obtain ⟨g₁, hg₁, P, hP, hPD⟩ := exists_le_centralizer_mulEquiv_of_conj_eq_mul_E7_of_one_le hset
    hf hK e htC ht hXodd hXJ hzL hz1 hzU hg
  refine ⟨g₁, (e.symm (e7Rep K 0) : G), ⟨e.symm (e7Rep K 0), ⟨e7Rep K 0, e7Rep_mem_perpLevi 0, rfl⟩,
    rfl⟩, fun h => ?_, hg₁, P, ?_, hPD⟩
  · apply e7Rep_zero_ne_one (K := K)
    have h' : e.symm (e7Rep K 0) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (e7Rep K 0), h', map_one]
  · rw [hg₁]
    exact hP

end CFSG.SeitzReduction.E7Pilot
