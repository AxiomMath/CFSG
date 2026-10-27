module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

section Generic

variable {J : Type} [Group J]

@[expose] def gammaSub (J : Type) [Group J] (D : Subgroup (MulAut J)) : Subgroup J :=
  ⨆ (D₀ : Subgroup (MulAut J)) (_ : D₀ ≤ D) (_ : pRank 2 ↥D - 1 ≤ pRank 2 ↥D₀), fixedIn J D₀

@[expose] def GenSub (J : Type) [Group J] : Prop :=
  ∀ D : Subgroup (MulAut J), CFSG.IsElementaryAbelian 2 ↥D → (pRank 2 ↥D = 2 ∨ pRank 2 ↥D = 3) →
    gammaSub J D = ⊤

theorem gammaSub_eq_gammaAct (D : Subgroup (MulAut J)) : gammaSub J D = gammaAct D.subtype := by
  refine le_antisymm (iSup₂_le fun D₀ hD₀ => iSup_le fun hr => ?_) (iSup₂_le fun E hE => ?_)
  · have hle : D₀ ≤ D.subtype.range := by rw [Subgroup.range_subtype]; exact hD₀
    have hmap := Subgroup.map_comap_eq_self hle
    have hrank : pRank 2 ↥(D₀.comap D.subtype) = pRank 2 ↥D₀ :=
      GenLocBasic.pRank_congr (((D₀.comap D.subtype).equivMapOfInjective D.subtype
        D.subtype_injective).trans (MulEquiv.subgroupCongr hmap))
    have := le_gammaAct D.subtype (E := D₀.comap D.subtype) (by rw [hrank]; exact hr)
    rwa [hmap] at this
  · have hrank : pRank 2 ↥E = pRank 2 ↥(E.map D.subtype) :=
      GenLocBasic.pRank_congr (E.equivMapOfInjective D.subtype D.subtype_injective)
    exact le_iSup₂_of_le (E.map D.subtype) (Subgroup.map_subtype_le E)
      (le_iSup_of_le (by rw [← hrank]; exact hE) le_rfl)

theorem genProp_of_genSub [Finite J] (h : GenSub J) : GenProp J := by
  intro A _ _ α hA
  by_cases hex : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hk⟩ := hex
    exact gammaAct_eq_top_of_le_ker α hE hk
  · simp only [not_exists, not_and] at hex
    obtain ⟨hR, hg, -⟩ := range_reduction α hA hex
    rw [hg, ← gammaSub_eq_gammaAct]
    exact h α.range hR.1 hR.2

theorem genLoc_of_mulEquiv {J' : Type} [Group J'] (e : J ≃* J') (h : GenLoc J) : GenLoc J' :=
  GenLoc.of_mulEquiv e h

theorem fixedIn_map_conj (B : Subgroup J) :
    fixedIn J (B.map (MulAut.conj : J →* MulAut J)) = centralizer (B : Set J) := by
  ext x
  rw [mem_centralizer_iff]
  constructor
  · intro hx b hb
    have := hx (MulAut.conj b) (mem_map_of_mem _ hb)
    simp only [MulAut.conj_apply] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  · intro hx φ hφ
    obtain ⟨b, hb, rfl⟩ := mem_map.1 hφ
    simp only [MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.2 (hx b hb)

namespace GenLocBasic

theorem conj_injective_of_center_trivial (hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1) :
    Function.Injective (MulAut.conj : J →* MulAut J) := by
  intro g h hgh
  have hc : ∀ x : J, g * x * g⁻¹ = h * x * h⁻¹ := fun x => by
    simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut J => φ x) hgh
  have := hZ (h⁻¹ * g) fun x => by
    have := hc x
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [this]
      _ = (h⁻¹ * g) * x := by group
  exact (inv_mul_eq_one.1 this).symm

end GenLocBasic

theorem map_comap_conj_of_le_inn [Finite J] (hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1)
    {D : Subgroup (MulAut J)} (hD : D ≤ (MulAut.conj : J →* MulAut J).range) :
    (D.comap (MulAut.conj : J →* MulAut J)).map MulAut.conj = D ∧
      pRank 2 ↥(D.comap (MulAut.conj : J →* MulAut J)) = pRank 2 ↥D := by
  have hmap := Subgroup.map_comap_eq_self hD
  refine ⟨hmap, GenLocBasic.pRank_congr ?_⟩
  exact ((D.comap (MulAut.conj : J →* MulAut J)).equivMapOfInjective _
    (GenLocBasic.conj_injective_of_center_trivial hZ)).trans (MulEquiv.subgroupCongr hmap)

theorem gammaSub_map_conj [Finite J] {B : Subgroup J} (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    gammaSub J (B.map (MulAut.conj : J →* MulAut J)) =
      gammaAct ((MulAut.conj : J →* MulAut J).comp B.subtype) := by
  rw [gammaSub_eq_gammaAct]
  have hπ := MonoidHom.subgroupMap_surjective (MulAut.conj : J →* MulAut J) B
  exact (GenLocBasic.gammaAct_comp_surj hB (B.map (MulAut.conj : J →* MulAut J)).subtype _ hπ).symm

theorem centralizer_le_gammaAct_conj [Finite J] {B : Subgroup J} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    {V : Subgroup J} (hVB : V ≤ B) (hV : Nat.card ↥B ≤ 2 * Nat.card ↥V) :
    centralizer (V : Set J) ≤ gammaAct ((MulAut.conj : J →* MulAut J).comp B.subtype) := by
  let E : Subgroup ↥B := V.comap B.subtype
  have hmapE : E.map B.subtype = V := Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  have hcard : Nat.card ↥E = Nat.card ↥V := by
    rw [← hmapE, Subgroup.card_map_of_injective B.subtype_injective]
  have hadm : pRank 2 ↥B - 1 ≤ pRank 2 ↥E := by
    rw [GenLocBasic.adm_iff_index hB]
    have h1 := Subgroup.card_mul_index E
    have hpos : 0 < Nat.card ↥E := Nat.card_pos
    exact Nat.le_of_mul_le_mul_left (by rw [h1]; omega) hpos
  have := le_gammaAct ((MulAut.conj : J →* MulAut J).comp B.subtype) hadm
  rwa [← Subgroup.map_map, hmapE, fixedIn_map_conj] at this

namespace GenLocBasic

theorem exists_two_ne_one {B : Subgroup J} [Finite B] (h : 2 < Nat.card ↥B) :
    ∃ t ∈ B, ∃ u ∈ B, t ≠ 1 ∧ u ≠ 1 ∧ t ≠ u := by
  have := Fintype.ofFinite ↥B
  have h' : 2 < Fintype.card ↥B := by rwa [Fintype.card_eq_nat_card]
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h'
  by_cases ha : a = 1
  · refine ⟨b, b.2, c, c.2, fun h => hab (ha.trans (Subtype.ext h.symm)), fun h => hac (ha.trans (Subtype.ext h.symm)),
      fun h => hbc (Subtype.ext h)⟩
  · by_cases hb : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha (Subtype.ext h), fun h => hbc (hb.trans (Subtype.ext h.symm)),
        fun h => hac (Subtype.ext h)⟩
    · refine ⟨a, a.2, b, b.2, fun h => ha (Subtype.ext h), fun h => hb (Subtype.ext h), fun h => hab (Subtype.ext h)⟩

end GenLocBasic

theorem gammaSub_inner_two [Finite J] {B : Subgroup J} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hr : pRank 2 ↥B = 2)
    (hgen : ∀ t ∈ B, ∀ u ∈ B, t ≠ 1 → u ≠ 1 → t ≠ u →
      centralizer ({t} : Set J) ⊔ centralizer ({u} : Set J) = ⊤) :
    gammaSub J (B.map (MulAut.conj : J →* MulAut J)) = ⊤ := by
  rw [gammaSub_map_conj hB]
  have hcard : Nat.card ↥B = 4 := by rw [GenLocBasic.card_eq_two_pow_pRank_type hB, hr]; norm_num
  obtain ⟨t, ht, u, hu, ht1, hu1, htu⟩ := GenLocBasic.exists_two_ne_one (B := B) (by omega)
  have key : ∀ t ∈ B, t ≠ 1 → centralizer ({t} : Set J) ≤
      gammaAct ((MulAut.conj : J →* MulAut J).comp B.subtype) := by
    intro t ht ht1
    have hsq : t ^ 2 = 1 := by
      rw [sq]; exact (WeakSigGen.forall_of_isElementaryAbelian hB).2 t ht
    have h2 : orderOf t = 2 := have := Fact.mk Nat.prime_two; orderOf_eq_prime hsq ht1
    have hV : Nat.card ↥(zpowers t) = 2 := by rw [Nat.card_zpowers, h2]
    have := centralizer_le_gammaAct_conj hB (V := zpowers t) (zpowers_le.2 ht) (by omega)
    rwa [zpowers_eq_closure, centralizer_closure] at this
  rw [eq_top_iff, ← hgen t ht u hu ht1 hu1 htu]
  exact sup_le (key t ht ht1) (key u hu hu1)

theorem gammaSub_inner_three [Finite J] {B : Subgroup J} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hr : pRank 2 ↥B = 3)
    (hloc : ∀ t ∈ B, t ≠ 1 → centralizer ({t} : Set J) ≤
      ⨆ (V : Subgroup J) (_ : V ≤ B) (_ : t ∈ V) (_ : Nat.card ↥V = 4), centralizer (V : Set J))
    (hgen : ∀ t ∈ B, ∀ u ∈ B, t ≠ 1 → u ≠ 1 → t ≠ u →
      centralizer ({t} : Set J) ⊔ centralizer ({u} : Set J) = ⊤) :
    gammaSub J (B.map (MulAut.conj : J →* MulAut J)) = ⊤ := by
  rw [gammaSub_map_conj hB]
  have hcard : Nat.card ↥B = 8 := by rw [GenLocBasic.card_eq_two_pow_pRank_type hB, hr]; norm_num
  obtain ⟨t, ht, u, hu, ht1, hu1, htu⟩ := GenLocBasic.exists_two_ne_one (B := B) (by omega)
  have key : ∀ t ∈ B, t ≠ 1 → centralizer ({t} : Set J) ≤
      gammaAct ((MulAut.conj : J →* MulAut J).comp B.subtype) := by
    intro t ht ht1
    refine (hloc t ht ht1).trans (iSup_le fun V => iSup_le fun hVB => iSup_le fun _ => iSup_le fun hV4 => ?_)
    exact centralizer_le_gammaAct_conj hB hVB (by omega)
  rw [eq_top_iff, ← hgen t ht u hu ht1 hu1 htu]
  exact sup_le (key t ht ht1) (key u hu hu1)

end Generic

end CFSG.GH74.Generic.BProg.B2
