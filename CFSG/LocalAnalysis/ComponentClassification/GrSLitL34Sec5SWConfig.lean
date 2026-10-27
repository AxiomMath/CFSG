module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoreAt

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

structure L34WConfigAt (τ : ∀ (X : Type) [Group X], Prop) (G : Type) [Group G] [Finite G] (t : G)
    (P W : Subgroup G) : Prop where
  base : L34BaseSetting G
  order_two : orderOf t = 2
  le_centralizer : P ≤ centralizer ({t} : Set G)
  isPComponent : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G)))
  normal : (P.subgroupOf (centralizer ({t} : Set G))).Normal
  mirror : FooteLit.GSMirrorMaximal P
  type : τ (P ⧸ Open.fusionZStar P)
  odd : Odd (Nat.card W)
  ne_bot : W ≠ ⊥
  le_normalizer : normalizer (P : Set G) ≤ normalizer (W : Set G)
  wGroup_eq : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemTwo E → 8 ≤ Nat.card E →
    wGroup E = W

namespace L34WConfigAt

variable {τ : ∀ (X : Type) [Group X], Prop} {G : Type} [Group G] [Finite G] {t : G}
  {P W : Subgroup G}

theorem of_normalSetting (h : L34NormalSettingAt τ G t P) (hWo : Odd (Nat.card W)) (hW : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → wGroup E = W) : L34WConfigAt τ G t P W where
  base := h.1
  order_two := h.2.1
  le_centralizer := h.2.2.1
  isPComponent := h.2.2.2.1
  normal := h.2.2.2.2.1
  mirror := h.2.2.2.2.2.1
  type := h.2.2.2.2.2.2
  odd := hWo
  ne_bot := hW
  le_normalizer := hPW
  wGroup_eq := fun E hEt hE hE8 =>
    hWE E hEt ⟨isMulCommutative_iff_of_setLike.mpr hE.1, fun x hx => by
      rw [pow_two]
      exact hE.2 x hx⟩ hE8

theorem gwTwoBalanced (hc : L34WConfigAt τ G t P W) : GWTwoBalanced G :=
  gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hc.base.2.2.2.2.2.1

theorem centralizer_le_normalizer (hc : L34WConfigAt τ G t P W) :
    centralizer ({t} : Set G) ≤ normalizer (P : Set G) :=
  (normal_subgroupOf_iff_le_normalizer hc.le_centralizer).mp hc.normal

theorem centralizer_le (hc : L34WConfigAt τ G t P W) :
    centralizer ({t} : Set G) ≤ normalizer (W : Set G) :=
  hc.centralizer_le_normalizer.trans hc.le_normalizer

theorem mem_normalizer (hc : L34WConfigAt τ G t P W) : t ∈ normalizer (W : Set G) :=
  hc.centralizer_le (mem_centralizer_singleton_iff.mpr rfl)

theorem le_normalizer' (hc : L34WConfigAt τ G t P W) : P ≤ normalizer (W : Set G) :=
  hc.le_centralizer.trans hc.centralizer_le

theorem normalizer_ne_top (hc : L34WConfigAt τ G t P W) : normalizer (W : Set G) ≠ ⊤ := by
  intro hMt
  have hWn : W.Normal := ⟨fun n hn g => by
    have hg : g ∈ normalizer (W : Set G) := hMt ▸ mem_top g
    exact (mem_normalizer_iff.mp hg n).mp hn⟩
  have := hc.base.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
  · exact hc.ne_bot h
  · have h2 : 2 ∣ Nat.card W := by
      rw [h, card_top, ← hc.order_two]
      exact orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.mpr hc.odd) (even_iff_two_dvd.mpr h2)

theorem isKGroupCat (hc : L34WConfigAt τ G t P W) :
    SectionRank.IsKGroupCat ↥(normalizer (W : Set G)) :=
  UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
    (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hc.base.2.2.1
    _ hc.normalizer_ne_top

theorem isPerfect (hc : L34WConfigAt τ G t P W) : Group.IsPerfect ↥P := by
  have := CatalogueBAlternating.pComponent_perfect hc.isPComponent
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hc.le_centralizer).toMonoidHom)
    (subgroupOfEquivOfLe hc.le_centralizer).surjective

theorem commutator_mem_oddIn_of_centralizes (hc : L34WConfigAt τ G t P W) {M : Subgroup G}
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)}
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
      L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom)
    {v : G} (hvM : v ∈ M) (htv : t * v = v * t)
    (hvL : ∀ y ∈ L ⊔ L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom,
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hvM⟩ * y =
          y * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hvM⟩) :
    ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P := by
  intro p hp
  have hPM : P ≤ M := hM ▸ hc.le_normalizer'
  have hvN : v ∈ normalizer (P : Set G) :=
    hc.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr htv.symm)
  have hcP : p⁻¹ * v⁻¹ * p * v ∈ P := by
    have h1 : v⁻¹ * p * v⁻¹⁻¹ ∈ P := (mem_normalizer_iff.mp (inv_mem hvN) p).mp hp
    rw [inv_inv] at h1
    have h2 := mul_mem (inv_mem hp) h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set p' : ↥M := ⟨p, hPM hp⟩ with hp'
  set v' : ↥M := ⟨v, hvM⟩ with hv'
  have hpL : π p' ∈ L ⊔ L.map (MulAut.conj (π ⟨t, htM⟩)).toMonoidHom :=
    hPL (Subgroup.mem_map_of_mem _ (mem_subgroupOf.mpr hp))
  have hcomm := hvL _ hpL
  have hker : p'⁻¹ * v'⁻¹ * p' * v' ∈ pPrimeCore 2 ↥M := by
    have h2 : π (v'⁻¹ * p' * v') = π p' := by
      rw [map_mul, map_mul, map_inv, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 : π (p'⁻¹ * v'⁻¹ * p' * v') = 1 := by
      rw [show p'⁻¹ * v'⁻¹ * p' * v' = p'⁻¹ * (v'⁻¹ * p' * v') by group, map_mul, h2, map_inv,
        inv_mul_cancel]
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)]
    exact h1
  have hcO : p⁻¹ * v⁻¹ * p * v ∈ oddIn M :=
    Subgroup.mem_map.mpr ⟨_, hker, rfl⟩
  exact GrS5.inf_oddIn_le_oddIn hPM ⟨hcO, hcP⟩

end L34WConfigAt

end CFSG.ComponentClassification.GrSLit.L34Sec5S
