module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UChiefModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UFix
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.ABGLocalTools Subgroup Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

theorem u4ChiefFacts : U4ChiefFacts := by
  intro G _ _ p n L U d hp hpq hn hLU S hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  obtain ⟨σ, hσ, h2, hSU⟩ := statedSU_data d.card_F
  let e : ↥(StatedSU 4 (2 ^ n) d.F) ≃* ↥(SUid σ 4) := MulEquiv.subgroupCongr hSU.symm
  let ε' : ↥L →* ↥(SUid σ 4) := (e : ↥(StatedSU 4 (2 ^ n) d.F) →* ↥(SUid σ 4)).comp d.ε
  have hε'surj : Function.Surjective ε' := e.surjective.comp d.ε_surj
  have hε'ker : ε'.ker = CFSG.pCore 2 ↥L := by
    rw [MonoidHom.ker_mulEquiv_comp]
    exact d.ε_ker
  have hε'val : ∀ l : ↥L, ((ε' l : ↥(SUid σ 4)) : GL (Fin 4) d.F) = ((d.ε l : _) : GL (Fin 4) d.F) :=
    fun l => rfl
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq_subgroupOf
  have hPpc : CFSG.pCore 2 ↥L ≤ (P : Subgroup ↥L) := by
    have hp2g := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_sup_of_normal_left P.isPGroup'
    have := P.is_maximal' hp2g le_sup_right
    rw [← this]
    exact le_sup_left
  set E : Subgroup ↥(SUid σ 4) := (S.subgroupOf L).map ε' with hEdef
  have hE : IsSylowOf 2 E ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · exact (hP ▸ P.isPGroup').map ε'
    · have hker_le : ε'.ker ≤ S.subgroupOf L := by rw [hε'ker, ← hP]; exact hPpc
      have hidx : E.index = (S.subgroupOf L).index := Subgroup.index_map_eq (S.subgroupOf L) hε'surj hker_le
      rw [Subgroup.relIndex_top_right, hidx, ← hP]
      exact P.not_dvd_index
  obtain ⟨Qb, hQbE, xb, hxn, hx1, hxp, hxfix⟩ := chief_model hσ h2 hSU d.card_F hn hp hpq hE
  have hker2 : IsPGroup 2 ↥ε'.ker := by
    rw [hε'ker]
    exact CFSG.pCore_isPGroup
  obtain ⟨S'', hS''a, -, hS''map⟩ := exists_elemAbelian_lift_of_ker ε' hker2 hp hp2
    (E := Subgroup.zpowers xb) (CFSG.Open.isElemAbelian_zpowers hxp)
    (fun z _ => MonoidHom.mem_range.mpr (hε'surj z))
  obtain ⟨xt, hxtS, hxt⟩ := Subgroup.mem_map.mp (hS''map ▸ Subgroup.mem_zpowers xb)
  have hxt1 : xt ≠ 1 := by
    intro h
    apply hx1
    rw [← hxt, h, map_one]
  have hxtp : xt ^ p = 1 := hS''a.2 xt hxtS
  let Qc : Subgroup ↥L := Qb.comap ε'
  refine ⟨Qc.map L.subtype, ?_, (xt : G), ⟨xt.2, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨s, hs, hsl⟩ := Subgroup.mem_map.mp (hQbE hl)
    have hmem : l * s⁻¹ ∈ (P : Subgroup ↥L) := by
      apply hPpc
      rw [← hε'ker, MonoidHom.mem_ker, map_mul, map_inv, hsl, mul_inv_cancel]
    have hl' : l ∈ (P : Subgroup ↥L) := by
      have hs' : s ∈ (P : Subgroup ↥L) := by rw [hP]; exact hs
      have := (P : Subgroup ↥L).mul_mem hmem hs'
      simpa using this
    rw [hP] at hl'
    exact hl'
  ·
    have hnorm : ∀ y : ↥L, ε' y ∈ Subgroup.normalizer (Qb : Set ↥(SUid σ 4)) →
        ∀ q ∈ Qc.map L.subtype, (y : G) * q * (y : G)⁻¹ ∈ Qc.map L.subtype := by
      intro y hy q hq
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hq
      refine Subgroup.mem_map.mpr ⟨y * l * y⁻¹, ?_, rfl⟩
      show ε' (y * l * y⁻¹) ∈ Qb
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy (ε' l)).mp hl
    have hxn' : ε' xt ∈ Subgroup.normalizer (Qb : Set ↥(SUid σ 4)) := by rw [hxt]; exact hxn
    have hxinv : ε' xt⁻¹ ∈ Subgroup.normalizer (Qb : Set ↥(SUid σ 4)) := by
      rw [map_inv]
      exact (Subgroup.normalizer (Qb : Set ↥(SUid σ 4))).inv_mem hxn'
    refine Subgroup.mem_normalizer_iff.mpr fun g => ?_
    constructor
    · intro hg
      exact hnorm xt hxn' g hg
    · intro hg
      have := hnorm xt⁻¹ hxinv _ hg
      simpa [mul_assoc] using this
  · intro h
    exact hxt1 (Subtype.ext h)
  · have := congrArg (fun t : ↥L => (t : G)) hxtp
    simpa using this
  ·
    intro u hu hs
    let uu : ↥U := ⟨u, hu⟩
    have key : ∀ l : ↥L, (⁅(l : G), u⁆ ∈ centralizer (L : Set G)) ↔
        ((d.ε l : _) : GL (Fin 4) d.F).1 *ᵥ Multiplicative.toAdd (d.φ uu) =
          Multiplicative.toAdd (d.φ uu) := by
      intro l
      have hu' : (l : G) * u * (l : G)⁻¹ ∈ U := (mem_normalizer_iff.mp (hLU l.2) u).mp hu
      let u' : ↥U := ⟨(l : G) * u * (l : G)⁻¹, hu'⟩
      have hφ : d.φ u' = Multiplicative.ofAdd
          (((d.ε l : _) : GL (Fin 4) d.F).1 *ᵥ Multiplicative.toAdd (d.φ uu)) :=
        d.equiv l uu u' rfl
      let c : ↥U := u' * uu⁻¹
      have hc : (c : G) = ⁅(l : G), u⁆ := by
        simp [c, u', uu, commutatorElement_def]
      have hker : (⁅(l : G), u⁆ ∈ centralizer (L : Set G)) ↔ d.φ c = 1 := by
        rw [← hc, ← MonoidHom.mem_ker, d.φ_ker, Subgroup.mem_subgroupOf]
        exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
      rw [hker, map_mul, map_inv, hφ, mul_inv_eq_one]
      constructor
      · intro h
        exact Multiplicative.ofAdd.injective h
      · intro h
        rw [h]
        rfl
    have hfixQ : ∀ y ∈ Qb, y • Multiplicative.toAdd (d.φ uu) = Multiplicative.toAdd (d.φ uu) := by
      intro y hy
      obtain ⟨l, rfl⟩ := hε'surj y
      have hlQ : (l : G) ∈ Qc.map L.subtype := Subgroup.mem_map.mpr ⟨l, hy, rfl⟩
      exact (key l).mp (hs _ hlQ)
    have hxw := hxfix _ hfixQ
    rw [← hxt] at hxw
    exact (key xt).mpr hxw

end CFSG.LocalAnalysis.RankThreeUC
