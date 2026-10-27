module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OChiefModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UFix
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.ABGLocalTools Subgroup Matrix
open scoped commutatorElement

theorem o6ChiefFacts : O6ChiefFacts := by
  intro G _ _ p n L U d hp hpq hn hLU S hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  haveI : CharP d.F 2 := by
    letI : Fintype d.F := Fintype.ofFinite d.F
    have h : Fintype.card d.F = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact d.card_F
    exact charP_of_card_eq_prime_pow h
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq_subgroupOf
  have hPpc : CFSG.pCore 2 ↥L ≤ (P : Subgroup ↥L) := by
    have hp2g := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_sup_of_normal_left P.isPGroup'
    have := P.is_maximal' hp2g le_sup_right
    rw [← this]
    exact le_sup_left
  set E : Subgroup ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c)) := (S.subgroupOf L).map d.ε
    with hEdef
  have hE : IsSylowOf 2 E ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · exact (hP ▸ P.isPGroup').map d.ε
    · have hker_le : d.ε.ker ≤ S.subgroupOf L := by rw [d.ε_ker, ← hP]; exact hPpc
      have hidx : E.index = (S.subgroupOf L).index :=
        Subgroup.index_map_eq (S.subgroupOf L) d.ε_surj hker_le
      rw [Subgroup.relIndex_top_right, hidx, ← hP]
      exact P.not_dvd_index
  obtain ⟨Qb, hQbE, xb, hxn, hx1, hxp, hxfix⟩ := chief_model_O6 d.irred d.card_F hn hp hpq hE
  have hker2 : IsPGroup 2 ↥d.ε.ker := by
    rw [d.ε_ker]
    exact CFSG.pCore_isPGroup
  obtain ⟨S'', hS''a, -, hS''map⟩ := exists_elemAbelian_lift_of_ker d.ε hker2 hp hp2
    (E := Subgroup.zpowers xb) (CFSG.Open.isElemAbelian_zpowers hxp)
    (fun z _ => MonoidHom.mem_range.mpr (d.ε_surj z))
  obtain ⟨xt, hxtS, hxt⟩ := Subgroup.mem_map.mp (hS''map ▸ Subgroup.mem_zpowers xb)
  have hxt1 : xt ≠ 1 := by
    intro h
    apply hx1
    rw [← hxt, h, map_one]
  have hxtp : xt ^ p = 1 := hS''a.2 xt hxtS
  let Qc : Subgroup ↥L := Qb.comap d.ε
  refine ⟨Qc.map L.subtype, ?_, (xt : G), ⟨xt.2, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨s, hs, hsl⟩ := Subgroup.mem_map.mp (hQbE hl)
    have hmem : l * s⁻¹ ∈ (P : Subgroup ↥L) := by
      apply hPpc
      rw [← d.ε_ker, MonoidHom.mem_ker, map_mul, map_inv, hsl, mul_inv_cancel]
    have hl' : l ∈ (P : Subgroup ↥L) := by
      have hs' : s ∈ (P : Subgroup ↥L) := by rw [hP]; exact hs
      have := (P : Subgroup ↥L).mul_mem hmem hs'
      simpa using this
    rw [hP] at hl'
    exact hl'
  ·
    have hnorm : ∀ y : ↥L, d.ε y ∈ Subgroup.normalizer
        (Qb : Set ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) →
        ∀ q ∈ Qc.map L.subtype, (y : G) * q * (y : G)⁻¹ ∈ Qc.map L.subtype := by
      intro y hy q hq
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hq
      refine Subgroup.mem_map.mpr ⟨y * l * y⁻¹, ?_, rfl⟩
      show d.ε (y * l * y⁻¹) ∈ Qb
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy (d.ε l)).mp hl
    have hxn' : d.ε xt ∈ Subgroup.normalizer
        (Qb : Set ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) := by
      rw [hxt]
      exact hxn
    have hxinv : d.ε xt⁻¹ ∈ Subgroup.normalizer
        (Qb : Set ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) := by
      rw [map_inv]
      exact (Subgroup.normalizer
        (Qb : Set ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c)))).inv_mem hxn'
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
        ((d.ε l : _) : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F).1 *ᵥ
          Multiplicative.toAdd (d.φ uu) = Multiplicative.toAdd (d.φ uu) := by
      intro l
      have hu' : (l : G) * u * (l : G)⁻¹ ∈ U := (mem_normalizer_iff.mp (hLU l.2) u).mp hu
      let u' : ↥U := ⟨(l : G) * u * (l : G)⁻¹, hu'⟩
      have hφ : d.φ u' = Multiplicative.ofAdd
          (((d.ε l : _) : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F).1 *ᵥ
            Multiplicative.toAdd (d.φ uu)) :=
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
      obtain ⟨l, rfl⟩ := d.ε_surj y
      have hlQ : (l : G) ∈ Qc.map L.subtype := Subgroup.mem_map.mpr ⟨l, hy, rfl⟩
      exact (key l).mp (hs _ hlQ)
    have hxw := hxfix _ hfixQ
    rw [← hxt] at hxw
    exact (key xt).mpr hxw

end CFSG.LocalAnalysis.RankThreeUC
