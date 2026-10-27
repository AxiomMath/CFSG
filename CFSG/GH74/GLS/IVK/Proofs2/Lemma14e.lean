module

public import CFSG.Dihedral.PSL2CyclingOddCore
public import CFSG.Dihedral.OriginalOddCore
public import CFSG.Dihedral.Glauberman.DicksonMaxCases
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.GH74.GLS.IVK.L2.Borel
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open Subgroup CFSG.DihedralBlueprint CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Glauberman.Dickson.MaxCases CFSG.Glauberman.Dickson.MaxUp in
theorem exists_cycles_of_a4 {G : Type} [Group G] [Finite G] (S : Subgroup G)
    (e : S ≃* alternatingGroup (Fin 4)) :
    ∃ V : Subgroup G, IsKleinFour V ∧ V ≤ S ∧ Cycles S V := by
  obtain ⟨V, hVcard, hVmem⟩ := exists_kleinFour e
  have hVS : V ≤ S := fun x hx => ((hVmem x).mp hx).1
  have hsq : ∀ v : V, v ^ 2 = 1 := by
    intro v
    have := ((hVmem v).mp v.2).2
    exact Subtype.ext (by simpa [sq] using this)
  have hexp : Monoid.exponent V = 2 := by
    have hdvd : Monoid.exponent V ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
    have hne : Monoid.exponent V ≠ 1 := by
      intro h1
      have hsub : Subsingleton V := ⟨fun a b => by
        have ha := Monoid.pow_exponent_eq_one a
        have hb := Monoid.pow_exponent_eq_one b
        rw [h1, pow_one] at ha hb
        rw [ha, hb]⟩
      have h2 := Nat.card_unique (α := V)
      omega
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hK : IsKleinFour V := ⟨hVcard, hexp⟩
  have h3 : 3 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv, card_alternatingFour']
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨V, hK, hVS, (x : G), x.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro v
    have hxS : (x : G) ∈ S := x.2
    constructor
    · intro hv
      obtain ⟨hvS, hvv⟩ := (hVmem v).mp hv
      rw [hVmem]
      refine ⟨S.mul_mem (S.mul_mem hxS hvS) (S.inv_mem hxS), ?_⟩
      calc (x : G) * v * (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹)
          = (x : G) * (v * v) * (x : G)⁻¹ := by group
        _ = 1 := by rw [hvv]; group
    · intro hv
      obtain ⟨hvS, hvv⟩ := (hVmem _).mp hv
      rw [hVmem]
      have hvS' : v ∈ S := by
        have h1 := S.mul_mem (S.mul_mem (S.inv_mem hxS) hvS) hxS
        have h2 : (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹) * (x : G) = v := by group
        rwa [h2] at h1
      refine ⟨hvS', ?_⟩
      have : (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹)) * (x : G) = 1 := by
        rw [hvv]; group
      calc v * v = (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹)) * (x : G) := by
            group
        _ = 1 := this
  · intro v hvV hv1 hxv
    obtain ⟨hvS, hvv⟩ := (hVmem v).mp hvV
    have hcomm : Commute (x : G) v := by
      have : (x : G) * v * (x : G)⁻¹ = v := hxv
      exact mul_inv_eq_iff_eq_mul.mp this
    have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hvv) hv1
    have hx3' : orderOf (x : G) = 3 := by rw [← hx3]; exact Subgroup.orderOf_coe x
    have hord : orderOf ((x : G) * v) = 6 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx3', hv2]; decide), hx3', hv2]
    have hxvS : (x : G) * v ∈ S := S.mul_mem x.2 hvS
    rcases pow_of_mulEquiv_alternatingFour e hxvS with h | h
    · have := orderOf_dvd_of_pow_eq_one h
      rw [hord] at this
      omega
    · have := orderOf_dvd_of_pow_eq_one h
      rw [hord] at this
      omega


section Fixed

open CFSG.GH74.GLS.IVK.L2Borel

theorem exists_a4_of_equiv_psl2 {G : Type} [Group G] {F₀ : Type} [Field F₀] [Finite F₀]
    (h2 : (2 : F₀) ≠ 0) (φ : G ≃* PSL2 F₀) :
    ∃ S : Subgroup G, Nonempty (S ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨H, ⟨eH⟩⟩ := CFSG.Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup h2
  exact ⟨H.map φ.symm.toMonoidHom,
    ⟨(Subgroup.equivMapOfInjective H φ.symm.toMonoidHom φ.symm.injective).symm.trans eH⟩⟩

theorem exists_a4_of_equiv_pgl2 {G : Type} [Group G] {F₀ : Type} [Field F₀] [Finite F₀]
    (h2 : (2 : F₀) ≠ 0) (φ : G ≃* PGL2 F₀) :
    ∃ S : Subgroup G, Nonempty (S ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨H, ⟨eH⟩⟩ := CFSG.Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup h2
  let ι : PSL2 F₀ →* PGL2 F₀ := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hι : Function.Injective ι := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  refine ⟨(H.map ι).map φ.symm.toMonoidHom, ⟨?_⟩⟩
  exact ((Subgroup.equivMapOfInjective _ _ φ.symm.injective).symm.trans
    (Subgroup.equivMapOfInjective H ι hι).symm).trans eH

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem exists_a4_le_fixed (hF : L2Field F) (e : K ≃* L2 F) (σ : F ≃+* F) :
    ∃ S : Subgroup K, S ≤ fixedSubgroup K (fieldAutHom e σ) ∧
      Nonempty (S ≃* alternatingGroup (Fin 4)) := by
  have key : ∃ S₀ : Subgroup ↥(fixedSubgroup K (fieldAutHom e σ)),
      Nonempty (S₀ ≃* alternatingGroup (Fin 4)) := by
    rcases Nat.even_or_odd (orderOf σ) with heven | hodd
    · obtain ⟨F₀, _, _, hq₀, ⟨φ⟩⟩ := isPGL2_fixedSubgroup e σ heven
      have hodd₀ : Odd (Nat.card F₀) := by
        have : Odd (Nat.card F₀ ^ orderOf σ) := hq₀ ▸ hF.1
        exact (Nat.odd_pow_iff (by
          have := orderOf_pos σ
          omega)).mp this
      exact exists_a4_of_equiv_pgl2 (two_ne_zero_of_odd_card hodd₀) φ
    · obtain ⟨F₀, _, _, hq₀, ⟨φ⟩⟩ := isL2_fixedSubgroup e σ hodd
      have hodd₀ : Odd (Nat.card F₀) := by
        have : Odd (Nat.card F₀ ^ orderOf σ) := hq₀ ▸ hF.1
        exact (Nat.odd_pow_iff (by
          have := orderOf_pos σ
          omega)).mp this
      exact exists_a4_of_equiv_psl2 (two_ne_zero_of_odd_card hodd₀) (φ.trans (L2.equivPSL F₀))
  obtain ⟨S₀, ⟨eS⟩⟩ := key
  exact ⟨S₀.map (fixedSubgroup K (fieldAutHom e σ)).subtype, Subgroup.map_subtype_le S₀,
    ⟨(Subgroup.equivMapOfInjective S₀ _ (fixedSubgroup K (fieldAutHom e σ)).subtype_injective).symm.trans
      eS⟩⟩

end Fixed


section Main14e

open CFSG.GH74.GLS.IVK.L2Borel

theorem ivk_1_4e
    : IVK_1_4e := by
  intro F _ _ hF K _ _ e σ X hX1 hXodd
  by_contra hcon
  push Not at hcon
  obtain ⟨S, hSA, ⟨eS⟩⟩ := exists_a4_le_fixed hF e σ
  have hSN : S ≤ normalizer (X : Set K) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hcon s (hSA hs) x hx
    · intro hx
      have h1 := hcon s⁻¹ ((fixedSubgroup K (fieldAutHom e σ)).inv_mem (hSA hs)) _ hx
      have h2 : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rwa [h2] at h1
  let φ : K ≃* PSL2 F := toPSL e
  set X' : Subgroup (PSL2 F) := X.map φ.toMonoidHom with hX'
  set S' : Subgroup (PSL2 F) := S.map φ.toMonoidHom with hS'
  have hSN' : S' ≤ normalizer (X' : Set (PSL2 F)) := by
    rw [hX', normalizer_map_equiv]
    exact Subgroup.map_mono hSN
  have eS' : S' ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective S φ.toMonoidHom φ.injective).symm.trans eS
  obtain ⟨V, hV, hVS, hc⟩ := exists_cycles_of_a4 S' eS'
  obtain ⟨x, hxS, hxN, hxmove⟩ := hc
  have hCyc : Cycles (normalizer (X' : Set (PSL2 F))) V := ⟨x, hSN' hxS, hxN, hxmove⟩
  have hbot := psl2_cycling_oddCoreOf_eq_bot F (isOddPrimePower_of_L2Field hF)
    (normalizer (X' : Set (PSL2 F))) V hV (hVS.trans hSN') hCyc
  have hodd' : Odd (Nat.card X') := by
    rwa [Nat.card_congr (Subgroup.equivMapOfInjective X φ.toMonoidHom φ.injective).toEquiv.symm]
  have hle : X' ≤ CFSG.DihedralBlueprint.oddCoreOf (normalizer (X' : Set (PSL2 F))) :=
    normal_odd_le_oddCoreOf X' _ Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hodd'
  rw [hbot] at hle
  exact hX1 ((Subgroup.map_eq_bot_iff_of_injective X (f := φ.toMonoidHom) φ.injective).mp (le_bot_iff.mp hle))

end Main14e

end CFSG.GH74.GLS.IVK.Proofs2
