module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Cls
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29M12One
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NonTriv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section M12

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

omit [Finite G] in
theorem barOf_zpowers (z : G) : barOf z (zpowers z) = zpowers (toBar z ⟨z, z_mem_cen z⟩) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨n, hn⟩ := hc
    refine ⟨n, ?_⟩
    have hn' : z ^ n = (c : G) := hn
    have : (⟨z, z_mem_cen z⟩ : ↥(Cen z)) ^ n = c := Subtype.ext hn'
    show (toBar z ⟨z, z_mem_cen z⟩) ^ n = toBar z c
    rw [← this, map_zpow]
  · rintro ⟨n, hn⟩
    refine ⟨(⟨z, z_mem_cen z⟩ : ↥(Cen z)) ^ n, ⟨n, rfl⟩, ?_⟩
    have hn' : (toBar z ⟨z, z_mem_cen z⟩) ^ n = y := hn
    rw [← hn', map_zpow]

theorem m12_bar_isPGroup (h : Stage1M12 G z S) (hz2 : z * z = 1) {u : G} (hu : u ∈ Cen z)
    (hu2 : u * u = 1) (hu1 : u ∉ zpowers z) :
    IsPGroup 2 ↥(centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z))) := by
  obtain ⟨A, B, hAB, ⟨eA⟩, ⟨eB⟩, -⟩ := h.W_shape
  obtain ⟨A₃, ⟨e₃⟩, -, -, -, -, hfix⟩ := h.L_shape
  obtain ⟨hWn, ⟨hquot⟩⟩ := h.quot
  have hWc : Nat.card ↥(WBar z) = 32 := by
    obtain ⟨hsup, hcomm, hcard⟩ := hAB
    have h1 := IVK.Proofs2.Ivk93Adapt.jm_card_sup_mul_card_inf A B hcomm
    rw [hsup, hcard] at h1
    have hA8 : Nat.card ↥A = 8 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hB8 : Nat.card ↥B = 8 := by
      rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [hA8, hB8] at h1
    omega
  have hW2 : IsPGroup 2 ↥(WBar z) := IsPGroup.of_card (n := 5) (by rw [hWc]; norm_num)
  have hA3 : Nat.card ↥A₃ = 3 := by
    rw [Nat.card_congr e₃.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hfix' : ∀ w ∈ WBar z, (∀ a ∈ A₃, a * w = w * a) → w ∈ zpowers (toBar z ⟨z, z_mem_cen z⟩) :=
    fun w hw hc => by
      have := hfix w hw hc
      rwa [barOf_zpowers] at this
  have hv1 : toBar z ⟨u, hu⟩ ∉ zpowers (toBar z ⟨z, z_mem_cen z⟩) := fun hmem =>
    hu1 (mem_zpowers_of_toBar_mem hz2 hu hu2 hmem)
  have hsq : toBar z ⟨u, hu⟩ * toBar z ⟨u, hu⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, hu⟩ * ⟨u, hu⟩ : ↥(Cen z)) = 1 := Subtype.ext hu2
    rw [this, map_one]
  exact m12_centralizer_isPGroup (fun y => (zbar_central z y).symm) hW2 hWc hA3 ⟨hquot⟩ hfix'
    hsq hv1

theorem m12_twoNilp_of_mem (h : Stage1M12 G z S) (hz2 : z * z = 1) {U : Subgroup G}
    (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U) : TwoNilp ↥(centralizer (U : Set G)) := by
  obtain ⟨u, huU, hu1⟩ := exists_mem_not_zpowers hU hzU
  have hu : u ∈ Cen z := by
    show u ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_mem_four hU huU hzU
  exact twoNilp_centralizer_of_bar hzU huU hu
    (twoNilp_of_isPGroup (m12_bar_isPGroup h hz2 hu (four_sq_eq_one hU huU) hu1))

theorem lemma29FirstAt_of_mem_or_noconj {k : Kind}
    (hnoconj : ∀ U : Subgroup G, IVK.IsFourSubgroup U → (∀ u ∈ U, ¬ IsConj z u) →
      Lemma29Alt z k U)
    (hmem : ∀ U : Subgroup G, IVK.IsFourSubgroup U → z ∈ U → Lemma29Alt z k U) :
    Lemma29FirstAt z k := by
  intro U hU
  by_cases hno : ∀ u ∈ U, ¬ IsConj z u
  · exact hnoconj U hU hno
  push Not at hno
  obtain ⟨u₀, hu₀U, hu₀z⟩ := hno
  obtain ⟨c, hc⟩ := isConj_iff.mp hu₀z
  apply lemma29Alt_of_map_conj_inv U c
  apply hmem
  · exact four_map_of_injective _ (MulAut.conj c⁻¹).injective hU
  · refine ⟨u₀, hu₀U, ?_⟩
    show c⁻¹ * u₀ * c⁻¹⁻¹ = z
    rw [← hc]
    group

theorem lemma29FirstAt_of_m12 (ctx : Stage2Ctx G z Kind.m12 S)
    (hD2 : ∀ U : Subgroup G, IVK.IsFourSubgroup U → (∀ u ∈ U, ¬ IsConj z u) →
      HasNormal2Compl (centralizer (U : Set G))) : Lemma29FirstAt z Kind.m12 := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [ctx.central.1, pow_two] at this
  cases ctx.data with
  | m12 h =>
    refine lemma29FirstAt_of_mem_or_noconj (fun U hU hno => Or.inl (hD2 U hU hno))
      (fun U hU hzU => Or.inl ((hasNormal2Compl_iff_twoNilp _).mpr
        (m12_twoNilp_of_mem h hz2 hU hzU)))

end M12

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
