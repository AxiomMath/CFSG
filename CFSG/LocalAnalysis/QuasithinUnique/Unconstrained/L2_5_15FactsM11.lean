module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M11
public import CFSG.Sporadic.Schreier.M11
public meta import Mathlib
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGen
public meta import CFSG.Sporadic.Schreier.M11Data
public meta import CFSG.Sporadic.Mathieu.M11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsM11Inputs
public import Certificates.Certificate4144
public import Certificates.Certificate110
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public meta import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public meta import CFSG.CGT.Timmesfeld75.ListWCBasic
public meta import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public meta import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public meta import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public meta import CFSG.ClassicalGroups
public import CFSG.LieType.BorelTits.CompleteFlag
public meta import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public meta import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public meta import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public meta import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Aux
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

theorem raw_c1 : m11Elements.all
    (fun g => decide ((g * m11gA = m11gA * g ∧ g ^ 3 = 1) ↔ g ∈ TlP)) = true :=
  Certificates.certificate4144.1

theorem raw_c2 : m11Elements.all
    (fun g => decide (g * m11gA = m11gA * g → TlP.all (fun t => decide (t * g = g * t)) = true →
      g = 1 ∨ g = m11gA)) = true :=
  Certificates.certificate4144.2.1

theorem raw_c3 : m11Elements.all
    (fun g => decide (TlP.all (fun t => decide (g * t = t * g)) = true →
      g = 1 ∨ g = m11gA)) = true :=
  Certificates.certificate4144.2.2.1

theorem raw_conj_M : m11Elements.all
    (fun u => decide (u ≠ 1 → u * u = 1 →
      m11Elements.any (fun g => decide (g * m11gA = u * g)) = true)) = true :=
  Certificates.certificate4144.2.2.2.1

theorem hgenM : ∀ t ∈ TlM, ∃ w ∈ WsM, t = evB aM bM w :=
  Certificates.certificate4144.2.2.2.2.1

theorem abM :
    aM ≠ 1 ∧ bM ≠ 1 ∧ (aM * bM) ^ 2 ≠ 1 ∧ (aM * bM) ^ 4 = 1 :=
  Certificates.certificate4144.2.2.2.2.2.1

theorem hPlcM : PlM.length ≤ 24 :=
  Certificates.certificate4144.2.2.2.2.2.2.1

theorem u0M_word : m11a = evB aM bM [true, false, true, false] :=
  Certificates.certificate4144.2.2.2.2.2.2.2

theorem hPlM : ∀ x ∈ TlM, ∀ y ∈ TlM, x ≠ 1 → y ≠ 1 → (x * y) ^ 2 ≠ 1 → (x * y) ^ 4 = 1 →
    (x, y) ∈ PlM := by
  intro x hx y hy h1 h2 h3 h4
  unfold PlM
  rw [List.mem_filter]
  refine ⟨List.mem_product.mpr ⟨hx, hy⟩, ?_⟩
  simp [h1, h2, h3, h4]

theorem aM_mem : aM ∈ TlM := List.mem_map.2 ⟨_, by simp [tWords], rfl⟩

theorem bM_mem : bM ∈ TlM := List.mem_map.2 ⟨_, by simp [tWords], rfl⟩

theorem u0M_mem_closure : m11a ∈ Subgroup.closure {x : M11G | x ∈ TlM} := by
  rw [u0M_word]
  refine Subgroup.closure_mono ?_ (evB_mem_closure aM bM _)
  intro x hx
  rcases hx with rfl | rfl
  · exact aM_mem
  · exact bM_mem

theorem coe_comm_iff (x y : M11G) : x * y = y * x ↔ x.1 * y.1 = y.1 * x.1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem coe_cube_iff (x : M11G) : x ^ 3 = 1 ↔ x.1 ^ 3 = 1 :=
  ⟨fun h => by simpa using congrArg Subtype.val h, fun h => Subtype.ext (by simpa using h)⟩

theorem coe_eq_one_iff (x : M11G) : x = 1 ↔ x.1 = 1 :=
  ⟨fun h => by simp [h], fun h => Subtype.ext h⟩

theorem coe_eq_u0_iff (x : M11G) : x = m11a ↔ x.1 = m11gA :=
  ⟨fun h => by simp [h], fun h => Subtype.ext h⟩

theorem mem_TlP (x : M11G) : x.1 ∈ TlP ↔ x ∈ TlM :=
  List.mem_map_of_injective Subtype.val_injective

theorem hTlM : ∀ x : M11G, (x * m11a = m11a * x ∧ x ^ 3 = 1) ↔ x ∈ TlM := by
  intro x
  have h := of_decide_eq_true (List.all_eq_true.1 raw_c1 x.1 ((mem_m11Elements _).2 x.2))
  rw [mem_TlP] at h
  rw [coe_comm_iff, coe_cube_iff]
  exact h

theorem hcenterM :
    ∀ w : M11G, w * m11a = m11a * w → (∀ t ∈ TlM, t * w = w * t) → w = 1 ∨ w = m11a := by
  intro w h1 h2
  have h := of_decide_eq_true (List.all_eq_true.1 raw_c2 w.1 ((mem_m11Elements _).2 w.2))
  rw [coe_eq_one_iff, coe_eq_u0_iff]
  apply h
  · exact (coe_comm_iff w m11a).1 h1
  · rw [List.all_eq_true]
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact decide_eq_true ((coe_comm_iff s w).1 (h2 s hs))

theorem hcentM : ∀ b : M11G, (∀ t ∈ TlM, b * t = t * b) → b = 1 ∨ b = m11a := by
  intro b h2
  have h := of_decide_eq_true (List.all_eq_true.1 raw_c3 b.1 ((mem_m11Elements _).2 b.2))
  rw [coe_eq_one_iff, coe_eq_u0_iff]
  apply h
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact decide_eq_true ((coe_comm_iff b s).1 (h2 s hs))

theorem hconjM : ∀ u : M11G, u ≠ 1 → u ^ 2 = 1 → ∃ g : M11G, g * m11a * g⁻¹ = u := by
  intro u hu1 hu2
  have hu1' : u.1 ≠ 1 := fun h => hu1 ((coe_eq_one_iff u).2 h)
  have hu2' : u.1 * u.1 = 1 := by
    have := congrArg Subtype.val hu2
    simpa [sq] using this
  have h := of_decide_eq_true (List.all_eq_true.1 raw_conj_M u.1 ((mem_m11Elements _).2 u.2))
  obtain ⟨g', hg', hgg⟩ := List.any_eq_true.1 (h hu1' hu2')
  have hgg' : g' * m11gA = u.1 * g' := of_decide_eq_true hgg
  refine ⟨⟨g', (mem_m11Elements _).1 hg'⟩, ?_⟩
  have : (⟨g', (mem_m11Elements _).1 hg'⟩ : M11G) * m11a = u * ⟨g', (mem_m11Elements _).1 hg'⟩ :=
    Subtype.ext hgg'
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem k33Facts_M11 : K33Facts (⊤ : Subgroup M11G) := by
  refine ⟨?_, ?_, ?_⟩
  · right
    rw [Subgroup.card_top]
    exact m11_card
  · obtain ⟨E, hE, hcard⟩ := Unc25G2.m11_exists_elemAbelian_nine
    exact ⟨E, le_top, hE, hcard⟩
  · intro u _ hu1 hu2
    exact k33InvFacts_top_of_data m11a hconjM TlM hTlM u0M_mem_closure hcenterM hcentM aM bM
      aM_mem bM_mem WsM hgenM abM.1 abM.2.1 abM.2.2.1 abM.2.2.2 PlM hPlM hPlcM u hu1 hu2

theorem k33Facts_of_M11 {G : Type} [Group G] {K : Subgroup G}
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) : K33Facts K :=
  k33Facts_of_mulEquiv e k33Facts_M11

end CFSG.QuasithinUnique.Unc25K1
