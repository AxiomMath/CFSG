module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.RecogE4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFullCentralizer

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution
open CFSG.Open (componentClassificationOddCore)
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

namespace Vtx

theorem autOddFree_of_oddCore_inf_centralizer {P : Type} [Group P]
    (h : ∀ H : Subgroup (MulAut P), inner P ≤ H → ∀ α ∈ H, orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) : Q3NM.AutOddFree P := by
  intro 𝒳 hinn f hf
  have h1 := h 𝒳 hinn (f : MulAut P) f.2 (by rwa [Subgroup.orderOf_coe])
  have hmap : (Subgroup.centralizer ({f} : Set ↥𝒳)).map 𝒳.subtype =
      𝒳 ⊓ Subgroup.centralizer {(f : MulAut P)} := by
    ext α
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.2, congrArg Subtype.val hg⟩
    · rintro ⟨hα, hαc⟩
      exact ⟨⟨α, hα⟩, Subtype.ext hαc, rfl⟩
  let e : ↥(Subgroup.centralizer ({f} : Set ↥𝒳)) ≃*
      ↥(𝒳 ⊓ Subgroup.centralizer {(f : MulAut P)}) :=
    ((Subgroup.centralizer ({f} : Set ↥𝒳)).equivMapOfInjective 𝒳.subtype
      𝒳.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  have h2 := CFSG.ComponentClassification.OddCore.equiv_invariant e
  have h3 : componentClassificationOddCore ↥(Subgroup.centralizer ({f} : Set ↥𝒳)) = ⊥ := by
    have h4 : (componentClassificationOddCore ↥(Subgroup.centralizer ({f} : Set ↥𝒳))).map
        e.toMonoidHom = ⊥ := h2.trans h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h4
  change (componentClassificationOddCore ↥(Subgroup.centralizer ({f} : Set ↥𝒳))).map
    (Subgroup.centralizer ({f} : Set ↥𝒳)).subtype = ⊥
  rw [h3, Subgroup.map_bot]

theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (φ : K ≃+* K) : φ = 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push Not at hx
    have : Fintype K := Fintype.ofFinite K
    have h3 : 3 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      have hs : ({0, 1, x} : Finset K).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hx.2)]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨zero_ne_one, Ne.symm hx.1⟩
      rw [← hs]
      exact Finset.card_le_univ _
    omega
  ext x
  rcases h01 x with rfl | rfl
  · simp
  · simp

theorem autOddFree_of_lieModel_PSp {M : Type} [Group M] [Finite M]
    (h : CFSG.Blueprint.LieModel M .PSp 3 2 1) : Q3NM.AutOddFree M := by
  rcases h with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl hK
    have : NeZero (3 : ℕ) := ⟨by norm_num⟩
    have hFin : Finite (StatedProj (StatedSp 3 K)) := Finite.of_equiv M e.toEquiv
    refine Q3NM.AutOddFree.of_mulEquiv e.symm (autOddFree_of_oddCore_inf_centralizer ?_)
    intro H hIH α hαH hα
    have hαI : α ∈ inner (StatedProj (StatedSp 3 K)) := by
      have hE := (automorphism_generation (K := K) (r := 3) le_rfl).1
      obtain ⟨g, φ, hgφ⟩ := SpChain.exists_eq_spInner_mul_fieldAut
        (show α ∈ spSemilinearAutGroup 3 K by rw [hE]; exact Subgroup.mem_top α)
      by_contra hn
      exact ((SpChain.spInner_mul_fieldAut_not_mem_inner_iff g φ).1 (hgφ ▸ hn))
        (ringEquiv_eq_one_of_card_two hK2 φ)
    exact even_symplectic_inner_involution_full_centralizer_odd_core (by norm_num) le_rfl hK H hIH
      hαI hα
  all_goals exact absurd h0 (by norm_num)

theorem autOddFree_of_lieModel_POmegaPlus {M : Type} [Group M] [Finite M]
    (h : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) : Q3NM.AutOddFree M := by
  rcases h with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hfull := even_orthogonal_all_involution_full_centralizer_odd_core M .POmegaPlus
      (Or.inl rfl) 4 1 hcl
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    let e' := coordinatePlusWitnessEquiv K e
    have hFin : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
      Finite.of_equiv M e'.toEquiv
    exact Q3NM.AutOddFree.of_mulEquiv e'.symm
      (autOddFree_of_oddCore_inf_centralizer (hfull K hK e))
  all_goals exact absurd h0 (by norm_num)

theorem autOddFree_of_exLie {M : Type} [Group M] [Finite M]
    (h : PhilipHall.QuaternionBridge.ExLie M) : Q3NM.AutOddFree M := by
  rcases h with h | h
  · exact autOddFree_of_lieModel_PSp h
  · exact autOddFree_of_lieModel_POmegaPlus h

theorem isSimpleGroup_of_exLie {M : Type} [Group M] [Finite M]
    (h : PhilipHall.QuaternionBridge.ExLie M) : IsSimpleGroup M := by
  rcases h with hQ | hQ
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp M 3 2 1 hcl
    all_goals exact absurd h0 (by norm_num)
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
        M 4 2 1 hcl).2
    all_goals exact absurd h0 (by norm_num)

theorem oddCoreIn_centralizer_eq_bot_of_exLie {M : Type} [Group M] [Finite M]
    (hM : PhilipHall.QuaternionBridge.ExLie M) (hZ : Subgroup.center M = ⊥) {s : M}
    (hs : orderOf s = 2) : Balance.oddCoreIn (Subgroup.centralizer ({s} : Set M)) = ⊥ := by
  let e : M ≃* ↥(Q3NM.innSubgroup M) :=
    MonoidHom.ofInjective (Q3NM.conj_injective_of_center_eq_bot hZ)
  have hf : orderOf (e s) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hs
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv e s (autOddFree_of_exLie hM _ le_rfl (e s) hf)

theorem center_quot_center_eq_bot {Y : Type} [Group Y]
    (hs : IsSimpleGroup (Y ⧸ Subgroup.center Y)) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Y ⧸ Subgroup.center Y)) with
    h | h
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := exists_ne (1 : Y ⧸ Subgroup.center Y)
    have hn : (Subgroup.zpowers g).Normal := ⟨fun x hx k => by
      have hxc : x ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := h ▸ Subgroup.mem_top x
      rw [Subgroup.mem_center_iff.mp hxc k, mul_inv_cancel_right]
      exact hx⟩
    have hcyc : IsCyclic (Y ⧸ Subgroup.center Y) := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with hb | ht
      · exact absurd (Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_zpowers g)) hg
      · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, ht⟩
    have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center Y)) (by rw [QuotientGroup.ker_mk'])
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    apply hg
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_center_iff.mpr fun k => hcomm.is_comm.comm k y

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
