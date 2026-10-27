module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (upperUnit diagUnit diagSL2 twistedDiagSL2
  upperUnit_mul_comm upperUnit_one_inv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer
  normalizer_le_normalizer_centralizerPerfectCore)
open scoped MatrixGroups

section Root

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G} {k : Fin n}

@[expose] noncomputable def SwapNeighbourParam.rootHom (P : SwapNeighbourParam e t k) {j : Fin n}
    (hkj : k ≠ j) (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) : SL(2, K) × SL(2, K) →* G :=
  P.Ψ.comp (((simpleRootHom K j).codRestrict _ (simpleRootHom_mem_spBlock hkj hk1)).prodMap
    ((simpleRootHom K j).codRestrict _ (simpleRootHom_mem_spBlock hkj hk1)))

variable (P : SwapNeighbourParam e t k) {j : Fin n} (hkj : k ≠ j)
  (hk1 : j.val + 1 < n → k.val ≠ j.val + 1)

theorem SwapNeighbourParam.rootHom_apply (A B : SL(2, K)) :
    P.rootHom hkj hk1 (A, B) = P.Ψ (⟨simpleRootHom K j A, simpleRootHom_mem_spBlock hkj hk1 A⟩,
      ⟨simpleRootHom K j B, simpleRootHom_mem_spBlock hkj hk1 B⟩) :=
  rfl

theorem SwapNeighbourParam.rootHom_diag (A : SL(2, K)) :
    P.rootHom hkj hk1 (A, A) = ((e.symm (simpleRootHom K j A) : L) : G) := by
  rw [SwapNeighbourParam.rootHom_apply, P.diag]

theorem SwapNeighbourParam.conj_rootHom (A B : SL(2, K)) :
    t * P.rootHom hkj hk1 (A, B) * t⁻¹ = P.rootHom hkj hk1 (B, A) := by
  rw [SwapNeighbourParam.rootHom_apply, P.swap, SwapNeighbourParam.rootHom_apply]

theorem SwapNeighbourParam.commute_rootHom_diagUnit (α : Kˣ) (s : Fin n → Kˣ) :
    Commute (P.rootHom hkj hk1 (diagUnit α, 1)) ((e.symm (diagSp K n s) : L) : G) := by
  obtain ⟨u, hu⟩ := simpleRootHom_diagUnit (R := K) j α
  set x : spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n)) :=
    (⟨simpleRootHom K j (diagUnit α), simpleRootHom_mem_spBlock hkj hk1 _⟩,
      ⟨simpleRootHom K j 1, simpleRootHom_mem_spBlock hkj hk1 _⟩) with hx
  have hfix1 : conjDiagSp ({k}ᶜ : Finset (Fin n)) (liftParam (RingHom.id K) s) x.1 = x.1 := by
    apply Subtype.ext
    rw [coe_conjDiagSp_apply, hx]
    simp only
    rw [hu, (commute_diagSp_diagSp (K := K) (liftParam (RingHom.id K) s) u).eq,
      mul_inv_cancel_right]
  have hfix2 : conjDiagSp ({k}ᶜ : Finset (Fin n)) (liftParam (RingHom.id K) s) x.2 = x.2 := by
    apply Subtype.ext
    rw [coe_conjDiagSp_apply, hx]
    simp
  have h := P.N2 s (mem_top s) x
  rw [hfix1, hfix2] at h
  change P.Ψ x * ((e.symm (diagSp K n s) : L) : G) = ((e.symm (diagSp K n s) : L) : G) * P.Ψ x
  calc P.Ψ x * ((e.symm (diagSp K n s) : L) : G) =
        (((e.symm (diagSp K n s) : L) : G) * P.Ψ x * ((e.symm (diagSp K n s) : L) : G)⁻¹) *
          ((e.symm (diagSp K n s) : L) : G) := by rw [← h]
    _ = ((e.symm (diagSp K n s) : L) : G) * P.Ψ x := by group

theorem SwapNeighbourParam.range_rootHom [Finite G] [Finite K] (hK : 4 ≤ Nat.card K) :
    (P.rootHom hkj hk1).range = pieceCore e ({j} : Finset (Fin n)) := by
  rw [P.pieceCore_singleton_eq_map hK hkj hk1]
  ext y
  constructor
  · rintro ⟨⟨A, B⟩, rfl⟩
    exact ⟨(⟨simpleRootHom K j A, simpleRootHom_mem_spBlock hkj hk1 A⟩,
      ⟨simpleRootHom K j B, simpleRootHom_mem_spBlock hkj hk1 B⟩),
      ⟨mem_subgroupOf.2 ⟨A, rfl⟩, mem_subgroupOf.2 ⟨B, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨x₁, x₂⟩, ⟨hx₁, hx₂⟩, rfl⟩
    obtain ⟨A, hA⟩ := mem_subgroupOf.1 hx₁
    obtain ⟨B, hB⟩ := mem_subgroupOf.1 hx₂
    refine ⟨(A, B), ?_⟩
    rw [SwapNeighbourParam.rootHom_apply]
    congr 1
    exact Prod.ext (Subtype.ext hA) (Subtype.ext hB)

end Root

section Orth

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_swap
    (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {k : Fin 3} (hk : k ≠ 2)
    (P : SwapNeighbourParam e t k) :
    modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  classical
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  have hk1 : (2 : Fin 3).val + 1 < 3 → k.val ≠ (2 : Fin 3).val + 1 :=
    fun h => absurd h (by decide)
  have h2 : ¬ (2 : Fin 3).val + 1 < 3 := by decide
  set ψ := P.rootHom hk hk1 with hψdef
  have hM : ψ.range = pieceCore e ({2} : Finset (Fin 3)) := P.range_rootHom hk hk1 hK
  have hψΔ : ∀ A : SL(2, K), ψ (A, A) = ((e.symm (longBlock K 3 2 A) : L) : G) := by
    intro A
    rw [hψdef, P.rootHom_diag, simpleRootHom_of_not_lt h2]
  have hψt : ∀ p : SL(2, K) × SL(2, K), t * ψ p * t⁻¹ = ψ p.swap := fun p =>
    P.conj_rootHom hk hk1 p.1 p.2
  set u : SL(2, K) × SL(2, K) := (upperUnit 1, upperUnit 1) with hudef
  set z : G := ((e.symm (siegDiag K 2 1) : L) : G) with hzdef
  have hz : ψ u = z := by rw [hudef, hψΔ, hzdef, siegDiag_eq_longBlock]
  set g : G := ψ (upperUnit 1, 1) with hgdef
  have hgg : g * g = 1 := by
    rw [hgdef, ← map_mul, Prod.mk_mul_mk, mul_one, ← LinearPilot.upperUnit_add,
      CharTwo.add_self_eq_zero, LinearPilot.upperUnit_zero]
    exact map_one ψ
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hg : g⁻¹ * t * g = t * z := by
    have htg : t * g * t⁻¹ = ψ (1, upperUnit 1) := hψt _
    have hzt : z * t = t * z := mem_centralizer_iff.1 htC z (e.symm _).2
    calc g⁻¹ * t * g = g * (t * g * t⁻¹) * t := by rw [hginv]; group
      _ = z * t := by
          rw [htg, hgdef, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ← hz]
      _ = t * z := hzt
  have hgz : g * z = z * g := by
    rw [hgdef, ← hz, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one]
  set e₁ := swapChart e with he₁
  have hz₁ : ((e₁.symm (siegDiag K 1 1) : L) : G) = z := by
    rw [he₁, swapChart_symm_siegDiag]
  set φ' : StatedSp 3 K →* G :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp e₁.symm.toMonoidHom) with hφ'def
  have hφ' : Function.Injective φ' :=
    (MulAut.conj g⁻¹).injective.comp (L.subtype_injective.comp e₁.symm.injective)
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    rfl
  have hφ'z : φ' (siegDiag K 1 1) = ((e₁.symm (siegDiag K 1 1) : L) : G) := by
    rw [hz₁]
    change g⁻¹ * ((e₁.symm (siegDiag K 1 1) : L) : G) * g⁻¹⁻¹ = z
    rw [hz₁, ((show Commute g z from hgz).inv_left).eq, mul_inv_cancel_right]
  obtain ⟨θ⟩ := LinearPilot.nonempty_mulEquiv_twistedDiagSL2 (K := K)
  set j : SL(2, K) →* G := ψ.comp ((twistedDiagSL2 K).subtype.comp θ.toMonoidHom) with hjdef
  have hj : ∀ s, j s = ψ (θ s : twistedDiagSL2 K) := fun s => rfl
  have hjmem : ∀ p ∈ twistedDiagSL2 K, ψ p ∈ j.range := fun p hp =>
    ⟨θ.symm ⟨p, hp⟩, by rw [hj, MulEquiv.apply_symm_apply]⟩
  have hS : (twistedDiagSL2 K).map ψ = j.range := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hjmem p hp
    · rintro ⟨s, rfl⟩
      exact ⟨_, (θ s).2, rfl⟩
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hK
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hfixed : ∀ p ∈ twistedDiagSL2 K, (t * z) * ψ p * (t * z)⁻¹ = ψ p := by
    intro p hp
    rw [← hz]
    calc t * ψ u * ψ p * (t * ψ u)⁻¹ = t * ψ (u * p * u⁻¹) * t⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = ψ (u * p * u⁻¹).swap := hψt _
      _ = ψ p := by rw [hudef, LinearPilot.twistedDiagSL2_fixed hp]
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff, hg]
    have h' := hfixed _ (θ s).2
    rw [mul_inv_eq_iff_eq_mul] at h'
    exact h'.symm
  have hSY : j.range ≤ centralizer (modelToG e₁ (threeTorus K) : Set G) := by
    have h1 : j.range ≤ ψ.range := by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    rw [hM] at h1
    exact h1.trans ((centralizerPerfectCore_le_centralizer _).trans
      (centralizer_le ((modelToG_swapChart_threeTorus_le e).trans inf_le_right)))
  have hzS : z ∈ j.range := hz ▸ hjmem u LinearPilot.upperUnit_one_pair_mem_twistedDiagSL2
  set B := modelToG e (simpleRootSL2 K (0 : Fin 3)) with hBdef
  have hBperf : ⁅B, B⁆ = B := by
    rw [hBdef, UnitaryPilot.modelToG_def, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_simpleRootSL2_eq_of_four_le hK 0]
  have hBL : B ≤ L := map_subtype_le _
  have hBA : B ≤ centralizer (modelToG e (longRootSp2 K 3 2) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_zero_le_complSp_two.trans (complSp_le_centralizer_longRootSp2 2))
  have hzA : z ∈ modelToG e (longRootSp2 K 3 2) :=
    UnitaryPilot.symm_mem_modelToG e (siegDiag_mem_longRootSp2 2 1)
  have hBz : B ≤ centralizer ({z} : Set G) :=
    hBA.trans (centralizer_le (Set.singleton_subset_iff.2 hzA))
  have hBY : B ≤ centralizer (modelToG e₁ (threeTorus K) : Set G) :=
    (UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_le_centralizer_leviTorusSp (Finset.mem_singleton_self 0))).trans
      (centralizer_le ((modelToG_swapChart_threeTorus_le e).trans inf_le_left))
  have hcore := le_centralizer_of_conj_eq_mul_three hset.standardSetting hOut hK e₁ htC ht
    (by rw [hz₁]; exact hg) hφ' hφ'r hφ'z (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt hSY (by rw [hz₁]; exact hzS) hBperf
    hBL (by rw [hz₁]; exact hBz) hBY
  rw [le_centralizer_iff, ← hM, MonoidHom.range_eq_map,
    ← LinearPilot.diag_sup_twistedDiag_eq_top hK, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    change ψ (A, A) ∈ _
    rw [hψΔ A]
    exact (le_centralizer_iff.1 hBA) (UnitaryPilot.symm_mem_modelToG e ⟨A, rfl⟩)
  · rw [hS]
    exact hcore

omit [Finite G] [Finite K] in
theorem pieceCore_zero_le_centralizer_pieceCore_two_of_le_swap [Finite G] [Finite K]
    (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G} (P₂ : SwapNeighbourParam e t 2)
    (hB : modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G)) :
    pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  have hkj : (2 : Fin 3) ≠ 0 := by decide
  have hk1 : (0 : Fin 3).val + 1 < 3 → (2 : Fin 3).val ≠ (0 : Fin 3).val + 1 := fun _ => by decide
  set ψ' := P₂.rootHom hkj hk1 with hψ'def
  set C := centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) with hC
  have htop : C.comap ψ' = ⊤ := by
    refine LinearPilot.eq_top_of_diag_mem_of_conj_mem hK ?_ ?_
    · intro s
      change ψ' (s, s) ∈ C
      rw [hψ'def, P₂.rootHom_diag]
      exact hB (UnitaryPilot.symm_mem_modelToG e ⟨s, rfl⟩)
    · intro α p hp
      change ψ' ((diagUnit α, 1) * p * (diagUnit α, 1)⁻¹) ∈ C
      rw [map_mul, map_mul, map_inv]
      have hy : ψ' (diagUnit α, 1) ∈
          centralizer (modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Set G) := by
        rw [mem_centralizer_iff]
        intro d hd
        obtain ⟨x', hx', rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hd
        obtain ⟨s, -, rfl⟩ := hx'
        exact (P₂.commute_rootHom_diagUnit hkj hk1 α s).eq.symm
      exact CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer
        (normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ hy)) hp
  rw [← P₂.range_rootHom hkj hk1 hK, MonoidHom.range_eq_map, ← htop]
  exact map_comap_le _ _

theorem commute_pieceCore_zero_two_swap_three (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {k : Fin 3} (hk : k ≠ 2) (P : SwapNeighbourParam e t k) (P₂ : SwapNeighbourParam e t 2) :
    ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)),
      Commute a b := by
  have h := pieceCore_zero_le_centralizer_pieceCore_two_of_le_swap hK e P₂
    (modelToG_simpleRootSL2_zero_le_centralizer_pieceCore_two_swap hset hK e htC ht hk P)
  intro a ha b hb
  exact (mem_centralizer_iff.1 (h ha) b hb).symm

end Orth

end CFSG.SeitzReduction.SymplecticPilot
