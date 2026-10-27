module

public import CFSG.CGT.PushingUpLit.SolK.FourTheta
public import CFSG.CGT.PushingUpLit.SolK.Fusion
public import CFSG.CGT.PushingUpLit.SolK.ThetaKer

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

theorem coreAct_eq_of_fix {d : ℕ} {J : Finset (Fin d)} {σ : Perm (Fin d)}
    (hσ : ∀ j ∈ J, σ j = j) {v : ↥(coreMod d)} (hv : vsupp v ⊆ J) : coreAct d σ v = v := by
  refine (coreAct_eq_iff σ v).2 fun x => ?_
  constructor
  · intro hx
    have h1 : σ (σ x) = σ x := hσ _ (hv hx)
    have h2 : σ x = x := σ.injective h1
    rwa [h2] at hx
  · intro hx
    rw [hσ x (hv hx)]
    exact hx

theorem setStab_compl_of_fix {d : ℕ} {J : Finset (Fin d)} {σ : Perm (Fin d)}
    (hσ : ∀ j ∈ J, σ j = j) : σ ∈ setStab Jᶜ := by
  intro x
  rw [Finset.mem_compl, Finset.mem_compl]
  constructor
  · intro hx hxJ
    exact hx (by rw [hσ x hxJ]; exact hxJ)
  · intro hx hxJ
    have h1 : σ (σ x) = σ x := hσ _ hxJ
    exact hx (by rwa [σ.injective h1] at hxJ)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

theorem vsupp_mul_subset {d : ℕ} (u v : ↥(coreMod d)) : vsupp (u * v) ⊆ vsupp u ∪ vsupp v := by
  intro i hi
  rw [mem_vsupp, vcoord_mul] at hi
  rw [Finset.mem_union, mem_vsupp, mem_vsupp]
  by_contra hcon
  push Not at hcon
  have h1 : vcoord u i = 0 := by
    generalize vcoord u i = a at hcon hi ⊢
    generalize vcoord v i = b at hcon hi
    revert a b
    decide
  have h2 : vcoord v i = 0 := by
    generalize vcoord u i = a at hcon hi h1 ⊢
    generalize vcoord v i = b at hcon hi ⊢
    revert a b
    decide
  rw [h1, h2] at hi
  exact zero_ne_one hi

@[expose] def SolCfg.DeltaJ (J : Finset (Fin (2 * n + 1))) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ S.D.W, vsupp (S.D.β ⟨g, hg⟩) ⊆ J}
  mul_mem' := by
    rintro a b ⟨ha, haJ⟩ ⟨hb, hbJ⟩
    refine ⟨S.D.W.mul_mem ha hb, ?_⟩
    have : S.D.β ⟨a * b, S.D.W.mul_mem ha hb⟩ = S.D.β ⟨a, ha⟩ * S.D.β ⟨b, hb⟩ := by
      rw [← map_mul]
      rfl
    rw [this]
    exact (vsupp_mul_subset _ _).trans (Finset.union_subset haJ hbJ)
  one_mem' := by
    refine ⟨S.D.W.one_mem, ?_⟩
    have : S.D.β ⟨1, S.D.W.one_mem⟩ = 1 := by
      have h : (⟨1, S.D.W.one_mem⟩ : ↥S.D.W) = 1 := rfl
      rw [h, map_one]
    rw [this]
    intro i hi
    simp [mem_vsupp, vcoord_one] at hi
  inv_mem' := by
    rintro a ⟨ha, haJ⟩
    refine ⟨S.D.W.inv_mem ha, ?_⟩
    have : S.D.β ⟨a⁻¹, S.D.W.inv_mem ha⟩ = (S.D.β ⟨a, ha⟩)⁻¹ := map_inv S.D.β ⟨a, ha⟩
    rw [this]
    intro i hi
    rw [mem_vsupp, vcoord_inv] at hi
    exact haJ (mem_vsupp.2 hi)

namespace SolCfg

include S

theorem DeltaJ_le_W (J : Finset (Fin (2 * n + 1))) : S.DeltaJ J ≤ S.D.W := fun _ hg => hg.1

theorem DeltaJ_le_Q (J : Finset (Fin (2 * n + 1))) : S.DeltaJ J ≤ pCoreOf 2 M :=
  (S.DeltaJ_le_W J).trans S.W_le_Q

theorem DeltaJ_mono {J J' : Finset (Fin (2 * n + 1))} (h : J ⊆ J') : S.DeltaJ J ≤ S.DeltaJ J' :=
  fun _ hg => ⟨hg.1, hg.2.trans h⟩

theorem pairVec_lift_mem {J : Finset (Fin (2 * n + 1))} {a b : Fin (2 * n + 1)} (ha : a ∈ J)
    (hb : b ∈ J) : ((S.D.β.symm (pairVec a b) : ↥S.D.W) : G) ∈ S.DeltaJ J := by
  refine ⟨(S.D.β.symm (pairVec a b)).2, ?_⟩
  have : S.D.β ⟨((S.D.β.symm (pairVec a b) : ↥S.D.W) : G), (S.D.β.symm (pairVec a b)).2⟩ =
      pairVec a b := S.D.β.apply_symm_apply _
  rw [this]
  intro i hi
  rw [mem_vsupp, vcoord_pairVec] at hi
  by_cases hia : i = a
  · rw [hia]; exact ha
  · by_cases hib : i = b
    · rw [hib]; exact hb
    · simp [hia, hib] at hi

theorem DeltaJ_ne_bot {J : Finset (Fin (2 * n + 1))} (hJ : 2 ≤ J.card) : S.DeltaJ J ≠ ⊥ := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
  intro hbot
  have hmem := S.pairVec_lift_mem ha hb
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 : S.D.β.symm (pairVec a b) = 1 := Subtype.ext hmem
  have h2 : pairVec a b = 1 := by
    have := congrArg S.D.β h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have h3 := congrArg (fun v => vcoord v a) h2
  simp [vcoord_pairVec, vcoord_one, hab] at h3

theorem centralizes_DeltaJ_of_fix {J : Finset (Fin (2 * n + 1))} {m : ↥M}
    (hm : ∀ j ∈ J, S.θ m j = j) : ∀ g ∈ S.DeltaJ J, (m : G) * g * (m : G)⁻¹ = g := by
  rintro g ⟨hg, hgJ⟩
  have hW : (m : G) * g * (m : G)⁻¹ ∈ S.D.W := S.W_normalized m.2 hg
  have h1 := S.θ_spec m ⟨g, hg⟩ hW
  rw [coreAct_eq_of_fix hm hgJ] at h1
  exact congrArg Subtype.val (S.D.β.injective h1)

theorem fix_of_centralizes_DeltaJ {J : Finset (Fin (2 * n + 1))} (hJ : 3 ≤ J.card) {m : ↥M}
    (hc : ∀ g ∈ S.DeltaJ J, (m : G) * g * (m : G)⁻¹ = g) : ∀ j ∈ J, S.θ m j = j := by
  refine fix_of_fix_pairs hJ ?_
  intro a ha b hb
  have hmem := S.pairVec_lift_mem ha hb
  have hW : (m : G) * ((S.D.β.symm (pairVec a b) : ↥S.D.W) : G) * (m : G)⁻¹ ∈ S.D.W :=
    S.W_normalized m.2 (S.D.β.symm (pairVec a b)).2
  have h1 := S.θ_spec m (S.D.β.symm (pairVec a b)) hW
  have h2 : (⟨(m : G) * ((S.D.β.symm (pairVec a b) : ↥S.D.W) : G) * (m : G)⁻¹, hW⟩ :
      ↥S.D.W) = S.D.β.symm (pairVec a b) := Subtype.ext (hc _ hmem)
  rw [h2, MulEquiv.apply_symm_apply] at h1
  exact h1.symm

theorem exists_lift_J {τ : Perm (Fin (2 * n + 1))} (hτ : τ ∈ alternatingGroup (Fin (2 * n + 1))) :
    ∃ c : G, ∃ hcM : c ∈ M, S.θ ⟨c, hcM⟩ = τ := by
  obtain ⟨c, hcτ⟩ := S.D.ρ_surj τ hτ
  have hcM : (c : G) ∈ M := S.hyp.le c.2
  exact ⟨c, hcM, by rw [S.θ_X c]; exact hcτ⟩

theorem pCoreOf_centralizer_DeltaJ_le (hR : RSmall S) {J : Finset (Fin (2 * n + 1))}
    (hJ : 3 ≤ J.card) (hJc : Jᶜ.card ≤ 1 ∨ Jᶜ.card = 3 ∨ 5 ≤ Jᶜ.card) :
    pCoreOf 2 (M ⊓ Subgroup.centralizer ((S.DeltaJ J : Subgroup G) : Set G)) ≤
      pCoreOf 2 M := by
  classical
  set C : Subgroup G := M ⊓ Subgroup.centralizer ((S.DeltaJ J : Subgroup G) : Set G) with hC
  set TB : Subgroup G := pCoreOf 2 C with hTB
  have hTBM : TB ≤ M := (pCoreOf_le_self C).trans inf_le_left
  set N : Subgroup (Perm (Fin (2 * n + 1))) := (TB.subgroupOf M).map S.θ with hN
  have hN2 : IsPGroup 2 N := S.theta_isPGroup hTBM (isPGroup_pCoreOf' C)
  have hcentral : ∀ c : G, c ∈ C → ∀ g ∈ S.DeltaJ J, c * g * c⁻¹ = g := by
    intro c hc g hg
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 g hg
    calc c * g * c⁻¹ = (g * c) * c⁻¹ := by rw [← h1]
      _ = g := by group
  have hfixJ : ∀ σ ∈ N, ∀ j ∈ J, σ j = j := by
    intro σ hσ j hj
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hmC : (m : G) ∈ C := pCoreOf_le_self C (Subgroup.mem_subgroupOf.1 hm)
    exact S.fix_of_centralizes_DeltaJ hJ (hcentral _ hmC) j hj
  have hNJ : N ≤ setStab Jᶜ := fun σ hσ => setStab_compl_of_fix (hfixJ σ hσ)
  have hnorm : ∀ τ ∈ altOn Jᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N := by
    intro τ hτ σ hσ
    have hτalt : τ ∈ alternatingGroup (Fin (2 * n + 1)) :=
      Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2
    have hτJ : ∀ j ∈ J, τ j = j := fun j hj => (mem_altOn.1 hτ).1 j (by simpa using hj)
    obtain ⟨c, hcM, hcτ⟩ := S.exists_lift_J hτalt
    have hcC : c ∈ C := by
      refine Subgroup.mem_inf.2 ⟨hcM, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have := S.centralizes_DeltaJ_of_fix (m := ⟨c, hcM⟩) (by rw [hcτ]; exact hτJ) g hg
      calc g * c = (c * g * c⁻¹) * c := by rw [this]
        _ = c * g := by group
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    have hcm : c * (m : G) * c⁻¹ ∈ TB := pCoreOf_normalized C hcC (Subgroup.mem_subgroupOf.1 hm)
    have hcmM : c * (m : G) * c⁻¹ ∈ M :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcM m.2) (M.inv_mem hcM)
    refine Subgroup.mem_map.2 ⟨⟨c * (m : G) * c⁻¹, hcmM⟩, Subgroup.mem_subgroupOf.2 hcm, ?_⟩
    have : (⟨c * (m : G) * c⁻¹, hcmM⟩ : ↥M) = ⟨c, hcM⟩ * m * ⟨c, hcM⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hcτ]
  have hfixc := block_fixes hN2 hNJ hnorm hJc
  intro t ht
  have htM : t ∈ M := hTBM ht
  refine S.mem_Q_of_theta_eq_one hR htM ?_
  have hmem : S.θ ⟨t, htM⟩ ∈ N :=
    Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  refine Equiv.ext fun x => ?_
  rw [Perm.one_apply]
  by_cases hx : x ∈ J
  · exact hfixJ _ hmem x hx
  · exact hfixc _ hmem x (Finset.mem_compl.2 hx)

theorem centralizer_DeltaJ_le_M (hT : TightData S) (hR : RSmall S)
    {J : Finset (Fin (2 * n + 1))} (hJ : 3 ≤ J.card)
    (hJc : Jᶜ.card ≤ 1 ∨ Jᶜ.card = 3 ∨ 5 ≤ Jᶜ.card) :
    Subgroup.centralizer ((S.DeltaJ J : Subgroup G) : Set G) ≤ M ∧
      Subgroup.normalizer ((S.DeltaJ J : Subgroup G) : Set G) ≤ M := by
  have h := S.centralizer_le_M S.hyp.charTwo hT.abelian (S.DeltaJ_le_Q J)
    (S.DeltaJ_ne_bot (by omega)) (S.pCoreOf_centralizer_DeltaJ_le hR hJ hJc)
  exact ⟨(Subgroup.centralizer_le_normalizer _).trans h.2, h.2⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
