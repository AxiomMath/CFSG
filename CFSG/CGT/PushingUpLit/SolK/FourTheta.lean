module

public import CFSG.CGT.PushingUpLit.SolK.FourPerm
public import CFSG.CGT.PushingUpLit.SolK.ThetaT

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

abbrev CMOf {G : Type} [Group G] (M : Subgroup G) (x : G) : Subgroup G :=
  M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)

theorem eq_of_pairVec_eq {d : ℕ} {x y a b : Fin d} (hxy : x ≠ y) (h : pairVec x y = pairVec a b) :
    x = a ∨ x = b := by
  have h1 := congrArg (fun v => vcoord v x) h
  simp only [vcoord_pairVec] at h1
  by_contra hcon
  push Not at hcon
  simp [hxy, hcon.1, hcon.2] at h1

theorem fix_of_fix_pairs {d : ℕ} {J : Finset (Fin d)} (hJ : 3 ≤ J.card) {σ : Perm (Fin d)}
    (hσ : ∀ a ∈ J, ∀ b ∈ J, coreAct d σ (pairVec a b) = pairVec a b) : ∀ a ∈ J, σ a = a := by
  classical
  intro a ha
  obtain ⟨b, hbJ, hbs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a} : Finset (Fin d))) (t := J) (by simp; omega)
  simp only [Finset.mem_singleton] at hbs
  obtain ⟨c, hcJ, hcs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset (Fin d))) (t := J) (by
      have := Finset.card_le_two (a := a) (b := b)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs
  have h1 := hσ a ha b hbJ
  have h2 := hσ a ha c hcJ
  rw [coreAct_pairVec] at h1 h2
  have hab : σ a ≠ σ b := fun h' => hbs (σ.injective h').symm
  have hac : σ a ≠ σ c := fun h' => hcs.1 (σ.injective h').symm
  rcases eq_of_pairVec_eq hab h1 with h3 | h3
  · exact h3
  · rcases eq_of_pairVec_eq hac h2 with h4 | h4
    · exact h4
    · exact absurd (h3.symm.trans h4) (Ne.symm hcs.2)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem exists_lift {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    {τ : Perm (Fin (2 * n + 1))} (hτ : τ ∈ alternatingGroup (Fin (2 * n + 1)))
    (hτI : τ ∈ setStab (vsupp (S.D.β ⟨w, hw⟩))) :
    ∃ c : G, c ∈ CMOf M (w * r) ∧ ∃ hcM : c ∈ M, S.θ ⟨c, hcM⟩ = τ := by
  obtain ⟨c, hcτ⟩ := S.D.ρ_surj τ hτ
  have hfix : coreAct (2 * n + 1) (S.D.ρ c) (S.D.β ⟨w, hw⟩) = S.D.β ⟨w, hw⟩ := by
    rw [hcτ]
    exact (coreAct_eq_iff _ _).2 hτI
  have hcx := S.comm_of_fix_X hw hr c hfix
  have hcM : (c : G) ∈ M := S.hyp.le c.2
  refine ⟨(c : G), Subgroup.mem_inf.2 ⟨hcM, mem_centralizer_zpowers_iff.2 hcx⟩, hcM, ?_⟩
  rw [S.θ_X c]
  exact hcτ

noncomputable abbrev TN (x : G) : Subgroup (Perm (Fin (2 * n + 1))) :=
  ((TOf M x).subgroupOf M).map S.θ

theorem mem_TN {x : G} {σ : Perm (Fin (2 * n + 1))} :
    σ ∈ S.TN x ↔ ∃ t : ↥M, (t : G) ∈ TOf M x ∧ S.θ t = σ := by
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨t, ht, h⟩ => ⟨t, ht, h⟩, fun ⟨t, ht, h⟩ => ⟨t, ht, h⟩⟩

theorem theta_isPGroup {U : Subgroup G} (hUM : U ≤ M) (hU2 : IsPGroup 2 U) :
    IsPGroup 2 ((U.subgroupOf M).map S.θ) :=
  (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM).symm).map S.θ

theorem theta_le_setStab {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) {U : Subgroup G}
    (hUC : U ≤ CMOf M (w * r)) :
    (U.subgroupOf M).map S.θ ≤ setStab (vsupp (S.D.β ⟨w, hw⟩)) := by
  intro σ hσ
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
  have hmC := hUC (Subgroup.mem_subgroupOf.1 hm)
  have hcomm : (m : G) * (w * r) * (m : G)⁻¹ = w * r :=
    mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hmC).2
  exact (coreAct_eq_iff _ _).1 (S.fix_of_comm hw hr m hcomm)

theorem theta_norm {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) {U : Subgroup G}
    (hUn : ∀ k ∈ CMOf M (w * r), ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    {τ : Perm (Fin (2 * n + 1))} (hτ : τ ∈ alternatingGroup (Fin (2 * n + 1)))
    (hτI : τ ∈ setStab (vsupp (S.D.β ⟨w, hw⟩))) :
    ∀ σ ∈ (U.subgroupOf M).map S.θ, τ * σ * τ⁻¹ ∈ (U.subgroupOf M).map S.θ := by
  intro σ hσ
  obtain ⟨c, hcC, hcM, hcτ⟩ := S.exists_lift hw hr hτ hτI
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
  have hcm : c * (m : G) * c⁻¹ ∈ U := hUn c hcC m (Subgroup.mem_subgroupOf.1 hm)
  have hcmM : c * (m : G) * c⁻¹ ∈ M :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hcM m.2) (M.inv_mem hcM)
  refine Subgroup.mem_map.2 ⟨⟨c * (m : G) * c⁻¹, hcmM⟩, Subgroup.mem_subgroupOf.2 hcm, ?_⟩
  have : (⟨c * (m : G) * c⁻¹, hcmM⟩ : ↥M) = ⟨c, hcM⟩ * m * ⟨c, hcM⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hcτ]

theorem fourGroup_theta_of_fix {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) {U : Subgroup G}
    (hUM : U ≤ M) (hUC : U ≤ CMOf M (w * r)) (hU2 : IsPGroup 2 U)
    (hUn : ∀ k ∈ CMOf M (w * r), ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hfix : ∀ σ ∈ (U.subgroupOf M).map S.θ, ∀ y, y ∉ vsupp (S.D.β ⟨w, hw⟩) → σ y = y) :
    FourGroup (vsupp (S.D.β ⟨w, hw⟩)) ((U.subgroupOf M).map S.θ) :=
  ⟨S.theta_isPGroup hUM hU2, S.theta_le_setStab hw hr hUC, hfix, fun _ hτ =>
    S.theta_norm hw hr hUn (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2)
      (altOn_le_setStab _ hτ)⟩

theorem fourGroup_theta {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4) {U : Subgroup G} (hUM : U ≤ M)
    (hUC : U ≤ CMOf M (w * r)) (hU2 : IsPGroup 2 U)
    (hUn : ∀ k ∈ CMOf M (w * r), ∀ u ∈ U, k * u * k⁻¹ ∈ U) :
    FourGroup (vsupp (S.D.β ⟨w, hw⟩)) ((U.subgroupOf M).map S.θ) := by
  have hn : 2 ≤ n := S.hyp.two_le
  refine S.fourGroup_theta_of_fix hw hr hUM hUC hU2 hUn ?_
  intro σ hσ y hy
  have hNI := S.theta_le_setStab hw hr hUC
  have hNI' : ((U.subgroupOf M).map S.θ) ≤ setStab (vsupp (S.D.β ⟨w, hw⟩))ᶜ := fun σ hσ x => by
    have := mem_setStab.1 (hNI hσ) x
    simp [this]
  have hfixc := block_fixes (S.theta_isPGroup hUM hU2) hNI'
    (fun τ hτ => S.theta_norm hw hr hUn
      (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2)
      (by
        intro x
        have := altOn_le_setStab (vsupp (S.D.β ⟨w, hw⟩))ᶜ hτ x
        rw [Finset.mem_compl, Finset.mem_compl] at this
        exact not_iff_not.1 this))
    (by
      rw [Finset.card_compl, Fintype.card_fin, hcard]
      omega)
  exact hfixc σ hσ y (Finset.mem_compl.2 hy)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
