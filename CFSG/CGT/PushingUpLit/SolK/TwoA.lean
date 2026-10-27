module

public import CFSG.CGT.PushingUpLit.SolK.SwapVec
public import CFSG.CGT.PushingUpLit.SolK.FourA
public import CFSG.CGT.PushingUpLit.SolK.ThetaKer

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem fix_of_two {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) {U : Subgroup G} (hUM : U ≤ M)
    (hUC : U ≤ CMOf M (w * r)) (hU2 : IsPGroup 2 U)
    (hUn : ∀ k ∈ CMOf M (w * r), ∀ u ∈ U, k * u * k⁻¹ ∈ U) :
    ∀ σ ∈ (U.subgroupOf M).map S.θ, ∀ y, y ∉ vsupp (S.D.β ⟨w, hw⟩) → σ y = y := by
  have hn : 2 ≤ n := S.hyp.two_le
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

theorem eq_one_or_swap_of_two {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) {i j : Fin (2 * n + 1)} (hij : i ≠ j)
    (hI : vsupp (S.D.β ⟨w, hw⟩) = {i, j}) {U : Subgroup G} (hUM : U ≤ M)
    (hUC : U ≤ CMOf M (w * r)) (hU2 : IsPGroup 2 U)
    (hUn : ∀ k ∈ CMOf M (w * r), ∀ u ∈ U, k * u * k⁻¹ ∈ U) {σ : Perm (Fin (2 * n + 1))}
    (hσ : σ ∈ (U.subgroupOf M).map S.θ) : σ = 1 ∨ σ = swap i j := by
  refine eq_one_or_swap hij ?_ (fun x hxi hxj => S.fix_of_two hw hr hcard hUM hUC hU2 hUn σ hσ x
    (by rw [hI]; simp [hxi, hxj]))
  have := S.theta_le_setStab hw hr hUC hσ
  rwa [hI] at this

theorem not_TOf_le_Q (hT : TightData S) {x : G} (hxQ : x ∈ pCoreOf 2 M) (hx1 : x ≠ 1)
    (hKM : ¬ CGOf x ≤ M) : ¬ TOf M x ≤ pCoreOf 2 M := by
  intro h
  apply hKM
  have hB : Subgroup.zpowers x ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have h2 := (S.centralizer_le_M S.hyp.charTwo hT.abelian (Subgroup.zpowers_le.2 hxQ) hB h).2
  exact (Subgroup.centralizer_le_normalizer _).trans h2

theorem le_of_swap {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) {i j : Fin (2 * n + 1)} (hij : i ≠ j)
    (hI : vsupp (S.D.β ⟨w, hw⟩) = {i, j}) (hR : RSmall S) {U : Subgroup G}
    (hQU : pCoreOf 2 M ≤ U) {u : G} (huU : u ∈ U) (huT : u ∈ TOf M (w * r))
    (hu : u ∉ pCoreOf 2 M) : TOf M (w * r) ≤ U := by
  intro t ht
  have htM : t ∈ M := TOf_le_M M _ ht
  have huM : u ∈ M := TOf_le_M M _ huT
  have hcases : ∀ s : G, ∀ hs : s ∈ TOf M (w * r),
      S.θ ⟨s, TOf_le_M M _ hs⟩ = 1 ∨ S.θ ⟨s, TOf_le_M M _ hs⟩ = swap i j := fun s hs =>
    S.eq_one_or_swap_of_two hw hr hcard hij hI (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u' hu' => normalized_TOf M (w * r) hk hu')
      (Subgroup.mem_map.2 ⟨⟨s, TOf_le_M M _ hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩)
  have hθu : S.θ ⟨u, huM⟩ = swap i j := by
    rcases hcases u huT with h | h
    · exact absurd (S.mem_Q_of_theta_eq_one hR huM h) hu
    · exact h
  rcases hcases t ht with h | h
  · exact hQU (S.mem_Q_of_theta_eq_one hR htM h)
  · have hM' : t * u⁻¹ ∈ M := M.mul_mem htM (M.inv_mem huM)
    have hdiv : t * u⁻¹ ∈ pCoreOf 2 M := by
      refine S.mem_Q_of_theta_eq_one hR hM' ?_
      have : (⟨t * u⁻¹, hM'⟩ : ↥M) = ⟨t, htM⟩ * ⟨u, huM⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, h, hθu, mul_inv_cancel]
    have e : t = (t * u⁻¹) * u := by group
    rw [e]
    exact U.mul_mem (hQU hdiv) huU

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
