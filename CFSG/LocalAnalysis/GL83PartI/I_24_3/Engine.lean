module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Gen
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Reduce

public section

namespace GL83.I243

open CFSG CFSG.Open CFSG.PreuniquenessRankFour.Helpers Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem eq_top_of_sup_center_eq_top {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    {N : Subgroup Q} (h : N ⊔ Subgroup.center Q = ⊤) : N = ⊤ := by
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ N ⊔ Subgroup.center Q := h ▸ Subgroup.mem_top g
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hcc := Subgroup.mem_center_iff.mp hc
    have : a * c * n * (a * c)⁻¹ = a * n * a⁻¹ := by
      rw [mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc c n, ← hcc n]
      group
    rw [this]
    exact N.mul_mem (N.mul_mem ha hn) (N.inv_mem ha)
  have hder : commutator Q ≤ N :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top h inferInstance
  rw [hperf] at hder
  exact top_unique hder

theorem le_core_of_closure
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup X} {z : X}
    (hperf : commutator K = ⊤) (hBel : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hzB : z ∈ B) (hzK : z ∈ K) (hzc : z ∈ Subgroup.centralizer (K : Set X)) (hzp : orderOf z = p)
    (hΩ : ∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ p = 1 → c ∈ Subgroup.zpowers z)
    (hgen : Subgroup.closure {k : ↥K | ∃ f ∈ B, f ∉ Subgroup.zpowers z ∧
        f * (k : X) * f⁻¹ * (k : X)⁻¹ ∈ Subgroup.centralizer (K : Set X)} = ⊤) :
    K ≤ GLBCore p 2 B := by
  set Γ := GLBCore p 2 B with hΓ
  set N : Subgroup K := (K ⊓ Γ).subgroupOf K with hN
  have hS : {k : ↥K | ∃ f ∈ B, f ∉ Subgroup.zpowers z ∧
        f * (k : X) * f⁻¹ * (k : X)⁻¹ ∈ Subgroup.centralizer (K : Set X)} ⊆
      ((N ⊔ Subgroup.center K : Subgroup K) : Set K) := by
    rintro s ⟨f, hfB, hfz, hζ⟩
    have hfp : f ^ p = 1 := hBel.2 f hfB
    have hfzc : f * z = z * f := congrArg Subtype.val (hBel.1.is_comm.comm ⟨f, hfB⟩ ⟨z, hzB⟩)
    obtain ⟨c, hcK, hcc, hsc⟩ := exists_central_mul_mem_normalizer hp hp2 (hBN hfB) hfp hzK hzc
      hzp hfzc hΩ s.2 hζ
    have hc : (⟨c, hcK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (by
        have := Subgroup.mem_centralizer_iff.mp hcc (y : X) y.2
        simpa using this)
    have hQB : Subgroup.zpowers f ⊔ Subgroup.zpowers z ≤ B :=
      sup_le (Subgroup.zpowers_le.mpr hfB) (Subgroup.zpowers_le.mpr hzB)
    have hQrank : 2 ≤ Open.pRank p (Subgroup.zpowers f ⊔ Subgroup.zpowers z) := by
      rw [sup_comm]
      exact two_le_pRank_sup_zpowers hp hzp hfzc.symm hfp hfz
    have hQΓ : Subgroup.normalizer ((Subgroup.zpowers f ⊔ Subgroup.zpowers z : Subgroup X) : Set X)
        ≤ Γ := le_sSup ⟨_, hQB, hQrank, rfl⟩
    have hsc' : s * ⟨c, hcK⟩ ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact ⟨(s * ⟨c, hcK⟩).2, hQΓ hsc⟩
    have hs : s = (s * ⟨c, hcK⟩) * (⟨c, hcK⟩ : K)⁻¹ := by group
    rw [hs]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hsc')
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc))
  have hle : (⊤ : Subgroup K) ≤ N ⊔ Subgroup.center K := by
    rw [← hgen]
    exact Subgroup.closure_le _ |>.mpr hS
  have htop : N ⊔ Subgroup.center K = ⊤ := top_unique hle
  have hNtop : N = ⊤ := eq_top_of_sup_center_eq_top hperf htop
  intro x hx
  have : (⟨x, hx⟩ : K) ∈ N := hNtop ▸ Subgroup.mem_top _
  rw [hN, Subgroup.mem_subgroupOf] at this
  exact this.2

end GL83.I243
