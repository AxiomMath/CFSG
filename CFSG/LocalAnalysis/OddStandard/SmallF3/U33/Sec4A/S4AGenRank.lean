module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G]

@[expose] def RankLE (K : Subgroup G) (r : ℕ) : Prop :=
  ∀ Q : Subgroup G, Q ≤ K → ∃ s : Finset G, s.card ≤ r ∧ closure (s : Set G) = Q

theorem RankLE.of_isCyclic {K : Subgroup G} [IsCyclic K] : RankLE K 1 := by
  intro Q hQ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Q.subgroupOf K))
  refine ⟨{((g : ↥K) : G)}, by simp, ?_⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    rw [hx]
    exact g.2
  · intro q hq
    have hqK : q ∈ K := hQ hq
    have hmem : (⟨⟨q, hqK⟩, hq⟩ : ↥(Q.subgroupOf K)) ∈ zpowers g := hg _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hpow : ((g : ↥K) : G) ^ n = q := by
      have := congrArg (fun x : ↥(Q.subgroupOf K) => ((x : ↥K) : G)) hn
      simpa using this
    rw [← hpow]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n

theorem RankLE.sup {U V : Subgroup G} {a b : ℕ} (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hU : RankLE U a) (hV : RankLE V b) : RankLE (U ⊔ V) (a + b) := by
  classical
  intro Q hQ
  let QV : Subgroup G :=
    { carrier := {v | v ∈ V ∧ ∃ u ∈ U, u * v ∈ Q}
      one_mem' := ⟨V.one_mem, 1, U.one_mem, by simpa using Q.one_mem⟩
      mul_mem' := by
        rintro v₁ v₂ ⟨hv₁, u₁, hu₁, hq₁⟩ ⟨hv₂, u₂, hu₂, hq₂⟩
        refine ⟨V.mul_mem hv₁ hv₂, u₁ * u₂, U.mul_mem hu₁ hu₂, ?_⟩
        have e : u₁ * u₂ * (v₁ * v₂) = (u₁ * v₁) * (u₂ * v₂) := by
          calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by group
            _ = u₁ * (v₁ * u₂) * v₂ := by rw [hcomm u₂ hu₂ v₁ hv₁]
            _ = (u₁ * v₁) * (u₂ * v₂) := by group
        rw [e]
        exact Q.mul_mem hq₁ hq₂
      inv_mem' := by
        rintro v ⟨hv, u, hu, hq⟩
        refine ⟨V.inv_mem hv, u⁻¹, U.inv_mem hu, ?_⟩
        have e : u⁻¹ * v⁻¹ = (u * v)⁻¹ := by
          rw [mul_inv_rev, hcomm u⁻¹ (U.inv_mem hu) v⁻¹ (V.inv_mem hv)]
        rw [e]
        exact Q.inv_mem hq }
  have hQVmem : ∀ v, v ∈ QV ↔ v ∈ V ∧ ∃ u ∈ U, u * v ∈ Q := fun v => Iff.rfl
  have hQVle : QV ≤ V := fun v hv => ((hQVmem v).mp hv).1
  obtain ⟨s₁, hs₁, hs₁c⟩ := hU (Q ⊓ U) inf_le_right
  obtain ⟨s₂, hs₂, hs₂c⟩ := hV QV hQVle
  have hlift : ∀ v ∈ s₂, ∃ u : G, u ∈ U ∧ u * v ∈ Q := fun v hv =>
    (((hQVmem v).mp (hs₂c ▸ Subgroup.subset_closure hv)).2)
  choose! f hfU hfQ using hlift
  refine ⟨s₁ ∪ s₂.image (fun v => f v * v), ?_, ?_⟩
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add hs₁ (Finset.card_image_le.trans hs₂))
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (inf_le_left : Q ⊓ U ≤ Q) (hs₁c ▸ Subgroup.subset_closure hx)
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        exact hfQ v hv
    · intro q hq
      obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp (hQ hq)
      have hvQV : v ∈ QV := (hQVmem v).mpr ⟨hv, u, hu, hq⟩
      have hvcl : v ∈ closure (s₂ : Set G) := hs₂c ▸ hvQV
      have hlift' : ∃ c ∈ closure ((s₂.image (fun v => f v * v) : Finset G) : Set G),
          ∃ u' ∈ U, c = u' * v := by
        refine Subgroup.closure_induction
          (p := fun x _ => ∃ c ∈ closure ((s₂.image (fun v => f v * v) : Finset G) : Set G),
            ∃ u' ∈ U, c = u' * x) ?_ ?_ ?_ ?_ hvcl
        · intro x hx
          refine ⟨f x * x, Subgroup.subset_closure ?_, f x, hfU x hx, rfl⟩
          rw [Finset.mem_coe]
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        · exact ⟨1, Subgroup.one_mem _, 1, U.one_mem, by simp⟩
        · rintro x y hx hy ⟨c₁, hc₁, u₁, hu₁, rfl⟩ ⟨c₂, hc₂, u₂, hu₂, rfl⟩
          have hxV : x ∈ V := hQVle (hs₂c ▸ hx)
          refine ⟨(u₁ * x) * (u₂ * y), Subgroup.mul_mem _ hc₁ hc₂, u₁ * u₂,
            U.mul_mem hu₁ hu₂, ?_⟩
          calc (u₁ * x) * (u₂ * y) = u₁ * (x * u₂) * y := by group
            _ = u₁ * (u₂ * x) * y := by rw [← hcomm u₂ hu₂ x hxV]
            _ = u₁ * u₂ * (x * y) := by group
        · rintro x hx ⟨c, hc, u', hu', rfl⟩
          have hxV : x ∈ V := hQVle (hs₂c ▸ hx)
          refine ⟨(u' * x)⁻¹, Subgroup.inv_mem _ hc, u'⁻¹, U.inv_mem hu', ?_⟩
          rw [mul_inv_rev, hcomm u'⁻¹ (U.inv_mem hu') x⁻¹ (V.inv_mem hxV)]
      obtain ⟨c, hc, u', hu', hcv⟩ := hlift'
      have hcQ : c ∈ Q := by
        refine (Subgroup.closure_le Q).mpr ?_ hc
        intro x hx
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
        exact hfQ v' hv'
      have hqc : u * v * c⁻¹ ∈ Q ⊓ U := by
        refine ⟨Q.mul_mem hq (Q.inv_mem hcQ), ?_⟩
        have e : u * v * c⁻¹ = u * u'⁻¹ := by
          rw [hcv, mul_inv_rev]
          group
        rw [e]
        exact U.mul_mem hu (U.inv_mem hu')
      have hqcl : u * v * c⁻¹ ∈ closure (↑(s₁ ∪ s₂.image (fun v => f v * v)) : Set G) := by
        have : u * v * c⁻¹ ∈ closure (s₁ : Set G) := hs₁c ▸ hqc
        exact Subgroup.closure_mono (by simp) this
      have hccl : c ∈ closure (↑(s₁ ∪ s₂.image (fun v => f v * v)) : Set G) :=
        Subgroup.closure_mono (by simp) hc
      have e : u * v = (u * v * c⁻¹) * c := by group
      rw [e]
      exact Subgroup.mul_mem _ hqcl hccl

theorem RankLE.of_relIndex_two [Finite G] {N S : Subgroup G} {a : ℕ} (hNS : N ≤ S)
    (hi : N.relIndex S = 2) (hN : RankLE N a) : RankLE S (a + 1) := by
  classical
  intro Q hQ
  obtain ⟨s, hs, hsc⟩ := hN (Q ⊓ N) inf_le_right
  by_cases hQN : Q ≤ N
  · refine ⟨s, hs.trans (Nat.le_succ a), ?_⟩
    rw [hsc]
    exact inf_eq_left.mpr hQN
  · obtain ⟨q, hqQ, hqN⟩ := SetLike.not_le_iff_exists.mp hQN
    refine ⟨insert q s, (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hs), ?_⟩
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hx
      · exact hqQ
      · exact (inf_le_left : Q ⊓ N ≤ Q) (hsc ▸ Subgroup.subset_closure (Finset.mem_coe.mpr hx))
    · intro x hxQ
      have hmono : closure (s : Set G) ≤ closure (↑(insert q s) : Set G) :=
        Subgroup.closure_mono (by simp)
      by_cases hxN : x ∈ N
      · exact hmono (hsc ▸ (⟨hxQ, hxN⟩ : x ∈ Q ⊓ N))
      · rcases mem_or_mem_or_mul_mem_of_relIndex_two hNS hi (hQ hxQ) (hQ hqQ) with h1 | h2 | h3
        · exact absurd h1 hxN
        · exact absurd h2 hqN
        · have hxq : x * q ∈ Q ⊓ N := ⟨Q.mul_mem hxQ hqQ, h3⟩
          have h4 : x * q ∈ closure (↑(insert q s) : Set G) := hmono (hsc ▸ hxq)
          have h5 : q ∈ closure (↑(insert q s) : Set G) :=
            Subgroup.subset_closure (by simp)
          have e : x = (x * q) * q⁻¹ := by group
          rw [e]
          exact Subgroup.mul_mem _ h4 (Subgroup.inv_mem _ h5)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
