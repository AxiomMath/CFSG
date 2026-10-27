module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace GL83.I243

open CFSG.Open CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.CentralCover

theorem congr_centerQuotientHom_apply_mk {K L : Type*} [Group K] [Group L]
    (e : K ⧸ Subgroup.center K ≃* L) (ε : MulAut K) (k : K) :
    ((MulAut.congr e).toMonoidHom.comp (centerQuotientHom K)) ε (e (k : K ⧸ Subgroup.center K)) =
      e ((ε k : K) : K ⧸ Subgroup.center K) := by
  simp [MulAut.congr_apply, centerQuotientHom_apply_mk]

theorem closure_fix_lift {K L : Type} [Group K] [Group L] {p : ℕ}
    (hperf : Group.IsPerfect K) (e : K ⧸ Subgroup.center K ≃* L)
    (Q : Subgroup (MulAut L) → Prop)
    (hS : ∀ E' : Subgroup (MulAut L), IsElemAbelian p E' → Nat.card E' = p ^ 2 → Q E' →
      Subgroup.closure {l : L | ∃ a ∈ E', a ≠ 1 ∧ a l = l} = ⊤) :
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
      Q (E.map ((MulAut.congr e).toMonoidHom.comp
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K))) →
      Subgroup.closure {k : K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center K} = ⊤ := by
  intro E hE hEcard hQ
  let ρ : MulAut K →* MulAut L :=
    (MulAut.congr e).toMonoidHom.comp (centerQuotientHom K)
  have hρ : Function.Injective ρ :=
    (MulAut.congr e).injective.comp (centerQuotientHom_injective K)
  let q : K →* L := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : ∀ k, q k = 1 ↔ k ∈ Subgroup.center K := by
    intro k
    simp [q]
  have hρq : ∀ (ε : MulAut K) (k : K), ρ ε (q k) = q (ε k) := fun ε k =>
    congr_centerQuotientHom_apply_mk e ε k
  set S : Set K := {k : K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center K} with hSdef
  have hcl := hS (E.map ρ) (hE.map ρ) (by rw [Subgroup.card_map_of_injective hρ, hEcard]) hQ
  have hsub : {l : L | ∃ a ∈ E.map ρ, a ≠ 1 ∧ a l = l} ⊆ q '' S := by
    rintro l ⟨a, ha, ha1, hal⟩
    obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨k, rfl⟩ := hq l
    refine ⟨k, ⟨ε, hε, ?_, ?_⟩, rfl⟩
    · rintro rfl
      exact ha1 (map_one ρ)
    · rw [← hqker, map_mul, map_inv, ← hρq, hal, mul_inv_cancel]
  have hmap : (Subgroup.closure S).map q = ⊤ := by
    rw [MonoidHom.map_closure, eq_top_iff, ← hcl]
    exact Subgroup.closure_mono hsub
  by_cases hE1 : ∃ ε ∈ E, ε ≠ 1
  · obtain ⟨ε₀, hε₀, hε₀1⟩ := hE1
    have hZF : (Subgroup.center K : Set K) ⊆ S := fun z hz =>
      ⟨ε₀, hε₀, hε₀1,
        Subgroup.mul_mem _ (MulEquivClass.apply_mem_center ε₀ hz) (Subgroup.inv_mem _ hz)⟩
    rw [eq_top_iff]
    intro k _
    obtain ⟨c, hc, hck⟩ : ∃ c ∈ Subgroup.closure S, q c = q k := by
      have : q k ∈ (Subgroup.closure S).map q := hmap ▸ Subgroup.mem_top _
      exact Subgroup.mem_map.mp this
    have hcz : c⁻¹ * k ∈ Subgroup.center K := by
      rw [← hqker, map_mul, map_inv, hck, inv_mul_cancel]
    have hk : k = c * (c⁻¹ * k) := by group
    rw [hk]
    exact Subgroup.mul_mem _ hc (Subgroup.subset_closure (hZF hcz))
  · push Not at hE1
    have hempty : S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun k hk => ?_
      obtain ⟨ε, hε, hε1, -⟩ := hk
      exact hε1 (hE1 ε hε)
    rw [hempty, Subgroup.closure_empty, Subgroup.map_bot] at hmap
    rw [hempty, Subgroup.closure_empty]
    have hL1 : ∀ l : L, l = 1 := fun l => by
      have hl : l ∈ (⊥ : Subgroup L) := by
        rw [hmap]
        exact Subgroup.mem_top l
      exact Subgroup.mem_bot.mp hl
    have hKc : ∀ k : K, k ∈ Subgroup.center K := fun k => (hqker k).mp (hL1 _)
    let f : K →* Subgroup.center K :=
      { toFun := fun k => ⟨k, hKc k⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : f = 1 := hom_eq_one_of_commutative f
    rw [eq_top_iff]
    intro k _
    have hk1 : k = 1 := congrArg Subtype.val (DFunLike.congr_fun hf k)
    rw [hk1]
    exact Subgroup.one_mem _

theorem not_le_range_conj_map {K L : Type} [Group K] [Group L] (hperf : Group.IsPerfect K)
    (e : K ⧸ Subgroup.center K ≃* L) {E : Subgroup (MulAut K)}
    (hE : ¬ E ≤ (MulAut.conj : K →* MulAut K).range) :
    ¬ E.map ((MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)) ≤
      (MulAut.conj : L →* MulAut L).range := by
  intro hle
  apply hE
  let ρ : MulAut K →* MulAut L :=
    (MulAut.congr e).toMonoidHom.comp (centerQuotientHom K)
  have hρ : Function.Injective ρ :=
    (MulAut.congr e).injective.comp (centerQuotientHom_injective K)
  let q : K →* L := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρq : ∀ (ε : MulAut K) (k : K), ρ ε (q k) = q (ε k) := fun ε k =>
    congr_centerQuotientHom_apply_mk e ε k
  intro ε hεE
  obtain ⟨l, hl⟩ := hle (Subgroup.mem_map_of_mem ρ hεE)
  obtain ⟨k, rfl⟩ := hq l
  refine ⟨k, hρ ?_⟩
  rw [← hl]
  ext x
  obtain ⟨m, rfl⟩ := hq x
  rw [hρq, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

end GL83.I243
