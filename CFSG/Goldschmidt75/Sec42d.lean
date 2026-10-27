module

public import CFSG.Goldschmidt75.Sec42K
public import CFSG.Goldschmidt75.Sec42Bender

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.kSub_le_of_centralizers
    (h : MinCE G T S₁ S₂) {M : Subgroup G}
    (hM : ∀ s ∈ S₁, s ≠ 1 → s ^ 2 = 1 → kSub S₁ S₂ ⊓ centralizer ({s} : Set G) ≤ M) :
    kSub S₁ S₂ ≤ M := by
  set K := kSub S₁ S₂ with hK
  have hS₁K : S₁ ≤ K := le_kSub (h.comm.trans (centralizer_le_normalizer _))
  obtain ⟨TK, hATK, -, hAcl, -⟩ :=
    exists_sylow_subgroupOf T h.le₁ h.le₁ h.sc₁ h.sc₁ (sup_le hS₁K hS₁K)
  have hA1 : S₁.subgroupOf K ≠ ⊥ := by
    intro h0
    apply h.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hS₁K hx⟩ : K) ∈ S₁.subgroupOf K := hx
    rw [h0, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  have hgen : closure (invClass (S₁.subgroupOf K)) = ⊤ := by
    have hle : closure {y | ∃ k ∈ K, ∃ s ∈ S₁, s ^ 2 = 1 ∧ y = k * s * k⁻¹} ≤
        (closure (invClass (S₁.subgroupOf K))).map K.subtype := by
      refine (closure_le _).mpr ?_
      rintro _ ⟨k, hk, s, hs, hs2, rfl⟩
      by_cases hs1 : s = 1
      · rw [hs1, mul_one, mul_inv_cancel]
        exact one_mem _
      · refine ⟨⟨k, hk⟩ * ⟨s, hS₁K hs⟩ * ⟨k, hk⟩⁻¹, subset_closure ⟨⟨k, hk⟩, ⟨s, hS₁K hs⟩, hs,
          fun e => hs1 (congrArg Subtype.val e), Subtype.ext hs2, rfl⟩, rfl⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle (h.kSub_le_closure x.2)
    rwa [show x = y from Subtype.ext hyx.symm]
  rcases centralizers_eq_top_or_stronglyEmbedded TK hATK hAcl hA1 hgen with h0 | ⟨E, hE⟩
  · intro x hx
    have hle : (⨆ s : {s : K // s ∈ S₁.subgroupOf K ∧ s ≠ 1 ∧ s ^ 2 = 1},
        centralizer ({s.1} : Set K)) ≤ M.subgroupOf K := by
      refine iSup_le fun s c hc => mem_subgroupOf.mpr ?_
      refine hM (s.1 : G) s.2.1 (fun e => s.2.2.1 (Subtype.ext e))
        (congrArg Subtype.val s.2.2.2) (mem_inf.mpr ⟨c.2, ?_⟩)
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
    exact mem_subgroupOf.mp (hle (by rw [h0]; exact mem_top (⟨x, hx⟩ : K)))
  · exfalso
    apply h.omega1_not_comm
    refine isMulCommutative_closure fun t ht t' ht' _ => ?_
    have h1 := commute_of_stronglyEmbedded hE TK (s := ⟨t, hS₁K ht.1⟩) (t := ⟨t', hS₁K ht'.1⟩)
      (hATK ht.1) (hATK ht'.1) (Subtype.ext ht.2) (Subtype.ext ht'.2)
    exact congrArg Subtype.val h1

end CFSG.Goldschmidt75
