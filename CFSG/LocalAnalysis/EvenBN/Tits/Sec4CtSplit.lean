module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4FusionTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.exists_compl_zpowers_t
    (hd : d.Hyp) :
    ∃ A₀ : Subgroup G, A₀ ≤ centralizer {d.t} ∧ d.t ∉ A₀ ∧
      ∀ x ∈ centralizer ({d.t} : Set G), x ∈ A₀ ∨ d.t * x ∈ A₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : d.t * d.t = 1 := by rw [← sq]; exact hd.t_two ▸ pow_orderOf_eq_one d.t
  have ht2 : orderOf (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hd.t_two
  have hV : (zpowers (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G))).Normal :=
    ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
      have hg : g * ⟨d.t, d.t_mem_centralizer⟩ = ⟨d.t, d.t_mem_centralizer⟩ * g :=
        Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
      rw [(Commute.zpow_right (hg : Commute g _) k).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) k⟩
  have hVp : IsPGroup 2 (zpowers (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (centralizer ({d.t} : Set G))))
  obtain ⟨Tt, hTtT, -, htTt, hcov, -⟩ :=
    hd.exists_complement (T := (P : Subgroup (centralizer ({d.t} : Set G))).map
      (centralizer ({d.t} : Set G)).subtype) ⟨P, rfl⟩
  have hTtH : Tt ≤ centralizer ({d.t} : Set G) := hTtT.trans (map_subtype_le _)
  have hVP := hVp.le_sylow_of_normal P
  have hmemV : ∀ v ∈ zpowers (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G)),
      v = 1 ∨ v = ⟨d.t, d.t_mem_centralizer⟩ := fun v hv =>
    (Model.mem_zpowers_of_orderOf_two ht2).1 hv
  have hsplit : ∃ K : Subgroup (centralizer ({d.t} : Set G)), K ≤ P ∧
      zpowers ⟨d.t, d.t_mem_centralizer⟩ ⊓ K = ⊥ ∧ zpowers ⟨d.t, d.t_mem_centralizer⟩ ⊔ K = P := by
    refine ⟨Tt.subgroupOf (centralizer ({d.t} : Set G)), fun x hx => ?_, ?_, ?_⟩
    · obtain ⟨y, hy, hyx⟩ := hTtT (mem_subgroupOf.1 hx)
      rwa [show y = x from Subtype.ext hyx] at hy
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxV, hxT⟩ := mem_inf.1 hx
      rcases hmemV x hxV with rfl | rfl
      · exact one_mem _
      · exact absurd (mem_subgroupOf.1 hxT) htTt
    · refine le_antisymm (sup_le hVP fun x hx => ?_) fun x hx => ?_
      · obtain ⟨y, hy, hyx⟩ := hTtT (mem_subgroupOf.1 hx)
        rwa [show y = x from Subtype.ext hyx] at hy
      · rcases hcov x ⟨x, hx, rfl⟩ with h | h
        · exact mem_sup_right (mem_subgroupOf.2 h)
        · have hx' : x = ⟨d.t, d.t_mem_centralizer⟩ * (⟨d.t, d.t_mem_centralizer⟩ * x) := by
            rw [← mul_assoc, show (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G)) *
              ⟨d.t, d.t_mem_centralizer⟩ = 1 from Subtype.ext htt, one_mul]
          rw [hx']
          exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_subgroupOf.2 h))
  obtain ⟨K₀, hK₀1, hK₀2⟩ := (CFSG.Quasithin.gaschutz hVp P).2 hsplit
  refine ⟨K₀.map (centralizer ({d.t} : Set G)).subtype, map_subtype_le _, ?_, fun x hx => ?_⟩
  · rintro ⟨y, hy, hyt⟩
    have hyV : y = ⟨d.t, d.t_mem_centralizer⟩ := Subtype.ext hyt
    have : y ∈ zpowers (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G)) ⊓ K₀ :=
      mem_inf.2 ⟨hyV ▸ mem_zpowers _, hy⟩
    rw [hK₀1, mem_bot, hyV] at this
    exact hd.t_ne_one (congrArg Subtype.val this)
  · have hx' : (⟨x, hx⟩ : centralizer ({d.t} : Set G)) ∈
        zpowers ⟨d.t, d.t_mem_centralizer⟩ ⊔ K₀ := hK₀2 ▸ mem_top _
    obtain ⟨v, hv, k, hk, hvk⟩ := mem_sup_of_normal_left.1 hx'
    rcases hmemV v hv with rfl | rfl
    · left
      rw [one_mul] at hvk
      exact ⟨k, hk, congrArg Subtype.val hvk⟩
    · right
      refine ⟨k, hk, ?_⟩
      have := congrArg Subtype.val hvk
      simp only [Subgroup.coe_mul] at this
      rw [← this, ← mul_assoc, htt, one_mul]
      rfl

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
