module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Sit
public import CFSG.GH74.GLS.IVK.L2.Transport

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem commute_of_mul_eq {M : Type*} [Mul M] {a b : M} (h : a * b = b * a) : Commute a b := h

namespace SitFacts

theorem T_le_C (h : SitFacts x Kb e N T) : T ≤ Cx x := h.sylow.1

theorem phig_mem_inn {g : G} (hg : g ∈ Kg x Kb) : phig x Kb g ∈ IVK.innAut ↥Kb := by
  rw [phig_eq_conj x Kb hg]
  exact ⟨_, rfl⟩

theorem phig_inj_P [Finite G] (h : SitFacts x Kb e N T) {p₁ p₂ : G} (h₁ : p₁ ∈ Pg x Kb T) (h₂ : p₂ ∈ Pg x Kb T)
    (heq : phig x Kb p₁ = phig x Kb p₂) : p₁ = p₂ := by
  have hconj := IVK.conj_injective_of_L2 e
  have hmem : p₁⁻¹ * p₂ ∈ Pg x Kb T ⊓ Qg x Kb T := by
    refine ⟨(Pg x Kb T).mul_mem ((Pg x Kb T).inv_mem h₁) h₂, ?_⟩
    have hC₁ : p₁ ∈ Cx x := h.T_le_C h₁.1
    have hC₂ : p₂ ∈ Cx x := h.T_le_C h₂.1
    refine ⟨T.mul_mem (T.inv_mem h₁.1) h₂.1, mul_mem (inv_mem hC₁) hC₂, ?_⟩
    rw [phig_mul x Kb (inv_mem hC₁) hC₂, phig_inv x Kb hC₁, heq, inv_mul_cancel]
  rw [Pg_inf_Qg x Kb hconj h.sylow, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.1 hmem

theorem inn_iff [Finite G] (h : SitFacts x Kb e N T) {g : G} (hg : g ∈ T) :
    phig x Kb g ∈ IVK.innAut ↥Kb ↔ g ∈ Pg x Kb T ⊔ Qg x Kb T := by
  rw [mem_sup_iff_of_comm (Pg_comm_Qg x Kb h.sylow)]
  have hgC : g ∈ Cx x := h.T_le_C hg
  constructor
  · intro hinn
    have hgP : phig x Kb g ∈ N.P := ⟨h.hTN g hg, hinn⟩
    obtain ⟨p, hp, hpg⟩ := (h.hPN _).1 hgP
    have hpC : p ∈ Cx x := h.T_le_C hp.1
    refine ⟨p, hp, p⁻¹ * g, ⟨T.mul_mem (T.inv_mem hp.1) hg, mul_mem (inv_mem hpC) hgC, ?_⟩, by simp⟩
    rw [phig_mul x Kb (inv_mem hpC) hgC, phig_inv x Kb hpC, hpg, inv_mul_cancel]
  · rintro ⟨p, hp, q, hq, rfl⟩
    have hpC : p ∈ Cx x := h.T_le_C hp.1
    rw [phig_mul x Kb hpC hq.2.1, hq.2.2, mul_one]
    exact phig_mem_inn hp.2

theorem Qg_le_Rd : Qg x Kb T ≤ Rdg x Kb e T := by
  rintro g ⟨hgT, hgC, hg1⟩
  exact ⟨hgT, hgC, by rw [hg1]; exact one_mem _⟩

theorem Pg_le_Rd : Pg x Kb T ≤ Rdg x Kb e T := by
  rintro g ⟨hgT, hgK⟩
  exact ⟨hgT, ((mem_Kg x Kb).1 hgK).1, IVK.innAut_le_innDiagSub e (phig_mem_inn hgK)⟩

theorem Rd_normal (h : SitFacts x Kb e N T) : NormalIn (Rdg x Kb e T) T := by
  refine ⟨fun g hg => hg.1, fun t ht d hd => ?_⟩
  obtain ⟨hdT, hdC, hdD⟩ := hd
  have htC := h.T_le_C ht
  refine ⟨T.mul_mem (T.mul_mem ht hdT) (T.inv_mem ht), mul_mem (mul_mem htC hdC) (inv_mem htC), ?_⟩
  rw [phig_mul x Kb (mul_mem htC hdC) (inv_mem htC), phig_mul x Kb htC hdC, phig_inv x Kb htC]
  exact (IVK.innDiagSub_normal e).conj_mem _ hdD _

theorem PQ_le_Rd : Pg x Kb T ⊔ Qg x Kb T ≤ Rdg x Kb e T :=
  sup_le Pg_le_Rd Qg_le_Rd

theorem mem_PQ_of_inn [Finite G] (h : SitFacts x Kb e N T) {g : G} (hg : g ∈ Rdg x Kb e T)
    (hinn : phig x Kb g ∈ IVK.innAut ↥Kb) : g ∈ Pg x Kb T ⊔ Qg x Kb T :=
  (h.inn_iff hg.1).1 hinn

theorem x_mem_Q [Finite G] (h : SitFacts x Kb e N T) (hx : x * x = 1) (hx1 : x ≠ 1) : x ∈ Qg x Kb T :=
  ⟨x_mem_of_sylow x h.sylow hx hx1, x_mem_Cx x, phig_x_eq_one x Kb⟩

theorem relIndex_PQ_Rd_le [Finite G] (h : SitFacts x Kb e N T) :
    (Pg x Kb T ⊔ Qg x Kb T).relIndex (Rdg x Kb e T) ≤ 2 := by
  have hRdC : Rdg x Kb e T ≤ Cx x := fun g hg => hg.2.1
  let Φ : ↥(Rdg x Kb e T) →* MulAut ↥Kb := (phiC x Kb).comp (Subgroup.inclusion hRdC)
  have hΦ : ∀ g : ↥(Rdg x Kb e T), Φ g = phig x Kb g := fun g =>
    (phig_of_mem x Kb g.2.2.1).symm
  have hcomap : (Pg x Kb T ⊔ Qg x Kb T).subgroupOf (Rdg x Kb e T) =
      (IVK.innAut ↥Kb).comap Φ := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hΦ, ← h.inn_iff g.2.1]
  have hrange : Φ.range ≤ IVK.innDiagSub e := by
    rintro _ ⟨g, rfl⟩
    rw [hΦ]
    exact g.2.2.2
  have h2 : (IVK.innAut ↥Kb).relIndex (IVK.innDiagSub e) = 2 := IVK.innAut_relIndex_two e h.hF
  calc (Pg x Kb T ⊔ Qg x Kb T).relIndex (Rdg x Kb e T)
      = ((Pg x Kb T ⊔ Qg x Kb T).subgroupOf (Rdg x Kb e T)).index := rfl
    _ = ((IVK.innAut ↥Kb).comap Φ).index := by rw [hcomap]
    _ = (IVK.innAut ↥Kb).relIndex Φ.range := Subgroup.index_comap (IVK.innAut ↥Kb) Φ
    _ ≤ (IVK.innAut ↥Kb).relIndex (IVK.innDiagSub e) :=
        Subgroup.relIndex_le_of_le_right hrange (by rw [h2]; norm_num)
    _ = 2 := h2

end SitFacts

end CFSG.GH74.GLS.Stage1.Thm6.Glue
