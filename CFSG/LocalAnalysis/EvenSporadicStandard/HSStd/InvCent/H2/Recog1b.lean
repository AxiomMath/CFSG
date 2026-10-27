module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Recog1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Prod


public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Two

variable {G : Type*} [Group G] [Finite G] {t v : G} {J S₁ : Subgroup G}

theorem card_jOne (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) :
    Nat.card ↥(jOne t S₁) = 120 := by
  have hcomm : ∀ a ∈ kleinV t v, ∀ b ∈ jOne t S₁, a * b = b * a :=
    fun a ha b hb => cfg.kleinV_central hb.1 ha
  have hdisj : kleinV t v ⊓ jOne t S₁ = ⊥ := by
    rw [inf_comm]
    exact jOne_inf_kleinV cfg hF hs
  obtain ⟨e⟩ :=
    CFSG.EvenSporadicStandard.HSStd.InvCent.nonempty_mulEquiv_sup_prod hcomm hdisj
  have hcard : Nat.card ↥(kleinV t v ⊔ jOne t S₁)
      = Nat.card ↥(kleinV t v) * Nat.card ↥(jOne t S₁) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have hsup : kleinV t v ⊔ jOne t S₁ = centralizer ({t} : Set G) := by
    refine le_antisymm (sup_le cfg.kleinV_le_centralizer inf_le_left) ?_
    intro c hc
    obtain ⟨x, hx, j, hj, rfl⟩ := exists_mul_of_mem_centralizer cfg hF hs φ hc
    exact Subgroup.mul_mem_sup hx hj
  rw [hsup, cfg.card_kleinV, cfg.card_centralizer] at hcard
  omega

private noncomputable def recog1b_f (cfg : H2Cfg G t v J) : ↥(kleinV t v) × ↥J →* G :=
  MonoidHom.noncommCoprod (kleinV t v).subtype J.subtype
    fun a b => (commute_iff_eq _ _).mpr (cfg.comm a a.2 b b.2)

private theorem recog1b_f_injective (cfg : H2Cfg G t v J) :
    Function.Injective (recog1b_f cfg) := by
  simp only [recog1b_f]
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨Subtype.coe_injective, Subtype.coe_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype]
  exact disjoint_iff.mpr cfg.disj

private theorem recog1b_f_range (cfg : H2Cfg G t v J) :
    (recog1b_f cfg).range = kleinV t v ⊔ J := by
  simp only [recog1b_f]
  rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

private noncomputable def recog1b_e (cfg : H2Cfg G t v J) :
    ↥(kleinV t v) × ↥J ≃* (recog1b_f cfg).range :=
  MonoidHom.ofInjective (f := recog1b_f cfg) (recog1b_f_injective cfg)

private theorem recog1b_jOne_le_range (cfg : H2Cfg G t v J) :
    jOne t S₁ ≤ (recog1b_f cfg).range := by
  rw [recog1b_f_range, ← cfg.cent_t]
  exact inf_le_left

private theorem recog1b_e_symm_apply_mul (cfg : H2Cfg G t v J)
    {a : G} (ha : a ∈ kleinV t v) {b : G} (hb : b ∈ J)
    (h : a * b ∈ (recog1b_f cfg).range) :
    (recog1b_e cfg).symm ⟨a * b, h⟩ = (⟨a, ha⟩, ⟨b, hb⟩) := by
  have h1 : recog1b_e cfg (⟨a, ha⟩, ⟨b, hb⟩) = ⟨a * b, h⟩ := by
    apply Subtype.ext
    rfl
  rw [← h1]
  exact MulEquiv.symm_apply_apply (recog1b_e cfg) _

private noncomputable def recog1b_psi (cfg : H2Cfg G t v J) :
    ↥(jOne t S₁) →* ↥J :=
  (MonoidHom.snd ↥(kleinV t v) ↥J).comp
    ((recog1b_e cfg).symm.toMonoidHom.comp
      (Subgroup.inclusion (recog1b_jOne_le_range cfg)))

private theorem recog1b_psi_apply (cfg : H2Cfg G t v J)
    {a : G} (ha : a ∈ kleinV t v) {b : G} (hb : b ∈ J)
    (hmem : a * b ∈ jOne t S₁) :
    recog1b_psi (S₁ := S₁) cfg ⟨a * b, hmem⟩ = ⟨b, hb⟩ := by
  simp only [recog1b_psi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [show Subgroup.inclusion (recog1b_jOne_le_range cfg) ⟨a * b, hmem⟩
        = ⟨a * b, recog1b_jOne_le_range cfg hmem⟩ from rfl,
      recog1b_e_symm_apply_mul cfg ha hb]
  rfl

private theorem recog1b_psi_injective (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) :
    Function.Injective (recog1b_psi (S₁ := S₁) cfg) := by
  rw [injective_iff_map_eq_one]
  intro j hj
  obtain ⟨a, ha, b, hb, heq⟩ := H2Cfg.exists_mul_of_mem_centralizer cfg j.2.1
  have hmem : a * b ∈ jOne t S₁ := heq ▸ j.2
  have hpsi : recog1b_psi (S₁ := S₁) cfg ⟨a * b, hmem⟩ = ⟨b, hb⟩ :=
    recog1b_psi_apply cfg ha hb hmem
  have hj' : recog1b_psi (S₁ := S₁) cfg ⟨a * b, hmem⟩ = 1 := by
    have hjeq : j = ⟨a * b, hmem⟩ := by
      apply Subtype.ext
      exact heq
    rw [← hjeq]
    exact hj
  have hb1 : b = 1 := by
    have hbJ : (⟨b, hb⟩ : ↥J) = 1 := by rw [← hpsi, hj']
    simpa using congrArg Subtype.val hbJ
  have hja : (j : G) = a := by rw [heq, hb1, mul_one]
  have hmemV : (j : G) ∈ kleinV t v := hja ▸ ha
  have hbot : (j : G) ∈ (⊥ : Subgroup G) := by
    have hmem' : (j : G) ∈ jOne t S₁ ⊓ kleinV t v := ⟨j.2, hmemV⟩
    rwa [jOne_inf_kleinV cfg hF hs] at hmem'
  exact Subtype.ext (by simpa using hbot)

theorem jOne_equiv (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) :
    Nonempty (↥(jOne t S₁) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨eJ⟩ := cfg.J_iso
  have hcard : Nat.card ↥(jOne t S₁) = Nat.card ↥J := by
    rw [card_jOne cfg hF hs φ, cfg.card_J]
  have hbij : Function.Bijective (recog1b_psi (S₁ := S₁) cfg) :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨recog1b_psi_injective cfg hF hs, hcard⟩
  exact ⟨(MulEquiv.ofBijective (recog1b_psi (S₁ := S₁) cfg) hbij).trans eJ⟩

end H2Two

end CFSG.EvenSporadicStandard.HSStd.InvCent
