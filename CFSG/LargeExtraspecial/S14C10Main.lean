module

public import CFSG.LargeExtraspecial.S14C10Alt2
public import CFSG.LargeExtraspecial.S14C10Schur
public import CFSG.LargeExtraspecial.S14C10Sym3
public import CFSG.LargeExtraspecial.S14NQIrred

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem false_of_perm_three_prod (hNQ : NQIrredStmt) [IsSimpleGroup G] {t0 : Mbar0 S}
    {c : Config} (hSt : Stage S g ((t0 : S.Mbar) : S.O))
    (hocc : c.Occurs S g ((t0 : S.Mbar) : S.O))
    (hext : IsExtraspecialPGroup 2 (Nbar S g ((t0 : S.Mbar) : S.O)))
    (h8b : c ≠ .omegaPlus8b) (h6 : c ≠ .omegaPlus6) (h7 : Concl14_7 S g ((t0 : S.Mbar) : S.O))
    (hperf : ⁅Rbar S g ((t0 : S.Mbar) : S.O), Rbar S g ((t0 : S.Mbar) : S.O)⁆ =
      Rbar S g ((t0 : S.Mbar) : S.O))
    (hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    {P : Type*} [Group P] (φ : centralizer ({t0} : Set (Mbar0 S)) →* Equiv.Perm (Fin 3) × P)
    (hφ : Function.Surjective φ)
    (hker : φ.ker = timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))) : False := by
  obtain ⟨a, haF, ha2, haK⟩ := exists_of_perm_three_prod φ hφ hker
    (comap_inclC_perfect hR0 hperf)
  have hx2 : inclC (Mbar0 S) t0 a * inclC (Mbar0 S) t0 a ∈ Nbar S g ((t0 : S.Mbar) : S.O) := by
    rw [← inclC_mul]
    exact (mem_fstar_iff hmap _).mp ha2
  have hxR : ∀ r ∈ Rbar S g ((t0 : S.Mbar) : S.O),
      inclC (Mbar0 S) t0 a * r * (inclC (Mbar0 S) t0 a)⁻¹ * r⁻¹ ∈
        Nbar S g ((t0 : S.Mbar) : S.O) := by
    intro r hr
    rw [← map_comap_inclC hR0] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    have := (mem_fstar_iff hmap _).mp (haK k hk)
    simpa only [inclC_mul, inclC_inv] using this
  exact haF ((mem_fstar_iff hmap a).mpr
    (mem_Nbar_of_sq_mem hNQ hSt hocc hext h8b h6 h7 (inclC_mem a) hx2 hxR))

theorem exists_noncomm_Mbar0 {t : S.O} (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (htN : t ∈ Nbar S g t) (ht1 : t ≠ 1) (htc : ∀ y ∈ Nbar S g t, t * y = y * t)
    (h8 : Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype) : ∃ a b : Mbar0 S, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_eq_of_extraspecial hext htN ht1 htc
  refine exists_noncomm_of_mem (h8 (Nbar_le_Rbar ha)) (h8 (Nbar_le_Rbar hb)) fun h => ht1 ?_
  rw [← hab, h, mul_inv_cancel_right, mul_inv_cancel]

theorem claim14_10_of (hCE : CentralExtInput.{0}) (hNQ : NQIrredStmt) (h2 : PSLPSU10Input) :
    Claim14_10 := by
  intro G _ _ _ S g t c hSt hc hocc hext _ h7 h8 hF ih
  obtain ⟨H, C, ht, ht1, hVQ, hcase, -⟩ := case_of_occurs hocc
  have haQ := H.conj_mem
  have htN := S6.self_mem_Nbar H ht
  have htc : ∀ y ∈ Nbar S g t, t * y = y * t := fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  have hperf := rbarPerfectStmt_of hCE G S g t c hSt hocc hext
  have hcardN : Nat.card (Nbar S g t) = 2 ^ 17 := by
    rcases hc with rfl | rfl | rfl <;> exact hocc.2.2
  have hd : finrank (ZMod 2) (Vt S g t) = 8 ∨ finrank (ZMod 2) (Vt S g t) = 10 := by
    rcases hc with rfl | rfl | rfl
    · exact Or.inl hocc.1.1.2.2.2.2.2.2
    · exact Or.inr hocc.1.1.2.2.2.2.2.2
    · exact Or.inl hocc.1.2.2.2.2.2.2
  have h8b : c ≠ .omegaPlus8b := by rcases hc with rfl | rfl | rfl <;> nofun
  have h6 : c ≠ .omegaPlus6 := by rcases hc with rfl | rfl | rfl <;> nofun
  have hnonab := exists_noncomm_Mbar0 hext htN ht1 htc h8
  have hle : FCt S t ≤ (Mbar0 S).map S.Mbar.subtype := fun x hx => by
    rw [hF] at hx
    exact h8 (Nbar_le_Rbar hx)
  obtain ⟨t0, rfl⟩ : ∃ t0 : Mbar0 S, ((t0 : S.Mbar) : S.O) = t := by
    obtain ⟨m, hm, hmt⟩ := h8 (Nbar_le_Rbar htN)
    exact ⟨⟨m, hm⟩, hmt⟩
  have ht2 : orderOf t0 = 2 := by
    refine orderOf_eq_prime ?_ fun h => ht1 (congrArg (fun y : Mbar0 S => ((y : S.Mbar) : S.O)) h)
    have := mul_self_of_mem_Lbar S haQ ht
    exact Subtype.ext (Subtype.ext (by simpa [pow_two] using this))
  have hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O) := fun r hr =>
    mem_Ct0.mpr ⟨Subgroup.mem_map.mp (h8 hr),
      mem_centralizer_singleton_iff.mp (Rbar_le_centralizer haQ hr)⟩
  have hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O) :=
    (map_fstar_inclC (timmesfeldFStar_normal S.Mbar) h7.2 hle).trans hF
  obtain ⟨X, _, φ, hφs, hφk, hconc⟩ := exists_conclusion_of_mainFor (w := 8) ih hnonab ht2 hmap
    hext (hcardN.trans (by norm_num))
  rcases hconc.width_eight with hX | ⟨-, -, q, -, h3⟩
  · have e := (Subgroup.equivMapOfInjective _ _ (inclC_injective (t0 := t0))).trans
      (MulEquiv.subgroupCongr hmap)
    exact false_of_alt2 h2 hcase hd hcardN hperf hR0 hmap
      ((Bridge.timmesfeldIsExtraspecial_congr e).mpr
        ((Bridge.timmesfeldIsExtraspecial_iff _).mpr hext))
      ((Nat.card_congr e.toEquiv).trans hcardN) ht2 hX
  · rcases h3 with h3 | h3
    · obtain ⟨e⟩ := h3
      exact false_of_perm_three_prod hNQ hSt hocc hext h8b h6 h7 hperf hR0 hmap
        (e.toMonoidHom.comp φ) (e.surjective.comp hφs) ((ker_mulEquiv_comp φ e).trans hφk)
    · obtain ⟨e⟩ := h3
      exact false_of_perm_three_prod hNQ hSt hocc hext h8b h6 h7 hperf hR0 hmap
        (e.toMonoidHom.comp φ) (e.surjective.comp hφs) ((ker_mulEquiv_comp φ e).trans hφk)

theorem claim14_10_of_inputs (hCE : CentralExtInput.{0}) (h2 : PSLPSU10Input) : Claim14_10 :=
  claim14_10_of hCE (nqIrredStmt_of hCE) h2

end CFSG.LargeExtraspecial.S14
