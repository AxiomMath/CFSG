module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_conj_beta_of_outer {α : MulAut NativeSporadic.M12} (h2 : orderOf α = 2)
    (hα : α ∉ inner NativeSporadic.M12) :
    ∃ g : NativeSporadic.M12, α = MulAut.conj g * beta * (MulAut.conj g)⁻¹ := by
  set δ : autModel := autModelEquiv.symm α with hδdef
  have hδ2 : orderOf (δ : Equiv.Perm (Fin 24)) = 2 := by
    rw [Subgroup.orderOf_coe, hδdef, MulEquiv.orderOf_eq, h2]
  have hδD : (δ : Equiv.Perm (Fin 24)) ∉ blockGroup := by
    intro h
    obtain ⟨g, hg⟩ := mem_blockGroup_iff_iota.1 h
    exact hα ⟨g, by rw [← autModelEquiv_iota, hg, hδdef, MulEquiv.apply_symm_apply]⟩
  have hσ : m12Sigma * (δ : Equiv.Perm (Fin 24)) ∈ blockGroup := δ.2.resolve_left hδD
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, hord⟩ := m12_sigma_cover
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hord' : orderOf m12Sigma = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn m12D m12D_check.1 (pairTables_spec hn hA hB)
    m12Sigma (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq) (by norm_num) [m12Sigma]
    (fun r hr => by
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨by simp, hord'⟩) 1000 hok
  obtain ⟨r, hr, c, hc, hδc⟩ := hcov δ (by rw [sigma_inv]; exact hσ) hδ2
  rw [List.mem_singleton] at hr
  subst hr
  obtain ⟨g, hg⟩ := (mem_blockGroup_iff_iota (δ := ⟨c, blockGroup_le_autModel hc⟩)).1 hc
  refine ⟨g, ?_⟩
  have hδ' : δ = autModelIota g * sigmaModel * (autModelIota g)⁻¹ := by
    apply Subtype.ext
    rw [hδc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg, sigmaModel_coe]
  rw [← autModelEquiv.apply_symm_apply α, ← hδdef, hδ', map_mul, map_mul, map_inv,
    autModelEquiv_iota]
  rfl

theorem outer_involution_iff_conj_beta (α : MulAut NativeSporadic.M12) :
    (orderOf α = 2 ∧ α ∉ inner NativeSporadic.M12) ↔
      ∃ g : NativeSporadic.M12, α = MulAut.conj g * beta * (MulAut.conj g)⁻¹ := by
  refine ⟨fun h => exists_conj_beta_of_outer h.1 h.2, ?_⟩
  rintro ⟨g, rfl⟩
  refine ⟨by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_beta], fun h => ?_⟩
  apply beta_not_mem_inner
  have h' := (inner_normal NativeSporadic.M12).conj_mem _ h (MulAut.conj g)⁻¹
  rwa [show (MulAut.conj g)⁻¹ * (MulAut.conj g * beta * (MulAut.conj g)⁻¹) *
    (MulAut.conj g)⁻¹⁻¹ = beta by group] at h'

theorem conj_beta_apply_conj (g x : NativeSporadic.M12) (hx : beta x = x) :
    (MulAut.conj g * beta * (MulAut.conj g)⁻¹) (g * x * g⁻¹) = g * x * g⁻¹ := by
  simp only [MulAut.mul_apply, ← map_inv, MulAut.conj_apply]
  rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group, hx]

theorem fixSub_conj_beta (g : NativeSporadic.M12) :
    fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹) =
      (fixSub beta).map (MulAut.conj g).toMonoidHom :=
  fixSub_conj _ _

theorem card_fixSub_conj_beta (g : NativeSporadic.M12) :
    Nat.card (fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹)) = 120 := by
  rw [fixSub_conj_beta, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    card_fixSub_beta]

theorem commutator_fixSub_conj_beta (g : NativeSporadic.M12) :
    ⁅fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹),
        fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹)⁆ =
      fixedD.map (MulAut.conj g).toMonoidHom :=
  (fusionData_pinned.map (MulAut.conj g)).1.symm

@[expose] noncomputable def conjFixedDEquiv (g : NativeSporadic.M12) :
    fixedD.map (MulAut.conj g).toMonoidHom ≃* fixedD :=
  (fixedD.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

theorem conj_conjFixedDEquiv (g : NativeSporadic.M12)
    (c : fixedD.map (MulAut.conj g).toMonoidHom) :
    g * (conjFixedDEquiv g c : NativeSporadic.M12) * g⁻¹ = c :=
  congrArg Subtype.val ((fixedD.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).apply_symm_apply c)

theorem fixedD_map_conj_perfect (g : NativeSporadic.M12) :
    ⁅fixedD.map (MulAut.conj g).toMonoidHom, fixedD.map (MulAut.conj g).toMonoidHom⁆ =
      fixedD.map (MulAut.conj g).toMonoidHom := by
  rw [← Subgroup.map_commutator, fixedD_perfect]

theorem card_fixedD_map_conj (g : NativeSporadic.M12) :
    Nat.card (fixedD.map (MulAut.conj g).toMonoidHom) = 60 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_fixedD]

theorem card_outer_fixedD_map_conj_dvd (g : NativeSporadic.M12) :
    Nat.card (Outer (fixedD.map (MulAut.conj g).toMonoidHom)) ∣ 2 := by
  rw [Nat.card_congr (equivalence (conjFixedDEquiv g)).toEquiv]
  exact card_outer_fixedD_dvd

end CFSG.ComponentClassification.M12Cover
