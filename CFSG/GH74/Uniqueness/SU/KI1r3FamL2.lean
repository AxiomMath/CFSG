module

public import CFSG.GH74.Uniqueness.SU.KI1r3FamDefs
public import CFSG.GH74.GLS.IVK.L2.KI2Aux

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ABGDGroups CFSG.ABGLocalTools CFSG.GH74.GLS.IVK
open CFSG.GH74.GLS (fixedSubgroup)

section L2Aux

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

include e in
theorem exists_fourGroup_fixed_of_outside (hF : L2Field F) (u : MulAut K) (hu : orderOf u = 2)
    (hud : u ∉ innDiagSub e) :
    ∃ V : Subgroup K, (∀ v ∈ V, u v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haD, hconj⟩ := exists_conj_fieldAut e u hu hud
  obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, σ = fieldProj e u := ⟨_, rfl⟩
  rw [← hσ] at hconj
  have hu2' : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have hσ1 : σ ≠ 1 := fun h => hud ((mem_innDiagSub_iff e u).2 (hσ ▸ h))
  have hσ2 : σ ^ 2 = 1 := by rw [hσ, ← map_pow, hu2', map_one]
  have hord2 : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have h14 := ivk_1_4a F hF K e σ
  obtain ⟨F₀, hF₀f, hF₀fin, hq, ⟨eF⟩⟩ := h14.2.2 (by rw [hord2]; exact even_two)
  have hq2 : Nat.card F₀ ^ 2 = Nat.card F := by rw [← hord2]; exact hq
  have hF₀odd : Odd (Nat.card F₀) := by
    have h1 : Odd (Nat.card F₀ ^ 2) := by rw [hq2]; exact hF.1
    rw [pow_two] at h1
    exact (Nat.odd_mul.1 h1).1
  have hF₀pp : IsOddPrimePower (Nat.card F₀) := isOddPrimePower_card_of_odd hF₀odd
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 (PGL2 F₀)))
  obtain ⟨m, hm, ⟨d⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F₀ hF₀pp S₀
  obtain ⟨V₀, -, hV₀⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S₀ : Subgroup (PGL2 F₀)) hm d
  have hV₀ea : IsElementaryAbelian 2 ↥V₀ :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [hV₀.exponent_two] }
  obtain ⟨hV₀c, hV₀s⟩ := isElementaryAbelian_two_data V₀ hV₀ea
  let ψ : PGL2 F₀ →* K :=
    (a : MulAut K).toMonoidHom.comp
      ((fixedSubgroup K (fieldAutHom e σ)).subtype.comp eF.symm.toMonoidHom)
  have hψ : Function.Injective ψ :=
    a.injective.comp (Subtype.val_injective.comp eF.symm.injective)
  have hψfix : ∀ y, u (ψ y) = ψ y := by
    intro y
    have hk : fieldAutHom e σ ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K) =
        ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K) := (eF.symm y).2
    have hu' : u = a * fieldAutHom e σ * a⁻¹ := by rw [← hconj]; group
    show u (a ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K)) =
      a ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K)
    rw [hu']
    simp [hk]
  refine ⟨V₀.map ψ, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact hψfix y
  · rw [SU1.isElemAbelian_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, hV₀c a' ha' b' hb']
    · rintro _ ⟨a', ha', rfl⟩
      rw [← map_pow, pow_two, hV₀s a' ha', map_one]
  · rw [Subgroup.card_map_of_injective hψ]
    exact hV₀.card_four

include e in
theorem nonempty_equiv_pgl2_innAut_sup_zpowers (hF : L2Field F) (α : MulAut K)
    (hα : α ∈ innDiagSub e) (hαn : α ∉ innAut K) :
    Nonempty (↥(innAut K ⊔ Subgroup.zpowers α) ≃* Matrix.ProjGenLinGroup (Fin 2) F) :=
  ⟨(MulEquiv.subgroupCongr (innAut_sup_zpowers_eq e hF hα hαn)).trans
    (MonoidHom.ofInjective (innDiagHom_injective e)).symm⟩

end L2Aux

theorem famL2 : FamL2 := by
  intro K _ _ p f hp hp2 hLie _ α hα2 hαinn hno
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hFfield, hFfin, hFcard, hne3, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = p ^ f ∧ p ^ f ≠ 3 ∧ Nonempty (K ≃* L2 F) := by
    rcases hLie with ⟨_, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨hadm, F, hf, hfin, hc, he⟩ := hmod
      refine ⟨F, hf, hfin, hc, ?_, he⟩
      intro h3
      exact hadm.2.2.2.2 (by rw [h3])
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
  have hf1 : 1 ≤ f := by
    rcases hLie with ⟨_, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hmod.1.2.1
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card F) := by rw [hFcard]; exact hpodd.pow
  have h3 : 3 < Nat.card F := by
    rw [hFcard]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hF : L2Field F := ⟨hodd, h3⟩
  have hαinn' : α ∉ innAut K := hαinn
  by_cases hD : α ∈ innDiagSub e
  · exact ⟨F, hFfield, hFfin, hFcard, nonempty_equiv_pgl2_innAut_sup_zpowers e hF α hD hαinn'⟩
  · exfalso
    have hα1 : α ≠ 1 := fun h => hαinn' (by rw [h]; exact (innAut K).one_mem)
    have hu : orderOf α = 2 := orderOf_eq_prime hα2 hα1
    exact hno (exists_fourGroup_fixed_of_outside e hF α hu hD)

end CFSG.GH74.Uniqueness.SU.K.R3
