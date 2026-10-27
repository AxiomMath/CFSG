module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

open scoped commutatorElement

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Quasithin.B6

theorem kerIn_top_normal {H : Type*} [Group H] (M : Subgroup H) : (kerIn M ⊤).Normal :=
  ⟨fun x hx g b _ => by
    have h := hx (b * g) (Subgroup.mem_top _)
    have e : b * (g * x * g⁻¹) * b⁻¹ = b * g * x * (b * g)⁻¹ := by group
    rw [e]; exact h⟩

instance instNormalKerInTop {H : Type*} [Group H] (M : Subgroup H) : (kerIn M ⊤).Normal :=
  kerIn_top_normal M

variable {H : Type*} [Group H] [Finite H]

theorem core_isFitting_radical_and_residual_perfect {T M : Subgroup H}
    (hns : ¬ Group.IsSolvable H) (hO2 : CFSG.pCore 2 H = ⊥)
    (hT : IsSylowTwoOf T (⊤ : Subgroup H)) (hTn : ¬ T.Normal) (hTM : T ≤ M) (hMH : M < ⊤)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M)
    {K : Subgroup H} (hK : K = Subgroup.closure {h : H | Odd (orderOf h)}) :
    kerIn M ⊤ = CFSG.solvableRadical H ∧ kerIn M ⊤ = CFSG.fittingSubgroup H ∧
      Group.IsNilpotent ↥(kerIn M ⊤) ∧ Odd (Nat.card ↥(kerIn M ⊤)) ∧ kerIn M ⊤ < K ∧
      ⁅K, K⁆ = K ∧ K ⊔ T = ⊤ ∧ (kerIn M ⊤).Normal ∧ K.Normal ∧
      (∀ N : Subgroup H, N.Normal → kerIn M ⊤ ≤ N → N ≤ K → N = kerIn M ⊤ ∨ N = K) ∧
      (∃ F : Set (Subgroup (H ⧸ kerIn M ⊤)), F.Nonempty ∧
        (∀ S ∈ F, IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧
          (S.subgroupOf (K.map (QuotientGroup.mk' (kerIn M ⊤)))).Normal) ∧
        sSupIndep F ∧ sSup F = K.map (QuotientGroup.mk' (kerIn M ⊤)) ∧
        (∀ S ∈ F, ∀ S' ∈ F, ∃ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)),
          S.map (MulAut.conj t).toMonoidHom = S') ∧
        (∀ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), ∀ S ∈ F,
          S.map (MulAut.conj t).toMonoidHom ∈ F)) ∧
      (∀ U : Subgroup H, U.Normal → ¬ U ≤ kerIn M ⊤ → K ≤ U) := by
  have hO2' : CFSG.Open.pCore 2 H = ⊥ := by exact hO2
  obtain ⟨⟨hRJ, hJK⟩, ⟨hnil', hodd', hsolv⟩, hHKT, ⟨hKn, hmin⟩, hcont, hsimple⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT hTn hTM hMH hmax
  have hpc : ∀ N : Subgroup H, CFSG.Open.pCore 2 H ≤ N := fun N => hO2'.le.trans bot_le
  have hKeq : K = oddResidualPreimage H := by
    rw [hK, oddResidualPreimage_eq, hO2', sup_bot_eq, ← oddOrderSubgroup_eq_twoResidual (⊤ : Subgroup H)]
    unfold oddOrderSubgroup
    congr 1
    ext x
    simp
  subst hKeq
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.Open.pCore 2 H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO2']
  have e : ↥(kerIn M ⊤) ≃* ↥((kerIn M ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H))) :=
    Subgroup.equivMapOfInjective _ _ hinj
  have hnil : Group.IsNilpotent ↥(kerIn M ⊤) := (Group.isNilpotent_congr e).2 hnil'
  have hodd : Odd (Nat.card ↥(kerIn M ⊤)) := by
    rw [Nat.card_congr e.toEquiv]; exact hodd'
  have hCn := kerIn_top_normal M
  have hKns : ¬ Group.IsSolvable ↥(oddResidualPreimage H) := by
    intro hKs
    obtain ⟨L, hL, hLn, hLK, -⟩ := hsimple hns
    have h1 : Group.IsSolvable ↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))) :=
      Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
    have h2 : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLK)
    exact hLn ⟨⟨fun a b => (IsSimpleGroup.comm_iff_isSolvable.2 h2) a b⟩⟩
  have hRad : kerIn M ⊤ = CFSG.solvableRadical H := by
    refine le_antisymm (le_sSup ⟨hCn, inferInstance⟩) ?_
    by_contra hnle
    have hRn : (CFSG.solvableRadical H).Normal := CFSG.ABGLocalTools.solvableRadical_normal
    have hRs : Group.IsSolvable ↥(CFSG.solvableRadical H) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    have := hcont _ hRn (hpc _) hnle
    exact hKns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective this))
  have hFit : kerIn M ⊤ = CFSG.fittingSubgroup H := by
    obtain ⟨hFnil, hFn, hFmax, -⟩ := CFSG.LocalCores.fitting_nilpotent (G := H)
    refine le_antisymm (hFmax _ hCn hnil) ?_
    rw [hRad]
    exact le_sSup ⟨hFn, inferInstance⟩
  have hperf : ⁅oddResidualPreimage H, oddResidualPreimage H⁆ = oddResidualPreimage H := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    have hn : ⁅oddResidualPreimage H, oddResidualPreimage H⁆.Normal := by
      have := hKn; infer_instance
    refine hcont _ hn (hpc _) fun hle => ?_
    obtain ⟨L, hL, hLn, hLK, -⟩ := hsimple hns
    have h1 : ⁅(oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)),
        (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, eq_bot_iff, Subgroup.map_le_iff_le_comap]
      intro x hx
      have := hle hx
      rw [Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact this
    refine hLn ⟨⟨fun a b => ?_⟩⟩
    have hab : ⁅(a : H ⧸ kerIn M ⊤), (b : H ⧸ kerIn M ⊤)⁆ ∈
        ⁅(oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)),
        (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))⁆ :=
      Subgroup.commutator_mem_commutator (hLK a.2) (hLK b.2)
    rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact Subtype.ext hab
  refine ⟨hRad, hFit, hnil, hodd, hJK, hperf, hHKT, hCn, hKn, hmin, ?_, ?_⟩
  ·
    obtain ⟨L, hL, hLn, hLK, hgen, hind, hnorm, hsimp, htrans⟩ := hsimple hns
    refine ⟨{S | ∃ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), S = L.map (MulAut.conj t).toMonoidHom},
      ⟨L, 1, Subgroup.one_mem _, (B6.conjSub_one L).symm⟩, ?_, hind, ?_, ?_, ?_⟩
    · rintro S ⟨t, ht, rfl⟩
      exact ⟨(hsimp t ht).1, (hsimp t ht).2, hnorm t ht⟩
    · rw [hgen]
      refine le_antisymm (sSup_le ?_) (iSup₂_le fun t ht => le_sSup ⟨t, ht, rfl⟩)
      rintro S ⟨t, ht, rfl⟩
      exact le_iSup₂_of_le t ht le_rfl
    · rintro S ⟨t₁, ht₁, rfl⟩ S' ⟨t₂, ht₂, rfl⟩
      obtain ⟨-, s, hs, hst⟩ := htrans t₁ ht₁ t₂ ht₂
      exact ⟨s, hs, hst⟩
    · rintro t ht S ⟨t', ht', rfl⟩
      obtain ⟨⟨s, hs, hst⟩, -⟩ := htrans t ht t' ht'
      exact ⟨s, hs, hst⟩
  · intro U hUn hUC
    exact hcont U hUn (hpc _) hUC

end CFSG.QuasithinUnique.Setup.Layer
