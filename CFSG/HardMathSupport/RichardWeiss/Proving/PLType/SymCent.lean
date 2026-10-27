module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseKeySym

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.RichardWeiss.Proving.PLType

open Equiv Equiv.Perm CFSG.HardMathSupport.Cooperstein.StructureLie
  CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseKeySym CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

section SwapCent

variable {m : ℕ} {a b : Fin m}

abbrev Comp (a b : Fin m) : Type := {x : Fin m // x ≠ a ∧ x ≠ b}

theorem card_comp (hab : a ≠ b) : Fintype.card (Comp a b) = m - 2 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : Fin m => x ≠ a ∧ x ≠ b) = Finset.univ \ {a, b} := by
    ext x; simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.card_pair hab]

@[expose] noncomputable def compEquiv (hab : a ≠ b) : Fin (m - 2) ≃ Comp a b :=
  (Fintype.equivFinOfCardEq (card_comp hab)).symm

@[expose] noncomputable def extComp (hab : a ≠ b) : Perm (Fin (m - 2)) →* Perm (Fin m) :=
  extendDomainHom (compEquiv hab)

theorem extComp_fix (hab : a ≠ b) (π : Perm (Fin (m - 2))) {i : Fin m} (hi : ¬ (i ≠ a ∧ i ≠ b)) :
    extComp hab π i = i := by
  rw [extComp, extendDomainHom_apply]
  exact extendDomain_apply_not_subtype π (compEquiv hab) hi

theorem extComp_commute (hab : a ≠ b) (π : Perm (Fin (m - 2))) :
    extComp hab π * swap a b = swap a b * extComp hab π := by
  have ha : extComp hab π a = a := extComp_fix hab π (by simp)
  have hb : extComp hab π b = b := extComp_fix hab π (by simp)
  have h1 : (extComp hab π)⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, ha]
  have h2 : (extComp hab π)⁻¹ b = b := by rw [Perm.inv_eq_iff_eq, hb]
  have := swap_mul_eq_mul_swap (extComp hab π) a b
  rw [h1, h2] at this
  exact this.symm

@[expose] def signCorr (a b : Fin m) (u : ℤˣ) : Perm (Fin m) := if u = 1 then 1 else swap a b

theorem signCorr_mul (u v : ℤˣ) :
    signCorr a b (u * v) = signCorr a b u * signCorr a b v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp [signCorr, swap_mul_self]

@[expose] noncomputable def centHom (hab : a ≠ b) : Perm (Fin (m - 2)) →* Perm (Fin m) where
  toFun π := extComp hab π * signCorr a b (sign π)
  map_one' := by simp [signCorr]
  map_mul' π ρ := by
    rw [map_mul, map_mul, signCorr_mul]
    have hc : signCorr a b (sign π) * extComp hab ρ = extComp hab ρ * signCorr a b (sign π) := by
      unfold signCorr
      split_ifs
      · rw [one_mul, mul_one]
      · exact (extComp_commute hab ρ).symm
    calc extComp hab π * extComp hab ρ * (signCorr a b (sign π) * signCorr a b (sign ρ))
        = extComp hab π * (extComp hab ρ * signCorr a b (sign π)) * signCorr a b (sign ρ) := by
          group
      _ = extComp hab π * (signCorr a b (sign π) * extComp hab ρ) * signCorr a b (sign ρ) := by
          rw [hc]
      _ = extComp hab π * signCorr a b (sign π) * (extComp hab ρ * signCorr a b (sign ρ)) := by
          group

theorem centHom_apply (hab : a ≠ b) (π : Perm (Fin (m - 2))) :
    centHom hab π = extComp hab π * signCorr a b (sign π) := rfl

theorem centHom_mem (hab : a ≠ b) (π : Perm (Fin (m - 2))) :
    centHom hab π ∈ Subgroup.centralizer {swap a b} ⊓ alternatingGroup (Fin m) := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · rw [centHom_apply]
    unfold signCorr
    split_ifs
    · rw [mul_one]
      exact extComp_commute hab π
    · rw [mul_assoc, swap_mul_self, mul_one, extComp_commute hab π, ← mul_assoc, swap_mul_self,
        one_mul]
  · rw [mem_alternatingGroup, centHom_apply, map_mul, extComp, extendDomainHom_apply,
      sign_extendDomain]
    unfold signCorr
    rcases Int.units_eq_one_or (sign π) with h | h
    · simp [h]
    · simp [h, sign_swap hab]

theorem centHom_injective (hab : a ≠ b) : Function.Injective (centHom hab) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro π hπ
  rw [MonoidHom.mem_ker, centHom_apply] at hπ
  have h0 : sign π = 1 := by
    by_contra h
    have := congrArg (fun f : Perm (Fin m) => f a) hπ
    simp only [Perm.mul_apply, Perm.one_apply, signCorr, h, ite_false] at this
    rw [swap_apply_left, extComp_fix hab π (by simp)] at this
    exact hab this.symm
  simp only [signCorr, h0, ite_true, mul_one] at hπ
  exact (extendDomainHom_injective (compEquiv hab)) (hπ.trans (map_one _).symm)

theorem card_inf_alt_of_odd' {K : Subgroup (Perm (Fin m))} {τ : Perm (Fin m)} (hτ : τ ∈ K)
    (hodd : sign τ = -1) :
    Nat.card (K ⊓ alternatingGroup (Fin m) : Subgroup (Perm (Fin m))) * 2 = Nat.card K := by
  let φ : K →* ℤˣ := sign.comp K.subtype
  have hsurj : Function.Surjective φ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one φ⟩
    · exact ⟨⟨τ, hτ⟩, hodd⟩
  have hrange : Nat.card φ.range = 2 := by
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hker : Nat.card φ.ker = Nat.card (K ⊓ alternatingGroup (Fin m) : Subgroup _) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, (MonoidHom.mem_ker.1 x.2 :)⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, MonoidHom.mem_ker.2
          (Subgroup.mem_inf.1 x.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [← hker, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem card_altCent_swap (hab : a ≠ b) :
    Nat.card (Subgroup.centralizer {swap a b} ⊓ alternatingGroup (Fin m) :
      Subgroup (Perm (Fin m))) = (m - 2).factorial := by
  have h := card_inf_alt_of_odd' (K := Subgroup.centralizer {swap a b}) (τ := swap a b)
    (Subgroup.mem_centralizer_singleton_iff.2 rfl) (sign_swap hab)
  have hc : Nat.card (Subgroup.centralizer ({swap a b} : Set (Perm (Fin m)))) =
      (m - 2).factorial * 2 := by
    rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.isSwap_iff_cycleType.1 ⟨a, b, hab, rfl⟩]
    simp
  omega

theorem centHom_range (hab : a ≠ b) :
    (centHom hab).range = Subgroup.centralizer {swap a b} ⊓ alternatingGroup (Fin m) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨π, rfl⟩
    exact centHom_mem hab π
  · rw [card_altCent_swap hab,
      ← Nat.card_congr (MonoidHom.ofInjective (centHom_injective hab)).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]

noncomputable def altCentSwapEquiv (hab : a ≠ b) :
    Perm (Fin (m - 2)) ≃*
      ↥(Subgroup.centralizer {swap a b} ⊓ alternatingGroup (Fin m) : Subgroup (Perm (Fin m))) :=
  (MonoidHom.ofInjective (centHom_injective hab)).trans (MulEquiv.subgroupCongr (centHom_range hab))

end SwapCent

section Transport

variable {W V : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup V] [Module (ZMod 2) V]
  {m : ℕ}

theorem congr_apply (β : W ≃ₗ[ZMod 2] V) (g : LinearMap.GeneralLinearGroup (ZMod 2) W) (x : V) :
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv β g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) x = β ((g : W →ₗ[ZMod 2] W) (β.symm x)) := by
  rw [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  rfl

@[expose] def symEmb (ρ : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (β : W ≃ₗ[ZMod 2] V) : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) W :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv β).symm.toMonoidHom.comp ρ

theorem congr_symEmb (ρ : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (β : W ≃ₗ[ZMod 2] V) (σ : Perm (Fin m)) :
    LinearMap.GeneralLinearGroup.congrLinearEquiv β (symEmb ρ β σ) = ρ σ :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv β).apply_symm_apply (ρ σ)

theorem symEmb_range (ρ : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (β : W ≃ₗ[ZMod 2] V) {H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = ρ.range) :
    (symEmb ρ β).range = H := by
  set c := LinearMap.GeneralLinearGroup.congrLinearEquiv β with hc
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    have : ρ σ ∈ H.map c.toMonoidHom := by rw [hH]; exact ⟨σ, rfl⟩
    obtain ⟨h, hh, hσ⟩ := this
    have : symEmb ρ β σ = h := by
      change c.symm (ρ σ) = h
      rw [← hσ]; exact c.symm_apply_apply h
    rw [this]; exact hh
  · intro hx
    have : c x ∈ ρ.range := by
      rw [← hH]; exact ⟨x, hx, rfl⟩
    obtain ⟨σ, hσ⟩ := this
    refine ⟨σ, ?_⟩
    change c.symm (ρ σ) = x
    rw [hσ]; exact c.symm_apply_apply x

theorem comm_eq_map (ρ : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (β : W ≃ₗ[ZMod 2] V) {H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = ρ.range) :
    ⁅H, H⁆ = Subgroup.map (symEmb ρ β) ⁅(⊤ : Subgroup (Perm (Fin m))), ⊤⁆ := by
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, symEmb_range ρ β hH]

theorem five_le_of_perfect (ρ : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (β : W ≃ₗ[ZMod 2] V) {H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = ρ.range)
    (hperf : ⁅⁅H, H⁆, ⁅H, H⁆⁆ = ⁅H, H⁆) (hne : ⁅H, H⁆ ≠ ⊥) : 5 ≤ m := by
  by_contra hlt
  have hsolv : Group.IsSolvable (Perm (Fin m)) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  obtain ⟨n, hn⟩ := hsolv.solvable
  have key : ∀ k : ℕ, ⁅H, H⁆ ≤ (derivedSeries (Perm (Fin m)) (k + 1)).map (symEmb ρ β) := by
    intro k
    induction k with
    | zero =>
      rw [comm_eq_map ρ β hH, derivedSeries_succ, derivedSeries_zero]
    | succ k ih =>
      calc ⁅H, H⁆ = ⁅⁅H, H⁆, ⁅H, H⁆⁆ := hperf.symm
        _ ≤ ⁅(derivedSeries (Perm (Fin m)) (k + 1)).map (symEmb ρ β),
            (derivedSeries (Perm (Fin m)) (k + 1)).map (symEmb ρ β)⁆ :=
          Subgroup.commutator_mono ih ih
        _ = (derivedSeries (Perm (Fin m)) (k + 1 + 1)).map (symEmb ρ β) := by
          rw [← Subgroup.map_commutator, ← derivedSeries_succ]
  apply hne
  rw [eq_bot_iff]
  refine (key n).trans ?_
  rw [derivedSeries_succ, hn, Subgroup.commutator_bot_left]
  simp

theorem symCent_of_data (D : SymHeartData m V) (β : W ≃ₗ[ZMod 2] V)
    {H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = D.ρ.range)
    (hperf : ⁅⁅H, H⁆, ⁅H, H⁆⁆ = ⁅H, H⁆) (hne : ⁅H, H⁆ ≠ ⊥)
    (t : LinearMap.GeneralLinearGroup (ZMod 2) W) (ht : t ∈ H) (htv : IsF2Transvection t) :
    5 ≤ m ∧ Nonempty (↥⁅H, H⁆ ≃* alternatingGroup (Fin m)) ∧
      Nonempty (↥(⁅H, H⁆ ⊓ Subgroup.centralizer {t}) ≃* Perm (Fin (m - 2))) := by
  have h5 : 5 ≤ m := five_le_of_perfect D.ρ β hH hperf hne
  set Ψ := symEmb D.ρ β with hΨ
  have hinj : Function.Injective Ψ := fun x y hxy =>
    D.ρ_injective h5 ((LinearMap.GeneralLinearGroup.congrLinearEquiv β).symm.injective hxy)
  have hcomm : ⁅H, H⁆ = (alternatingGroup (Fin m)).map Ψ := by
    rw [comm_eq_map D.ρ β hH]
    congr 1
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simpa using h5)
  refine ⟨h5, ⟨(MulEquiv.subgroupCongr hcomm).trans
    (Subgroup.equivMapOfInjective (alternatingGroup (Fin m)) Ψ hinj).symm⟩, ?_⟩
  have htH : t ∈ Ψ.range := by rw [hΨ, symEmb_range D.ρ β hH]; exact ht
  obtain ⟨σ₀, rfl⟩ := htH
  have hσ1 : σ₀ ≠ 1 := by
    rintro rfl
    exact htv.1 (map_one Ψ)
  obtain ⟨φ, a, hφa, -, -, hta⟩ := (isF2Transvection_iff _).1 htv
  have hsw : σ₀.IsSwap := by
    refine D.isSwap_of_tv h5 σ₀ hσ1 (β a) fun x => ?_
    refine ⟨φ (β.symm x), ?_⟩
    have h1 := congr_symEmb D.ρ β σ₀
    rw [← hΨ] at h1
    rw [← h1, hta, congr_apply, tv_apply, map_add, map_smul]
    simp
  obtain ⟨a', b', hab, rfl⟩ := hsw
  have hX : ⁅H, H⁆ ⊓ Subgroup.centralizer {Ψ (swap a' b')} =
      (Subgroup.centralizer {swap a' b'} ⊓ alternatingGroup (Fin m)).map Ψ := by
    rw [hcomm]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hc⟩
      refine ⟨y, ⟨?_, hy⟩, rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      exact hc
    · rintro ⟨y, ⟨hc, hy⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rw [← map_mul, ← map_mul]
      exact congrArg Ψ hc
  exact ⟨(MulEquiv.subgroupCongr hX).trans
    (((Subgroup.equivMapOfInjective _ Ψ hinj).symm).trans (altCentSwapEquiv hab).symm)⟩

end Transport

@[expose] noncomputable def symSumZeroData (m : ℕ) : SymHeartData m (sumZero m) where
  q := LinearMap.id
  ρ := sumZeroRep m
  q_surj := Function.surjective_id
  ρ_q _ _ := rfl
  ker_q x hx := ⟨0, by rw [LinearMap.id_apply] at hx; rw [hx]; rfl⟩

@[expose] noncomputable def symHeartData (m : ℕ) : SymHeartData m (sumZero m ⧸ onesLine m) where
  q := (onesLine m).mkQ
  ρ := heartRep m
  q_surj := Submodule.mkQ_surjective _
  ρ_q σ x := heartRep_apply_mk σ x
  ker_q _ hx := mem_onesLine.mp ((Submodule.Quotient.mk_eq_zero _).mp hx)

theorem symTransvectionCent_holds :
    CFSG.HardMathSupport.Curtis.Coordinator.PLType.SymTransvectionCent := by
  intro W _ _ _ H _ hβ hperf hne t ht htv _
  rcases hβ with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · obtain ⟨h5, h1, h2⟩ := symCent_of_data (V := sumZero (Module.finrank (ZMod 2) W + 1))
      (symSumZeroData (Module.finrank (ZMod 2) W + 1)) β hβ hperf hne t ht htv
    exact ⟨_, h5, h1, h2⟩
  · obtain ⟨h5, h1, h2⟩ := symCent_of_data
      (V := sumZero (Module.finrank (ZMod 2) W + 2) ⧸ onesLine (Module.finrank (ZMod 2) W + 2))
      (symHeartData (Module.finrank (ZMod 2) W + 2)) β hβ hperf hne t ht htv
    exact ⟨_, h5, h1, h2⟩

end CFSG.HardMathSupport.RichardWeiss.Proving.PLType
