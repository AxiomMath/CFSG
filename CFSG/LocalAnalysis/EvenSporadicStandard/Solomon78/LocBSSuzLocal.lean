module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

@[expose] def SuzPair (G : Type) [Group G] (L K : Subgroup G) (u : G) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ Group.IsPerfect K ∧
    Nat.card K = 20160

section Suz

theorem suz_equiv_of_isSporadic {X : Type} [Group X] (h : IsSporadic X .Suz) :
    Nonempty (X ≃* ↥suzM) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans suzEquivM⟩

theorem suz_isSimpleGroup_of_isSporadic {X : Type} [Group X] (h : IsSporadic X .Suz) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e

theorem suz_exists_not_commute {X : Type} [Group X] (h : IsSporadic X .Suz) :
    ∃ a b : X, a * b ≠ b * a := by
  have hs := suz_isSimpleGroup_of_isSporadic h
  obtain ⟨e⟩ := h
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := X)
  have hcX : Nat.card X = 448345497600 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  rw [hcX] at hp
  norm_num at hp

theorem suz_model {G : Type} [Group G] {L K : Subgroup G} {u : G} (hL : IsSporadic L .Suz)
    (hQ : SuzPair G L K u) :
    ∃ Ψ : ↥L →* Equiv.Perm (Fin 1782), Function.Injective Ψ ∧ (∀ x, Ψ x ∈ suzM) ∧
      (∀ y ∈ suzM, ∃ x, Ψ x = y) ∧ Ψ ⟨u, hQ.1⟩ = suzInv 0 := by
  obtain ⟨f⟩ := suz_equiv_of_isSporadic hL
  refine suz_exists_model_aux f ⟨u, hQ.1⟩ (by rw [Subgroup.orderOf_mk, hQ.2.1]) ?_
  have hle : K.subgroupOf L ≤ Subgroup.centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  have hcK : Nat.card (K.subgroupOf L) = 20160 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.2.2.1).toEquiv]
    exact hQ.2.2.2.2.2
  have := Subgroup.card_dvd_of_le hle
  rwa [hcK] at this

theorem suz_K_equiv {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hQ : SuzPair G L K u) (Ψ : ↥L →* Equiv.Perm (Fin 1782)) (hΨ : Function.Injective Ψ)
    (hΨL : ∀ x, Ψ x ∈ suzM) (hΨu : Ψ ⟨u, hQ.1⟩ = suzInv 0) : Nonempty (↥K ≃* ↥suzD) := by
  obtain ⟨M⟩ := suz_outModel
  exact M.equiv_D hQ.1 hQ.2.2.1 hQ.2.2.2.1 Ψ hΨ hΨL hΨu hQ.2.2.2.2.1
    (hQ.2.2.2.2.2.trans card_suzD.symm)

theorem suz_K₀_data {G : Type} [Group G] {L K : Subgroup G} {u : G} (hQ : SuzPair G L K u)
    (Ψ : ↥L →* Equiv.Perm (Fin 1782)) (hΨ : Function.Injective Ψ) (hΨL : ∀ x, Ψ x ∈ suzM)
    (hΨu : Ψ ⟨u, hQ.1⟩ = suzInv 0) :
    (K.subgroupOf L).map Ψ ≤ invE 0 ∧ Group.IsPerfect ((K.subgroupOf L).map Ψ) ∧
      Nat.card ((K.subgroupOf L).map Ψ) = 20160 := by
  have hperf : Group.IsPerfect (K.subgroupOf L) :=
    isPerfect_subgroupOf_of_le hQ.2.2.1 hQ.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    refine mem_invE_zero.2 ⟨hΨL k, ?_⟩
    rw [← hΨu, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  · have := hperf
    exact Group.IsPerfect.map _
  · rw [Subgroup.card_map_of_injective hΨ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.2.2.1).toEquiv, hQ.2.2.2.2.2]

theorem suz_twoAdic_centralizer_L {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hQ : SuzPair G L K u) (Ψ : ↥L →* Equiv.Perm (Fin 1782)) (hΨ : Function.Injective Ψ)
    (hΨL : ∀ x, Ψ x ∈ suzM) (hΨu : Ψ ⟨u, hQ.1⟩ = suzInv 0) :
    twoAdic (Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2 := by
  obtain ⟨hE, hperf, hcard⟩ := suz_K₀_data hQ Ψ hΨ hΨL hΨu
  have h1 := suz_twoAdic_centralizer_T hE hperf hcard
  have h2 : (Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)).map Ψ ≤
      suzT ⊓ Subgroup.centralizer (((K.subgroupOf L).map Ψ : Subgroup (Equiv.Perm (Fin 1782))) :
        Set (Equiv.Perm (Fin 1782))) := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨suzM_le_suzT (hΨL c), Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_iff.1 hc k hk
  have h3 : twoAdic (Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤
      twoAdic (suzT ⊓ Subgroup.centralizer (((K.subgroupOf L).map Ψ :
        Subgroup (Equiv.Perm (Fin 1782))) : Set (Equiv.Perm (Fin 1782)))) :=
    twoAdic_le_of_map_le (H := Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L))
      Ψ hΨ h2
  exact h3.trans h1

theorem suz_twoAdic_autCentralizer {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hQ : SuzPair G L K u) (Ψ : ↥L →* Equiv.Perm (Fin 1782)) (hΨ : Function.Injective Ψ)
    (hΨL : ∀ x, Ψ x ∈ suzM) (hΨR : ∀ y ∈ suzM, ∃ x, Ψ x = y)
    (hΨu : Ψ ⟨u, hQ.1⟩ = suzInv 0) : twoAdic (autCentralizer L K) ≤ 2 := by
  obtain ⟨hE, hperf, hcard⟩ := suz_K₀_data hQ Ψ hΨ hΨL hΨu
  have h1 := suz_twoAdic_centralizer_T hE hperf hcard
  let Ψ' : ↥L →* ↥suzM := Ψ.codRestrict suzM hΨL
  have hbij : Function.Bijective Ψ' := ⟨fun a b h => hΨ (congrArg Subtype.val h), fun y => by
    obtain ⟨x, hx⟩ := hΨR y y.2
    exact ⟨x, Subtype.ext hx⟩⟩
  let ψ : ↥L ≃* ↥suzM := MulEquiv.ofBijective Ψ' hbij
  let κ : ↥suzT ≃* MulAut ↥suzM := MulEquiv.ofBijective suzConjT suzConjT_bijective
  let Θ : MulAut ↥L →* Equiv.Perm (Fin 1782) :=
    suzT.subtype.comp (κ.symm.toMonoidHom.comp (MulAut.congr ψ).toMonoidHom)
  have hΘ : Function.Injective Θ :=
    suzT.subtype_injective.comp (κ.symm.injective.comp (MulAut.congr ψ).injective)
  have h2 : (autCentralizer L K).map Θ ≤
      suzT ⊓ Subgroup.centralizer (((K.subgroupOf L).map Ψ : Subgroup (Equiv.Perm (Fin 1782))) :
        Set (Equiv.Perm (Fin 1782))) := by
    rintro _ ⟨α, hα, rfl⟩
    refine ⟨(κ.symm (MulAut.congr ψ α)).2, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    set τ : ↥suzT := κ.symm (MulAut.congr ψ α) with hτdef
    have hτ : suzConjT τ = MulAut.congr ψ α := κ.apply_symm_apply _
    have h2 := congrArg (fun β : MulAut ↥suzM => ((β (ψ k) : ↥suzM) : Equiv.Perm (Fin 1782))) hτ
    have h3 : α k = k := hα k (Subgroup.mem_subgroupOf.1 hk)
    simp only [suzConjT_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, h3] at h2
    have h5 : (τ : Equiv.Perm (Fin 1782)) * Ψ k * (τ : Equiv.Perm (Fin 1782))⁻¹ = Ψ k := h2
    show Ψ k * (τ : Equiv.Perm (Fin 1782)) = (τ : Equiv.Perm (Fin 1782)) * Ψ k
    calc Ψ k * (τ : Equiv.Perm (Fin 1782))
        = ((τ : Equiv.Perm (Fin 1782)) * Ψ k * (τ : Equiv.Perm (Fin 1782))⁻¹) *
        (τ : Equiv.Perm (Fin 1782)) := by rw [h5]
      _ = (τ : Equiv.Perm (Fin 1782)) * Ψ k := by group
  have h3 : twoAdic (autCentralizer L K) ≤
      twoAdic (suzT ⊓ Subgroup.centralizer (((K.subgroupOf L).map Ψ :
        Subgroup (Equiv.Perm (Fin 1782))) : Set (Equiv.Perm (Fin 1782)))) :=
    twoAdic_le_of_map_le (H := autCentralizer L K) Θ hΘ h2
  exact h3.trans h1

theorem solomonLocal_suz {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .Suz) (hQ : SuzPair G L K u) : SolomonLocal L K u := by
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := suz_model hL hQ
  obtain ⟨eK⟩ := suz_K_equiv hQ Ψ hΨ hΨL hΨu
  obtain ⟨f⟩ := suz_equiv_of_isSporadic hL
  have hKL := hQ.2.2.1
  have hcardK : Nat.card (K.subgroupOf L) = 20160 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hQ.2.2.2.2.2
  let eK' : ↥(K.subgroupOf L) ≃* ↥suzD := (Subgroup.subgroupOfEquivOfLe hKL).trans eK
  have hquasi : CFSG.Open.IsQuasisimple ↥(K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv' eK'.symm (isQuasisimple_of_simple suzD_simple suzD_noncomm)
  have hu2 : orderOf (⟨u, hQ.1⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk, hQ.2.1]
  have huC : (⟨u, hQ.1⟩ : ↥L) ∈ Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  have huniq : ∀ t : ↥L, orderOf t = 2 →
      t ∈ Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) →
      ∀ K'' : Subgroup ↥L, K'' ≤ Subgroup.centralizer ({t} : Set ↥L) → Group.IsPerfect K'' →
        Nat.card K'' = Nat.card (K.subgroupOf L) → K'' = K.subgroupOf L := by
    intro t ht2 htC K'' hK'' hperf'' hcard''
    have hKt : K.subgroupOf L ≤ Subgroup.centralizer ({t} : Set ↥L) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 htC k hk
    have hdvd : 20160 ∣ Nat.card (Subgroup.centralizer ({t} : Set ↥L)) := by
      have := Subgroup.card_dvd_of_le hKt
      rwa [hcardK] at this
    obtain ⟨ζ⟩ := suz_centralizer_equiv_zero f t ht2 hdvd
    have hq := suz_quot2Data.comp_equiv ζ
    have hperfK : Group.IsPerfect ((K.subgroupOf L).subgroupOf (Subgroup.centralizer
        ({t} : Set ↥L))) :=
      isPerfect_subgroupOf_of_le hKt (isPerfect_subgroupOf_of_le hKL hQ.2.2.2.2.1)
    have hcardK' : Nat.card ((K.subgroupOf L).subgroupOf (Subgroup.centralizer
        ({t} : Set ↥L))) = Nat.card suzD := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKt).toEquiv, hcardK, card_suzD]
    have hcard2 : Nat.card (K''.subgroupOf (Subgroup.centralizer ({t} : Set ↥L))) =
        Nat.card suzD := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'').toEquiv, hcard'', hcardK, card_suzD]
    have heq := hq.eq_of_perfect hperfK hcardK' (isPerfect_subgroupOf_of_le hK'' hperf'')
      hcard2
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hK'', inf_eq_left.2 hKt] at heq
    exact heq
  have hcent : twoAdic (Subgroup.centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) <
      twoAdic (K.subgroupOf L) := by
    have h1 := suz_twoAdic_centralizer_L hQ Ψ hΨ hΨL hΨu
    have h2 : twoAdic (K.subgroupOf L) = 6 := by
      unfold twoAdic
      rw [hcardK, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num]
      exact factorization_two_pow_mul 6 (by norm_num) (by norm_num)
    omega
  exact
  { simpleL := suz_isSimpleGroup_of_isSporadic hL
    nonabelianL := suz_exists_not_commute hL
    u_order := hQ.2.1
    u_mem := hQ.1
    K_le := hKL
    u_mem_centralizer_K := Subgroup.mem_centralizer_iff.2 fun k hk => hQ.2.2.2.1 k hk
    standard_in_L := standard_of_unique hquasi hu2 huC huniq hcent
    autCentralizer_two := suz_twoAdic_autCentralizer hQ Ψ hΨ hΨL hΨR hΨu }

end Suz

end CFSG.EvenSporadicStandard.Solomon78
