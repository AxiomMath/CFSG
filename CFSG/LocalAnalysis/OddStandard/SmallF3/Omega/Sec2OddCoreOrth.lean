module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreDim2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem oddCore_oGroup_of_finrank_zero (h : Module.finrank (ZMod 3) V = 0) :
    oddCore (OGroup Q) = ⊥ := by
  haveI : Subsingleton V := Module.finrank_zero_iff.mp h
  haveI : Subsingleton (OGroup Q) :=
    ⟨fun f g => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩
  exact eq_bot_iff.mpr fun x _ => by rw [Subgroup.mem_bot]; exact Subsingleton.elim _ _

theorem card_oGroup_of_finrank_one (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V = 1) : Nat.card (OGroup Q) = 2 := by
  have hQ0 : Q ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (by omega : 0 < Module.finrank (ZMod 3) V)
    have hrad : x ∈ Q.radical := by
      rw [QuadraticMap.mem_radical_iff']
      subst hzero
      exact ⟨rfl, fun y => rfl⟩
    rw [hQ.radical_eq_bot, Submodule.mem_bot] at hrad
    exact hx hrad
  exact TauCeti.QuadraticMap.card_orthogonalGroup_of_finrank_eq_one hQ0 h

theorem oddCore_centralizer_involution_eq_bot (hQ : Q.Nondegenerate) {s : OGroup Q}
    (hs : s * s = 1) (hs1 : s ≠ 1) (hsπ : s ≠ piOrth Q)
    (IH : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
      (R : QuadraticForm (ZMod 3) W), R.Nondegenerate →
        Module.finrank (ZMod 3) W < Module.finrank (ZMod 3) V → oddCore (OGroup R) = ⊥) :
    oddCore ↥(Subgroup.centralizer ({s} : Set (OGroup Q))) = ⊥ := by
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv hQ hs
  have hsum := finrank_fixSp_add_finrank_commSp s
  have hc0 : Module.finrank (ZMod 3) (commSp s) ≠ 0 := fun h0 => hs1 ((invDim_eq_zero_iff hs).mp h0)
  have hcn : Module.finrank (ZMod 3) (commSp s) ≠ Module.finrank (ZMod 3) V :=
    fun h0 => hsπ ((invDim_eq_finrank_iff hs).mp h0)
  have hf : oddCore (OGroup (Q.restrict (fixSp s))) = ⊥ :=
    IH _ _ (nondegenerate_restrict_fixSp hQ hs) (by omega)
  have hc : oddCore (OGroup (Q.restrict (commSp s))) = ⊥ :=
    IH _ _ (nondegenerate_restrict_commSp hQ hs) (by omega)
  exact oddCore_eq_bot_of_mulEquiv e.symm (oddCore_prod_eq_bot hc hf)

theorem exists_three_involutions (hQ : Q.Nondegenerate) (hn : 3 ≤ Module.finrank (ZMod 3) V) :
    ∃ a b : OGroup Q, a * a = 1 ∧ b * b = 1 ∧ (a * b) * (a * b) = 1 ∧ a ≠ 1 ∧ a ≠ piOrth Q ∧
      b ≠ 1 ∧ b ≠ piOrth Q ∧ a * b ≠ 1 ∧ a * b ≠ piOrth Q := by
  obtain ⟨a, haa, hat⟩ := (exists_involution_of_type hQ 1 1).mpr
    ⟨by omega, fun h => absurd h one_ne_zero, fun h => absurd h (by omega)⟩
  have hinv : invDim a = 1 := by simpa only [invType] using congrArg Prod.fst hat
  have hdimc : Module.finrank (ZMod 3) (commSp a) = 1 := hinv
  have hsum := finrank_fixSp_add_finrank_commSp a
  obtain ⟨b', hb'b', hb't⟩ :=
    (exists_involution_of_type (nondegenerate_restrict_fixSp hQ haa) 1 1).mpr
      ⟨by omega, fun h => absurd h one_ne_zero, fun h => absurd h (by omega)⟩
  have hb'dim : invDim b' = 1 := by simpa only [invType] using congrArg Prod.fst hb't
  have hπc1 : piOrth (Q.restrict (commSp a)) ≠ 1 := piOrth_ne_one (by omega)
  have hab : a * blockHom haa (b', 1) = blockHom haa (b', piOrth (Q.restrict (commSp a))) :=
    calc a * blockHom haa (b', 1)
        = blockHom haa (1, piOrth (Q.restrict (commSp a))) * blockHom haa (b', 1) := by
          rw [blockHom_one_piOrth haa]
      _ = blockHom haa ((1, piOrth (Q.restrict (commSp a))) * (b', 1)) := (map_mul _ _ _).symm
      _ = blockHom haa (b', piOrth (Q.restrict (commSp a))) := by simp
  have hbb : blockHom haa (b', 1) * blockHom haa (b', 1) = 1 := by
    rw [← map_mul, show (b', (1 : OGroup (Q.restrict (commSp a)))) * (b', 1) = 1 from
      Prod.ext hb'b' (mul_one 1), map_one]
  have hb1 : blockHom haa (b', 1) ≠ 1 := by
    intro h
    have h' : blockHom haa (b', 1) = blockHom haa (1, 1) := h.trans (map_one (blockHom haa)).symm
    have hb'1 : b' = 1 := congrArg Prod.fst (blockHom_injective haa h')
    have := (invDim_eq_zero_iff hb'b').mpr hb'1
    omega
  have hbπ : blockHom haa (b', 1) ≠ piOrth Q := by
    intro h
    rw [← blockHom_piOrth_piOrth haa] at h
    exact hπc1 (congrArg Prod.snd (blockHom_injective haa h)).symm
  have habab : (a * blockHom haa (b', 1)) * (a * blockHom haa (b', 1)) = 1 := by
    rw [hab, ← map_mul, show (b', piOrth (Q.restrict (commSp a))) *
      (b', piOrth (Q.restrict (commSp a))) = 1 from Prod.ext hb'b' piOrth_mul_self, map_one]
  have hab1 : a * blockHom haa (b', 1) ≠ 1 := by
    intro h
    rw [hab] at h
    have h' : blockHom haa (b', piOrth (Q.restrict (commSp a))) = blockHom haa (1, 1) :=
      h.trans (map_one (blockHom haa)).symm
    have hb'1 : b' = 1 := congrArg Prod.fst (blockHom_injective haa h')
    have := (invDim_eq_zero_iff hb'b').mpr hb'1
    omega
  have habπ : a * blockHom haa (b', 1) ≠ piOrth Q := by
    intro h
    rw [hab, ← blockHom_piOrth_piOrth haa] at h
    have hb'π : b' = piOrth (Q.restrict (fixSp a)) := congrArg Prod.fst (blockHom_injective haa h)
    have := (invDim_eq_finrank_iff hb'b').mpr hb'π
    omega
  refine ⟨a, blockHom haa (b', 1), haa, hbb, habab, ?_, ?_, hb1, hbπ, hab1, habπ⟩
  · intro h
    have := (invDim_eq_zero_iff haa).mpr h
    omega
  · intro h
    have := (invDim_eq_finrank_iff haa).mpr h
    omega

theorem oddCore_oGroup_eq_bot_of_dim_two
    (hdim2 : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
      (R : QuadraticForm (ZMod 3) W), R.Nondegenerate →
        Module.finrank (ZMod 3) W = 2 → oddCore (OGroup R) = ⊥) :
    ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
      (R : QuadraticForm (ZMod 3) W), R.Nondegenerate →
        Module.finrank (ZMod 3) W = n → oddCore (OGroup R) = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ R hR hn
    have IH : ∀ (W' : Type) [AddCommGroup W'] [Module (ZMod 3) W'] [FiniteDimensional (ZMod 3) W']
        (R' : QuadraticForm (ZMod 3) W'), R'.Nondegenerate →
          Module.finrank (ZMod 3) W' < Module.finrank (ZMod 3) W → oddCore (OGroup R') = ⊥ :=
      fun W' _ _ _ R' hR' hlt => ih _ (hn ▸ hlt) W' R' hR' rfl
    by_cases h3 : 3 ≤ n
    · obtain ⟨a, b, haa, hbb, habab, ha1, haπ, hb1, hbπ, hab1, habπ⟩ :=
        exists_three_involutions hR (hn ▸ h3)
      exact oddCore_eq_bot_of_three_involutions haa hbb
        (oddCore_centralizer_involution_eq_bot hR haa ha1 haπ IH)
        (oddCore_centralizer_involution_eq_bot hR hbb hb1 hbπ IH)
        (oddCore_centralizer_involution_eq_bot hR habab hab1 habπ IH)
    · interval_cases n
      · exact oddCore_oGroup_of_finrank_zero hn
      · exact oddCore_eq_bot_of_isPGroup_two (IsPGroup.of_card (n := 1) (by
          rw [card_oGroup_of_finrank_one hR hn]; simp))
      · exact hdim2 W R hR hn

theorem oddCore_oGroup_eq_bot (hQ : Q.Nondegenerate) : oddCore (OGroup Q) = ⊥ :=
  oddCore_oGroup_eq_bot_of_dim_two (fun _ _ _ _ _ hR h2 =>
    oddCore_eq_bot_of_isPGroup_two (isPGroup_two_oGroup_of_finrank_two hR h2)) _ V Q hQ rfl

end CFSG.OddStandard.SmallF3.Omega
