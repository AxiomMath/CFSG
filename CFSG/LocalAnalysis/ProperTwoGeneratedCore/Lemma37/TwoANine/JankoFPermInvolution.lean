module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFPerm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF

open Equiv Subgroup Janko

theorem card_centralizer_tbar :
    Nat.card (centralizer ({tbar} : Set (alternatingGroup (Fin 9)))) = 192 := by
  have h := CFSG.GH74.GLS.Layer3.card_centralizer_alt_mul_two tbar (swap 1 2)
    (Perm.sign_swap (by decide)) (by decide)
  have h384 : Nat.card (centralizer ({(tbar : Perm (Fin 9))} : Set (Perm (Fin 9)))) = 384 := by
    rw [Perm.nat_card_centralizer, cycleType_tbar, Fintype.card_fin]
    decide
  omega

theorem eq_zero_of_tbar_apply_eq : ∀ x : Fin 9, (tbar : Perm (Fin 9)) x = x → x = 0 := by
  decide

theorem card_support_tbar : (tbar : Perm (Fin 9)).support.card = 8 := by
  decide

theorem apply_tbar_apply {g : alternatingGroup (Fin 9)}
    (hg : g ∈ centralizer ({tbar} : Set (alternatingGroup (Fin 9)))) (x : Fin 9) :
    (g : Perm (Fin 9)) ((tbar : Perm (Fin 9)) x) =
      (tbar : Perm (Fin 9)) ((g : Perm (Fin 9)) x) := by
  have h := congrArg (fun k : alternatingGroup (Fin 9) => (k : Perm (Fin 9)) x)
    (mem_centralizer_singleton_iff.mp hg)
  simpa only [Subgroup.coe_mul, Perm.mul_apply] using h

theorem Fbar_inf_centralizer_tbar_eq :
    Fbar ⊓ centralizer ({tbar} : Set (alternatingGroup (Fin 9))) =
      (MulAction.stabilizer (centralizer ({tbar} : Set (alternatingGroup (Fin 9)))) (1 : Fin 9)).map
        (centralizer ({tbar} : Set (alternatingGroup (Fin 9)))).subtype := by
  ext g
  constructor
  · rintro ⟨hgF, hgC⟩
    exact ⟨⟨g, hgC⟩, MulAction.mem_stabilizer_iff.mpr (mem_Fbar_iff.mp hgF).2.1, rfl⟩
  · rintro ⟨⟨g, hgC⟩, hg1, rfl⟩
    have hg1' : (g : Perm (Fin 9)) 1 = 1 := MulAction.mem_stabilizer_iff.mp hg1
    show g ∈ Fbar ⊓ centralizer ({tbar} : Set (alternatingGroup (Fin 9)))
    refine ⟨mem_Fbar_iff.mpr ⟨?_, hg1', ?_⟩, hgC⟩
    · refine eq_zero_of_tbar_apply_eq _ ?_
      rw [← apply_tbar_apply hgC 0]
      rfl
    · have h := apply_tbar_apply hgC 1
      rw [hg1'] at h
      exact h

theorem card_Fbar_inf_centralizer_tbar :
    Nat.card (Fbar ⊓ centralizer ({tbar} : Set (alternatingGroup (Fin 9))) : Subgroup _) = 24 := by
  set C := centralizer ({tbar} : Set (alternatingGroup (Fin 9))) with hCdef
  have hstab : 24 ≤ Nat.card (MulAction.stabilizer C (1 : Fin 9)) := by
    have h := (MulAction.stabilizer C (1 : Fin 9)).card_mul_index
    rw [MulAction.index_stabilizer, card_centralizer_tbar] at h
    have horb : (MulAction.orbit C (1 : Fin 9)).ncard ≤
        ((tbar : Perm (Fin 9)).support : Set (Fin 9)).ncard := by
      refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
      rintro _ ⟨g, rfl⟩
      rw [Finset.mem_coe, Perm.mem_support]
      show (tbar : Perm (Fin 9)) (((g : alternatingGroup (Fin 9)) : Perm (Fin 9)) 1) ≠
        ((g : alternatingGroup (Fin 9)) : Perm (Fin 9)) 1
      rw [← apply_tbar_apply g.2 1]
      intro h
      exact absurd (((g : alternatingGroup (Fin 9)) : Perm (Fin 9)).injective h) (by decide)
    rw [Set.ncard_coe_finset, card_support_tbar] at horb
    by_contra hlt
    have : Nat.card (MulAction.stabilizer C (1 : Fin 9)) * (MulAction.orbit C (1 : Fin 9)).ncard
      ≤ 23 * 8 := Nat.mul_le_mul (by omega) horb
    omega
  have hW : Nat.card (Fbar ⊓ C : Subgroup _) = Nat.card (MulAction.stabilizer C (1 : Fin 9)) := by
    rw [hCdef, Fbar_inf_centralizer_tbar_eq,
      card_map_of_injective (centralizer _).subtype_injective]
  have h360 : Nat.card (Fbar ⊓ C : Subgroup _) ∣ 360 := card_Fbar ▸ card_dvd_of_le inf_le_left
  have h192 : Nat.card (Fbar ⊓ C : Subgroup _) ∣ 192 :=
    card_centralizer_tbar ▸ card_dvd_of_le inf_le_right
  have h24 : Nat.card (Fbar ⊓ C : Subgroup _) ∣ 24 := by
    have := Nat.dvd_gcd h360 h192
    rwa [show Nat.gcd 360 192 = 24 by norm_num] at this
  have := Nat.le_of_dvd (by norm_num) h24
  omega

theorem commute_tbar_sbar₂ : Commute tbar sbar₂ :=
  Subtype.ext (show (tbar : Perm (Fin 9)) * sbar₂ = (sbar₂ : Perm (Fin 9)) * tbar by decide)

theorem commute_tbar_ybar : Commute tbar ybar :=
  Subtype.ext (show (tbar : Perm (Fin 9)) * ybar = (ybar : Perm (Fin 9)) * tbar by decide)

@[expose] def wbar : alternatingGroup (Fin 9) :=
  ⟨swap 3 4 * swap 4 8 * swap 6 7 * swap 7 5, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem wbar_mem_Fbar : wbar ∈ Fbar :=
  mem_Fbar_iff.mpr (by decide)

theorem commute_tbar_wbar : Commute tbar wbar :=
  Subtype.ext (show (tbar : Perm (Fin 9)) * wbar = (wbar : Perm (Fin 9)) * tbar by decide)

theorem orderOf_wbar : orderOf wbar = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (Subtype.ext (show (wbar : Perm (Fin 9)) ^ 3 = 1 by decide))
    (fun h => absurd (congrArg (fun g : alternatingGroup (Fin 9) => (g : Perm (Fin 9)) 3) h)
      (by decide))

theorem conj_wbar_sbar₂_notMem : wbar * sbar₂ * wbar⁻¹ ∉ zpowers sbar₂ := by
  intro h
  have hc : wbar * sbar₂ * wbar⁻¹ ∈ centralizer ({sbar₂} : Set (alternatingGroup (Fin 9))) :=
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) h
  rw [mem_centralizer_singleton_iff] at hc
  have hc' := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hc'
  exact absurd hc' (by decide)

@[expose] def hbar : alternatingGroup (Fin 9) :=
  ⟨swap 0 8 * swap 8 3 * swap 3 7 * swap 7 1 * swap 1 4 * swap 2 5,
    Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem hbar_conj_tbar : hbar * tbar * hbar⁻¹ = aNineSylowGenA * aNineSylowGenC :=
  Subtype.ext (show (hbar : Perm (Fin 9)) * tbar * (hbar : Perm (Fin 9))⁻¹ =
    (aNineSylowGenA : Perm (Fin 9)) * aNineSylowGenC by decide)

theorem hbar_conj_ybar : hbar * ybar * hbar⁻¹ = aNineSylowGenB :=
  Subtype.ext (show (hbar : Perm (Fin 9)) * ybar * (hbar : Perm (Fin 9))⁻¹ =
    (aNineSylowGenB : Perm (Fin 9)) by decide)

theorem cycleType_ybar : (ybar : Perm (Fin 9)).cycleType = {2, 2} := by
  rw [← multiset_replicate_two_two, cycleType_eq_replicate_iff_of_sq_eq_one (by decide)]
  decide

theorem cycleType_tbar_mul_ℓbar : ((tbar * ℓbar : alternatingGroup (Fin 9)) :
    Perm (Fin 9)).cycleType = {2, 2} := by
  rw [Subgroup.coe_mul, ← multiset_replicate_two_two,
    cycleType_eq_replicate_iff_of_sq_eq_one (by decide)]
  decide

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF
