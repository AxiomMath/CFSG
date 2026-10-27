module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma card_fixedPoints_even_involution (f : Equiv.Perm (Fin 7))
    (hf2 : f * f = 1) (hsign : Equiv.Perm.sign f = 1) (hfne : f ≠ 1) :
    Fintype.card (Function.fixedPoints f) = 3 := by
  have hsq : f ^ 2 = 1 := by rw [pow_two, hf2]
  have hct : f.cycleType = Multiset.replicate f.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hsq
  have hk_le : f.cycleType.card ≤ 3 := by
    have h := Equiv.Perm.sum_cycleType_le f
    rw [hct, Multiset.sum_replicate] at h
    simp at h
    omega
  have hk_pos : 1 ≤ f.cycleType.card := by
    have := (Equiv.Perm.card_cycleType_pos (σ := f)).mpr hfne
    omega
  have hsum_k : f.cycleType.sum = f.cycleType.card * 2 := by
    rw [hct, Multiset.sum_replicate]
    simp
  have hsign_eq : (-1 : ℤˣ) ^ (f.cycleType.sum + f.cycleType.card) = 1 := by
    rw [← Equiv.Perm.sign_of_cycleType]
    exact hsign
  have hk_even : Even f.cycleType.card := by
    have h2 : Even (f.cycleType.sum + f.cycleType.card) :=
      (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by norm_num)).mp hsign_eq
    rw [hsum_k] at h2
    obtain ⟨t, ht⟩ := h2
    exact ⟨t - f.cycleType.card, by omega⟩
  have hk : f.cycleType.card = 2 := by
    obtain ⟨s, hs⟩ := hk_even
    omega
  rw [Equiv.Perm.card_fixedPoints]
  have hsum4 : f.cycleType.sum = 4 := by
    rw [hct, hk]
    decide
  rw [hsum4]
  decide

private abbrev FixVec (F : Subgroup (Equiv.Perm (Fin 7))) : Type :=
  {v : Fin 7 → ZMod 2 // ∀ f ∈ F, permVec f v = v}

private abbrev FixEvenVec (F : Subgroup (Equiv.Perm (Fin 7))) : Type :=
  {v : Fin 7 → ZMod 2 // IsEvenVec v ∧ ∀ f ∈ F, permVec f v = v}

private def oddVec (i0 : Fin 7) : Fin 7 → ZMod 2 := Pi.single i0 1

private lemma permVec_add (f : Equiv.Perm (Fin 7)) (v w : Fin 7 → ZMod 2) :
    permVec f (v + w) = permVec f v + permVec f w := by
  ext i
  simp [permVec]

private lemma permVec_eq_self_iff (F : Subgroup (Equiv.Perm (Fin 7)))
    (v : Fin 7 → ZMod 2) :
    (∀ f ∈ F, permVec f v = v) ↔
      ∀ a b : Fin 7, MulAction.orbitRel F (Fin 7) a b → v a = v b := by
  constructor
  · intro hv a b hab
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
    obtain ⟨g, hg⟩ := hab
    have hg' : (g : Equiv.Perm (Fin 7)) b = a := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg
    have hfix := hv (g : Equiv.Perm (Fin 7)) g.2
    have hfun : v ((g : Equiv.Perm (Fin 7)).symm a) = v a :=
      congr_fun hfix a
    have hsymm : (g : Equiv.Perm (Fin 7)).symm a = b := by
      rw [← hg']
      simp
    rw [hsymm] at hfun
    exact hfun.symm
  · intro hv f hf
    ext i
    have hmem : f.symm ∈ F := F.inv_mem hf
    have horb : MulAction.orbitRel F (Fin 7) (f.symm i) i := by
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨⟨f.symm, hmem⟩, ?_⟩
      simp [Subgroup.smul_def, Equiv.Perm.smul_def]
    have := hv (f.symm i) i horb
    simpa [permVec, Function.comp_apply] using this

private noncomputable def fixVecEquivFun (F : Subgroup (Equiv.Perm (Fin 7))) :
    FixVec F ≃ (MulAction.orbitRel.Quotient F (Fin 7) → ZMod 2) where
  toFun v q := v.1 (Quotient.out q)
  invFun w := ⟨fun i => w (Quotient.mk _ i), (permVec_eq_self_iff F _).mpr (by
    intro a b hab
    exact congrArg w (Quotient.sound hab))⟩
  left_inv v := by
    ext i
    show v.1 (Quotient.out (Quotient.mk _ i)) = v.1 i
    have hconst := (permVec_eq_self_iff F v.1).mp v.2
    exact hconst _ _ (Quotient.exact (Quotient.out_eq (Quotient.mk _ i)))
  right_inv w := by
    ext q
    show w (Quotient.mk _ (Quotient.out q)) = w q
    rw [Quotient.out_eq]

private lemma card_fixVec (F : Subgroup (Equiv.Perm (Fin 7))) :
    Nat.card (FixVec F) = 2 ^ Nat.card (MulAction.orbitRel.Quotient F (Fin 7)) := by
  classical
  rw [Nat.card_congr (fixVecEquivFun F), Nat.card_fun]
  have hZ : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hZ]

private lemma card_fixedBy_one (F : Subgroup (Equiv.Perm (Fin 7))) :
    Nat.card (MulAction.fixedBy (Fin 7) (1 : F)) = 7 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun i => by
    simp [MulAction.mem_fixedBy])), Nat.card_fin]

private lemma card_fixedBy_ne_one (F : Subgroup (Equiv.Perm (Fin 7)))
    (hF : F ≤ alternatingGroup (Fin 7)) (h2 : ∀ f ∈ F, f * f = 1)
    (g : F) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (Fin 7) g) = 3 := by
  have hcard : Nat.card (MulAction.fixedBy (Fin 7) g) =
      Nat.card (Function.fixedPoints (g : Equiv.Perm (Fin 7))) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun i => by
      show g • i = i ↔ (g : Equiv.Perm (Fin 7)) i = i
      simp [Subgroup.smul_def, Equiv.Perm.smul_def]))
  rw [hcard, Nat.card_eq_fintype_card]
  exact card_fixedPoints_even_involution (g : Equiv.Perm (Fin 7)) (h2 g g.2)
    (Equiv.Perm.mem_alternatingGroup.mp (hF g.2))
    (fun h => hg (Subtype.ext h))

private lemma burnside_sum_card (F : Subgroup (Equiv.Perm (Fin 7))) [Fintype F]
    (hF : F ≤ alternatingGroup (Fin 7)) (h2 : ∀ f ∈ F, f * f = 1) :
    (∑ g : F, Nat.card (MulAction.fixedBy (Fin 7) g)) = 3 * Fintype.card F + 4 := by
  classical
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset F)
    (fun g => Nat.card (MulAction.fixedBy (Fin 7) g)) (Finset.mem_univ (1 : F))
  rw [← hsplit, card_fixedBy_one F]
  have hthree : (Finset.univ.erase (1 : F)).sum
      (fun g => Nat.card (MulAction.fixedBy (Fin 7) g)) =
      3 * (Fintype.card F - 1) := by
    rw [Finset.sum_const_nat (fun g hg =>
      card_fixedBy_ne_one F hF h2 g (Finset.mem_erase.mp hg).1)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : F)), Finset.card_univ]
    ring
  rw [hthree]
  have hc : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨1⟩
  omega

private lemma burnside (F : Subgroup (Equiv.Perm (Fin 7)))
    (hF : F ≤ alternatingGroup (Fin 7)) (h2 : ∀ f ∈ F, f * f = 1) :
    Nat.card (MulAction.orbitRel.Quotient F (Fin 7)) * Nat.card F =
      3 * Nat.card F + 4 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hsum : (∑ g : F, Nat.card (MulAction.fixedBy (Fin 7) g)) =
      3 * Fintype.card F + 4 := burnside_sum_card F hF h2
  have hsum' : (∑ g : F, Fintype.card (MulAction.fixedBy (Fin 7) g)) =
      3 * Fintype.card F + 4 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro g _
    rw [Nat.card_eq_fintype_card]
  have hbs := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group F (Fin 7)
  rw [hsum'] at hbs
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hbs.symm

private lemma card_dvd_four (F : Subgroup (Equiv.Perm (Fin 7)))
    (hF : F ≤ alternatingGroup (Fin 7)) (h2 : ∀ f ∈ F, f * f = 1) :
    Nat.card F ∣ 4 := by
  have hb := burnside F hF h2
  have h1 : Nat.card F ∣ 3 * Nat.card F + 4 := by
    refine ⟨Nat.card (MulAction.orbitRel.Quotient F (Fin 7)), ?_⟩
    rw [mul_comm (Nat.card F) (Nat.card (MulAction.orbitRel.Quotient F (Fin 7)))]
    exact hb.symm
  have h2dvd : Nat.card F ∣ 3 * Nat.card F := ⟨3, by ring⟩
  have hsub : Nat.card F ∣ (3 * Nat.card F + 4) - 3 * Nat.card F :=
    Nat.dvd_sub h1 h2dvd
  rwa [show (3 * Nat.card F + 4) - 3 * Nat.card F = 4 by omega] at hsub

private lemma exists_fixed_point (F : Subgroup (Equiv.Perm (Fin 7)))
    (hF : F ≤ alternatingGroup (Fin 7)) (h2 : ∀ f ∈ F, f * f = 1) (hne : F ≠ ⊥) :
    ∃ i0 : Fin 7, ∀ f ∈ F, f i0 = i0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hpg : IsPGroup 2 F := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (by simpa using h2 g g.2)
  have hnot : ¬ 2 ∣ Nat.card (Fin 7) := by
    rw [Nat.card_fin]
    norm_num
  obtain ⟨i0, hi0⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card (Fin 7) hnot
  refine ⟨i0, ?_⟩
  intro f hf
  have := hi0 ⟨f, hf⟩
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using this

private lemma sum_oddVec (i0 : Fin 7) : (∑ i, oddVec i0 i) = 1 := by
  show (∑ i, Pi.single i0 (1 : ZMod 2) i) = 1
  rw [Finset.sum_pi_single' i0 1 Finset.univ]
  simp

private lemma isEvenVec_add_oddVec_iff (i0 : Fin 7) (v : Fin 7 → ZMod 2) :
    IsEvenVec (v + oddVec i0) ↔ ¬ IsEvenVec v := by
  unfold IsEvenVec
  have h1 : (∑ i, (v + oddVec i0) i) = (∑ i, v i) + (∑ i, oddVec i0 i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.add_apply]
  rw [h1, sum_oddVec]
  exact (by decide : ∀ x : ZMod 2, x + 1 = 0 ↔ x ≠ 0) _

private lemma permVec_oddVec (F : Subgroup (Equiv.Perm (Fin 7))) (i0 : Fin 7)
    (hi0 : ∀ f ∈ F, f i0 = i0) :
    ∀ f ∈ F, permVec f (oddVec i0) = oddVec i0 := by
  intro f hf
  have hsymm_i0 : f.symm i0 = i0 := (Equiv.symm_apply_eq f).mpr (hi0 f hf).symm
  ext i
  by_cases hi : i = i0
  · subst hi
    simp [oddVec, permVec, hsymm_i0]
  · have hne : f.symm i ≠ i0 := by
      intro h
      apply hi
      have := congrArg f h
      simpa [hi0 f hf] using this
    simp [oddVec, permVec, hi, hne]

private lemma flip_even_card (F : Subgroup (Equiv.Perm (Fin 7))) (i0 : Fin 7)
    (hi0 : ∀ f ∈ F, f i0 = i0) :
    2 * Nat.card (FixEvenVec F) = Nat.card (FixVec F) := by
  classical
  have he_fixed : ∀ f ∈ F, permVec f (oddVec i0) = oddVec i0 :=
    permVec_oddVec F i0 hi0
  let neg : FixVec F → FixVec F := fun v =>
    ⟨v.1 + oddVec i0, by
      intro f hf
      rw [permVec_add, v.2 f hf, he_fixed f hf]⟩
  have neg_invol : Function.Involutive neg := by
    intro v
    apply Subtype.ext
    show (v.1 + oddVec i0) + oddVec i0 = v.1
    funext i
    simp only [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hflip : ∀ v : FixVec F,
      IsEvenVec (neg v).1 ↔ ¬ IsEvenVec v.1 := by
    intro v
    show IsEvenVec (v.1 + oddVec i0) ↔ ¬ IsEvenVec v.1
    exact isEvenVec_add_oddVec_iff i0 v.1
  have card_eq : Fintype.card {v : FixVec F // IsEvenVec v.1} =
      Fintype.card {v : FixVec F // ¬ IsEvenVec v.1} := by
    apply Fintype.card_congr
    exact {
      toFun := fun x => ⟨neg x.1, fun h => ((hflip x.1).mp h) x.2⟩
      invFun := fun x => ⟨neg x.1, (hflip x.1).mpr x.2⟩
      left_inv := fun x => Subtype.ext (neg_invol x.1)
      right_inv := fun x => Subtype.ext (neg_invol x.1) }
  have hcompl := Fintype.card_subtype_compl (fun v : FixVec F => IsEvenVec v.1)
  have hle : Fintype.card {v : FixVec F // IsEvenVec v.1} ≤ Fintype.card (FixVec F) :=
    Fintype.card_subtype_le _
  have h2 : 2 * Fintype.card {v : FixVec F // IsEvenVec v.1} =
      Fintype.card (FixVec F) := by
    rw [hcompl] at card_eq
    omega
  have hequiv : FixEvenVec F ≃ {v : FixVec F // IsEvenVec v.1} :=
    ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun v : Fin 7 → ZMod 2 => ∀ f ∈ F, permVec f v = v)
        (fun v => IsEvenVec v)).trans
      (Equiv.subtypeEquivRight (fun v => and_comm))).symm
  have hcard_even : Nat.card (FixEvenVec F) =
      Fintype.card {v : FixVec F // IsEvenVec v.1} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr hequiv
  rw [hcard_even, Nat.card_eq_fintype_card]
  exact h2

theorem sec4I_card_mul_fixEven_le (F : Subgroup (Equiv.Perm (Fin 7)))
    (hF : F ≤ alternatingGroup (Fin 7)) (h2 : ∀ f ∈ F, f * f = 1) (hne : F ≠ ⊥) :
    Nat.card F * Nat.card {v : Fin 7 → ZMod 2 // IsEvenVec v ∧ ∀ f ∈ F, permVec f v = v} ≤ 32 := by
  classical
  obtain ⟨i0, hi0⟩ := exists_fixed_point F hF h2 hne
  have hb := burnside F hF h2
  have hdvd := card_dvd_four F hF h2
  haveI : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).mpr hne
  have hge : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    have := Fintype.one_lt_card (α := F)
    omega
  have hle4 : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hFixEven := flip_even_card F i0 hi0
  have hFix := card_fixVec F
  change Nat.card F * Nat.card (FixEvenVec F) ≤ 32
  set c := Nat.card F with hcdef
  set o := Nat.card (MulAction.orbitRel.Quotient F (Fin 7)) with hodef
  set E := Nat.card (FixEvenVec F) with hEdef
  have hc_cases : c = 2 ∨ c = 4 := by
    interval_cases c
    · left; rfl
    · exfalso; norm_num at hdvd
    · right; rfl
  rcases hc_cases with hc2 | hc4
  · rw [hc2] at hb ⊢
    have ho : o = 5 := by omega
    rw [ho] at hFix
    rw [hFix] at hFixEven
    norm_num at hFixEven
    omega
  · rw [hc4] at hb ⊢
    have ho : o = 4 := by omega
    rw [ho] at hFix
    rw [hFix] at hFixEven
    norm_num at hFixEven
    omega

end CFSG.OddStandard.SmallF3.Omega
