module

public import CFSG.GH74.Uniqueness.CorZD
public import CFSG.GH74.Uniqueness.Lemma313
public import CFSG.GH74.Uniqueness.Prop36

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

@[expose] def ZDInduction (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (Z' : Set Y) (M' : Subgroup Y),
    IsInvariantInvolutionSet Z' → Subgroup.closure Z' = ⊤ → IsProductDisconnected Z' M' →
      ZDConclusion Y Z' M'

structure ZDSetup (X : Type) [Group X] [Finite X] (Z : Set X) (M : Subgroup X) : Prop where
  invariant : IsInvariantInvolutionSet Z
  gen : Subgroup.closure Z = ⊤
  prodDisc : IsProductDisconnected Z M
  ih : ZDInduction (Nat.card X)
  counterexample : ¬ ZDConclusion X Z M

section Setup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.two_le_twoRank (S : ZDSetup X Z M) : 2 ≤ Open.twoRank X := by
  by_contra hlt
  exact S.counterexample (Or.inl (by omega))

theorem ZDSetup.exists_mem_not_mem (S : ZDSetup X Z M) : ∃ t ∈ Z, t ∉ M :=
  S.prodDisc.exists_mem_not_mem S.invariant

theorem ZDSetup.exists_mem_inter (S : ZDSetup X Z M) : ∃ z ∈ Z, z ∈ M := by
  obtain ⟨z, hz, hzM⟩ := S.prodDisc.2.1
  exact ⟨z, hz, hzM⟩

theorem ZDSetup.exists_commuting_ne (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) :
    ∃ y ∈ Z, y ≠ z ∧ y * z = z * y :=
  S.prodDisc.exists_commuting_ne S.invariant S.gen S.two_le_twoRank hz

theorem ZDSetup.not_isZStarIn (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    ¬ IsZStarIn M z :=
  S.prodDisc.not_isZStarIn S.invariant S.gen S.two_le_twoRank hz hzM

theorem ZDSetup.two_le_pRank_zHull (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    2 ≤ Open.pRank 2 (zHull Z M) :=
  S.prodDisc.two_le_pRank_zHull S.invariant S.gen S.two_le_twoRank hz hzM

theorem ZDSetup.odd_zNum (S : ZDSetup X Z M) : Odd (zNum Z M) := by
  obtain ⟨t, ht, htM⟩ := S.exists_mem_not_mem
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  exact S.prodDisc.odd_zNum S.invariant ht htM hz hzM

theorem ZDSetup.one_lt_card_inter_centralizer (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z) :
    1 < Nat.card ↥(Z ∩ ((centralizer ({z} : Set X) : Subgroup X) : Set X)) :=
  S.prodDisc.one_lt_card_inter_centralizer S.invariant S.gen S.two_le_twoRank hz

theorem ZDSetup.lemma313 (S : ZDSetup X Z M) {Y : Subgroup X} (hY : Odd (Nat.card Y))
    (hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer (Y : Set X)))) {s : X} (hs : s ∈ Z)
    (hsY : s ∈ normalizer (Y : Set X)) {β : Subgroup X} (hβ : β ∈ omega M)
    (hsβ : conjugate β s = β) : Y ≤ β :=
  S.prodDisc.lemma313_le S.invariant hY hrank hs hsY hβ hsβ

omit [Finite X] in
theorem le_normalizer_zHull (hZ : IsInvariantInvolutionSet Z) (H : Subgroup X) :
    H ≤ normalizer (zHull Z H : Set X) := by
  have hmap : ∀ h ∈ H, ∀ x ∈ zHull Z H, h⁻¹ * x * h ∈ zHull Z H := by
    intro h hh x hx
    have : zHull Z H ≤ (zHull Z H).comap (MulAut.conj h⁻¹).toMonoidHom := by
      rw [zHull, Subgroup.closure_le]
      rintro y ⟨hyZ, hyH⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (MulAut.conj h⁻¹).toMonoidHom y = h⁻¹ * y * h := by simp
      rw [e]
      exact Subgroup.subset_closure ⟨hZ.2 y hyZ h,
        H.mul_mem (H.mul_mem (H.inv_mem hh) hyH) hh⟩
    simpa using this hx
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := hmap h⁻¹ (H.inv_mem hh) x hx
    simpa using this
  · intro hx
    have := hmap h hh _ hx
    simpa [mul_assoc] using this

theorem ZDSetup.zdConclusion_zHull (S : ZDSetup X Z M) {H : Subgroup X} (hH : H ≠ ⊤)
    (hHM : ¬ H ≤ M) (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty) :
    ZDConclusion ↥(zHull Z H) {l | (l : X) ∈ Z} (M.comap (zHull Z H).subtype) := by
  obtain ⟨z, hz, hzHM⟩ := hne
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hzHM).1
  have hzM : z ∈ M := (Subgroup.mem_inf.mp hzHM).2
  have hLH : zHull Z H ≤ H := (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, hzH⟩
  have hLtop : zHull Z H ≠ ⊤ := fun h => hH (top_le_iff.mp (h ▸ hLH))
  have hlt : Nat.card (zHull Z H) < Nat.card X := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq => hLtop
      ((Subgroup.card_eq_iff_eq_top _).mp heq)
  have hLM : ¬ zHull Z H ≤ M := by
    intro hLM
    have hnorm : normalizer (zHull Z H : Set X) ≤ M := S.prodDisc.normalizer_le hLM hz hzL
    exact hHM ((le_normalizer_zHull S.invariant H).trans hnorm)
  have hpd := S.prodDisc.restrict_of_mem hz hzL hzM hLM
  have hinv := S.invariant.restrict (zHull Z H)
  have hgen : Subgroup.closure {l : zHull Z H | (l : X) ∈ Z} = ⊤ := by
    have e : {l : zHull Z H | (l : X) ∈ Z} =
        (Subtype.val : zHull Z H → X) ⁻¹' (Z ∩ (H : Set X)) := by
      ext l
      exact ⟨fun hl => ⟨hl, hLH l.2⟩, fun hl => hl.1⟩
    rw [e]
    exact Subgroup.closure_closure_coe_preimage
  exact S.ih (zHull Z H) hlt _ _ hinv hgen hpd

end Setup

theorem S_ZD_gen_of_no_setup
    (H : ∀ (X : Type) [Group X] [Finite X] (Z : Set X) (M : Subgroup X), ZDSetup X Z M → False) :
    S_ZD_gen := by
  suffices key : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], Nat.card X = n →
      ∀ (Z : Set X) (M : Subgroup X), IsInvariantInvolutionSet Z → Subgroup.closure Z = ⊤ →
        IsProductDisconnected Z M → ZDConclusion X Z M by
    intro X _ _ Z M hZ hgen hpd
    exact key _ X rfl Z M hZ hgen hpd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ hn Z M hZ hgen hpd
    by_contra hfail
    exact H X Z M ⟨hZ, hgen, hpd, fun Y _ _ hlt Z' M' hZ' hgen' hpd' =>
      ih (Nat.card Y) (hn ▸ hlt) Y rfl Z' M' hZ' hgen' hpd', hfail⟩

theorem S_ZD_gen_iff_no_setup : S_ZD_gen ↔
    ∀ (X : Type) [Group X] [Finite X] (Z : Set X) (M : Subgroup X), ZDSetup X Z M → False :=
  ⟨fun h X _ _ Z M S => S.counterexample (h X Z M S.invariant S.gen S.prodDisc),
    S_ZD_gen_of_no_setup⟩

theorem S_ZD_of_no_setup
    (H : ∀ (X : Type) [Group X] [Finite X] (Z : Set X) (M : Subgroup X), ZDSetup X Z M → False) :
    S_ZD :=
  S_ZD_of_S_ZD_gen (S_ZD_gen_of_no_setup H)

theorem S_CorZD_of_no_setup
    (H : ∀ (X : Type) [Group X] [Finite X] (Z : Set X) (M : Subgroup X), ZDSetup X Z M → False) :
    S_CorZD :=
  S_CorZD_of_S_ZD_gen (S_ZD_gen_of_no_setup H)

end CFSG.GH74.Uniqueness
