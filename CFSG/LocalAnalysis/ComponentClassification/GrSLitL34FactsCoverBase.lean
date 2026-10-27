
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
import all CFSG.LieType.Multipliers.L34
public import CFSG.LieType.Multipliers.L34

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable Subgroup
open scoped commutatorElement

noncomputable abbrev cv (w : List (Fin 2 × Bool)) : Cover := PresentedGroup.mk _ (FreeGroup.mk w)

structure CoverParts : Prop where
  invs : invsOK 42 #[aST, bST] #[invTab 42 aST, invTab 42 bST] = true
  relsOK : ∀ r ∈ rels, abTab r = idTab 42
  coverWsOK : ∀ r ∈ coverWs, abTab r = idTab 42
  zOne : abTab zOne = idTab 42
  zTwo : abTab zTwo = idTab 42
  zThree : abTab zThree = idTab 42
  bne : bST ≠ idTab 42
  gen₁ : abTab (genABWords.getD 0 []) = g₁T
  gen₂ : abTab (genABWords.getD 1 []) = g₂T
  gen₃ : abTab (genABWords.getD 2 []) = g₃T
  autU : abTab uAU = conjTab 42 r₄T r₄T aST ∧ abTab uBU = conjTab 42 r₄T r₄T bST
  autF : abTab uAF = conjTab 42 r₂T r₂T aST ∧ abTab uBF = conjTab 42 r₂T r₂T bST
  autG : abTab uAG = conjTab 42 r₃T r₃T aST ∧ abTab uBG = conjTab 42 r₃T r₃T bST
  tw : ∀ k < 64, abTab (tw k) = wordTab (tg k) ∧
    found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs) (enumBFS 42 (wordTabs wT₀) 64).tabs
      (wordTab (tg k)) = true
  distinct : ∀ k < 64, ∀ l < k, wordTab (tg k) ≠ wordTab (tg l)
  specs : ∀ s ∈ coverSpecs, cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  invols : ∀ k < 64, ((comp 42 (wordTab (tg k)) (wordTab (tg k)) == idTab 42) =
    (k == 0 || (sqData.map (·.1)).contains k))
  r₄norm : ∀ k < 64, found (indexOf (enumBFS 42 (wordTabs wT₀) 64).tabs)
    (enumBFS 42 (wordTabs wT₀) 64).tabs (conjTab 42 r₄T r₄T (wordTab (tg k))) = true
  q8 : ∀ k < 64, ((comp 42 (wordTab (tg k)) r₄T == comp 42 r₄T (wordTab (tg k))) =
    q8Idx.contains k)
  count8 : countBelow 64 (fun k => comp 42 (wordTab (tg k))
    (conjTab 42 r₄T r₄T (wordTab (tg k))) == idTab 42) = 8
  witF : witnessOK witnessF r₂T = true
  witG : witnessOK witnessG r₃T = true
  witU : witnessOK witnessU r₄T = true

theorem cv_append (u v : List (Fin 2 × Bool)) : cv (u ++ v) = cv u * cv v := by
  rw [cv, cv, cv, ← FreeGroup.mul_mk, map_mul]

theorem cv_invRev (u : List (Fin 2 × Bool)) : cv (FreeGroup.invRev u) = (cv u)⁻¹ := by
  rw [cv, cv, ← FreeGroup.inv_mk, map_inv]

theorem cv_wpow (u : List (Fin 2 × Bool)) (k : ℕ) : cv (wpow u k) = cv u ^ k := by
  rw [cv, cv, mk_wpow, map_pow]

theorem cv_eq_one {w : List (Fin 2 × Bool)} (h : w ∈ coverWs) : cv w = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem h)

@[expose] def aS : Equiv.Perm (Fin 42) := wordPerm wa

@[expose] def bS : Equiv.Perm (Fin 42) := wordPerm wb

@[expose] def genAB (i : Fin 2) : Equiv.Perm (Fin 42) := if i = 0 then aS else bS

@[expose] def abPerm (w : List (Fin 2 × Bool)) : Equiv.Perm (Fin 42) :=
  FreeGroup.lift genAB (FreeGroup.mk w)

theorem tabRep_aS : TabRep aST aS := tabRep_wordTab wa

theorem tabRep_bS : TabRep bST bS := tabRep_wordTab wb

theorem lift_genAB_single (i : Fin 2) (b : Bool) :
    FreeGroup.lift genAB (FreeGroup.mk [(i, b)]) = if b then genAB i else (genAB i)⁻¹ := by
  cases b
  · show FreeGroup.lift genAB (FreeGroup.of i)⁻¹ = _
    rw [map_inv, FreeGroup.lift_apply_of]
    rfl
  · show FreeGroup.lift genAB (FreeGroup.of i) = _
    rw [FreeGroup.lift_apply_of]
    rfl

theorem lift_genAB_mem_S (f : FreeGroup (Fin 2)) : FreeGroup.lift genAB f ∈ S := by
  induction f using FreeGroup.induction_on with
  | one => rw [map_one]; exact S.one_mem
  | of i =>
    rw [FreeGroup.lift_apply_of]
    unfold genAB
    split_ifs
    · exact wordPerm_mem wa
    · exact wordPerm_mem wb
  | inv_of i ih => rw [map_inv]; exact S.inv_mem ih
  | mul x y hx hy => rw [map_mul]; exact S.mul_mem hx hy

theorem abPerm_mem_S (w : List (Fin 2 × Bool)) : abPerm w ∈ S := lift_genAB_mem_S _

theorem bFive_eq : bFive = wpow [(1, true)] 5 := by decide

theorem cv_b_pow_five : cv [(1, true)] ^ 5 = 1 := by
  rw [← cv_wpow, ← bFive_eq]
  exact cv_eq_one (List.mem_append_right _ (by simp [extraWs]))

section Lift

variable {E Q : Type*} [Group E] [Group Q]

theorem eq_of_mem_commutator_of_central {F : Type*} [Group F] (q : E →* Q)
    (hker : q.ker ≤ center E) (φ φ' : F →* E) (h : q.comp φ = q.comp φ') {x : F}
    (hx : x ∈ commutator F) : φ x = φ' x := by
  have hc : ∀ y, (φ y)⁻¹ * φ' y ∈ center E := fun y => hker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, h, MonoidHom.comp_apply,
      inv_mul_cancel]
  have hle : commutator F ≤ MonoidHom.eqLocus φ φ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change φ ⁅a, b⁆ = φ' ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha : φ' a = φ a * ((φ a)⁻¹ * φ' a) := by group
    have hb : φ' b = φ b * ((φ b)⁻¹ * φ' b) := by group
    rw [ha, hb, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc a) (hc b)]
  exact hle hx

theorem hom_ext_of_central {F : Type*} [Group F] (hF : commutator F = ⊤) (q : E →* Q)
    (hker : q.ker ≤ center E) {φ φ' : F →* E} (h : q.comp φ = q.comp φ') : φ = φ' :=
  MonoidHom.ext fun _ => eq_of_mem_commutator_of_central q hker φ φ' h (by rw [hF]; trivial)

theorem inv_cons_mem_coverWs (i : Fin 2) : (i, false) :: commWords (coverPairs i) ∈ coverWs :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))

end Lift

section Kernel

private theorem zHat_eq_cv (w : List (Fin 2 × Bool)) :
    zHat w = cv w := rfl

noncomputable abbrev z₁ : Cover := cv zOne

noncomputable abbrev z₂ : Cover := cv zTwo

noncomputable abbrev z₃ : Cover := cv zThree

theorem z₁_mem_center : z₁ ∈ center Cover := by
  have h := ker_piX_le_center (ker_pSL_le_ker_piX zOne_mem)
  rwa [zHat_eq_cv] at h

theorem z₂_mem_center : z₂ ∈ center Cover := by
  have h := ker_piX_le_center (ker_pSL_le_ker_piX zTwo_mem)
  rwa [zHat_eq_cv] at h

theorem z₃_mem_center : z₃ ∈ center Cover := by
  have h := ker_piX_le_center zThree_mem
  rwa [zHat_eq_cv] at h

theorem z₁_pow : z₁ ^ 4 = 1 := by
  have h := zOne_pow
  rwa [zHat_eq_cv] at h

theorem z₂_pow : z₂ ^ 4 = 1 := by
  have h := zTwo_pow
  rwa [zHat_eq_cv] at h

theorem z₃_pow : z₃ ^ 3 = 1 := by
  have h := zThree_pow
  rwa [zHat_eq_cv] at h

private abbrev Z443 : Type :=
  Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 3)

@[expose] noncomputable def zHom : Multiplicative (ZMod 4) ×
    Multiplicative (ZMod 4) × Multiplicative (ZMod 3) →* Cover :=
  (powHom z₁ 4 z₁_pow).noncommCoprod ((powHom z₂ 4 z₂_pow).noncommCoprod
    (powHom z₃ 3 z₃_pow) fun a b => by
      simp only [powHom_apply]
      exact Commute.pow_pow (mem_center_iff.mp z₃_mem_center z₂) _ _)
    fun a b => by
      exact Commute.symm (mem_center_iff.mp (Subgroup.pow_mem _ z₁_mem_center _) _)

theorem zHom_apply (d : Multiplicative (ZMod 4) ×
    Multiplicative (ZMod 4) × Multiplicative (ZMod 3)) :
    zHom d = z₁ ^ d.1.toAdd.val * (z₂ ^ d.2.1.toAdd.val * z₃ ^ d.2.2.toAdd.val) := rfl

private theorem m3_sq : ∀ a : Multiplicative (ZMod 3), a * a = 1 → a = 1 := by decide

private theorem m4_cube : ∀ b : Multiplicative (ZMod 4), b * b * b = 1 → b = 1 := by decide

private theorem m3_ne_one : ∀ a : Multiplicative (ZMod 3), a ≠ 1 →
    a = Multiplicative.ofAdd 1 ∨ a = Multiplicative.ofAdd 2 := by
  decide

private theorem m4m4_sq : ∀ b c : Multiplicative (ZMod 4), ¬(b = 1 ∧ c = 1) → b * b = 1 →
    c * c = 1 → b = Multiplicative.ofAdd 2 ∧ c = 1 ∨ b = 1 ∧ c = Multiplicative.ofAdd 2 ∨
      b = Multiplicative.ofAdd 2 ∧ c = Multiplicative.ofAdd 2 := by
  decide

private theorem z443_prime (d : Z443) (hd : d ≠ 1) (h : d * d = 1 ∨ d * d * d = 1) :
    d = (Multiplicative.ofAdd 2, 1, 1) ∨ d = (1, Multiplicative.ofAdd 2, 1) ∨
      d = (Multiplicative.ofAdd 2, Multiplicative.ofAdd 2, 1) ∨
      d = (1, 1, Multiplicative.ofAdd 1) ∨ d = (1, 1, Multiplicative.ofAdd 2) := by
  obtain ⟨b, c, a⟩ := d
  rcases h with h | h
  · simp only [Prod.mk_mul_mk, Prod.mk_eq_one] at h
    obtain rfl := m3_sq a h.2.2
    have hbc : ¬(b = 1 ∧ c = 1) := fun ⟨hb, hc⟩ => hd (by rw [hb, hc]; rfl)
    rcases m4m4_sq b c hbc h.1 h.2.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · simp only [Prod.mk_mul_mk, Prod.mk_eq_one] at h
    obtain rfl := m4_cube b h.1
    obtain rfl := m4_cube c h.2.1
    have ha : a ≠ 1 := fun ha => hd (by rw [ha]; rfl)
    rcases m3_ne_one a ha with rfl | rfl <;> simp

theorem zHom_injective : Function.Injective zHom := by
  refine injective_of_forall_prime_pow _ fun d hd p hp hpd hdp => ?_
  have hcard : Nat.card Z443 = 48 := by simp
  rw [hcard] at hpd
  have h23 : d * d = 1 ∨ d * d * d = 1 := by
    have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
    rw [h48] at hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      subst this
      exact Or.inl (by rw [← sq]; exact hdp)
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      subst this
      exact Or.inr (by rw [← hdp, pow_three, mul_assoc])
  have v1 : (1 : ZMod 3).val = 1 := rfl
  have v2 : (2 : ZMod 3).val = 2 := rfl
  have v4 : (2 : ZMod 4).val = 2 := rfl
  have h1 := zOne_sq_ne_one
  have h2 := zTwo_sq_ne_one
  have h12 := zOne_sq_mul_zTwo_sq_ne_one
  have h3 := zThree_ne_one
  rw [zHat_eq_cv] at h1 h2 h12 h3
  have h3' : z₃ ^ 2 ≠ 1 := by
    intro h
    apply h3
    calc z₃ = z₃ ^ 3 * (z₃ ^ 2)⁻¹ := by group
      _ = 1 := by rw [z₃_pow, h]; group
  rcases z443_prime d hd h23 with rfl | rfl | rfl | rfl | rfl <;>
    simp [zHom_apply, v1, v2, v4] <;> assumption

end Kernel

section Elements

end Elements

section Specs

theorem cv_zword (p q r : ℕ) : cv (zword p q r) = z₁ ^ p * z₂ ^ q * z₃ ^ r := by
  rw [zword, cv_append, cv_append, cv_wpow, cv_wpow, cv_wpow]

end Specs

end CFSG.ComponentClassification.GrSLit.L34Facts
