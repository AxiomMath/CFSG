module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Id2519.HS4

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X3Aut CFSG.QuasithinUnique.A6Facts
open CFSG.QuasithinUnique.A6Facts.Core

set_option maxRecDepth 100000

@[expose] def E8 : List (List Nat) := rep 8

@[expose] def normE8 (g : List Nat) : Bool := E8.all fun e => E8.contains (cmul (cmul g e) (invC g))

@[expose] def actL (g : List Nat) : List (List Nat) := E8.map fun e => cmul (cmul g e) (invC g)

@[expose] def twoPow (g : List Nat) : Bool := cpow g 32 == cid

@[expose] def nrmLit : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 6, 7, 8, 3, 4, 5, 9], [0, 6, 3, 1, 7, 4, 2, 8, 5, 9],
  [0, 6, 3, 2, 8, 5, 1, 7, 4, 9], [9, 2, 1, 3, 7, 8, 6, 4, 5, 0], [9, 2, 1, 6, 4, 5, 3, 7, 8, 0],
  [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], [0, 2, 1, 3, 5, 4, 6, 8, 7, 9], [9, 3, 6, 1, 8, 5, 2, 7, 4, 0],
  [9, 3, 6, 2, 7, 4, 1, 8, 5, 0], [9, 6, 3, 2, 4, 7, 1, 5, 8, 0], [9, 6, 3, 1, 5, 8, 2, 4, 7, 0],
  [0, 3, 6, 2, 5, 8, 1, 4, 7, 9], [0, 3, 6, 1, 4, 7, 2, 5, 8, 9], [9, 1, 2, 6, 5, 4, 3, 8, 7, 0],
  [9, 1, 2, 3, 8, 7, 6, 5, 4, 0], [1, 0, 9, 6, 7, 5, 3, 4, 8, 2], [1, 0, 9, 3, 4, 8, 6, 7, 5, 2],
  [2, 9, 0, 6, 4, 8, 3, 7, 5, 1], [2, 9, 0, 3, 7, 5, 6, 4, 8, 1], [1, 3, 6, 0, 4, 7, 9, 8, 5, 2],
  [1, 3, 6, 9, 8, 5, 0, 4, 7, 2], [2, 0, 9, 3, 5, 7, 6, 8, 4, 1], [2, 0, 9, 6, 8, 4, 3, 5, 7, 1],
  [2, 3, 6, 9, 7, 4, 0, 5, 8, 1], [2, 3, 6, 0, 5, 8, 9, 7, 4, 1], [6, 0, 9, 2, 8, 4, 1, 7, 5, 3],
  [6, 0, 9, 1, 7, 5, 2, 8, 4, 3], [3, 9, 0, 2, 7, 5, 1, 8, 4, 6], [3, 9, 0, 1, 8, 4, 2, 7, 5, 6],
  [1, 9, 0, 3, 8, 4, 6, 5, 7, 2], [1, 9, 0, 6, 5, 7, 3, 8, 4, 2], [2, 6, 3, 0, 8, 5, 9, 4, 7, 1],
  [2, 6, 3, 9, 4, 7, 0, 8, 5, 1], [1, 6, 3, 9, 5, 8, 0, 7, 4, 2], [1, 6, 3, 0, 7, 4, 9, 5, 8, 2],
  [6, 1, 2, 0, 7, 8, 9, 5, 4, 3], [6, 1, 2, 9, 5, 4, 0, 7, 8, 3], [3, 0, 9, 1, 4, 8, 2, 5, 7, 6],
  [3, 0, 9, 2, 5, 7, 1, 4, 8, 6], [3, 1, 2, 9, 8, 7, 0, 4, 5, 6], [3, 1, 2, 0, 4, 5, 9, 8, 7, 6],
  [6, 9, 0, 1, 5, 7, 2, 4, 8, 3], [6, 9, 0, 2, 4, 8, 1, 5, 7, 3], [3, 2, 1, 0, 5, 4, 9, 7, 8, 6],
  [3, 2, 1, 9, 7, 8, 0, 5, 4, 6], [6, 2, 1, 9, 4, 5, 0, 8, 7, 3], [6, 2, 1, 0, 8, 7, 9, 4, 5, 3]]

@[expose] def nrmComplete : Bool := autL.all fun c => !normE8 c || nrmLit.contains c

@[expose] def pairCheck : Bool := nrmLit.all fun g1 => nrmLit.all fun g2 =>
  !(twoPow g1 && twoPow g2 && actL g1 != E8 && actL g2 != E8 && actL g1 != actL g2) ||
    !twoPow (cmul g1 g2)

@[expose] def fixCheck : Bool :=
  nrmLit.all fun g => !twoPow g || 4 ≤ (E8.filter fun e => cmul g e == cmul e g).length

theorem E8_nodup : E8.Nodup := by decide +kernel

theorem E8_length : E8.length = 8 := by decide +kernel

theorem nrmComplete_true : nrmComplete = true := by decide +kernel

theorem pairCheck_true : pairCheck = true := by decide +kernel

theorem fixCheck_true : fixCheck = true := by decide +kernel

theorem rep_eight : ∀ j, j < repsC.length → (rep j).length = 8 → j = 8 := by decide +kernel

theorem cd_length (g : AutA6) : (cd g).length = 10 := by
  simp [cd, code]

theorem cd_pow (g : AutA6) (n : ℕ) : cd (g ^ n) = cpow (cd g) n := by
  induction n with
  | zero =>
    rw [pow_zero, cd_one]
    simp [cpow, cd_length, cid]
  | succ n ih => rw [pow_succ, cd_mul, ih]; rfl

theorem pow_thirtytwo {P : Subgroup AutA6} (hP : IsPGroup 2 ↥P) {g : AutA6} (hg : g ∈ P) :
    g ^ 32 = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have h1 : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : g ^ 1440 = 1 := by
    have := pow_card_eq_one' (G := AutA6) (x := g)
    rwa [card_autA6] at this
  have h3 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  have h4 : orderOf g ∣ 1440 := orderOf_dvd_of_pow_eq_one h2
  rw [hm'] at h4
  have hm5 : m ≤ 5 := by
    by_contra hcon
    have h64 : 2 ^ 6 ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
    have := h64.trans h4
    omega
  rw [← orderOf_dvd_iff_pow_eq_one, hm']
  exact (Nat.pow_dvd_pow 2 hm5)

theorem conj_code (g x : AutA6) :
    cmul (cmul (cd g) (cd x)) (invC (cd g)) = cd (g * x * g⁻¹) := by
  rw [← cd_inv, ← cd_mul, ← cd_mul]

theorem conj_code_eq_iff (g x : AutA6) : cmul (cmul (cd g) (cd x)) (invC (cd g)) = cd x ↔
    g * x = x * g := by
  rw [conj_code]
  constructor
  · intro h
    have h1 := cd_injective h
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  · intro h
    rw [h]
    simp

theorem fixed_code_iff (g x : AutA6) : cmul (cd g) (cd x) = cmul (cd x) (cd g) ↔ g * x = x * g := by
  rw [← cd_mul, ← cd_mul]
  exact ⟨fun h => cd_injective h, fun h => by rw [h]⟩

theorem fixed_ge_four {P E : Subgroup AutA6} (hP : IsPGroup 2 ↥P)
    (hEn : ∀ g ∈ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hsq : ∀ e ∈ E, e * e = 1)
    (h8 : 8 ≤ Nat.card E) :
    4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (P : Set AutA6)) := by
  classical
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hsq (a * b) (E.mul_mem ha hb))
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    rw [mul_inv_rev, ha', hb'] at h1
    exact h1.symm
  have : CFSG.IsElementaryAbelian 2 ↥E :=
    { toIsMulCommutative := IsMulCommutative.of_setLike_mul_comm fun a ha b hb => hcomm a ha b hb
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
        apply Subtype.ext
        simpa [pow_two] using hsq x x.2 }
  have hE2 : IsPGroup 2 ↥E := CFSG.IsElementaryAbelian.isPGroup 2 ↥E
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hE2
  obtain ⟨hr3, j, hj, hjlen, n, hn⟩ := rank_lemma r E inferInstance hr
  have hr8 : r = 3 := by
    rw [hr] at h8
    interval_cases r <;> simp_all
  subst hr8
  have hj8 : j = 8 := rep_eight j hj (by simpa using hjlen)
  subst hj8
  have hsurj : ∀ e ∈ E8, ∃ b ∈ E, cd (n * b * n⁻¹) = e :=
    conjInto_surj E8_nodup (by rw [hr, E8_length]; norm_num) hn
  have hnrm : ∀ g ∈ P, cd (n * g * n⁻¹) ∈ nrmLit := by
    intro g hg
    have hmem := cd_mem_autL (n * g * n⁻¹)
    have hnormE : normE8 (cd (n * g * n⁻¹)) = true := by
      unfold normE8
      rw [List.all_eq_true]
      intro e' he'
      obtain ⟨b, hb, rfl⟩ := hsurj e' he'
      rw [conj_code]
      have e1 : n * g * n⁻¹ * (n * b * n⁻¹) * (n * g * n⁻¹)⁻¹ = n * (g * b * g⁻¹) * n⁻¹ := by
        group
      rw [e1]
      exact List.elem_eq_true_of_mem (hn _ (hEn g hg b hb))
    have h2 := List.all_eq_true.mp nrmComplete_true _ hmem
    rw [hnormE] at h2
    simpa using h2
  have htwo : ∀ g ∈ P, twoPow (cd (n * g * n⁻¹)) = true := by
    intro g hg
    have h1 : (n * g * n⁻¹) ^ 32 = 1 := by
      rw [conj_pow, pow_thirtytwo hP hg]
      simp
    unfold twoPow
    rw [← cd_pow, h1, cd_one]
    simp
  have hpair : ∀ g1 ∈ P, ∀ g2 ∈ P, actL (cd (n * g1 * n⁻¹)) = E8 ∨ actL (cd (n * g2 * n⁻¹)) = E8 ∨
      actL (cd (n * g1 * n⁻¹)) = actL (cd (n * g2 * n⁻¹)) := by
    intro g1 hg1 g2 hg2
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hp := List.all_eq_true.mp pairCheck_true _ (hnrm g1 hg1)
    have hp2 := List.all_eq_true.mp hp _ (hnrm g2 hg2)
    have hprod : twoPow (cmul (cd (n * g1 * n⁻¹)) (cd (n * g2 * n⁻¹))) = true := by
      rw [← cd_mul]
      have e : n * g1 * n⁻¹ * (n * g2 * n⁻¹) = n * (g1 * g2) * n⁻¹ := by group
      rw [e]
      exact htwo _ (P.mul_mem hg1 hg2)
    simp [htwo g1 hg1, htwo g2 hg2, hprod, h1, h2, h3] at hp2
  have hact_fix : ∀ (g : AutA6) (x : AutA6), cd x ∈ E8 → actL (cd g) = E8 →
      g * x = x * g := by
    intro g x hx hg
    unfold actL at hg
    have := (List.map_inj_left (l := E8) (f := fun e => cmul (cmul (cd g) e) (invC (cd g)))
      (g := fun e => e)).mp (by simpa using hg) (cd x) hx
    exact (conj_code_eq_iff g x).mp this
  have key : ∃ T : List (List ℕ), (∀ e' ∈ T, e' ∈ E8) ∧ T.Nodup ∧ 4 ≤ T.length ∧
      ∀ e' ∈ T, ∀ x : AutA6, cd x = e' → ∀ g ∈ P, (n * g * n⁻¹) * x = x * (n * g * n⁻¹) := by
    by_cases hall : ∀ g ∈ P, actL (cd (n * g * n⁻¹)) = E8
    · refine ⟨E8, fun e' he' => he', E8_nodup, by rw [E8_length]; norm_num, ?_⟩
      intro e' he' x hx g hg
      exact hact_fix _ x (hx ▸ he') (hall g hg)
    · push Not at hall
      obtain ⟨g0, hg0, hne0⟩ := hall
      refine ⟨E8.filter (fun e => cmul (cd (n * g0 * n⁻¹)) e == cmul e (cd (n * g0 * n⁻¹))),
        fun e' he' => (List.mem_filter.mp he').1, E8_nodup.filter _, ?_, ?_⟩
      · have := List.all_eq_true.mp fixCheck_true _ (hnrm g0 hg0)
        simpa [htwo g0 hg0] using this
      · intro e' he' x hx g hg
        obtain ⟨heE, hfix⟩ := List.mem_filter.mp he'
        have hxE : cd x ∈ E8 := hx ▸ heE
        have hfix' : (n * g0 * n⁻¹) * x = x * (n * g0 * n⁻¹) := by
          rw [← hx] at hfix
          exact (fixed_code_iff _ _).mp (by simpa using hfix)
        rcases hpair g hg g0 hg0 with h | h | h
        · exact hact_fix _ x hxE h
        · exact absurd h hne0
        ·
          have hh : cmul (cmul (cd (n * g * n⁻¹)) (cd x)) (invC (cd (n * g * n⁻¹))) =
              cmul (cmul (cd (n * g0 * n⁻¹)) (cd x)) (invC (cd (n * g0 * n⁻¹))) := by
            unfold actL at h
            exact (List.map_inj_left.mp h) (cd x) hxE
          rw [(conj_code_eq_iff _ _).mpr hfix'] at hh
          exact (conj_code_eq_iff _ _).mp hh
  obtain ⟨T, hTE, hTnd, hT4, hTfix⟩ := key
  set S : Set AutA6 := ((E ⊓ Subgroup.centralizer (P : Set AutA6) : Subgroup AutA6) : Set AutA6)
    with hS
  let φ : AutA6 → List ℕ := fun x => cd (n * x * n⁻¹)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 := cd_injective hxy
    have h2 : n * x = n * y := mul_right_cancel h1
    exact mul_left_cancel h2
  have hsub : (T.toFinset : Set (List ℕ)) ⊆ φ '' S := by
    intro e' he'
    have he'T : e' ∈ T := by simpa using he'
    obtain ⟨b, hb, hbe⟩ := hsurj e' (hTE e' he'T)
    refine ⟨b, ⟨hb, ?_⟩, hbe⟩
    show b ∈ Subgroup.centralizer (P : Set AutA6)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := hTfix e' he'T (n * b * n⁻¹) hbe g hg
    have h2 : n * (g * b) * n⁻¹ = n * (b * g) * n⁻¹ := by
      have e1 : n * (g * b) * n⁻¹ = (n * g * n⁻¹) * (n * b * n⁻¹) := by group
      have e2 : n * (b * g) * n⁻¹ = (n * b * n⁻¹) * (n * g * n⁻¹) := by group
      rw [e1, e2]
      exact h1
    exact mul_left_cancel (mul_right_cancel h2)
  calc 4 ≤ T.length := hT4
    _ = (T.toFinset : Set (List ℕ)).ncard := by
      rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hTnd]
    _ ≤ (φ '' S).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = S.ncard := Set.ncard_image_of_injective _ hφ
    _ = Nat.card ↥(E ⊓ Subgroup.centralizer (P : Set AutA6)) := by
      rw [hS, ← Nat.card_coe_set_eq]
      rfl

end CFSG.QuasithinUnique.Id2519.HS4
