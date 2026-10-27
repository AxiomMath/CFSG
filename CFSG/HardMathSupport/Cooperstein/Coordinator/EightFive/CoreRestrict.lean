module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.HeartRestrict
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {X : Type*} [AddCommGroup X] {m n : ℕ}

@[expose] def FixPair (r : alternatingGroup (Fin n) →* AddMonoid.End X) (p q : Fin n) (x : X) :
    Prop :=
  ∀ h : alternatingGroup (Fin n), (h : Perm (Fin n)) p = p → (h : Perm (Fin n)) q = q → r h x = x

theorem FixPair.symm {r : alternatingGroup (Fin n) →* AddMonoid.End X} {p q : Fin n} {x : X}
    (h : FixPair r p q x) : FixPair r q p x :=
  fun g hq hp => h g hp hq

theorem FixPair.conj {r : alternatingGroup (Fin n) →* AddMonoid.End X} {p q : Fin n} {x : X}
    (h : FixPair r p q x) (g : alternatingGroup (Fin n)) :
    FixPair r ((g : Perm (Fin n)) p) ((g : Perm (Fin n)) q) (r g x) := by
  intro k hkp hkq
  have hconj : ∀ t : Fin n, (k : Perm (Fin n)) ((g : Perm (Fin n)) t) = (g : Perm (Fin n)) t →
      ((g⁻¹ * k * g : alternatingGroup (Fin n)) : Perm (Fin n)) t = t := fun t ht => by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, ht, perm_inv_apply_apply]
  have h1 : k * g = g * (g⁻¹ * k * g) := by group
  rw [← endo_mul_apply, h1, endo_mul_apply, h _ (hconj p hkp) (hconj q hkq)]

theorem endo_commute_of_fix (r : alternatingGroup (Fin n) →* AddMonoid.End X)
    (h t : alternatingGroup (Fin n))
    (hd : ∀ x, (h : Perm (Fin n)) x = x ∨ (t : Perm (Fin n)) x = x) (y : X) :
    r h (r t y) = r t (r h y) := by
  have hc : h * t = t * h := Subtype.ext (Perm.Disjoint.commute hd).eq
  rw [← endo_mul_apply, hc, endo_mul_apply]

theorem mk_pairEW_ne_zero' (hm : 3 ≤ m) {p q : Fin m} (hpq : p ≠ q) :
    (pairEW p q : altHeart m) ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_notMem_of_card_lt ({p, q} : Finset (Fin m))
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact mk_pairEW_ne_zero hpq hc.1 hc.2

theorem endo_injective (r : alternatingGroup (Fin n) →* AddMonoid.End X)
    (g : alternatingGroup (Fin n)) : Function.Injective (r g) := fun x y hxy => by
  have := congrArg (r g⁻¹) hxy
  rwa [endo_inv_apply_apply, endo_inv_apply_apply] at this

theorem altLift_apply_ω (ι : Fin m ↪ Fin n) {ω : Fin n} (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω)
    (σ : alternatingGroup (Fin m)) : (altLift ι σ : Perm (Fin n)) ω = ω :=
  altLift_apply_of_notMem ι σ fun h => (hι ω).1 h rfl

section Odd

theorem false_of_heartEquiv_odd (hm : Even m) (hm6 : 6 ≤ m) (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (r : alternatingGroup (Fin n) →* AddMonoid.End X)
    (θ : X ≃+ altHeart m)
    (hθ : ∀ (σ : alternatingGroup (Fin m)) x,
      θ (r (altLift ι σ) x) = altAct (σ : Perm (Fin m)) (θ x)) : False := by
  classical
  set a' : Fin m := ⟨0, by omega⟩
  set b' : Fin m := ⟨1, by omega⟩
  set c' : Fin m := ⟨2, by omega⟩
  have hab' : a' ≠ b' := by simp [a', b', Fin.ext_iff]
  have hac' : a' ≠ c' := by simp [a', c', Fin.ext_iff]
  have hbc' : b' ≠ c' := by simp [b', c', Fin.ext_iff]
  set a := ι a'
  set b := ι b'
  set c := ι c'
  have hab : a ≠ b := fun h => hab' (ι.injective h)
  have hac : a ≠ c := fun h => hac' (ι.injective h)
  have hbc : b ≠ c := fun h => hbc' (ι.injective h)
  have haω : a ≠ ω := (hι a).1 ⟨a', rfl⟩
  have hbω : b ≠ ω := (hι b).1 ⟨b', rfl⟩
  have hcω : c ≠ ω := (hι c).1 ⟨c', rfl⟩
  set vab := θ.symm (pairEW a' b' : altHeart m)
  set vac := θ.symm (pairEW a' c' : altHeart m)
  set vbc := θ.symm (pairEW b' c' : altHeart m)
  have hne_ab_bc : vab ≠ vbc := fun h =>
    mk_pairEW_ne_mk_pairEW hab' hac' hbc' (θ.symm.injective h)
  have hne_ab_ac : vab ≠ vac := fun h =>
    mk_pairEW_ne_mk_pairEW hab'.symm hbc' hac' (by
      rw [pairEW_comm]; exact θ.symm.injective h)
  have hne_ac_bc : vac ≠ vbc := fun h =>
    mk_pairEW_ne_mk_pairEW hac' hab' hbc'.symm (by
      rw [pairEW_comm c' b']; exact θ.symm.injective h)
  have hcoord : ∀ x : X, ∀ σ : alternatingGroup (Fin m), r (altLift ι σ) x = x →
      altAct (σ : Perm (Fin m)) (θ x) = θ x := fun x σ hx => by rw [← hθ, hx]
  have hpair_fix : ∀ (p q : Fin m) (σ : alternatingGroup (Fin m)), (σ : Perm (Fin m)) p = p →
      (σ : Perm (Fin m)) q = q → r (altLift ι σ) (θ.symm (pairEW p q : altHeart m)) =
        θ.symm (pairEW p q : altHeart m) := fun p q σ hp hq => by
    apply θ.injective
    rw [hθ, AddEquiv.apply_symm_apply, altAct_mk, evenWeightPerm_pairEW, hp, hq]
  let g₁ : alternatingGroup (Fin n) :=
    ⟨swap ω b * swap ω a, (isThreeCycle_swap_mul_swap_same hbω.symm haω.symm hab.symm).mem_alternatingGroup⟩
  let g₂ : alternatingGroup (Fin n) :=
    ⟨swap ω c * swap ω b, (isThreeCycle_swap_mul_swap_same hcω.symm hbω.symm hbc.symm).mem_alternatingGroup⟩
  have hg₁ : ∀ x, x ≠ ω → x ≠ a → x ≠ b → (g₁ : Perm (Fin n)) x = x := fun x h1 h2 h3 => by
    change (swap ω b * swap ω a) x = x
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]
  have hg₂ : ∀ x, x ≠ ω → x ≠ b → x ≠ c → (g₂ : Perm (Fin n)) x = x := fun x h1 h2 h3 => by
    change (swap ω c * swap ω b) x = x
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]
  have hfix3 : ∀ (p' q' : Fin m) (t : alternatingGroup (Fin n)), p' ≠ q' →
      (∀ x, x ≠ ω → x ≠ ι p' → x ≠ ι q' → (t : Perm (Fin n)) x = x) →
      r t (θ.symm (pairEW p' q' : altHeart m)) = θ.symm (pairEW p' q' : altHeart m) := by
    intro p' q' t hpq ht
    set v := θ.symm (pairEW p' q' : altHeart m)
    have hcomm : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) p' = p' →
        (σ : Perm (Fin m)) q' = q' → r (altLift ι σ) (r t v) = r t v := fun σ hp hq => by
      rw [endo_commute_of_fix r _ _ (fun x => by
        by_cases h1 : x = ω
        · left; rw [h1]; exact altLift_apply_ω ι hι σ
        by_cases h2 : x = ι p'
        · left; rw [h2, altLift_apply_apply, hp]
        by_cases h3 : x = ι q'
        · left; rw [h3, altLift_apply_apply, hq]
        right; exact ht x h1 h2 h3), hpair_fix p' q' σ hp hq]
    have hz0 : θ (r t v) ≠ 0 := by
      intro h
      have h1 : r t v = r t 0 := θ.injective (by rw [h, map_zero, map_zero])
      have h2 : (pairEW p' q' : altHeart m) = 0 :=
        θ.symm.injective ((endo_injective r t h1).trans (map_zero θ.symm).symm)
      exact mk_pairEW_ne_zero' (by omega) hpq h2
    have := heart_eq_pair_of_fix_two hm (by omega) hpq hz0 fun σ hp hq =>
      hcoord _ σ (hcomm σ hp hq)
    apply θ.injective
    rw [this, AddEquiv.apply_symm_apply]
  have h₁ : r g₁ vab = vab := hfix3 a' b' g₁ hab' hg₁
  have h₂bc : r g₂ vbc = vbc := hfix3 b' c' g₂ hbc' hg₂
  have hZ : ∀ x : X, (∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) a' = a' →
      (σ : Perm (Fin m)) b' = b' → (σ : Perm (Fin m)) c' = c' → r (altLift ι σ) x = x) →
      x = 0 ∨ x = vab ∨ x = vac ∨ x = vbc := by
    intro x hx
    rcases heart_fix_three hm hm6 hab' hac' hbc' (z := θ x) fun σ ha hb hc =>
      hcoord x σ (hx σ ha hb hc) with h | h | h | h
    · left; exact θ.injective (by rw [h, map_zero])
    · right; left; exact (θ.symm_apply_apply x).symm.trans (congrArg θ.symm h)
    · right; right; left; exact (θ.symm_apply_apply x).symm.trans (congrArg θ.symm h)
    · right; right; right; exact (θ.symm_apply_apply x).symm.trans (congrArg θ.symm h)
  have hg₂Z : ∀ v : X, (∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) a' = a' →
      (σ : Perm (Fin m)) b' = b' → (σ : Perm (Fin m)) c' = c' → r (altLift ι σ) v = v) →
      ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) a' = a' →
      (σ : Perm (Fin m)) b' = b' → (σ : Perm (Fin m)) c' = c' →
      r (altLift ι σ) (r g₂ v) = r g₂ v := fun v hv σ ha hb hc => by
    rw [endo_commute_of_fix r _ _ (fun x => by
      by_cases h1 : x = ω
      · left; rw [h1]; exact altLift_apply_ω ι hι σ
      by_cases h2 : x = b
      · left; rw [h2, altLift_apply_apply, hb]
      by_cases h3 : x = c
      · left; rw [h3, altLift_apply_apply, hc]
      right; exact hg₂ x h1 h2 h3), hv σ ha hb hc]
  have hinj₂ := endo_injective r g₂
  have hvab0 : vab ≠ 0 := fun h =>
    mk_pairEW_ne_zero' (by omega) hab' (θ.symm.injective (h.trans (map_zero θ.symm).symm))
  have hvac0 : vac ≠ 0 := fun h =>
    mk_pairEW_ne_zero' (by omega) hac' (θ.symm.injective (h.trans (map_zero θ.symm).symm))
  have hcase : ∀ v : X, v ≠ 0 → v ≠ vbc → (∀ σ : alternatingGroup (Fin m),
      (σ : Perm (Fin m)) a' = a' → (σ : Perm (Fin m)) b' = b' → (σ : Perm (Fin m)) c' = c' →
      r (altLift ι σ) v = v) → r g₂ v = vab ∨ r g₂ v = vac := by
    intro v hv0 hvbc hv
    rcases hZ _ (hg₂Z v hv) with h | h | h | h
    · exact absurd (hinj₂ (h.trans (map_zero _).symm)) hv0
    · left; exact h
    · right; exact h
    · exact absurd (hinj₂ (h.trans h₂bc.symm)) hvbc
  have hab_case := hcase vab hvab0 hne_ab_bc fun σ ha hb _ => hpair_fix a' b' σ ha hb
  have hac_case := hcase vac hvac0 hne_ac_bc fun σ ha _ hc => hpair_fix a' c' σ ha hc
  have hg₂3 : ∀ v, r g₂ (r g₂ (r g₂ v)) = v := by
    have h3 : (g₂ : Perm (Fin n)) ^ 3 = 1 := by
      have := (isThreeCycle_swap_mul_swap_same hcω.symm hbω.symm hbc.symm).orderOf
      rw [← this]
      exact pow_orderOf_eq_one _
    have h3' : g₂ * g₂ * g₂ = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_one, ← pow_three']
      exact h3)
    intro v
    rw [← endo_mul_apply, ← endo_mul_apply, h3', map_one]
    rfl
  have h₂ab : r g₂ vab = vab := by
    rcases hab_case with h | h
    · exact h
    · exfalso
      rcases hac_case with h' | h'
      · have := hg₂3 vab
        rw [h, h', h] at this
        exact hne_ab_ac this.symm
      · exact hne_ab_ac (hinj₂ (h.trans h'.symm))
  have hg₂ω : (g₂ : Perm (Fin n)) ω = b := by
    change (swap ω c * swap ω b) ω = b
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hbω hbc]
  have hg₂b : (g₂ : Perm (Fin n)) b = c := by
    change (swap ω c * swap ω b) b = c
    rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  have hg₁b : (g₁ : Perm (Fin n)) b = ω := by
    change (swap ω b * swap ω a) b = ω
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbω hab.symm, swap_apply_right]
  have hg₁a : (g₁ : Perm (Fin n)) a = b := by
    change (swap ω b * swap ω a) a = b
    rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  have hω : ((g₁ * g₂ : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
    rw [Subgroup.coe_mul, Perm.mul_apply, hg₂ω, hg₁b]
  obtain ⟨τ, hτ⟩ := exists_altLift_eq ι hι (g₁ * g₂) hω
  have hτa : (τ : Perm (Fin m)) a' = b' := ι.injective (by
    rw [← altLift_apply_apply, hτ, Subgroup.coe_mul, Perm.mul_apply,
      hg₂ a haω hab hac, hg₁a])
  have hτb : (τ : Perm (Fin m)) b' = c' := ι.injective (by
    rw [← altLift_apply_apply, hτ, Subgroup.coe_mul, Perm.mul_apply, hg₂b,
      hg₁ c hcω hac.symm hbc.symm])
  have key : θ (r (g₁ * g₂) vab) = (pairEW b' c' : altHeart m) := by
    rw [← hτ, hθ, AddEquiv.apply_symm_apply, altAct_mk, evenWeightPerm_pairEW, hτa, hτb]
  rw [endo_mul_apply, h₂ab, h₁, AddEquiv.apply_symm_apply] at key
  exact mk_pairEW_ne_mk_pairEW hab' hac' hbc' key

end Odd

section Even

theorem exists_heartEquiv_even (hn : Even n) (hn6 : 6 ≤ n) (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n)
    (r : alternatingGroup (Fin n) →* AddMonoid.End X) (θ : X ≃+ altHeart m)
    (hθ : ∀ (σ : alternatingGroup (Fin m)) x,
      θ (r (altLift ι σ) x) = altAct (σ : Perm (Fin m)) (θ x)) :
    ∃ Θ : altHeart n ≃+ X,
      ∀ (g : alternatingGroup (Fin n)) z, Θ (altAct (g : Perm (Fin n)) z) = r g (Θ z) := by
  classical
  have hm : Odd m := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k - 1, by omega⟩
  set η := heartRestrict ι hι hmn hn with hη
  set Θ : altHeart n ≃+ X := η.trans θ.symm with hΘ
  have hΘapp : ∀ z, Θ z = θ.symm (η z) := fun z => rfl
  have hθΘ : ∀ z, θ (Θ z) = η z := fun z => by rw [hΘapp, AddEquiv.apply_symm_apply]
  have hΘK : ∀ (σ : alternatingGroup (Fin m)) z,
      Θ (altAct (altLift ι σ : Perm (Fin n)) z) = r (altLift ι σ) (Θ z) := by
    intro σ z
    apply θ.injective
    rw [hθ, hθΘ, hθΘ, hη, heartRestrict_altAct]
  have hcoord : ∀ x : X, ∀ σ : alternatingGroup (Fin m), r (altLift ι σ) x = x →
      altAct (σ : Perm (Fin m)) (θ x) = θ x := fun x σ hx => by rw [← hθ, hx]
  have hηfix : ∀ (p q : Fin n) (σ : alternatingGroup (Fin m)),
      (altLift ι σ : Perm (Fin n)) p = p → (altLift ι σ : Perm (Fin n)) q = q →
      altAct (σ : Perm (Fin m)) (η (pairEW p q : altHeart n)) = η (pairEW p q : altHeart n) := by
    intro p q σ hp hq
    rw [hη, ← heartRestrict_altAct, altAct_mk, evenWeightPerm_pairEW, hp, hq]
  have hΘ0 : ∀ p q : Fin n, p ≠ q → Θ (pairEW p q : altHeart n) ≠ 0 := fun p q hpq h =>
    mk_pairEW_ne_zero' (by omega) hpq (Θ.injective (h.trans (map_zero Θ).symm))
  have hθ0 : ∀ x : X, x ≠ 0 → θ x ≠ 0 := fun x hx h => hx (θ.injective (h.trans (map_zero θ).symm))
  have step1a : ∀ q, FixPair r ω q (Θ (pairEW ω q : altHeart n)) := by
    intro q h hhω hhq
    obtain ⟨σ, rfl⟩ := exists_altLift_eq ι hι h hhω
    rw [← hΘK, altAct_mk, evenWeightPerm_pairEW, hhω, hhq]
  have step1b : ∀ q, q ≠ ω → ∀ x : X, x ≠ 0 → FixPair r ω q x →
      x = Θ (pairEW ω q : altHeart n) := by
    intro q hq x hx0 hx
    obtain ⟨q', rfl⟩ := (hι q).2 hq
    have h1 : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) q' = q' →
        altAct (σ : Perm (Fin m)) (θ x) = θ x := fun σ hσ =>
      hcoord x σ (hx _ (altLift_apply_ω ι hι σ) (by rw [altLift_apply_apply, hσ]))
    have h2 : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) q' = q' →
        altAct (σ : Perm (Fin m)) (θ (Θ (pairEW ω (ι q') : altHeart n))) =
          θ (Θ (pairEW ω (ι q') : altHeart n)) := fun σ hσ => by
      rw [hθΘ]
      exact hηfix _ _ σ (altLift_apply_ω ι hι σ) (by rw [altLift_apply_apply, hσ])
    exact θ.injective (heart_eq_of_fix_one hm (by omega) q' (hθ0 x hx0)
      (hθ0 _ (hΘ0 ω (ι q') (Ne.symm hq))) h1 h2)
  have step2 : ∀ p q, p ≠ ω → q ≠ ω → p ≠ q →
      FixPair r p q (Θ (pairEW p q : altHeart n)) ∧
        ∀ x : X, x ≠ 0 → FixPair r p q x → x = Θ (pairEW p q : altHeart n) := by
    intro p q hp hq hpq
    obtain ⟨g₀, hg₀p, hg₀q⟩ := exists_alt_apply_eq_apply_eq (by omega) hpq (Ne.symm hq)
    set w := r g₀⁻¹ (Θ (pairEW ω q : altHeart n)) with hw_def
    have hw : FixPair r p q w := by
      have := (step1a q).conj g₀⁻¹
      rwa [Subgroup.coe_inv, inv_apply_of_apply hg₀p, inv_apply_of_apply hg₀q] at this
    have huniq : ∀ x : X, x ≠ 0 → FixPair r p q x → x = w := by
      intro x hx0 hx
      have h1 := hx.conj g₀
      rw [hg₀p, hg₀q] at h1
      have h2 := step1b q hq (r g₀ x) (fun h => hx0 (endo_injective r g₀
        (h.trans (map_zero _).symm))) h1
      rw [hw_def, ← h2, endo_inv_apply_apply]
    have hw0 : w ≠ 0 := fun h => hΘ0 ω q (Ne.symm hq) (endo_injective r g₀⁻¹
      (h.trans (map_zero _).symm))
    obtain ⟨p', rfl⟩ := (hι p).2 hp
    obtain ⟨q', rfl⟩ := (hι q).2 hq
    have hpq' : p' ≠ q' := fun h => hpq (by rw [h])
    obtain ⟨e', he'p, he'q, -⟩ := exists_ne_three (n := m) (by omega) p' q' p'
    obtain ⟨f', hf'p, hf'q, hf'e⟩ := exists_ne_three (n := m) (by omega) p' q' e'
    let τ' : alternatingGroup (Fin m) :=
      ⟨swap p' q' * swap e' f', by
        rw [mem_alternatingGroup, map_mul, sign_swap hpq', sign_swap (Ne.symm hf'e)]
        decide⟩
    have hτp : (altLift ι τ' : Perm (Fin n)) (ι p') = ι q' := by
      rw [altLift_apply_apply]
      congr 1
      change (swap p' q' * swap e' f') p' = q'
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm he'p) (Ne.symm hf'p), swap_apply_left]
    have hτq : (altLift ι τ' : Perm (Fin n)) (ι q') = ι p' := by
      rw [altLift_apply_apply]
      congr 1
      change (swap p' q' * swap e' f') q' = p'
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm he'q) (Ne.symm hf'q),
        swap_apply_right]
    have hτw : r (altLift ι τ') w = w := by
      have h1 := hw.conj (altLift ι τ')
      rw [hτp, hτq] at h1
      exact huniq _ (fun h => hw0 (endo_injective r _ (h.trans (map_zero _).symm))) h1.symm
    have hfix2 : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) p' = p' →
        (σ : Perm (Fin m)) q' = q' → (altLift ι σ : Perm (Fin n)) (ι p') = ι p' ∧
          (altLift ι σ : Perm (Fin n)) (ι q') = ι q' := fun σ hp hq => by
      rw [altLift_apply_apply, altLift_apply_apply, hp, hq]
      exact ⟨rfl, rfl⟩
    have hθw : θ w = (pairEW p' q' : altHeart m) :=
      heart_eq_pair_of_fix_two_swap hm (by omega) hpq' he'p he'q hf'p hf'q (hθ0 w hw0)
        (fun σ hp hq => hcoord w σ (hw _ (hfix2 σ hp hq).1 (hfix2 σ hp hq).2))
        (by
          have := hθ τ' w
          rw [hτw] at this
          exact this.symm)
    have hθΘpq : θ (Θ (pairEW (ι p') (ι q') : altHeart n)) = (pairEW p' q' : altHeart m) :=
      heart_eq_pair_of_fix_two_swap hm (by omega) hpq' he'p he'q hf'p hf'q
        (hθ0 _ (hΘ0 _ _ hpq))
        (fun σ hp hq => by
          rw [hθΘ]; exact hηfix _ _ σ (hfix2 σ hp hq).1 (hfix2 σ hp hq).2)
        (by
          change altAct ((τ' : Perm (Fin m))) _ = _
          rw [hθΘ, hη, ← heartRestrict_altAct, altAct_mk, evenWeightPerm_pairEW, hτp, hτq,
            pairEW_comm])
    have hwΘ : w = Θ (pairEW (ι p') (ι q') : altHeart n) := θ.injective (hθw.trans hθΘpq.symm)
    exact ⟨hwΘ ▸ hw, fun x hx0 hx => (huniq x hx0 hx).trans hwΘ⟩
  have hall : ∀ p q, p ≠ q → FixPair r p q (Θ (pairEW p q : altHeart n)) ∧
      ∀ x : X, x ≠ 0 → FixPair r p q x → x = Θ (pairEW p q : altHeart n) := by
    intro p q hpq
    by_cases hp : p = ω
    · subst hp
      exact ⟨step1a q, step1b q (Ne.symm hpq)⟩
    by_cases hq : q = ω
    · subst hq
      rw [pairEW_comm]
      exact ⟨(step1a p).symm, fun x hx0 hx => step1b p hp x hx0 hx.symm⟩
    exact step2 p q hp hq hpq
  refine ⟨Θ, fun g z => ?_⟩
  have hext := altHeart_hom_ext (n := n)
    (f := Θ.toAddMonoidHom.comp (altAct (g : Perm (Fin n))))
    (g := (r g).comp Θ.toAddMonoidHom) fun a b hab => by
      change Θ (altAct (g : Perm (Fin n)) (pairEW a b : altHeart n)) = r g (Θ (pairEW a b))
      rw [altAct_mk, evenWeightPerm_pairEW]
      have hgab : (g : Perm (Fin n)) a ≠ (g : Perm (Fin n)) b :=
        fun h => hab ((g : Perm (Fin n)).injective h)
      exact ((hall _ _ hgab).2 _ (fun h => hΘ0 a b hab (endo_injective r g
        (h.trans (map_zero _).symm))) ((hall a b hab).1.conj g)).symm
  exact DFunLike.congr_fun hext z

end Even

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
