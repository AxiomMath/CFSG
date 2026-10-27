module

public import CFSG.CGT.PushingUpLit.BHS5.SymGlue
public import CFSG.CGT.PushingUpLit.BHS5.JStepSL
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenThree

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_one_or_eq_of_card_two {G : Type*} [Group G] (H : Subgroup G) (hH : Nat.card H = 2)
    {a c : G} (ha : a ∈ H) (hc : c ∈ H) (hc1 : c ≠ 1) : a = 1 ∨ a = c := by
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  · right
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : H)).1 hH
    have h1 := hy ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
    have h2 := hy ⟨c, hc⟩ (fun h => hc1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)

omit [Finite V] in
theorem SymDat.exists_swap_elem {E B : Subgroup (MulAut V)} {m : ℕ} (D : SymDat E m)
    (hBE : B ≤ E) (hBne : B ≠ ⊥)
    (hB : ∃ i j : Fin m, i ≠ j ∧ ∀ b : ↥E, (b : MulAut V) ∈ B →
      D.θ b = 1 ∨ D.θ b = Equiv.swap i j) :
    ∃ b₀ ∈ B, ∃ hb : b₀ ∈ E, ∃ i j : Fin m, i ≠ j ∧ D.θ ⟨b₀, hb⟩ = Equiv.swap i j := by
  obtain ⟨i, j, hij, h⟩ := hB
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  have hbE : (b : MulAut V) ∈ E := hBE b.2
  rcases h ⟨b, hbE⟩ b.2 with h1 | h1
  · exfalso
    have : (⟨(b : MulAut V), hbE⟩ : ↥E) = 1 := D.θ.injective (h1.trans (map_one D.θ).symm)
    exact hb1 (Subtype.ext (congrArg (fun z : ↥E => (z : MulAut V)) this))
  · exact ⟨b, b.2, hbE, i, j, hij, h1⟩

theorem jSplit_sym_three (hV : ∀ v : V, v ^ 2 = 1) {P E X B : Subgroup (MulAut V)}
    (D : SymDat E 3) (hXP : X ≤ P) (hXoff : IsOff X) (hBX : B ≤ X)
    (hsub : CFSG.Open.IsSubnormal E P) (hBE : B ≤ E) (hBne : B ≠ ⊥)
    (hB : ∃ i j : Fin 3, i ≠ j ∧ ∀ b : ↥E, (b : MulAut V) ∈ B →
      D.θ b = 1 ∨ D.θ b = Equiv.swap i j) : JSplit X B := by
  obtain ⟨b₀, hb₀B, hb₀E, i, j, hij, hθ⟩ := D.exists_swap_elem hBE hBne hB
  have hEX : ⁅altOf D.θ, X⁆ ≠ ⊥ := D.commutator_altOf_ne_bot (hBX hb₀B) hb₀E hij hθ
  obtain ⟨hAN, -, hcard, -, hidx⟩ := two_sixteen_three hV hXoff hXP
    (isSubnormal_altOf D.θ hsub) D.isAltNatSection_altOf hEX
  have hc := D.commV_altOf
  have hXst' : X ≤ stabSub (commV (altOf D.θ)) := hAN.trans (normalizer_commV_le_stabSub _)
  rw [hc] at hcard hidx hXst'
  have hb₀W : ∃ w ∈ commV E, b₀ w ≠ w := by
    by_contra hcon
    push Not at hcon
    have h1 : b₀ = 1 := eq_one_of_trivial_on_commV D.top hb₀E hcon
    have : (⟨b₀, hb₀E⟩ : ↥E) = 1 := Subtype.ext h1
    have h2 : D.θ ⟨b₀, hb₀E⟩ = 1 := by rw [this, map_one]
    rw [hθ] at h2
    have h3 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) h2
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h3
    exact hij h3.symm
  have hdec : ∀ x ∈ X, ∃ b ∈ B, ∀ w ∈ commV E, x w = b w := by
    intro x hx
    have hyX : resHom (commV E) ⟨x, hXst' hx⟩ ∈ autSub X (commV E) :=
      mem_autSub.2 ⟨⟨x, hXst' hx⟩, hx, rfl⟩
    have hybX : resHom (commV E) ⟨b₀, hXst' (hBX hb₀B)⟩ ∈ autSub X (commV E) :=
      mem_autSub.2 ⟨⟨b₀, hXst' (hBX hb₀B)⟩, hBX hb₀B, rfl⟩
    have hyb1 : resHom (commV E) ⟨b₀, hXst' (hBX hb₀B)⟩ ≠ 1 := by
      intro h1
      obtain ⟨w, hw, hne⟩ := hb₀W
      apply hne
      have := congrArg (fun φ : MulAut ↥(commV E) => ((φ ⟨w, hw⟩ : ↥(commV E)) : V)) h1
      exact this
    rcases eq_one_or_eq_of_card_two (autSub X (commV E)) hcard hyX hybX hyb1 with h1 | h1
    · refine ⟨1, B.one_mem, fun w hw => ?_⟩
      have := congrArg (fun φ : MulAut ↥(commV E) => ((φ ⟨w, hw⟩ : ↥(commV E)) : V)) h1
      exact this
    · refine ⟨b₀, hb₀B, fun w hw => ?_⟩
      have := congrArg (fun φ : MulAut ↥(commV E) => ((φ ⟨w, hw⟩ : ↥(commV E)) : V)) h1
      exact this
  exact jSplit_of_cen hXoff hBX hidx hdec ⟨b₀, hb₀B, hb₀W⟩

theorem jSplit_sym_alt (hV : ∀ v : V, v ^ 2 = 1) {P E X B : Subgroup (MulAut V)} {m : ℕ}
    (D : SymDat E m) (h5 : 5 ≤ m) (hXP : X ≤ P) (hXoff : IsOff X) (hBX : B ≤ X) (hEP : E ≤ P)
    (hsub : CFSG.Open.IsSubnormal E P) (hBE : B ≤ E) (hBne : B ≠ ⊥)
    (hB : ∃ i j : Fin m, i ≠ j ∧ ∀ b : ↥E, (b : MulAut V) ∈ B →
      D.θ b = 1 ∨ D.θ b = Equiv.swap i j) : JSplit X B := by
  obtain ⟨b₀, hb₀B, hb₀E, i, j, hij, hθ⟩ := D.exists_swap_elem hBE hBne hB
  have hb₀X : b₀ ∈ X := hBX hb₀B
  have hEX : ⁅altOf D.θ, X⁆ ≠ ⊥ := D.commutator_altOf_ne_bot hb₀X hb₀E hij hθ
  have hsub' := isSubnormal_altOf D.θ hsub
  have hq : CFSG.Open.IsQuasisimple ↥(altOf D.θ) :=
    isQuasisimple_of_mulEquiv' (altEquiv D.θ).symm (isQuasisimple_alternatingGroup h5)
  have hAN : X ≤ Subgroup.normalizer (altOf D.θ : Set (MulAut V)) :=
    offender_le_normalizer_of_isComponentOf hV hXoff hXP ⟨(altOf_le D.θ).trans hEP, hsub', hq⟩
  obtain ⟨-, θX, hbij, hequiv, -, -, -⟩ := two_sixteen_alt_gen hV D.odd h5 (A := X)
    (E := altOf D.θ) (W := commV (altOf D.θ)) rfl (altEquiv D.θ) D.βalt D.βalt_surjective
    D.βalt_ker D.βalt_equiv hAN hXoff hEX
  have hXst : X ≤ stabSub (commV (altOf D.θ)) := hAN.trans (normalizer_commV_le_stabSub _)
  have hXel : IsElemAbelian2 X := hXoff.2.2.1
  let W : Subgroup V := commV (altOf D.θ)
  let yx : ∀ x ∈ X, ↥(autSub (altOf D.θ) W ⊔ autSub X W) := fun x hx =>
    ⟨resHom W ⟨x, hXst hx⟩, Subgroup.mem_sup_right (mem_autSub.2 ⟨⟨x, hXst hx⟩, hx, rfl⟩)⟩
  let σ : ∀ x ∈ X, Equiv.Perm (Fin m) := fun x hx => θX (yx x hx)
  have hσ : ∀ x (hx : x ∈ X) (w : ↥W),
      D.βalt (resHom W ⟨x, hXst hx⟩ w) = coreAct m (σ x hx) (D.βalt w) :=
    fun x hx w => hequiv (yx x hx) w
  have hσb : σ b₀ hb₀X = Equiv.swap i j := by
    refine coreAct_injective (by omega : 3 ≤ m) (MulEquiv.ext fun u => ?_)
    obtain ⟨w, rfl⟩ := hbij.2 u
    rw [← hσ b₀ hb₀X w]
    have hp : (b₀ : MulAut V) (w : V) ∈ commV E := D.inv b₀ hb₀E _ (D.commV_altOf.le w.2)
    have h1 := D.equiv ⟨b₀, hb₀E⟩ ⟨(w : V), D.commV_altOf.le w.2⟩ hp
    rw [hθ] at h1
    exact h1
  have hcomm : ∀ x (hx : x ∈ X), σ x hx * Equiv.swap i j = Equiv.swap i j * σ x hx := by
    intro x hx
    rw [← hσb]
    have h1 : yx x hx * yx b₀ hb₀X = yx b₀ hb₀X * yx x hx := by
      refine Subtype.ext ?_
      show resHom W ⟨x, hXst hx⟩ * resHom W ⟨b₀, hXst hb₀X⟩ =
        resHom W ⟨b₀, hXst hb₀X⟩ * resHom W ⟨x, hXst hx⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hXel.1 x hx b₀ hb₀X)
    have h2 := congrArg θX h1
    rw [map_mul, map_mul] at h2
    exact h2
  obtain ⟨u₁, hu₁⟩ := hbij.2 (ptVec D.odd i)
  have hb₀w : b₀ (u₁ : V) ≠ (u₁ : V) := by
    intro h
    have h1 : resHom W ⟨b₀, hXst hb₀X⟩ u₁ = u₁ := Subtype.ext h
    have h2 := congrArg D.βalt h1
    rw [hσ b₀ hb₀X u₁, hσb, hu₁, coreAct_ptVec, Equiv.swap_apply_left] at h2
    exact hij (ptVec_injective D.odd h2).symm
  have hpoint : ∀ x ∈ X, x (u₁ : V) = (u₁ : V) ∨ (b₀ * x) (u₁ : V) = (u₁ : V) := by
    intro x hx
    rcases apply_mem_pair_of_commute_swap hij (hcomm x hx) with h | h
    · left
      have h1 : resHom W ⟨x, hXst hx⟩ u₁ = u₁ := by
        apply D.βalt_injective
        rw [hσ x hx u₁, hu₁, coreAct_ptVec, h]
      exact congrArg Subtype.val h1
    · right
      have h1 : resHom W ⟨b₀, hXst hb₀X⟩ (resHom W ⟨x, hXst hx⟩ u₁) = u₁ := by
        apply D.βalt_injective
        rw [hσ b₀ hb₀X, hσ x hx u₁, hσb, hu₁, coreAct_ptVec, coreAct_ptVec, h,
          Equiv.swap_apply_right]
      exact congrArg Subtype.val h1
  obtain ⟨X₀, h1, h2, h3, h4⟩ := jSplit_of_point hb₀X hb₀w hpoint
  exact ⟨X₀, h1, h2, h3, h4.trans (sup_le_sup_right (Subgroup.zpowers_le.2 hb₀B) _)⟩

end CFSG.CGT.PushingUpLit.BHS5
