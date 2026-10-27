module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.G18Split
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.MinimalMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.PlusIrr
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.ThompsonSchur
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.CGT6X
open scoped commutatorElement

section Irr

variable {V : Type} [CommGroup V]

theorem invariant_eq_bot_or_eq_of_equiv {X : Subgroup (MulAut V)} {P : Subgroup V} {S M : Type}
    [Group S] [Group M] {act : S → M → M} (θ : ↥X ≃* S) (φ : ↥P ≃* M)
    (hφ : ∀ (x : ↥X) (p : ↥P) (hp : (x : MulAut V) p ∈ P),
      φ ⟨(x : MulAut V) p, hp⟩ = act (θ x) (φ p))
    (hirr : ∀ W : Subgroup M, (∀ s, ∀ m ∈ W, act s m ∈ W) → W = ⊥ ∨ W = ⊤)
    (hinv : ∀ x ∈ X, ∀ p ∈ P, x p ∈ P) (A : Subgroup V) (hA : ∀ x ∈ X, ∀ a ∈ A, x a ∈ A)
    (hAP : A ≤ P) : A = ⊥ ∨ A = P := by
  let A' : Subgroup ↥P := A.subgroupOf P
  let W : Subgroup M := A'.map φ.toMonoidHom
  have hW : ∀ s, ∀ m ∈ W, act s m ∈ W := by
    rintro s _ ⟨a', ha', rfl⟩
    have hx : θ (θ.symm s) = s := θ.apply_symm_apply s
    have hp : ((θ.symm s : ↥X) : MulAut V) a' ∈ P := hinv _ (θ.symm s).2 a' a'.2
    refine ⟨⟨((θ.symm s : ↥X) : MulAut V) a', hp⟩, hA _ (θ.symm s).2 a' ha', ?_⟩
    show φ ⟨((θ.symm s : ↥X) : MulAut V) a', hp⟩ = act s (φ a')
    rw [hφ, hx]
  rcases hirr W hW with h | h
  · left
    refine (Subgroup.eq_bot_iff_forall A).2 fun a ha => ?_
    have h1 : φ ⟨a, hAP ha⟩ ∈ W := ⟨⟨a, hAP ha⟩, ha, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm))
  · right
    refine le_antisymm hAP fun p hp => ?_
    have h1 : φ ⟨p, hp⟩ ∈ W := by rw [h]; trivial
    obtain ⟨a', ha', ha'p⟩ := h1
    have : a' = ⟨p, hp⟩ := φ.injective ha'p
    rw [this] at ha'
    exact ha'

theorem rel_irreducible_of_abs {X : Subgroup (MulAut V)}
    (h : ∀ A : Subgroup V, (∀ x ∈ X, ∀ a ∈ A, x a ∈ A) → A ≤ commV X → A = ⊥ ∨ A = commV X) :
    ∀ N : Subgroup V, (∀ g ∈ X, ∀ n ∈ N, g n ∈ N) → N ≤ commV X → commV X ⊓ fixV X ≤ N →
      N = commV X ⊓ fixV X ∨ N = commV X := by
  intro N hN hNU hAN
  rcases h N hN hNU with h0 | h0
  · left
    exact le_antisymm (h0 ▸ bot_le) hAN
  · exact Or.inr h0

theorem NatOmegaN.irreducible {n : ℕ} (hn : 2 ≤ n) {X : Subgroup (MulAut V)}
    (hX : NatOmegaN n X) (A : Subgroup V) (hA : ∀ x ∈ X, ∀ a ∈ A, x a ∈ A)
    (hAU : A ≤ commV X) : A = ⊥ ∨ A = commV X := by
  have : NeZero n := ⟨by omega⟩
  rcases hX with h | h
  · obtain ⟨hinv, θ, φ, hφ⟩ := TwoEight.natSection_equiv h
    exact invariant_eq_bot_or_eq_of_equiv θ φ hφ (fun W hW => natPlus_irreducible n W hW) hinv A hA
      hAU
  · obtain ⟨hinv, θ, φ, hφ⟩ := exists_equiv_of_natSection h
    exact invariant_eq_bot_or_eq_of_equiv (act := fun A m => rhoW n A m) θ φ hφ
      (fun W hW => natModule_irreducible n W hW) hinv A hA hAU

variable [Finite V]

theorem ClassX4.invariant_irreducible {Y : Subgroup (MulAut V)} (hperf : ⁅Y, Y⁆ = Y)
    (hV : ∀ v : V, v ^ 2 = 1) (hY : ClassX4 Y) :
    ∀ N : Subgroup V, (∀ g ∈ Y, ∀ n ∈ N, g n ∈ N) → N ≤ commV Y → commV Y ⊓ fixV Y ≤ N →
      N = commV Y ⊓ fixV Y ∨ N = commV Y := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  rcases hY with hX | ⟨n, hn, hY⟩ | ⟨n, hn, hY⟩
  · intro N hN hNU hAN
    exact CFSG.CGT.PushingUpLit.CGT6.invariant_irreducible Y hV hX.1
      (shortU_eq_range Y (MulEquiv.refl (↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y))) hV hX.1) N hN hNU hAN
  · exact rel_irreducible_of_abs fun A hA hAU => NatOmegaN.irreducible hn (Or.inr hY) A hA hAU
  · exact rel_irreducible_of_abs fun A hA hAU => NatOmegaN.irreducible hn (Or.inl hY) A hA hAU

theorem commV_le_fixV_of_commute (hV : ∀ v : V, v ^ 2 = 1) {Y Q : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hY : ClassX4 Y) (hQ2 : IsPGroup 2 ↥Q)
    (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q * y = y * q) : commV Y ≤ fixV Q := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hUY : ∀ N : Subgroup V, (∀ g ∈ Y, ∀ u ∈ commV Y, g u * u⁻¹ ∈ N) → commV Y ≤ N :=
    fun N hN => commV_le_of_perfect Y N fun g u => hN g g.2 u u.2
  exact commV_le_fixV_of_irreducible hV hUY (ClassX4.invariant_irreducible hperf hV hY) hQ2 hQY

theorem commV_le_fixV_of_commute_three (hV : ∀ v : V, v ^ 2 = 1) {Y Q : Subgroup (MulAut V)}
    (h3 : Nat.card ↥Y = 3) (h4 : Nat.card ↥(commV Y) = 4) (hQ2 : IsPGroup 2 ↥Q)
    (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q * y = y * q) : commV Y ≤ fixV Q := by
  have hodd : Odd (Nat.card ↥Y) := by rw [h3]; decide
  have hbot : commV Y ⊓ fixV Y = ⊥ := commV_inf_fixV_eq_bot_of_odd hV Y hodd
  have habs : ∀ A : Subgroup V, (∀ x ∈ Y, ∀ a ∈ A, x a ∈ A) → A ≤ commV Y →
      A = ⊥ ∨ A = commV Y := by
    intro A hA hAU
    have hdvd : Nat.card ↥A ∣ 2 ^ 2 := by
      have := Subgroup.card_dvd_of_le hAU
      rwa [h4] at this
    obtain ⟨m, hm, hAm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases m
    · left
      exact Subgroup.card_eq_one.mp (by simpa using hAm)
    · exfalso
      have hA2 : Nat.card ↥A = 2 := by simpa using hAm
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp (by
        intro h
        rw [h] at hA2
        simp at hA2)
      obtain ⟨y0, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA2
      have hne : ∀ b : ↥A, (b : V) ≠ 1 → b = y0 := fun b hb => huniq b fun h => hb (by
        rw [h]; rfl)
      have hfix : ∀ g ∈ Y, g a = a := by
        intro g hg
        have h1 : g (a : V) ∈ A := hA g hg a a.2
        have h2 : g (a : V) ≠ 1 := fun h => ha1 (Subtype.ext ((MulEquiv.map_eq_one_iff g).mp h))
        have h3 := hne ⟨g (a : V), h1⟩ h2
        have h4 := hne a (fun h => ha1 (Subtype.ext h))
        exact congrArg Subtype.val (h3.trans h4.symm)
      have : (a : V) ∈ commV Y ⊓ fixV Y := ⟨hAU a.2, fun g hg => hfix g hg⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact ha1 (Subtype.ext this)
    · right
      refine Subgroup.eq_of_le_of_card_ge hAU ?_
      rw [h4]
      simp at hAm
      omega
  have hUY : ∀ N : Subgroup V, (∀ g ∈ Y, ∀ u ∈ commV Y, g u * u⁻¹ ∈ N) → commV Y ≤ N := by
    intro N hN
    have hN0 : commOn Y (commV Y) ≤ N := by
      unfold commOn
      rw [Subgroup.closure_le]
      rintro _ ⟨g, hg, s, hs, rfl⟩
      exact hN g hg s hs
    rcases habs (commOn Y (commV Y))
      (commOn_invariant fun g hg s hs => apply_mem_commV_of_mem hg s hs)
      (commOn_le_commV _) with h0 | h0
    · exfalso
      have hfix : ∀ u ∈ commV Y, ∀ g ∈ Y, g u = u := by
        intro u hu g hg
        have : g u * u⁻¹ ∈ commOn Y (commV Y) := Subgroup.subset_closure ⟨g, hg, u, hu, rfl⟩
        rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at this
        exact this
      have hle : commV Y ≤ ⊥ := by
        rw [← hbot]
        exact fun u hu => ⟨hu, fun g hg => hfix u hu g hg⟩
      have := Subgroup.card_eq_one.mpr (le_bot_iff.mp hle)
      omega
    · rw [← h0]
      exact hN0
  exact commV_le_fixV_of_irreducible hV hUY (rel_irreducible_of_abs habs) hQ2 hQY

end Irr

section PCore

variable {V : Type} [CommGroup V]

theorem yuSec_mem_pCore (hV : ∀ v : V, v ^ 2 = 1) (Y : Subgroup (MulAut V)) {r : ↥Y}
    (hr : r ∈ pCore 2 ↥Y) : yuSec Y r ∈ pCore 2 ↥(yuHol Y) := by
  have hNn : ((pCore 2 ↥Y).comap (yuProj Y)).Normal :=
    (pCore_normal (p := 2) (G := ↥Y)).comap _
  have hN2 : IsPGroup 2 ↥((pCore 2 ↥Y).comap (yuProj Y)) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := pCore_isPGroup (p := 2) (G := ↥Y) ⟨yuProj Y x, hx⟩
    have h1 : yuProj Y (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 : x ^ 2 ^ k ∈ (yuInc Y).range := by
      rw [← ker_yuProj]
      exact h1
    obtain ⟨u, hu⟩ := h2
    refine ⟨k + 1, Subtype.ext ?_⟩
    show x ^ 2 ^ (k + 1) = 1
    rw [pow_succ, pow_mul, ← hu]
    exact yuInc_sq Y hV u
  exact (le_sSup ⟨hNn, hN2⟩ : (pCore 2 ↥Y).comap (yuProj Y) ≤ pCore 2 ↥(yuHol Y))
    (by rw [Subgroup.mem_comap, yuProj_sec]; exact hr)

variable [Finite V]

theorem pCore_le_center_of_inClassX (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : IsShortGroup ↥(yuHol Y)) :
    pCore 2 ↥Y ≤ Subgroup.center ↥Y := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  intro r hr
  let φ : (↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y)) ≃* (↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y)) :=
    MulEquiv.refl _
  exact yuTheta_ker_le_center Y φ hV hX
    (MonoidHom.mem_ker.mpr ((yuTheta_eq_one_iff Y φ r).mpr (yuSec_mem_pCore hV Y hr)))

theorem commutator_oTwoIn_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hY : ClassX4 Y) : ⁅oTwoIn Y, Y⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨r, hr0, rfl⟩
  have hr : r ∈ pCore 2 ↥Y := hr0
  have hrc : r ∈ Subgroup.center ↥Y := by
    rcases hY with hX | ⟨n, hn, hY⟩ | ⟨n, hn, hY⟩
    · exact pCore_le_center_of_inClassX hV hperf hX.1 hr
    · rw [NatOmegaN.pCore_eq_bot hn (Or.inr hY), Subgroup.mem_bot] at hr
      rw [hr]
      exact one_mem _
    · rw [NatOmegaN.pCore_eq_bot hn (Or.inl hY), Subgroup.mem_bot] at hr
      rw [hr]
      exact one_mem _
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hrc ⟨y, hy⟩)

end PCore

end CFSG.CGT.PushingUpLit.CGT6
