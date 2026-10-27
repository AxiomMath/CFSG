module

public import CFSG.GH74.E2.Cl2CaseDefs
public import CFSG.GH74.E2.Cl2Cl3

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

section Calc

variable {Q : Type*} [Group Q] {a b : MulAut Q} {N : Subgroup Q}

private theorem caseA_cube {g : MulAut Q} (hg : g ^ 3 = 1) (x : Q) : g (g (g x)) = x := by
  have := congrArg (fun f : MulAut Q => f x) hg
  simpa [pow_succ, MulAut.mul_apply] using this

private theorem caseA_comm (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (q : Q) : q * n = n * q :=
  Subgroup.mem_center_iff.mp (h.N_central hn) q

private theorem caseA_conj (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (q : Q) : q * n * q⁻¹ = n := by
  rw [caseA_comm h hn q]
  group

private theorem caseA_conj' (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (q : Q) : n * q * n⁻¹ = q := by
  rw [← caseA_comm h hn q]
  group

private theorem caseA_N_inv (h : Cl3 Q a b N) (x : Q) : a x ∈ N ↔ x ∈ N := by
  refine ⟨fun hx => ?_, h.N_inva x⟩
  rw [← caseA_cube h.bpair.a_cube x]
  exact h.N_inva _ (h.N_inva _ hx)

private theorem caseA_dsub (g g' : Q) : ⁅g, g'⁆ ∈ dsub Q :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top g')

private theorem caseA_commN (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (z : Q) : ⁅u, z⁆ ∈ N := by
  rw [h.N_eq]
  exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_top z)

private theorem caseA_commN' (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (z : Q) :
    ⁅z, u⁆ ∈ N := by
  rw [← commutatorElement_inv]
  exact N.inv_mem (caseA_commN h hu z)

private theorem caseA_N_le (h : Cl3 Q a b N) : N ≤ dsub Q := by
  rw [h.N_eq]
  exact Subgroup.commutator_le_left _ _

private theorem caseA_comm_one (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (k : Q) : ⁅n, k⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (caseA_comm h hn k).symm

private theorem caseA_mul_central_left (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N) (w k : Q) :
    ⁅n * w, k⁆ = ⁅w, k⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, caseA_comm_one h hn k, mul_one,
    caseA_conj' h hn]

private theorem caseA_mul_left (h : Cl3 Q a b N) {g g' k : Q} (hg' : ⁅g', k⁆ ∈ N) :
    ⁅g * g', k⁆ = ⁅g', k⁆ * ⁅g, k⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, caseA_conj h hg' g]

private theorem caseA_mul_right (h : Cl3 Q a b N) {g k k' : Q} (hk' : ⁅g, k'⁆ ∈ N) :
    ⁅g, k * k'⁆ = ⁅g, k⁆ * ⁅g, k'⁆ := by
  have h1 := caseA_conj h hk' k
  calc ⁅g, k * k'⁆ = ⁅g, k⁆ * (k * ⁅g, k'⁆ * k⁻¹) := by
        rw [commutatorElement_mul_right_eq_mul_conj]
        simp only [mul_assoc]
    _ = ⁅g, k⁆ * ⁅g, k'⁆ := by rw [h1]

private theorem caseA_inv_left (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q) (k : Q) :
    ⁅u⁻¹, k⁆ = ⁅u, k⁆⁻¹ := by
  have h1 : ⁅u⁻¹ * u, k⁆ = ⁅u, k⁆ * ⁅u⁻¹, k⁆ := caseA_mul_left h (caseA_commN h hu k)
  rw [inv_mul_cancel, commutatorElement_one_left] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

private theorem caseA_triple_swap (h : Cl3 Q a b N) (g g' k : Q) :
    ⁅⁅g, g'⁆, k⁆ = ⁅⁅g', g⁆, k⁆⁻¹ := by
  rw [← commutatorElement_inv g' g]
  exact caseA_inv_left h (caseA_dsub g' g) k

private theorem caseA_triple_mul_left (h : Cl3 Q a b N) (g g' g'' k : Q) :
    ⁅⁅g * g', g''⁆, k⁆ = ⁅⁅g, g''⁆, k⁆ * ⁅⁅g', g''⁆, k⁆ := by
  have e : ⁅g * g', g''⁆ = ⁅g, ⁅g', g''⁆⁆ * (⁅g', g''⁆ * ⁅g, g''⁆) := by
    simp only [commutatorElement_def]
    group
  have hc : ⁅g, ⁅g', g''⁆⁆ ∈ N := caseA_commN' h (caseA_dsub g' g'') g
  rw [e, caseA_mul_central_left h hc]
  exact caseA_mul_left h (g := ⁅g', g''⁆) (g' := ⁅g, g''⁆) (caseA_commN h (caseA_dsub g g'') k)

private theorem caseA_triple_mul_mid (h : Cl3 Q a b N) (g g' g'' k : Q) :
    ⁅⁅g, g' * g''⁆, k⁆ = ⁅⁅g, g'⁆, k⁆ * ⁅⁅g, g''⁆, k⁆ := by
  have e : ⁅g, g' * g''⁆ = ⁅g, g'⁆ * (⁅g', ⁅g, g''⁆⁆ * ⁅g, g''⁆) := by
    simp only [commutatorElement_def]
    group
  have hc : ⁅g', ⁅g, g''⁆⁆ ∈ N := caseA_commN' h (caseA_dsub g g'') g'
  have e2 : ⁅g, g'⁆ * (⁅g', ⁅g, g''⁆⁆ * ⁅g, g''⁆) = ⁅g', ⁅g, g''⁆⁆ * (⁅g, g'⁆ * ⁅g, g''⁆) := by
    rw [← mul_assoc, caseA_comm h hc, mul_assoc]
  rw [e, e2, caseA_mul_central_left h hc,
    caseA_mul_left h (g := ⁅g, g'⁆) (g' := ⁅g, g''⁆) (caseA_commN h (caseA_dsub g g'') k)]
  exact (caseA_comm h (caseA_commN h (caseA_dsub g g'') k) _).symm

private theorem caseA_triple_mul_right (h : Cl3 Q a b N) (g g' k k' : Q) :
    ⁅⁅g, g'⁆, k * k'⁆ = ⁅⁅g, g'⁆, k⁆ * ⁅⁅g, g'⁆, k'⁆ :=
  caseA_mul_right h (caseA_commN h (caseA_dsub g g') k')

private theorem caseA_gen {s : Set Q} (hs : Subgroup.closure s = ⊤) {f : Q → Q}
    (hmul : ∀ x y, f (x * y) = f x * f y) (h1 : ∀ g ∈ s, f g = 1) (x : Q) : f x = 1 := by
  let φ : Q →* Q := MonoidHom.mk' f hmul
  have hle : Subgroup.closure s ≤ φ.ker :=
    (Subgroup.closure_le _).2 (fun g hg => MonoidHom.mem_ker.mpr (h1 g hg))
  rw [hs] at hle
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top x))

private theorem caseA_comm_comm {g g' k : Q} (h1 : ⁅g, k⁆ = 1) (h2 : ⁅g', k⁆ = 1) :
    ⁅⁅g, g'⁆, k⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute] at h1 h2 ⊢
  rw [commutatorElement_def]
  exact (((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left)

private def caseA_S (h : Cl3 Q a b N) (y : Q) : Subgroup Q where
  carrier := {z | ⁅z, y⁆ ∈ N}
  mul_mem' := fun {z z'} hz hz' => by
    show ⁅z * z', y⁆ ∈ N
    rw [caseA_mul_left h hz']
    exact N.mul_mem hz' hz
  one_mem' := by
    show ⁅(1 : Q), y⁆ ∈ N
    rw [commutatorElement_one_left]
    exact N.one_mem
  inv_mem' := fun {z} hz => by
    show ⁅z⁻¹, y⁆ ∈ N
    have h1 : ⁅y, z⁆ ∈ N := by
      rw [← commutatorElement_inv]
      exact N.inv_mem hz
    have h2 := caseA_conj h h1 z⁻¹
    rw [inv_inv] at h2
    rw [commutatorElement_inv_left, h2]
    exact h1

private theorem caseA_mem_S (h : Cl3 Q a b N) (y z : Q) : z ∈ caseA_S h y ↔ ⁅z, y⁆ ∈ N :=
  Iff.rfl

end Calc

section Fixed

variable {Q : Type*} [Group Q] [Finite Q]

private theorem caseA_fixed (hQ : IsPGroup 2 Q) {a b : MulAut Q} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) {S : Subgroup Q} (hS : ∀ z ∈ S, a z ∈ S) {x : Q} (hx : b x = x)
    (hxa : x⁻¹ * a x ∈ S) : ∃ n ∈ S, b n = n ∧ a (x * n) = x * n := by
  classical
  have h3 : ∀ y, a (a (a y)) = y := fun y => by
    have := congrArg (fun f : MulAut Q => f y) ha
    simpa [pow_succ, MulAut.mul_apply] using this
  have hba : ∀ y, a (b y) = b (a y) := fun y => by
    have := congrArg (fun f : MulAut Q => f y) hab
    simpa [MulAut.mul_apply] using this
  let X : Set Q := {y | x⁻¹ * y ∈ S ∧ b y = y}
  have hmaps : ∀ y ∈ X, a y ∈ X := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · have h1 : x⁻¹ * a y = (x⁻¹ * a x) * a (x⁻¹ * y) := by
        rw [map_mul, map_inv]; group
      show x⁻¹ * a y ∈ S
      rw [h1]
      exact S.mul_mem hxa (hS _ hy1)
    · show b (a y) = a y
      rw [← hba, hy2]
  let φ : X → X := fun y => ⟨a y.1, hmaps y.1 y.2⟩
  let σ : Equiv.Perm X :=
    { toFun := φ
      invFun := fun y => φ (φ y)
      left_inv := fun y => Subtype.ext (h3 y.1)
      right_inv := fun y => Subtype.ext (h3 y.1) }
  have hσ3' : ∀ y, σ (σ (σ y)) = y := fun y =>
    Subtype.ext (show a (a (a y.1)) = y.1 from h3 y.1)
  have hσ3 : σ ^ 3 = 1 := by
    ext y
    simp [pow_succ, Equiv.Perm.mul_apply, hσ3']
  have hpg : IsPGroup 3 (Subgroup.zpowers σ) := by
    rintro ⟨τ, hτ⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    refine ⟨1, Subtype.ext ?_⟩
    show (σ ^ m) ^ (3 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hσ3]
  have hmod := hpg.card_modEq_card_fixedPoints X
  have hXcard : Nat.card X = Nat.card ↥(S ⊓ fixSub b) := by
    refine Nat.card_congr (Equiv.mk
      (fun y : X => (⟨x⁻¹ * y.1, y.2.1, by
        show b (x⁻¹ * y.1) = x⁻¹ * y.1
        rw [map_mul, map_inv, hx, y.2.2]⟩ : ↥(S ⊓ fixSub b)))
      (fun n : ↥(S ⊓ fixSub b) => (⟨x * n.1, by
        have h1 : x⁻¹ * (x * n.1) = n.1 := by group
        rw [h1]; exact n.2.1, by
        have hb : b n.1 = n.1 := n.2.2
        show b (x * n.1) = x * n.1
        rw [map_mul, hx, hb]⟩ : X))
      (fun y => Subtype.ext (by simp)) (fun n => Subtype.ext (by simp)))
  have hNp : ∃ m, Nat.card ↥(S ⊓ fixSub b) = 2 ^ m :=
    (IsPGroup.iff_card).mp (hQ.to_subgroup _)
  have hne : (MulAction.fixedPoints (Subgroup.zpowers σ) X).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have h0 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) X) = 0 := by
      rw [hempty]; simp
    rw [h0] at hmod
    have h3d : 3 ∣ Nat.card X := Nat.modEq_zero_iff_dvd.mp hmod
    obtain ⟨m, hm⟩ := hNp
    rw [hXcard, hm] at h3d
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    omega
  obtain ⟨y, hy⟩ := hne
  have hfix : σ y = y := by
    have := hy ⟨σ, Subgroup.mem_zpowers σ⟩
    exact this
  have hgy : a y.1 = y.1 := congrArg Subtype.val hfix
  refine ⟨x⁻¹ * y.1, y.2.1, ?_, ?_⟩
  · show b (x⁻¹ * y.1) = x⁻¹ * y.1
    rw [map_mul, map_inv, hx, y.2.2]
  · rw [mul_inv_cancel_left]
    exact hgy

variable {a b : MulAut Q} {N : Subgroup Q}

private theorem caseA_A1 (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseAHyp Q a b N) {x y : Q}
    (hx : b x = x) (hy : a y = y) : ⁅x, y⁆ ∈ N := by
  obtain ⟨⟨hNb, hNa⟩, hG2⟩ := hc
  have hS : ∀ z ∈ caseA_S h y, a z ∈ caseA_S h y := by
    intro z hz
    have hz' : ⁅z, y⁆ ∈ N := hz
    show ⁅a z, y⁆ ∈ N
    have : ⁅a z, y⁆ = a ⁅z, y⁆ := by rw [map_commutatorElement, hy]
    rw [this]
    exact h.N_inva _ hz'
  have hxa : x⁻¹ * a x ∈ caseA_S h y := by
    show ⁅x⁻¹ * a x, y⁆ ∈ N
    have e : ⁅x⁻¹ * a x, y⁆ = x⁻¹ * (a ⁅x, y⁆ * ⁅x, y⁆⁻¹) * x := by
      have : ⁅a x, y⁆ = a ⁅x, y⁆ := by rw [map_commutatorElement, hy]
      rw [← this]
      simp only [commutatorElement_def]
      group
    rw [e]
    have hm : a ⁅x, y⁆ * ⁅x, y⁆⁻¹ ∈ N := (hG2 _ (caseA_dsub x y)).1
    have h2 := caseA_conj h hm x⁻¹
    rw [inv_inv] at h2
    rw [h2]
    exact hm
  obtain ⟨n, hn, hbn, hfix⟩ := caseA_fixed hQ h.bpair.comm h.bpair.a_cube hS hx hxa
  have hfx : x * n ∈ fixSub a ⊓ fixSub b := by
    refine ⟨hfix, ?_⟩
    show b (x * n) = x * n
    rw [map_mul, hx, hbn]
  have hD : x * n ∈ dsub Q := h.fixB_le_dsub hQ hfx
  have h2 : x * n ∈ caseA_S h y := caseA_commN h hD y
  have h3 : n⁻¹ ∈ caseA_S h y := (caseA_S h y).inv_mem hn
  have := (caseA_S h y).mul_mem h2 h3
  rwa [mul_inv_cancel_right] at this

private theorem caseA_A2 (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseAHyp Q a b N) {x : Q}
    (hx : b x = x) {w : Q} (hw : w ∈ commSub a b) : ⁅x, w⁆ = 1 := by
  have hNb : ∀ n ∈ N, b n = n := hc.1.1
  have hle : commSub a b ≤ Subgroup.centralizer {x} := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hz' : a z = z := hz
    have hν : ⁅g, z⁆ ∈ N := caseA_A1 hQ h hc hx hz'
    have h1 : ⁅g, b z⁆ = ⁅g, z⁆ := by
      have : ⁅g, b z⁆ = b ⁅g, z⁆ := by rw [map_commutatorElement, hx]
      rw [this]
      exact hNb _ hν
    have h2 : ⁅g, z⁻¹⁆ = ⁅g, z⁆⁻¹ := by
      have hn : ⁅g, z⁆⁻¹ ∈ N := N.inv_mem hν
      have h3 := caseA_conj h hn z⁻¹
      rw [inv_inv] at h3
      rw [commutatorElement_inv_right, ← commutatorElement_inv g z, h3]
    have h4 : ⁅g, z⁻¹ * b z⁆ = 1 := by
      rw [caseA_mul_right h (by rw [h1]; exact hν), h1, h2, inv_mul_cancel]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h4)
  have := Subgroup.mem_centralizer_iff.mp (hle hw) x rfl
  exact commutatorElement_eq_one_iff_mul_comm.mpr this

private theorem caseA_relIndex_ne_zero (H K : Subgroup Q) : H.relIndex K ≠ 0 := by
  have : H.IsFiniteRelIndex K := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
    exact Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.relIndex_ne_zero

private theorem caseA_key (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseAHyp Q a b N) {x y : Q}
    (hx : b x = x) (hy : y ∈ commSub a b)
    (hgen : Subgroup.closure ({x, a x, y, b y} : Set Q) = ⊤) :
    ¬ (⁅⁅x, a x⁆, x⁆ = 1 ∧ ⁅⁅x, a x⁆, a x⁆ = 1) := by
  rintro ⟨hu1, hu2⟩
  have hNa : ∀ n ∈ N, a n = n → n = 1 := hc.1.2
  have hba : ∀ z, a (b z) = b (a z) := fun z => by
    have := congrArg (fun f : MulAut Q => f z) h.bpair.comm
    simpa [MulAut.mul_apply] using this
  have hxa : b (a x) = a x := by rw [← hba, hx]
  have hya : a y = y := commSub_le_fixSub_a h.bpair hy
  have hby : b y ∈ commSub a b := by
    have h1 : y⁻¹ * b y ∈ commSub a b := Subgroup.subset_closure ⟨y, hya, rfl⟩
    have := (commSub a b).mul_mem hy h1
    rwa [mul_inv_cancel_left] at this
  have hbya : a (b y) = b y := by rw [hba, hya]
  have h1 : ⁅x, y⁆ = 1 := caseA_A2 hQ h hc hx hy
  have h2 : ⁅x, b y⁆ = 1 := caseA_A2 hQ h hc hx hby
  have h3 : ⁅a x, y⁆ = 1 := caseA_A2 hQ h hc hxa hy
  have h4 : ⁅a x, b y⁆ = 1 := caseA_A2 hQ h hc hxa hby
  have sw : ∀ g k : Q, ⁅g, k⁆ = 1 → ⁅k, g⁆ = 1 := fun g k hgk => by
    rw [← commutatorElement_inv, hgk, inv_one]
  have hu_y : ⁅⁅x, a x⁆, y⁆ = 1 := caseA_comm_comm h1 h3
  have hu_by : ⁅⁅x, a x⁆, b y⁆ = 1 := caseA_comm_comm h2 h4
  have hv_x : ⁅⁅y, b y⁆, x⁆ = 1 := caseA_comm_comm (sw _ _ h1) (sw _ _ h2)
  have hv_ax : ⁅⁅y, b y⁆, a x⁆ = 1 := caseA_comm_comm (sw _ _ h3) (sw _ _ h4)
  have hv_a : a ⁅y, b y⁆ = ⁅y, b y⁆ := by rw [map_commutatorElement, hya, hbya]
  have hvN : ∀ k : Q, a k = k → ⁅⁅y, b y⁆, k⁆ = 1 := fun k hk => by
    have hmem : ⁅⁅y, b y⁆, k⁆ ∈ N := caseA_commN h (caseA_dsub y (b y)) k
    have hfix : a ⁅⁅y, b y⁆, k⁆ = ⁅⁅y, b y⁆, k⁆ := by
      rw [map_commutatorElement, hv_a, hk]
    exact hNa _ hmem hfix
  have hv_y : ⁅⁅y, b y⁆, y⁆ = 1 := hvN y hya
  have hv_by : ⁅⁅y, b y⁆, b y⁆ = 1 := hvN _ hbya
  have hgens : ∀ g ∈ ({x, a x, y, b y} : Set Q), ∀ g' ∈ ({x, a x, y, b y} : Set Q),
      ∀ k ∈ ({x, a x, y, b y} : Set Q), ⁅⁅g, g'⁆, k⁆ = 1 := by
    intro g hg g' hg' k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hg' hk
    have Tu : ⁅⁅x, a x⁆, k⁆ = 1 := by
      rcases hk with hk | hk | hk | hk <;> rw [hk]
      · exact hu1
      · exact hu2
      · exact hu_y
      · exact hu_by
    have Tv : ⁅⁅y, b y⁆, k⁆ = 1 := by
      rcases hk with hk | hk | hk | hk <;> rw [hk]
      · exact hv_x
      · exact hv_ax
      · exact hv_y
      · exact hv_by
    have Tu' : ⁅⁅a x, x⁆, k⁆ = 1 := by rw [caseA_triple_swap h, Tu, inv_one]
    have Tv' : ⁅⁅b y, y⁆, k⁆ = 1 := by rw [caseA_triple_swap h, Tv, inv_one]
    rcases hg with hg | hg | hg | hg <;> rcases hg' with hg' | hg' | hg' | hg' <;> rw [hg, hg']
    · rw [commutatorElement_self, commutatorElement_one_left]
    · exact Tu
    · rw [h1, commutatorElement_one_left]
    · rw [h2, commutatorElement_one_left]
    · exact Tu'
    · rw [commutatorElement_self, commutatorElement_one_left]
    · rw [h3, commutatorElement_one_left]
    · rw [h4, commutatorElement_one_left]
    · rw [sw _ _ h1, commutatorElement_one_left]
    · rw [sw _ _ h3, commutatorElement_one_left]
    · rw [commutatorElement_self, commutatorElement_one_left]
    · exact Tv
    · rw [sw _ _ h2, commutatorElement_one_left]
    · rw [sw _ _ h4, commutatorElement_one_left]
    · exact Tv'
    · rw [commutatorElement_self, commutatorElement_one_left]
  have R : ∀ g ∈ ({x, a x, y, b y} : Set Q), ∀ g' ∈ ({x, a x, y, b y} : Set Q), ∀ k : Q,
      ⁅⁅g, g'⁆, k⁆ = 1 := fun g hg g' hg' =>
    caseA_gen hgen (f := fun k => ⁅⁅g, g'⁆, k⁆) (caseA_triple_mul_right h g g')
      (fun k hk => hgens g hg g' hg' k hk)
  have M : ∀ g ∈ ({x, a x, y, b y} : Set Q), ∀ k g' : Q, ⁅⁅g, g'⁆, k⁆ = 1 := fun g hg k =>
    caseA_gen hgen (f := fun g' => ⁅⁅g, g'⁆, k⁆) (fun g' g'' => caseA_triple_mul_mid h g g' g'' k)
      (fun g' hg' => R g hg g' hg' k)
  have L : ∀ g g' k : Q, ⁅⁅g, g'⁆, k⁆ = 1 := fun g g' k =>
    caseA_gen hgen (f := fun g₁ => ⁅⁅g₁, g'⁆, k⁆) (fun g₁ g₂ => caseA_triple_mul_left h g₁ g₂ g' k)
      (fun g₁ hg₁ => M g₁ hg₁ k g') g
  have hDc : dsub Q ≤ center Q := by
    refine Subgroup.commutator_le.2 (fun g _ g' _ => ?_)
    rw [Subgroup.mem_center_iff]
    intro k
    exact (commutatorElement_eq_one_iff_mul_comm.mp (L g g' k)).symm
  have hN : N ≤ ⊥ := by
    rw [h.N_eq]
    refine Subgroup.commutator_le.2 (fun u hu k _ => ?_)
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hDc hu) k).symm
  exact h.N_ne (le_bot_iff.mp hN)

private theorem caseA_final (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseAHyp Q a b N) {x : Q}
    (hx : b x = x) (hxV : ∀ w ∈ commSub a b, ⁅x, w⁆ = 1)
    (haxV : ∀ w ∈ commSub a b, ⁅a x, w⁆ = 1)
    (htop : Subgroup.closure ({x, a x} : Set Q) ⊔ commSub a b = ⊤)
    (hkey : ¬ (⁅⁅x, a x⁆, x⁆ = 1 ∧ ⁅⁅x, a x⁆, a x⁆ = 1)) : False := by
  classical
  have hNb : ∀ n ∈ N, b n = n := hc.1.1
  have hNa : ∀ n ∈ N, a n = n → n = 1 := hc.1.2
  have hG2 := hc.2
  have hba : ∀ z, a (b z) = b (a z) := fun z => by
    have := congrArg (fun f : MulAut Q => f z) h.bpair.comm
    simpa [MulAut.mul_apply] using this
  have hxa : b (a x) = a x := by rw [← hba, hx]
  have hud : ⁅x, a x⁆ ∈ dsub Q := caseA_dsub x (a x)
  have hbu : b ⁅x, a x⁆ = ⁅x, a x⁆ := by rw [map_commutatorElement, hx, hxa]
  have hn1 : ⁅x, a x⁆⁻¹ * a ⁅x, a x⁆ ∈ N := by
    have hm : a ⁅x, a x⁆ * ⁅x, a x⁆⁻¹ ∈ N := (hG2 _ hud).1
    have h3 : ⁅x, a x⁆⁻¹ * a ⁅x, a x⁆
        = ⁅x, a x⁆⁻¹ * (a ⁅x, a x⁆ * ⁅x, a x⁆⁻¹) * ⁅x, a x⁆⁻¹⁻¹ := by group
    rw [h3, caseA_conj h hm]
    exact hm
  have : N.Normal := ⟨fun n hn q => by rw [caseA_conj h hn q]; exact hn⟩
  obtain ⟨d, hd, hdfix⟩ := exists_fixed_mul_mem hQ h.bpair.a_cube (caseA_N_inv h) hn1
  generalize hu : ⁅x, a x⁆ = u at hud hbu hn1 hdfix hkey
  have hu'a : a (u * d) = u * d := hdfix
  have hu'b : b (u * d) = u * d := by rw [map_mul, hbu, hNb d hd]
  have hu'D : u * d ∈ dsub Q := (dsub Q).mul_mem hud (caseA_N_le h hd)
  have hu'comm : ∀ k : Q, ⁅u * d, k⁆ = ⁅u, k⁆ := fun k => by
    rw [commutatorElement_mul_left_eq_conj_mul, caseA_comm_one h hd k, mul_one, mul_inv_cancel,
      one_mul]
  have hkey' : ¬ (⁅u * d, x⁆ = 1 ∧ ⁅u * d, a x⁆ = 1) := by
    rw [hu'comm, hu'comm]
    exact hkey
  generalize hu' : u * d = u' at hu'a hu'b hu'D hu'comm hkey'
  have hVa : ∀ w ∈ commSub a b, a w = w := fun w hw => commSub_le_fixSub_a h.bpair hw
  have hu'V : ∀ v ∈ commSub a b, u' * v = v * u' := by
    intro v hv
    have h1 : ⁅⁅x, a x⁆, v⁆ = 1 := caseA_comm_comm (hxV v hv) (haxV v hv)
    rw [hu] at h1
    have h2 : u * v = v * u := commutatorElement_eq_one_iff_mul_comm.mp h1
    rw [← hu']
    calc u * d * v = u * (d * v) := mul_assoc _ _ _
      _ = u * (v * d) := by rw [(caseA_comm h hd v).symm]
      _ = u * v * d := (mul_assoc _ _ _).symm
      _ = v * u * d := by rw [h2]
      _ = v * (u * d) := mul_assoc _ _ _
  have hZle : zpowers u' ≤
      fixSub a ⊓ fixSub b ⊓ dsub Q ⊓ Subgroup.centralizer (commSub a b : Set Q) := by
    rw [Subgroup.zpowers_le]
    refine ⟨⟨⟨hu'a, hu'b⟩, hu'D⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun v hv => (hu'V v hv).symm)
  have hZa : ∀ z ∈ zpowers u', a z = z := fun z hz => (hZle hz).1.1.1
  have hZb : ∀ z ∈ zpowers u', b z = z := fun z hz => (hZle hz).1.1.2
  have hZD : ∀ z ∈ zpowers u', z ∈ dsub Q := fun z hz => (hZle hz).1.2
  have hZV : ∀ z ∈ zpowers u', ∀ v ∈ commSub a b, z * v = v * z := fun z hz v hv =>
    ((Subgroup.mem_centralizer_iff.mp (hZle hz).2) v hv).symm
  have hZZ : ∀ z ∈ zpowers u', ∀ r ∈ zpowers u', z * r = r * z := by
    intro z hz r hr
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    exact (Commute.zpow_zpow_self u' j k).eq
  have hZN : ∀ z ∈ zpowers u', ∀ n ∈ N, z * n = n * z := fun z _ n hn => caseA_comm h hn z
  have hcomm : ∀ p ∈ zpowers u' ⊔ N, ∀ v ∈ commSub a b, p * v = v * p := by
    intro p hp v hv
    obtain ⟨z, hz, n, hn, rfl⟩ := (mem_sup_iff_of_commute hZN).mp hp
    calc z * n * v = z * (n * v) := mul_assoc _ _ _
      _ = z * (v * n) := by rw [(caseA_comm h hn v).symm]
      _ = z * v * n := (mul_assoc _ _ _).symm
      _ = v * z * n := by rw [hZV z hz v hv]
      _ = v * (z * n) := mul_assoc _ _ _
  have hUZ : ∀ p ∈ zpowers u' ⊔ N, ∀ r ∈ zpowers u', p * r = r * p := by
    intro p hp r hr
    obtain ⟨z, hz, n, hn, rfl⟩ := (mem_sup_iff_of_commute hZN).mp hp
    calc z * n * r = z * (n * r) := mul_assoc _ _ _
      _ = z * (r * n) := by rw [(caseA_comm h hn r).symm]
      _ = z * r * n := (mul_assoc _ _ _).symm
      _ = r * z * n := by rw [hZZ z hz r hr]
      _ = r * (z * n) := mul_assoc _ _ _
  have hRU : zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q) ≤ zpowers u' ⊔ N :=
    inf_le_left.trans le_sup_left
  have hRV : frattini Q ⊓ commSub a b ≤ commSub a b := inf_le_right
  have hnU : ∀ p ∈ zpowers u' ⊔ N, ∀ r ∈ zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q),
      p * r * p⁻¹ ∈ zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q) := by
    intro p hp r hr
    rw [hUZ p hp r hr.1, mul_assoc, mul_inv_cancel, mul_one]
    exact hr
  have hnV : ∀ v ∈ commSub a b, ∀ r ∈ frattini Q ⊓ commSub a b,
      v * r * v⁻¹ ∈ frattini Q ⊓ commSub a b := by
    intro v hv r hr
    exact ⟨(inferInstance : (frattini Q).Normal).conj_mem r hr.1 v,
      (commSub a b).mul_mem ((commSub a b).mul_mem hv hr.2) ((commSub a b).inv_mem hv)⟩
  have hsqU : ∀ p ∈ zpowers u' ⊔ N,
      p * p ∈ zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q) := by
    intro p hp
    obtain ⟨z, hz, n, hn, rfl⟩ := (mem_sup_iff_of_commute hZN).mp hp
    have hnn : n * n = 1 := h.N_elem n hn
    have e : z * n * (z * n) = z * z := by
      calc z * n * (z * n) = z * (n * z) * n := by group
        _ = z * (z * n) * n := by rw [← hZN z hz n hn]
        _ = z * z * (n * n) := by group
        _ = z * z := by rw [hnn, mul_one]
    rw [e]
    have hC : z * z ∈ Subgroup.centralizer ({x, a x} : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g _
      have hzD := hZD z hz
      have h1 : ⁅z * z, g⁆ = 1 := by
        rw [caseA_mul_left h (caseA_commN h hzD g)]
        exact h.N_elem _ (caseA_commN h hzD g)
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    exact ⟨(zpowers u').mul_mem hz hz, hC⟩
  have hsqV : ∀ v ∈ commSub a b, v * v ∈ frattini Q ⊓ commSub a b := fun v hv =>
    ⟨mul_self_mem_frattini hQ v, (commSub a b).mul_mem hv hv⟩
  have hint : (zpowers u' ⊔ N) ⊓ commSub a b ≤
      (zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q)) ⊓ (frattini Q ⊓ commSub a b) := by
    rintro w ⟨hwU, hwV⟩
    obtain ⟨z, hz, n, hn, rfl⟩ := (mem_sup_iff_of_commute hZN).mp hwU
    have hwa : a (z * n) = z * n := hVa _ hwV
    have hn1 : n = 1 := by
      have h1 : z * a n = z * n := by
        have h2 := hwa
        rw [map_mul, hZa z hz] at h2
        exact h2
      exact hNa n hn (mul_left_cancel h1)
    subst hn1
    rw [mul_one] at hwV ⊢
    have hC : z ∈ Subgroup.centralizer ({x, a x} : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rcases hg with hg | hg
      · rw [hg]
        exact commutatorElement_eq_one_iff_mul_comm.mp (hxV z hwV)
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact commutatorElement_eq_one_iff_mul_comm.mp (haxV z hwV)
    exact ⟨⟨hz, hC⟩, h.bpair.fix_inf_le hQ h.four ⟨hVa z hwV, hZb z hz⟩, hwV⟩
  have hmain := FourGen.relIndex_mul_le h.four hcomm hRU hRV hnU hnV hsqU hsqV hint
  have hA : 2 ≤ (zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q)).relIndex (zpowers u') := by
    have h0 : (zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q)).relIndex (zpowers u') ≠ 0 :=
      caseA_relIndex_ne_zero _ _
    have h1 : (zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q)).relIndex (zpowers u') ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      have hu'mem : u' ∈ Subgroup.centralizer ({x, a x} : Set Q) :=
        (h1 (Subgroup.mem_zpowers u')).2
      rw [Subgroup.mem_centralizer_iff] at hu'mem
      apply hkey'
      exact ⟨commutatorElement_eq_one_iff_mul_comm.mpr (hu'mem x (by simp)).symm,
        commutatorElement_eq_one_iff_mul_comm.mpr (hu'mem (a x) (by simp)).symm⟩
    omega
  have hcard : 3 ≤ Nat.card N := by
    obtain ⟨⟨n₀, hn₀⟩, hn₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.N_ne
    have hn₀1' : n₀ ≠ 1 := fun h' => hn₀1 (Subtype.ext h')
    have han : a n₀ ≠ n₀ := fun h' => hn₀1' (hNa n₀ hn₀ h')
    have han1 : a n₀ ≠ 1 := fun h' => hn₀1' (by
      have : a n₀ = a 1 := by rw [h', map_one]
      exact EquivLike.injective a this)
    have hsub : ({1, n₀, a n₀} : Set Q) ⊆ (N : Set Q) := by
      intro z hz
      rcases hz with hz | hz | hz
      · rw [hz]; exact N.one_mem
      · rw [hz]; exact hn₀
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]; exact h.N_inva n₀ hn₀
    have h3 : ({1, n₀, a n₀} : Set Q).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, n₀, a n₀, fun h' => hn₀1' h'.symm, fun h' => han1 h'.symm,
        fun h' => han h'.symm, rfl⟩
    calc 3 = ({1, n₀, a n₀} : Set Q).ncard := h3.symm
      _ ≤ (N : Set Q).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card N := (Nat.card_coe_set_eq _).symm
  have hlow1 : 6 ≤
      (zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q)).relIndex (zpowers u' ⊔ N) := by
    have hsup := relIndex_sup_of_commute (U := zpowers u') (V := N)
      (RU := zpowers u' ⊓ Subgroup.centralizer ({x, a x} : Set Q)) (RV := ⊥)
      (fun z hz n hn => hZN z hz n hn) inf_le_left bot_le
      (fun z hz r hr => by
        rw [hZZ z hz r hr.1, mul_assoc, mul_inv_cancel, mul_one]
        exact hr)
      (fun n hn r hr => by
        rw [Subgroup.mem_bot] at hr ⊢
        rw [hr]
        group)
      (fun w hw => by
        obtain ⟨hwZ, hwN⟩ := hw
        have hw1 : w = 1 := hNa w hwN (hZa w hwZ)
        rw [hw1]
        exact ⟨(Subgroup.one_mem _), Subgroup.one_mem _⟩)
    rw [sup_bot_eq, Subgroup.relIndex_bot_left] at hsup
    rw [hsup]
    calc 6 = 2 * 3 := rfl
      _ ≤ _ := Nat.mul_le_mul hA hcard
  have hP1V : closure ({x, a x} : Set Q) ≤ Subgroup.centralizer (commSub a b : Set Q) := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_centralizer_iff.mpr
        (fun v hv => (commutatorElement_eq_one_iff_mul_comm.mp (hxV v hv)).symm)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Subgroup.mem_centralizer_iff.mpr
        (fun v hv => (commutatorElement_eq_one_iff_mul_comm.mp (haxV v hv)).symm)
  have hP1b : closure ({x, a x} : Set Q) ≤ fixSub b := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      exact hx
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hxa
  have hΦ : ∀ w ∈ closure ({x, a x} : Set Q) ⊓ commSub a b, w ∈ frattini Q := fun w hw =>
    h.bpair.fix_inf_le hQ h.four ⟨hVa w hw.2, hP1b hw.1⟩
  have hsup2 := relIndex_sup_of_commute (U := closure ({x, a x} : Set Q)) (V := commSub a b)
    (RU := frattini Q ⊓ closure ({x, a x} : Set Q)) (RV := frattini Q ⊓ commSub a b)
    (fun p hp v hv => ((Subgroup.mem_centralizer_iff.mp (hP1V hp)) v hv).symm)
    inf_le_right inf_le_right
    (fun p hp r hr => ⟨(inferInstance : (frattini Q).Normal).conj_mem r hr.1 p,
      (closure ({x, a x} : Set Q)).mul_mem
        ((closure ({x, a x} : Set Q)).mul_mem hp hr.2) ((closure ({x, a x} : Set Q)).inv_mem hp)⟩)
    hnV
    (fun w hw => ⟨⟨hΦ w hw, hw.1⟩, hΦ w hw, hw.2⟩)
  rw [htop, Subgroup.relIndex_top_right] at hsup2
  have hidx : 16 ≤
      ((frattini Q ⊓ closure ({x, a x} : Set Q)) ⊔ (frattini Q ⊓ commSub a b)).index := by
    have hle : (frattini Q ⊓ closure ({x, a x} : Set Q)) ⊔ (frattini Q ⊓ commSub a b) ≤
        frattini Q := sup_le inf_le_left inf_le_left
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [h.bpair.index_frattini hQ h.four] at hdvd
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
  have hP1 : (frattini Q ⊓ closure ({x, a x} : Set Q)).relIndex
      (closure ({x, a x} : Set Q)) ≤ 4 := by
    rw [Subgroup.inf_relIndex_right]
    have hs := relIndex_le_two_pow_card ({x, a x} : Finset Q) (R := frattini Q)
      (fun p _ r hr => (inferInstance : (frattini Q).Normal).conj_mem r hr p)
      (fun p _ => mul_self_mem_frattini hQ p)
    have hcoe : (({x, a x} : Finset Q) : Set Q) = ({x, a x} : Set Q) := by simp
    rw [hcoe] at hs
    have hc : ({x, a x} : Finset Q).card ≤ 2 := Finset.card_le_two
    calc _ ≤ 2 ^ ({x, a x} : Finset Q).card := hs
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hc
      _ = 4 := by norm_num
  have hlow2 : 4 ≤ (frattini Q ⊓ commSub a b).relIndex (commSub a b) := by
    by_contra hlt
    have h12 : (frattini Q ⊓ closure ({x, a x} : Set Q)).relIndex (closure ({x, a x} : Set Q)) *
        (frattini Q ⊓ commSub a b).relIndex (commSub a b) ≤ 4 * 3 :=
      Nat.mul_le_mul hP1 (by omega)
    omega
  have := Nat.mul_le_mul hlow1 hlow2
  omega

theorem caseA (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseAHyp Q a b N) : False := by
  obtain ⟨x, hx, y, hy, hgen⟩ := h.bpair.exists_gens hQ h.four
  have hba : ∀ z, a (b z) = b (a z) := fun z => by
    have := congrArg (fun f : MulAut Q => f z) h.bpair.comm
    simpa [MulAut.mul_apply] using this
  have hxa : b (a x) = a x := by rw [← hba, hx]
  have hya : a y = y := commSub_le_fixSub_a h.bpair hy
  have hby : b y ∈ commSub a b := by
    have h1 : y⁻¹ * b y ∈ commSub a b := Subgroup.subset_closure ⟨y, hya, rfl⟩
    have := (commSub a b).mul_mem hy h1
    rwa [mul_inv_cancel_left] at this
  have hxV : ∀ w ∈ commSub a b, ⁅x, w⁆ = 1 := fun w hw => caseA_A2 hQ h hc hx hw
  have haxV : ∀ w ∈ commSub a b, ⁅a x, w⁆ = 1 := fun w hw => caseA_A2 hQ h hc hxa hw
  have htop : Subgroup.closure ({x, a x} : Set Q) ⊔ commSub a b = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hg]
      exact Subgroup.mem_sup_right hy
    · rw [hg]
      exact Subgroup.mem_sup_right hby
  exact caseA_final hQ h hc hx hxV haxV htop (caseA_key hQ h hc hx hy hgen)

end Fixed

end CFSG.GH74.E2
