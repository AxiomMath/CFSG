module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOrbits
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem zmod2_neg (a : ZMod 2) : -a = a := by
  revert a; decide

theorem vec_neg {ι : Type*} (a : ι → ZMod 2) : -a = a := funext fun i => zmod2_neg (a i)

@[expose] def evenVec (Ω : Type*) [Fintype Ω] : AddSubgroup (Ω → ZMod 2) where
  carrier := {x | ∑ i, x i = 0}
  add_mem' := by
    intro a b ha hb
    change ∑ i, (a + b) i = 0
    have ha' : ∑ i, a i = 0 := ha
    have hb' : ∑ i, b i = 0 := hb
    simp only [Pi.add_apply, Finset.sum_add_distrib, ha', hb', add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    convert ha using 1
    exact vec_neg a

theorem mem_evenVec {x : Ω → ZMod 2} : x ∈ evenVec Ω ↔ ∑ i, x i = 0 := Iff.rfl

@[expose] def FixP (E : Subgroup (Perm Ω)) : AddSubgroup (Ω → ZMod 2) where
  carrier := {x | ∀ g ∈ E, ∀ i, x (g i) = x i}
  add_mem' := by
    intro a b ha hb g hg i
    simp [Pi.add_apply, ha g hg i, hb g hg i]
  zero_mem' := by intro g hg i; rfl
  neg_mem' := by
    intro a ha
    convert ha using 1
    exact vec_neg a

@[expose] def FixUp (E : Subgroup (Perm Ω)) : AddSubgroup (Ω → ZMod 2) where
  carrier := {x | ∑ i, x i = 0 ∧
    ∀ g ∈ E, (∀ i, x (g i) = x i) ∨ (∀ i, x (g i) = x i + 1)}
  add_mem' := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib]; rw [ha0, hb0]; rfl
    · intro g hg
      rcases ha g hg with h1 | h1 <;> rcases hb g hg with h2 | h2
      · left; intro i; simp [Pi.add_apply, h1 i, h2 i]
      · right; intro i; simp [Pi.add_apply, h1 i, h2 i]; ring
      · right; intro i; simp [Pi.add_apply, h1 i, h2 i]; ring
      · left; intro i
        simp only [Pi.add_apply, h1 i, h2 i]
        have := zmod2_add_self 1
        calc a i + 1 + (b i + 1) = a i + b i + (1 + 1) := by ring
          _ = a i + b i := by rw [this]; simp
  zero_mem' := by
    refine ⟨by simp, fun g hg => Or.inl fun i => rfl⟩
  neg_mem' := by
    intro a ha
    convert ha using 1
    exact vec_neg a

def sgn2 (c : ZMod 2) : ℂˣ := if c = 0 then 1 else -1

theorem neg_one_units_ne : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at this

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem sgn2_add (a b : ZMod 2) : sgn2 (a + b) = sgn2 a * sgn2 b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [sgn2, h11, h10]

theorem sgn2_inj {a b : ZMod 2} (h : sgn2 a = sgn2 b) : a = b := by
  have hne := neg_one_units_ne
  have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    first | rfl | (exfalso; simp [sgn2, h10] at h; try (first | exact hne h | exact hne h.symm))

theorem card_twist_le {G : Type*} [Group G] [Finite G] (hcomm : ∀ a b : G, a * b = b * a)
    (hG : ∀ g : G, g * g = 1) (Y : Subgroup G)
    (S : Set (G → ZMod 2)) (hS1 : ∀ c ∈ S, ∀ g h, c (g * h) = c g + c h)
    (hS2 : ∀ c ∈ S, ∀ y ∈ Y, c y = 0) : Nat.card S ≤ Y.index := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  have h2 : Monoid.exponent G ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g; simpa [pow_two] using hG g
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := HasEnoughRootsOfUnity.of_dvd ℂ h2
  have h0 : ∀ c ∈ S, c 1 = 0 := by
    intro c hc
    have := hS1 c hc 1 1
    simp only [one_mul] at this
    have h3 : c 1 + c 1 = c 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h3
  let f : S → (G →* ℂˣ) := fun c =>
    { toFun := fun g => sgn2 (c.1 g)
      map_one' := by simp [h0 c.1 c.2, sgn2]
      map_mul' := fun g h => by rw [hS1 c.1 c.2, sgn2_add] }
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    funext g
    have h1 := congrArg (fun φ : G →* ℂˣ => φ g) h
    exact sgn2_inj h1
  have hker : ∀ c, f c ∈ (MonoidHom.domRestrictHom Y ℂˣ).ker := by
    intro c
    rw [MonoidHom.mem_ker]
    ext ⟨y, hy⟩
    simp [f, hS2 c.1 c.2 y hy, sgn2]
  let f' : S → (MonoidHom.domRestrictHom Y ℂˣ).ker := fun c => ⟨f c, hker c⟩
  have hf' : Function.Injective f' := fun c d h => hf (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective f' hf'
  rw [CommGroup.card_domRestrictHom_ker] at this
  exact this

section Twist

variable (E : Subgroup (Perm Ω)) (i0 : Ω)

@[expose] def twist : (Ω → ZMod 2) →+ (E → ZMod 2) where
  toFun x g := x ((g : Perm Ω) i0) + x i0
  map_zero' := by funext g; simp
  map_add' x y := by funext g; simp only [Pi.add_apply]; ring

variable {E i0}

theorem twist_apply (x : Ω → ZMod 2) (g : E) :
    twist E i0 x g = x ((g : Perm Ω) i0) + x i0 := rfl

theorem FixUp.spec {x : Ω → ZMod 2} (hx : x ∈ FixUp E) {g : Perm Ω} (hg : g ∈ E) (i : Ω) :
    x (g i) = x i + twist E i0 x ⟨g, hg⟩ := by
  rcases hx.2 g hg with h | h
  · have : twist E i0 x ⟨g, hg⟩ = 0 := by
      rw [twist_apply]; simp only; rw [h i0]; exact zmod2_add_self _
    rw [this, add_zero]; exact h i
  · have : twist E i0 x ⟨g, hg⟩ = 1 := by
      rw [twist_apply]; simp only; rw [h i0]
      have := zmod2_add_self (x i0)
      calc x i0 + 1 + x i0 = (x i0 + x i0) + 1 := by ring
        _ = 1 := by rw [this, zero_add]
    rw [this]; exact h i

theorem twist_mul {x : Ω → ZMod 2} (hx : x ∈ FixUp E) (g h : E) :
    twist E i0 x (g * h) = twist E i0 x g + twist E i0 x h := by
  have e1 := FixUp.spec (i0 := i0) hx g.2 ((h : Perm Ω) i0)
  have e2 := FixUp.spec (i0 := i0) hx h.2 i0
  have hh : twist E i0 x (g * h) = x ((g : Perm Ω) ((h : Perm Ω) i0)) + x i0 := rfl
  rw [hh, e1, e2]
  have := zmod2_add_self (x i0)
  calc x i0 + twist E i0 x h + twist E i0 x ⟨g.1, g.2⟩ + x i0
      = (x i0 + x i0) + twist E i0 x h + twist E i0 x g := by ring
    _ = twist E i0 x g + twist E i0 x h := by rw [this]; ring

@[expose] def FixTriv (E : Subgroup (Perm Ω)) : Subgroup E where
  carrier := {g | ∀ x ∈ FixUp E, ∀ i, x ((g : Perm Ω) i) = x i}
  mul_mem' := by
    intro a b ha hb x hx i
    show x (((a : Perm Ω) * (b : Perm Ω)) i) = x i
    rw [Perm.mul_apply, ha x hx, hb x hx]
  one_mem' := fun x hx i => rfl
  inv_mem' := by
    intro a ha x hx i
    have := ha x hx (((a⁻¹ : E) : Perm Ω) i)
    have h2 : ((a : Perm Ω) (((a⁻¹ : E) : Perm Ω) i)) = i := by
      show ((a : Perm Ω) * ((a : Perm Ω)⁻¹)) i = i
      simp
    rw [h2] at this
    exact this.symm

theorem stabilizer_le_FixTriv (p : Ω) : stabilizer E p ≤ FixTriv E := by
  intro g hg x hx i
  have hgp : (g : Perm Ω) p = p := hg
  have := FixUp.spec (i0 := p) hx g.2 p
  rw [hgp] at this
  have h0 : twist E p x g = 0 := by
    have h3 : x p + twist E p x ⟨g.1, g.2⟩ = x p + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h3
  have h1 := FixUp.spec (i0 := p) hx g.2 i
  have h0' : twist E p x ⟨g.1, g.2⟩ = 0 := h0
  rw [h0', add_zero] at h1
  exact h1

end Twist

section Counting

variable {E : Subgroup (Perm Ω)}

@[expose] def FixEven (E : Subgroup (Perm Ω)) : AddSubgroup (Ω → ZMod 2) := FixP E ⊓ evenVec Ω

theorem FixUp_le_evenVec : FixUp E ≤ evenVec Ω := fun _ hx => hx.1

@[expose] noncomputable def offIdx (E : Subgroup (Perm Ω)) : ℕ :=
  ((FixUp E).addSubgroupOf (evenVec Ω)).index

theorem offIdx_mul_card : offIdx E * Nat.card (FixUp E) = Nat.card (evenVec Ω) := by
  have h := AddSubgroup.index_mul_card ((FixUp E).addSubgroupOf (evenVec Ω))
  rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (FixUp_le_evenVec (E := E))).toEquiv] at h
  exact h

@[expose] def weight (Ω : Type*) [Fintype Ω] : (Ω → ZMod 2) →+ ZMod 2 :=
  AddMonoidHom.mk' (fun x => ∑ i, x i) (by intro a b; simp [Finset.sum_add_distrib])

theorem ker_weight : (weight Ω).ker = evenVec Ω := by
  ext x; simp [weight, mem_evenVec]

theorem pow_le_two_mul_card_evenVec : 2 ^ Nat.card Ω ≤ 2 * Nat.card (evenVec Ω) := by
  have h := AddSubgroup.card_ker_mul_card_range (weight Ω)
  rw [ker_weight] at h
  have h1 : Nat.card (weight Ω).range ≤ 2 := by
    have := Nat.card_le_card_of_injective (fun x : (weight Ω).range => x.1) Subtype.val_injective
    simpa [Nat.card_zmod] using this
  rw [Nat.card_fun, Nat.card_zmod] at h
  calc 2 ^ Nat.card Ω = Nat.card (evenVec Ω) * Nat.card (weight Ω).range := h.symm
    _ ≤ Nat.card (evenVec Ω) * 2 := Nat.mul_le_mul_left _ h1
    _ = 2 * Nat.card (evenVec Ω) := by ring

variable (E) (i0 : Ω)

@[expose] def twistFix : FixUp E →+ (E → ZMod 2) := (twist E i0).comp (FixUp E).subtype

variable {E i0}

theorem card_FixUp_eq :
    Nat.card (FixUp E) = Nat.card (twistFix E i0).ker * Nat.card (twistFix E i0).range :=
  (AddSubgroup.card_ker_mul_card_range (twistFix E i0)).symm

theorem card_ker_twistFix_le : Nat.card (twistFix E i0).ker ≤ Nat.card (FixEven E) := by
  let f : (twistFix E i0).ker → FixEven E := fun x =>
    ⟨x.1.1, by
      refine ⟨?_, x.1.2.1⟩
      intro g hg i
      have h0 : twist E i0 x.1.1 ⟨g, hg⟩ = 0 := by
        have := x.2
        rw [AddMonoidHom.mem_ker] at this
        exact congrFun this ⟨g, hg⟩
      rw [FixUp.spec (i0 := i0) x.1.2 hg i, h0, add_zero]⟩
  refine Nat.card_le_card_of_injective f ?_
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : FixEven E => (z : Ω → ZMod 2)) h

theorem card_range_twistFix_le (hE : IsExp2 E) :
    Nat.card (twistFix E i0).range ≤ (FixTriv E).index := by
  refine card_twist_le (G := E) (fun a b => Subtype.ext (hE.comm a.2 b.2))
    (fun g => Subtype.ext (hE g.1 g.2)) (FixTriv E) ((twistFix E i0).range : Set (E → ZMod 2)) ?_ ?_
  · rintro c ⟨x, rfl⟩ g h
    exact twist_mul x.2 g h
  · rintro c ⟨x, rfl⟩ y hy
    have h1 := hy x.1 x.2 i0
    show x.1 ((y : Perm Ω) i0) + x.1 i0 = 0
    rw [h1]; exact zmod2_add_self _

theorem range_twistFix_trivial {p : Ω} (hp : ∀ g ∈ E, g p = p) :
    Nat.card (twistFix E i0).range = 1 := by
  have : (twistFix E i0).range = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨x, rfl⟩
    funext g
    have h := FixUp.spec (i0 := i0) x.2 g.2 p
    rw [hp g.1 g.2] at h
    have h3 : x.1 p + twist E i0 x.1 ⟨g.1, g.2⟩ = x.1 p + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h3
  rw [this]
  simp

theorem card_FixP_le (E : Subgroup (Perm Ω)) : Nat.card (FixP E) ≤ 2 ^ Nat.card (Orb E) := by
  classical
  let f : FixP E → (Orb E → ZMod 2) := fun x ω => x.1 ω.out
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    have hq : ∃ g : E, g • (Quotient.mk'' i : Orb E).out = i := by
      have h' : (orbitRel E Ω) i (Quotient.mk'' i : Orb E).out :=
        Quotient.exact' (Quotient.out_eq' (Quotient.mk'' i)).symm
      exact orbitRel_apply.1 h'
    obtain ⟨g, hg⟩ := hq
    have h1 := congrFun h (Quotient.mk'' i)
    simp only [f] at h1
    rw [← hg]
    have e1 : x.1 (g • (Quotient.mk'' i : Orb E).out) = x.1 (Quotient.mk'' i : Orb E).out :=
      x.2 g.1 g.2 _
    have e2 : y.1 (g • (Quotient.mk'' i : Orb E).out) = y.1 (Quotient.mk'' i : Orb E).out :=
      y.2 g.1 g.2 _
    rw [e1, e2, h1]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, Nat.card_zmod] at this

theorem FixEven_le_FixP : FixEven E ≤ FixP E := inf_le_left

theorem card_FixEven_le : Nat.card (FixEven E) ≤ Nat.card (FixP E) :=
  AddSubgroup.card_le_of_le FixEven_le_FixP

theorem card_FixEven_mul_two_le {p : Ω} (hp : ∀ g ∈ E, g p = p) :
    Nat.card (FixEven E) * 2 ≤ Nat.card (FixP E) := by
  have hne : (FixEven E).addSubgroupOf (FixP E) ≠ ⊤ := by
    intro htop
    have hmem : (Pi.single p (1 : ZMod 2) : Ω → ZMod 2) ∈ FixP E := by
      intro g hg i
      by_cases hi : i = p
      · subst hi; rw [hp g hg]
      · have : g i ≠ p := by
          intro h
          apply hi
          have := hp g hg
          exact g.injective (h.trans this.symm)
        simp [Pi.single_apply, hi, this]
    have h1 : (⟨Pi.single p 1, hmem⟩ : FixP E) ∈ (FixEven E).addSubgroupOf (FixP E) := by
      rw [htop]; trivial
    have h2 : (Pi.single p (1 : ZMod 2) : Ω → ZMod 2) ∈ evenVec Ω := h1.2
    rw [mem_evenVec] at h2
    simp at h2
  have h := AddSubgroup.card_mul_index ((FixEven E).addSubgroupOf (FixP E))
  rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (FixEven_le_FixP (E := E))).toEquiv] at h
  have hi : 1 < ((FixEven E).addSubgroupOf (FixP E)).index := by
    apply AddSubgroup.one_lt_index_of_ne_top hne
  calc Nat.card (FixEven E) * 2 ≤ Nat.card (FixEven E) * ((FixEven E).addSubgroupOf (FixP E)).index :=
        Nat.mul_le_mul_left _ hi
    _ = Nat.card (FixP E) := h

end Counting

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
