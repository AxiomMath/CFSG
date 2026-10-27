module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

set_option linter.unusedSectionVars false

section Core

variable {X : Type*} [Group X] (p : ℕ) (b : X) (L : Subgroup X)

@[expose] def lbp (k : ZMod p) : X := b ^ k.val

theorem lbp_natCast (hb : b ^ p = 1) (n : ℕ) : lbp p b (n : ZMod p) = b ^ n := by
  unfold lbp
  rw [ZMod.val_natCast, ← pow_eq_pow_mod n hb]

variable [NeZero p]

theorem lbp_succ (hb : b ^ p = 1) (k : ZMod p) : lbp p b (k + 1) = lbp p b k * b := by
  have h1 : k + 1 = ((k.val + 1 : ℕ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [h1, lbp_natCast p b hb, pow_succ]
  rfl

@[expose] def lphi (k : ZMod p) : ↥L →* X :=
  (MulAut.conj (lbp p b k)⁻¹).toMonoidHom.comp L.subtype

theorem lphi_apply (k : ZMod p) (x : ↥L) :
    lphi p b L k x = (lbp p b k)⁻¹ * (x : X) * lbp p b k := by
  simp [lphi]

theorem lphi_injective (k : ZMod p) : Function.Injective (lphi p b L k) :=
  (MulAut.conj (lbp p b k)⁻¹).injective.comp L.subtype_injective

@[expose] def LComm : Prop :=
  ∀ i j : ZMod p, i ≠ j → ∀ x y : ↥L, Commute (lphi p b L i x) (lphi p b L j y)

variable {p b L}

@[expose] def lPsi (hc : LComm p b L) : (ZMod p → ↥L) →* X :=
  MonoidHom.noncommPiCoprod (fun k => lphi p b L k) (fun i j h => hc i j h)

theorem lPsi_mulSingle (hc : LComm p b L) (k : ZMod p) (x : ↥L) :
    lPsi hc (Pi.mulSingle k x) = lphi p b L k x := by
  exact MonoidHom.noncommPiCoprod_mulSingle (N := fun _ => ↥L) (fun k => lphi p b L k) k x

theorem commute_lPsi (hc : LComm p b L) {m : X} {f : ZMod p → ↥L}
    (h : ∀ k, Commute m (lphi p b L k (f k))) : Commute m (lPsi hc f) := by
  have e : lPsi hc f = _ := MonoidHom.noncommPiCoprod_apply (fun k => lphi p b L k) f
  rw [e]
  exact Finset.noncommProd_commute _ _ _ _ fun k _ => h k

@[expose] def lshift (p : ℕ) (L : Subgroup X) : (ZMod p → ↥L) →* (ZMod p → ↥L) where
  toFun f := fun k => f (k - 1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem lshift_apply (f : ZMod p → ↥L) (k : ZMod p) : lshift p L f k = f (k - 1) := rfl

theorem lshift_mulSingle (i : ZMod p) (x : ↥L) :
    lshift p L (Pi.mulSingle i x) = Pi.mulSingle (i + 1) x := by
  funext k
  simp only [lshift_apply, Pi.mulSingle_apply]
  by_cases h : k = i + 1
  · subst h; simp
  · have : k - 1 ≠ i := fun h' => h (by rw [← h']; ring)
    simp [h, this]

theorem lPsi_conj (hb : b ^ p = 1) (hc : LComm p b L) (f : ZMod p → ↥L) :
    b⁻¹ * lPsi hc f * b = lPsi hc (lshift p L f) := by
  have key : ((MulAut.conj b⁻¹).toMonoidHom.comp (lPsi hc)) = (lPsi hc).comp (lshift p L) := by
    refine MonoidHom.pi_ext fun i x => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, lshift_mulSingle, lPsi_mulSingle,
      lphi_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, lbp_succ p b hb]
    group
  have := congrArg (fun g => g f) key
  simpa [MulAut.conj_apply] using this

theorem mem_center_of_commute (hc : LComm p b L) {f : ZMod p → ↥L} (k : ZMod p)
    (h : ∀ l : ↥L, Commute (lphi p b L k l) (lPsi hc f)) : f k ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff]
  intro l
  have e1 : (Pi.mulSingle k l * f * (Pi.mulSingle k l)⁻¹ * f⁻¹ : ZMod p → ↥L) =
      Pi.mulSingle k (l * f k * l⁻¹ * (f k)⁻¹) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp [Pi.mul_apply, Pi.inv_apply]
    · simp [Pi.mul_apply, Pi.inv_apply, hj]
  have e2 : lPsi hc (Pi.mulSingle k (l * f k * l⁻¹ * (f k)⁻¹)) = 1 := by
    rw [← e1]
    simp only [map_mul, map_inv, lPsi_mulSingle]
    rw [(h l).eq]
    group
  rw [lPsi_mulSingle] at e2
  have e3 := (map_eq_one_iff _ (lphi_injective p b L k)).1 e2
  have e4 : l * f k * l⁻¹ = f k := mul_inv_eq_one.1 e3
  calc l * f k = (l * f k * l⁻¹) * l := by group
    _ = f k * l := by rw [e4]

theorem lPsi_ker_le (hc : LComm p b L) {f : ZMod p → ↥L} (h : lPsi hc f = 1) (k : ZMod p) :
    f k ∈ Subgroup.center ↥L :=
  mem_center_of_commute hc k fun l => by rw [h]; exact Commute.one_right _

theorem lPsi_central (hc : LComm p b L) {f : ZMod p → ↥L}
    (hf : ∀ k, f k ∈ Subgroup.center ↥L) (g : ZMod p → ↥L) :
    Commute (lPsi hc f) (lPsi hc g) := by
  refine commute_lPsi hc fun k => ?_
  refine (commute_lPsi hc (m := lphi p b L k (g k)) (f := f) fun j => ?_).symm
  by_cases hj : j = k
  · subst hj
    exact Commute.map (show Commute (g j) (f j) from Subgroup.mem_center_iff.1 (hf j) (g j))
      (lphi p b L j)
  · exact hc k j (fun e => hj e.symm) _ _

@[expose] def lN (hc : LComm p b L) : ↥L →* X :=
  (lPsi hc).comp (Pi.constMonoidHom (ZMod p) ↥L)

theorem lN_apply (hc : LComm p b L) (l : ↥L) : lN hc l = lPsi hc (fun _ => l) := rfl

theorem lN_conj (hb : b ^ p = 1) (hc : LComm p b L) (l : ↥L) : b⁻¹ * lN hc l * b = lN hc l := by
  rw [lN_apply, lPsi_conj hb hc]
  rfl

theorem lN_ker_le (hc : LComm p b L) {l : ↥L} (h : lN hc l = 1) : l ∈ Subgroup.center ↥L :=
  lPsi_ker_le hc (f := fun _ => l) h 0

theorem lPsi_centralizer (hb : b ^ p = 1) (hc : LComm p b L) {f : ZMod p → ↥L}
    (hf : b⁻¹ * lPsi hc f * b = lPsi hc f) :
    ∃ l : ↥L, ∃ z : ZMod p → ↥L, (∀ k, z k ∈ Subgroup.center ↥L) ∧
      lPsi hc f = lN hc l * lPsi hc z := by
  rw [lPsi_conj hb hc] at hf
  have h1 : lPsi hc (lshift p L f * f⁻¹) = 1 := by
    rw [map_mul, map_inv, hf]; group
  have h2 : ∀ k, f (k - 1) * (f k)⁻¹ ∈ Subgroup.center ↥L := fun k => lPsi_ker_le hc h1 k
  have h3 : ∀ n : ℕ, (f 0)⁻¹ * f (n : ZMod p) ∈ Subgroup.center ↥L := by
    intro n
    induction n with
    | zero => simp [one_mem]
    | succ n ih =>
      have w := h2 ((n + 1 : ℕ) : ZMod p)
      have hn : ((n + 1 : ℕ) : ZMod p) - 1 = (n : ZMod p) := by push_cast; ring
      rw [hn] at w
      set c : ↥L := f ((n + 1 : ℕ) : ZMod p) * (f (n : ZMod p))⁻¹ with hcdef
      have hcC : c ∈ Subgroup.center ↥L := by
        have := (Subgroup.center ↥L).inv_mem w
        simpa [hcdef] using this
      have hf1 : f ((n + 1 : ℕ) : ZMod p) = c * f (n : ZMod p) := by rw [hcdef]; group
      have hcomm : (f 0)⁻¹ * c = c * (f 0)⁻¹ := Subgroup.mem_center_iff.1 hcC _
      have : (f 0)⁻¹ * f ((n + 1 : ℕ) : ZMod p) = c * ((f 0)⁻¹ * f (n : ZMod p)) := by
        rw [hf1, ← mul_assoc, hcomm, mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ hcC ih
  have h4 : ∀ k, (f 0)⁻¹ * f k ∈ Subgroup.center ↥L := by
    intro k
    have := h3 k.val
    rwa [ZMod.natCast_zmod_val] at this
  refine ⟨f 0, fun k => (f 0)⁻¹ * f k, h4, ?_⟩
  rw [lN_apply, ← map_mul]
  congr 1
  funext k
  simp

theorem lshift_iterate_const (f : ZMod p → ↥L) (h : lshift p L f = f) (n : ℕ) :
    f (n : ZMod p) = f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := congrFun h ((n + 1 : ℕ) : ZMod p)
    rw [lshift_apply] at this
    have hn : ((n + 1 : ℕ) : ZMod p) - 1 = (n : ZMod p) := by push_cast; ring
    rw [hn] at this
    rw [← this, ih]

theorem eq_const_of_lshift_eq (f : ZMod p → ↥L) (h : lshift p L f = f) (k : ZMod p) :
    f k = f 0 := by
  have := lshift_iterate_const f h k.val
  rwa [ZMod.natCast_zmod_val] at this

theorem lshift_pow_iterate (n : ℕ) (f : ZMod p → ↥L) (k : ZMod p) :
    (lshift p L)^[n] f k = f (k - n) := by
  induction n generalizing f k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [lshift_apply]
    congr 1
    push_cast
    ring

theorem exists_fixed_of_shift_stable [Fact p.Prime] [Finite ↥L] (D : Subgroup (ZMod p → ↥L))
    (hDs : ∀ f ∈ D, lshift p L f ∈ D) (hDp : ∀ f ∈ D, f ^ p = 1) (hD : D ≠ ⊥) :
    ∃ f ∈ D, f ≠ 1 ∧ lshift p L f = f := by
  classical
  have : Fintype ↥L := Fintype.ofFinite _
  have : Fintype ↥D := Fintype.ofFinite _
  let τ : Function.End ↥D := fun f => ⟨lshift p L f, hDs f f.2⟩
  have hτ : τ ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext f
    apply Subtype.ext
    have : ((τ ^ p) f : ↥D).1 = (lshift p L)^[p] f.1 := by
      have h : ∀ n : ℕ, (((τ ^ n) f : ↥D) : ZMod p → ↥L) = (lshift p L)^[n] (f : ZMod p → ↥L) := by
        intro n
        induction n generalizing f with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ]
          exact ih (τ f)
      exact h p
    rw [this]
    funext k
    rw [lshift_pow_iterate]
    simp only [ZMod.natCast_self, sub_zero]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hτ
  have hpg : IsPGroup p ↥D := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : (g : ZMod p → ↥L) ^ p = 1 := hDp g g.2
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hg))
    rcases (Nat.dvd_prime Fact.out).1 hdvd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hdvdD : p ∣ Nat.card ↥D := by
    rcases hpg.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hD
    · exact h
  have hdvdF : p ∣ Fintype.card (Function.fixedPoints τ) := by
    rw [Nat.card_eq_fintype_card] at hdvdD
    exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvdD)))
  have hfix1 : Function.IsFixedPt τ 1 := Subtype.ext (map_one _)
  have hpos : 0 < Fintype.card (Function.fixedPoints τ) :=
    Fintype.card_pos_iff.2 ⟨⟨1, hfix1⟩⟩
  have h1 : 1 < Fintype.card (Function.fixedPoints τ) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hdvdF)
  obtain ⟨g, hg⟩ := Fintype.exists_ne_of_one_lt_card h1 ⟨1, hfix1⟩
  refine ⟨g.1.1, g.1.2, ?_, congrArg Subtype.val g.2⟩
  intro h1'
  apply hg
  apply Subtype.ext
  apply Subtype.ext
  exact h1'

theorem eq_one_of_mem_center_of_card_eq_one (h : Nat.card (Subgroup.center ↥L) = 1) {x : ↥L}
    (hx : x ∈ Subgroup.center ↥L) : x = 1 := by
  have : Subsingleton (Subgroup.center ↥L) := (Nat.card_eq_one_iff_unique.1 h).1
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Subgroup.center ↥L) 1)

theorem pow_eq_one_of_mem_center [Fact p.Prime] [Finite ↥L]
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = p) {x : ↥L}
    (hx : x ∈ Subgroup.center ↥L) : x ^ p = 1 := by
  rcases hZ with h | h
  · rw [eq_one_of_mem_center_of_card_eq_one h hx, one_pow]
  · have := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨x, hx⟩)
    rw [h] at this
    exact congrArg Subtype.val this

theorem lN_center_trivial_or [Fact p.Prime] [Finite X] (hb : b ^ p = 1) (hc : LComm p b L)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = p) :
    (∀ x ∈ Subgroup.center ↥L, lN hc x = 1) ∨
      p ^ p ≤ Nat.card ↥((Subgroup.pi Set.univ
        (fun _ : ZMod p => Subgroup.center ↥L)).map (lPsi hc)) := by
  classical
  by_cases hall : ∀ x ∈ Subgroup.center ↥L, lN hc x = 1
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨z0, hz0, hz0n⟩ := hall
  have hz01 : z0 ≠ 1 := fun h => hz0n (by rw [h, map_one])
  have hcard : Nat.card (Subgroup.center ↥L) = p := by
    rcases hZ with h | h
    · exact absurd (eq_one_of_mem_center_of_card_eq_one h hz0) hz01
    · exact h
  have inj : ∀ h : ZMod p → ↥L, (∀ k, h k ∈ Subgroup.center ↥L) → lPsi hc h = 1 → h = 1 := by
    intro h hh h1
    by_contra hne
    set D : Subgroup (ZMod p → ↥L) :=
      (lPsi hc).ker ⊓ Subgroup.pi Set.univ (fun _ : ZMod p => Subgroup.center ↥L) with hD
    have hhD : h ∈ D := ⟨h1, fun k _ => hh k⟩
    have hDne : D ≠ ⊥ := fun e => hne (by simpa [e] using hhD)
    have hDs : ∀ f ∈ D, lshift p L f ∈ D := by
      intro f hf
      refine ⟨?_, fun k _ => hf.2 (k - 1) (Set.mem_univ _)⟩
      have hf1 : lPsi hc f = 1 := hf.1
      show lPsi hc (lshift p L f) = 1
      rw [← lPsi_conj hb hc, hf1]; group
    have hDp : ∀ f ∈ D, f ^ p = 1 := by
      intro f hf
      funext k
      exact pow_eq_one_of_mem_center (Or.inr hcard) (hf.2 k (Set.mem_univ _)) |> fun h' =>
        congrArg Subtype.val h' |> fun h'' => Subtype.ext (by simpa using h'')
    obtain ⟨f, hfD, hf1, hfs⟩ := exists_fixed_of_shift_stable D hDs hDp hDne
    have hconst : f = fun _ => f 0 := funext (eq_const_of_lshift_eq f hfs)
    have hc0 : f 0 ∈ Subgroup.center ↥L := hfD.2 0 (Set.mem_univ _)
    have hc1 : f 0 ≠ 1 := fun e => hf1 (by rw [hconst, e]; rfl)
    have hN1 : lN hc (f 0) = 1 := by
      rw [lN_apply, ← hconst]; exact hfD.1
    have htop := zpowers_eq_top_of_prime_card (G := Subgroup.center ↥L) hcard
      (g := ⟨f 0, hc0⟩) (fun e => hc1 (congrArg Subtype.val e))
    have hz : (⟨z0, hz0⟩ : Subgroup.center ↥L) ∈ Subgroup.zpowers (⟨f 0, hc0⟩ : Subgroup.center ↥L) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hm' : (f 0) ^ m = z0 := congrArg Subtype.val hm
    apply hz0n
    rw [← hm', map_zpow, hN1, one_zpow]
  let e : (ZMod p → ↥(Subgroup.center ↥L)) → ↥((Subgroup.pi Set.univ
        (fun _ : ZMod p => Subgroup.center ↥L)).map (lPsi hc)) :=
    fun g => ⟨lPsi hc (fun k => (g k : ↥L)), ⟨fun k => (g k : ↥L), fun k _ => (g k).2, rfl⟩⟩
  have he : Function.Injective e := by
    intro g g' hgg
    have h1 : lPsi hc (fun k => (g k : ↥L)) = lPsi hc (fun k => (g' k : ↥L)) :=
      congrArg Subtype.val hgg
    have h2 : lPsi hc ((fun k => (g k : ↥L)) * (fun k => (g' k : ↥L))⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]; group
    have h3 := inj _ (fun k => Subgroup.mul_mem _ (g k).2 (Subgroup.inv_mem _ (g' k).2)) h2
    funext k
    apply Subtype.ext
    have := congrFun h3 k
    exact mul_inv_eq_one.1 this
  have := Nat.card_le_card_of_injective e he
  rwa [Nat.card_fun, hcard, Nat.card_zmod] at this

end Core

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
