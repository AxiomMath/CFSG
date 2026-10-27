module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL22A
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

private lemma fzl_apply_pow_three (f : MulAut S) (hf3 : f ^ 3 = 1) (x : S) :
    f (f (f x)) = x := by
  have h : (f ^ 3) x = x := by rw [hf3]; rfl
  simpa [pow_succ, MulAut.mul_apply] using h

private lemma fzl_apply_mul_self (u : MulAut S) (hu2 : u * u = 1) (x : S) :
    u (u x) = x := by
  have h : (u * u) x = (1 : MulAut S) x := by rw [hu2]
  simpa [MulAut.mul_apply] using h

private lemma fzl_inv_eq_mul_self (f : MulAut S) (hf3 : f ^ 3 = 1) :
    f⁻¹ = f * f := by
  have h3 : f ^ 3 = f * f * f := by rw [pow_succ, pow_succ, pow_one]
  have h : f * f * f = 1 := by rw [← h3, hf3]
  calc f⁻¹ = f⁻¹ * 1 := by rw [mul_one]
    _ = f⁻¹ * (f * f * f) := by rw [h, mul_one]
    _ = f * f := by group

private lemma fzl_mul_eq (f u : MulAut S) (huf : u * f * u⁻¹ = f⁻¹) :
    u * f = f⁻¹ * u := by
  have := congrArg (fun x : MulAut S => x * u) huf
  simpa [mul_assoc] using this

theorem fzl_fpf_mod_center (hS : FzSuz S) (f : MulAut S) (hfix : ∀ g : S, f g = g → g = 1)
    {g : S} (hg : f g * g⁻¹ ∈ center S) : g ∈ center S := by
  haveI : Finite (center S) := Nat.finite_of_card_ne_zero (by rw [hS.center_card]; norm_num)
  let φ : center S →* center S :=
    { toFun := fun z => ⟨f z.1, fzl_map_center f z.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [map_mul] }
  let ψ : center S →* center S :=
    { toFun := fun z => z * (φ z)⁻¹
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        show (a * b) * (φ (a * b))⁻¹ = (a * (φ a)⁻¹) * (b * (φ b)⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hker : ψ.ker = ⊥ := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hz
      have h1 : z.1 * (f z.1)⁻¹ = 1 := by simpa [ψ, φ] using Subtype.ext_iff.mp hz
      exact Subtype.ext (hfix z.1 (mul_inv_eq_one.mp h1).symm)
    · intro hz; rw [hz]; exact map_one ψ
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  have hsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hinj
  obtain ⟨z', hz'⟩ := hsurj ⟨f g * g⁻¹, hg⟩
  have hz'e : z'.1 * (f z'.1)⁻¹ = f g * g⁻¹ := by
    simpa [ψ, φ] using Subtype.ext_iff.mp hz'
  have hfgz : f g * (f g * g⁻¹)⁻¹ = g := by
    have h1 : (f g * g⁻¹) * g = f g := by group
    rw [show f g * (f g * g⁻¹)⁻¹ = ((f g * g⁻¹) * g) * (f g * g⁻¹)⁻¹ from by rw [h1],
      show ((f g * g⁻¹) * g) * (f g * g⁻¹)⁻¹ = g from by
        rw [(Subgroup.mem_center_iff.mp hg g).symm]; group]
  have hfz' : f z'.1 = (f g * g⁻¹)⁻¹ * z'.1 := by
    rw [← hz'e]; group
  have hfixeq : f (g * z'.1) = g * z'.1 := by rw [map_mul, hfz', ← mul_assoc, hfgz]
  have hg_eq : g = (z'.1)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp (hfix (g * z'.1) hfixeq)
  rw [hg_eq]
  exact Subgroup.inv_mem _ z'.2

theorem fzl_norm_central (hS : FzSuz S) (f : MulAut S) (hf3 : f ^ 3 = 1)
    (hfix : ∀ g : S, f g = g → g = 1) (g : S) : g * f g * f (f g) ∈ center S := by
  have h3 : f (f (f g)) = g := fzl_apply_pow_three f hf3 g
  have hcomm : f (g * f g * f (f g)) * (g * f g * f (f g))⁻¹ ∈ center S := by
    have hfeq : f (g * f g * f (f g)) = g⁻¹ * (g * f g * f (f g)) * g := by
      rw [map_mul, map_mul, h3]; group
    rw [hfeq]
    have hcoe : g⁻¹ * (g * f g * f (f g)) * g * (g * f g * f (f g))⁻¹ =
        ⁅g⁻¹, g * f g * f (f g)⁆ := by
      rw [commutatorElement_def]; group
    rw [hcoe]
    exact hS.comm_central g⁻¹ (g * f g * f (f g))
  exact fzl_fpf_mod_center hS f hfix hcomm

theorem fzl_comm_f_self (hS : FzSuz S) (f : MulAut S) (hf3 : f ^ 3 = 1)
    (hfix : ∀ g : S, f g = g → g = 1) (g : S) : ⁅g, f g⁆ = 1 := by
  have h3 : f (f (f g)) = g := fzl_apply_pow_three f hf3 g
  let N : S := g * f g * f (f g)
  have hNz : N ∈ center S := fzl_norm_central hS f hf3 hfix g
  have hf2 : f (f g) = (f g)⁻¹ * g⁻¹ * N := by
    change f (f g) = (f g)⁻¹ * g⁻¹ * (g * f g * f (f g)); group
  have hff : f (f ⁅g, f g⁆) = ⁅g, f g⁆ := by
    have e1 : f ⁅g, f g⁆ = ⁅f g, f (f g)⁆ := map_commutatorElement f g (f g)
    rw [e1, map_commutatorElement, h3, fzl_gam_symm hS (f (f g)) g, hf2,
      fzl_gam_mul_right hS g ((f g)⁻¹ * g⁻¹) N,
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hNz g), mul_one,
      fzl_gam_mul_right hS g (f g)⁻¹ g⁻¹,
      fzl_gam_inv_right hS g (f g), fzl_gam_inv_right hS g g, fzl_gam_self g, mul_one]
  have hfw : f ⁅g, f g⁆ = ⁅g, f g⁆ := by
    have := congrArg f hff
    rw [fzl_apply_pow_three f hf3 ⁅g, f g⁆] at this
    exact this.symm
  exact hfix ⁅g, f g⁆ hfw

theorem fzl_card_le_fixed_sq {V : Type} [Group V] [Finite V] (hc : ∀ v w : V, v * w = w * v)
    (hV : ∀ v : V, v * v = 1) (φ : V →* V) (hφ : ∀ v : V, φ (φ v) = v) :
    Nat.card V ≤ Nat.card {v : V // φ v = v} ^ 2 := by
  haveI : IsMulCommutative V := IsMulCommutative.of_comm hc
  let ε : V →* V :=
    { toFun := fun v => v * φ v
      map_one' := by rw [map_one, mul_one]
      map_mul' := fun v w => by
        rw [show (v * w) * φ (v * w) = (v * φ v) * (w * φ w) from by rw [map_mul]; ac_rfl] }
  have hcard := Subgroup.card_ker_mul_card_range ε
  have hker : Nat.card ε.ker = Nat.card {v : V // φ v = v} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl V) ?_)
    intro v
    rw [MonoidHom.mem_ker]
    show (v * φ v = 1) ↔ φ v = v
    constructor
    · intro h
      rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right (hV (φ v))] at h
      exact h.symm
    · intro h; rw [h, hV v]
  have hrange : Nat.card ε.range ≤ Nat.card {v : V // φ v = v} := by
    let ψ : ε.range → {v : V // φ v = v} := fun x => ⟨x.1, by
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp x.2
      rw [← hv]
      show φ (v * φ v) = v * φ v
      rw [map_mul, hφ]
      exact hc (φ v) v⟩
    exact Nat.card_le_card_of_injective ψ (by
      intro x y hxy
      exact Subtype.ext (show (x : V) = (y : V) from
        congrArg (fun z : {v : V // φ v = v} => z.1) hxy))
  calc Nat.card V = Nat.card ε.ker * Nat.card ε.range := hcard.symm
    _ ≤ Nat.card {v : V // φ v = v} * Nat.card {v : V // φ v = v} := by
        rw [hker]
        exact Nat.mul_le_mul_left _ hrange
    _ = Nat.card {v : V // φ v = v} ^ 2 := by rw [pow_two]

theorem fzl_exists_fixed_pair (hS : FzSuz S) (u : MulAut S) (hu2 : u * u = 1) :
    ∃ a c : S, u a * a⁻¹ ∈ center S ∧ u c * c⁻¹ ∈ center S ∧ a ∉ center S ∧ c ∉ center S ∧
      a * c⁻¹ ∉ center S := by
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hS.card]; norm_num)
  have huu : ∀ x : S, u (u x) = x := fzl_apply_mul_self u hu2
  let φ : S ⧸ center S →* S ⧸ center S :=
    QuotientGroup.map (center S) (center S) u.toMonoidHom (fun z hz => fzl_map_center u hz)
  have hφ : ∀ v : S ⧸ center S, φ (φ v) = v := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [show φ (QuotientGroup.mk x) = QuotientGroup.mk (u x) from rfl,
        show φ (QuotientGroup.mk (u x)) = QuotientGroup.mk (u (u x)) from rfl, huu]
  have hc : ∀ v w : S ⧸ center S, v * w = w * v := by
    intro v w
    induction v using QuotientGroup.induction_on with
    | H x =>
      induction w using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          QuotientGroup.eq_iff_div_mem, div_eq_mul_inv,
          show x * y * (y * x)⁻¹ = ⁅x, y⁆ from by rw [commutatorElement_def]; group]
        exact hS.comm_central x y
  have hV : ∀ v : S ⧸ center S, v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff (N := center S) (x * x)).mpr (hS.sq_central x)
  have hcardV : Nat.card (S ⧸ center S) = 16 := by
    have h := Subgroup.card_ker_mul_card_of_surjective
      (QuotientGroup.mk'_surjective (center S))
    rw [QuotientGroup.ker_mk', hS.center_card, hS.card] at h
    omega
  have hle := fzl_card_le_fixed_sq hc hV φ hφ
  have hF4 : 4 ≤ Nat.card {v : S ⧸ center S // φ v = v} := by
    have h16 : (16 : ℕ) ≤ Nat.card {v : S ⧸ center S // φ v = v} ^ 2 := by
      calc (16 : ℕ) = Nat.card (S ⧸ center S) := hcardV.symm
        _ ≤ Nat.card {v : S ⧸ center S // φ v = v} ^ 2 := hle
    exact (Nat.pow_le_pow_iff_left (a := 4) (n := 2) (by norm_num)).mp (by simpa using h16)
  classical
  haveI : Fintype {v : S ⧸ center S // φ v = v} := Fintype.ofFinite _
  let F := {v : S ⧸ center S // φ v = v}
  let e : F := ⟨1, map_one φ⟩
  have hcardF : 4 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]; exact hF4
  have hgt : 1 < (Finset.univ.erase e).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ]; omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hgt
  rw [Finset.mem_erase] at hp hq
  have hp1 : p.1 ≠ 1 := fun h => hp.1 (Subtype.ext h)
  have hq1 : q.1 ≠ 1 := fun h => hq.1 (Subtype.ext h)
  have hpq1 : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (s := center S) p.1
  obtain ⟨c, hc'⟩ := QuotientGroup.mk_surjective (s := center S) q.1
  have hφmk : ∀ x : S, φ (x : S ⧸ center S) = (u x : S ⧸ center S) := fun x =>
    QuotientGroup.map_mk (center S) (center S) u.toMonoidHom (fun z hz => fzl_map_center u hz) x
  have hu_a : (u a : S ⧸ center S) = (a : S ⧸ center S) := by
    rw [show (u a : S ⧸ center S) = φ (a : S ⧸ center S) from (hφmk a).symm, ha, p.2]
  have hu_c : (u c : S ⧸ center S) = (c : S ⧸ center S) := by
    rw [show (u c : S ⧸ center S) = φ (c : S ⧸ center S) from (hφmk c).symm, hc', q.2]
  refine ⟨a, c, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem (N := center S)).mp hu_a
  · simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem (N := center S)).mp hu_c
  · exact fun haZ => hp1 (by rw [← ha, (QuotientGroup.eq_one_iff (N := center S) a).mpr haZ])
  · exact fun hcZ => hq1 (by rw [← hc', (QuotientGroup.eq_one_iff (N := center S) c).mpr hcZ])
  · intro hac
    exact hpq1 (by rw [← ha,
      (QuotientGroup.eq_iff_div_mem (N := center S)).mpr (by simpa [div_eq_mul_inv] using hac),
      hc'])

theorem fzl_Z_structure (hS : FzSuz S) (f u : MulAut S) (hf3 : f ^ 3 = 1)
    (hfix : ∀ g : S, f g = g → g = 1) (hu2 : u * u = 1) (huf : u * f * u⁻¹ = f⁻¹) :
    ∃ z₁ z₂ z₃ : S, z₁ ∈ center S ∧ z₂ ∈ center S ∧ z₃ ∈ center S ∧
      z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₃ ≠ 1 ∧ z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ ∧ z₃ = z₁ * z₂ ∧
      (∀ z ∈ center S, z = 1 ∨ z = z₁ ∨ z = z₂ ∨ z = z₃) ∧
      u z₁ = z₁ ∧ u z₂ = z₃ ∧ u z₃ = z₂ ∧ f z₁ = z₂ ∧ f z₂ = z₃ ∧ f z₃ = z₁ := by
  haveI : Finite (center S) :=
    Nat.finite_of_card_ne_zero (by rw [hS.center_card]; norm_num)
  have huu : ∀ x : S, u (u x) = x := fzl_apply_mul_self u hu2
  let φ : center S →* center S :=
    { toFun := fun z => ⟨u z.1, fzl_map_center u z.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [map_mul] }
  have hφ : ∀ z : center S, φ (φ z) = z := by intro z; ext; exact huu z.1
  have hle := fzl_card_le_fixed_sq (V := center S) (fun v w => mul_comm' v w)
    (fun v => Subtype.ext (hS.center_exp v.1 v.2)) φ hφ
  rw [hS.center_card] at hle
  have h2 : 2 ≤ Nat.card {z : center S // φ z = z} :=
    (Nat.pow_le_pow_iff_left (a := 2) (n := 2) (by norm_num)).mp (by simpa using hle)
  classical
  haveI : Fintype {z : center S // φ z = z} := Fintype.ofFinite _
  let e : {z : center S // φ z = z} := ⟨1, map_one φ⟩
  haveI : Nontrivial {z : center S // φ z = z} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]; omega
  obtain ⟨p, hp⟩ := exists_ne e
  let Z1 : center S := p.1
  let z₁ : S := Z1.1
  have hz₁Z : z₁ ∈ center S := Z1.2
  have hu_z₁ : u z₁ = z₁ := by simpa [φ, Z1, z₁] using Subtype.ext_iff.mp p.2
  have hz₁ne : z₁ ≠ 1 := fun h => hp (Subtype.ext (Subtype.ext h))
  let z₂ : S := f z₁
  let z₃ : S := z₁ * z₂
  have hz₂Z : z₂ ∈ center S := by
    change f z₁ ∈ center S; exact fzl_map_center f hz₁Z
  have hz₃Z : z₃ ∈ center S := by
    change z₁ * z₂ ∈ center S; exact Subgroup.mul_mem _ hz₁Z hz₂Z
  have hz₂_ne_z₁ : z₂ ≠ z₁ := fun h => hz₁ne (hfix z₁ h)
  have hz₂_ne_one : z₂ ≠ 1 := fun h =>
    hz₁ne (f.injective (by rw [show f z₁ = 1 from h, map_one]))
  have hz₃_ne_one : z₃ ≠ 1 := by
    intro h; change z₁ * z₂ = 1 at h
    exact hz₂_ne_z₁ (by rw [eq_inv_of_mul_eq_one_right h,
      inv_eq_of_mul_eq_one_right (hS.center_exp z₁ hz₁Z)])
  have hz₃_ne_z₁ : z₃ ≠ z₁ := fun h =>
    hz₂_ne_one (mul_left_cancel (by rw [show z₁ * z₂ = z₁ from h, mul_one]))
  have hz₃_ne_z₂ : z₃ ≠ z₂ := fun h =>
    hz₁ne (mul_right_cancel (by rw [show z₁ * z₂ = z₂ from h, one_mul]))
  have hTcard : ({1, z₁, z₂, z₃} : Set S).ncard = 4 := by
    rw [Set.ncard_eq_four]
    exact ⟨1, z₁, z₂, z₃, (fun h => hz₁ne h.symm), (fun h => hz₂_ne_one h.symm),
      (fun h => hz₃_ne_one h.symm), (fun h => hz₂_ne_z₁ h.symm),
      (fun h => hz₃_ne_z₁ h.symm), (fun h => hz₃_ne_z₂ h.symm), rfl⟩
  have hZeq : ({1, z₁, z₂, z₃} : Set S) = (center S : Set S) := by
    refine Set.eq_of_subset_of_ncard_le (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      exacts [Subgroup.one_mem _, hz₁Z, hz₂Z, hz₃Z]) ?_
    rw [hTcard, show (center S : Set S).ncard = 4 by
      rw [← Nat.card_coe_set_eq]; exact hS.center_card]
  have henum : ∀ z ∈ center S, z = 1 ∨ z = z₁ ∨ z = z₂ ∨ z = z₃ := by
    intro z hz
    have hzT : z ∈ ({1, z₁, z₂, z₃} : Set S) := by rw [hZeq]; exact hz
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzT
  have hfz₂ : f z₂ = z₃ := by
    rcases henum (f z₂) (fzl_map_center f hz₂Z) with h | h | h | h
    · exact absurd (f.injective (by rw [h, map_one])) hz₂_ne_one
    · exfalso
      have h3 := fzl_apply_pow_three f hf3 z₁
      have := congrArg f h
      rw [h3] at this
      exact hz₂_ne_z₁ this.symm
    · exact absurd (hfix z₁ (f.injective h)) hz₁ne
    · exact h
  have hfz₃ : f z₃ = z₁ := by
    change f (z₁ * z₂) = z₁
    rw [map_mul, hfz₂]
    change z₂ * (z₁ * z₂) = z₁
    rw [← mul_assoc, (Subgroup.mem_center_iff.mp hz₂Z z₁).symm, mul_assoc,
      hS.center_exp z₂ hz₂Z, mul_one]
  have huf' : u * f = f⁻¹ * u := fzl_mul_eq f u huf
  have hfinv : f⁻¹ = f * f := fzl_inv_eq_mul_self f hf3
  have hu_z₂ : u z₂ = z₃ := by
    change u (f z₁) = z₃
    rw [show u (f z₁) = (u * f) z₁ from rfl, huf',
      show (f⁻¹ * u) z₁ = f⁻¹ (u z₁) from rfl, hu_z₁, hfinv,
      show (f * f) z₁ = f (f z₁) from rfl]
    exact hfz₂
  have hu_z₃ : u z₃ = z₂ := by
    change u (z₁ * z₂) = z₂
    rw [map_mul, hu_z₁, hu_z₂]
    change z₁ * (z₁ * z₂) = z₂
    rw [← mul_assoc, hS.center_exp z₁ hz₁Z, one_mul]
  exact ⟨z₁, z₂, z₃, hz₁Z, hz₂Z, hz₃Z, hz₁ne, hz₂_ne_one, hz₃_ne_one,
    (fun h => hz₂_ne_z₁ h.symm), (fun h => hz₃_ne_z₁ h.symm), (fun h => hz₃_ne_z₂ h.symm),
    rfl, henum, hu_z₁, hu_z₂, hu_z₃, rfl, hfz₂, hfz₃⟩

end CFSG.OddStandard.SmallF3.FritzII
