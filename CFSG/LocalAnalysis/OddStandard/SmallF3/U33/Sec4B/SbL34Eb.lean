module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

theorem card_fixed_of_orderOf_seven (hE : Module.finrank (ZMod 2) E = 6) {g : E ≃ₗ[ZMod 2] E}
    (hg : orderOf g = 7) : Nat.card {e : E // g e = e} = 1 ∨ Nat.card {e : E // g e = e} = 8 := by
  classical
  let F : Submodule (ZMod 2) E :=
    { carrier := {e | g e = e}
      add_mem' := by
        intro a b ha hb
        change g a = a at ha
        change g b = b at hb
        change g (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        change g x = x at hx
        change g (c • x) = c • x
        rw [map_smul, hx] }
  have hFcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F), Nat.card_zmod]
  have hcardE : Nat.card E = 2 ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod, hE]
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcardE]; norm_num)
  let H : Subgroup (E ≃ₗ[ZMod 2] E) := Subgroup.zpowers g
  have hHcard : Nat.card H = 7 := by
    change Nat.card (Subgroup.zpowers g) = 7
    rw [Nat.card_zpowers, hg]
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hHp : IsPGroup 7 H := IsPGroup.of_card (p := 7) (n := 1) (by rw [hHcard, pow_one])
  have hfix : MulAction.fixedPoints H E = {e : E | g e = e} := by
    ext e
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro he
      have hm : g ∈ MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e :=
        he ⟨g, Subgroup.mem_zpowers g⟩
      rwa [MulAction.mem_stabilizer_iff] at hm
    · intro he h
      have hm : g ∈ MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e := by
        rwa [MulAction.mem_stabilizer_iff]
      have hh : (h : E ≃ₗ[ZMod 2] E) ∈ MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e :=
        (Subgroup.zpowers_le.mpr hm) h.2
      rwa [MulAction.mem_stabilizer_iff] at hh
  have hcong : Nat.card E ≡ Nat.card {e : E // g e = e} [MOD 7] := by
    have h := hHp.card_modEq_card_fixedPoints E
    rw [hfix] at h
    change Nat.ModEq 7 (Nat.card E) (Nat.card F)
    exact h
  have hd_le : Module.finrank (ZMod 2) F ≤ 6 := by
    have h := Submodule.finrank_le (R := ZMod 2) (M := E) F
    rwa [hE] at h
  have hmod : 2 ^ Module.finrank (ZMod 2) F ≡ 1 [MOD 7] := by
    have h1 : (2 : ℕ) ^ 6 ≡ 2 ^ Module.finrank (ZMod 2) F [MOD 7] := by
      have h := hcong
      rw [hcardE] at h
      have hNF : Nat.card {e : E // g e = e} = Nat.card F := rfl
      rw [hNF, hFcard] at h
      exact h
    exact h1.symm.trans (by norm_num [Nat.ModEq])
  have hN : Nat.card {e : E // g e = e} = 2 ^ Module.finrank (ZMod 2) F := by
    have hNF : Nat.card {e : E // g e = e} = Nat.card F := rfl
    rw [hNF, hFcard]
  rw [hN]
  set d := Module.finrank (ZMod 2) F with hd
  have hd_le' : d ≤ 6 := hd.symm ▸ hd_le
  have hmod' : 2 ^ d ≡ 1 [MOD 7] := hd.symm ▸ hmod
  interval_cases d
  · left; norm_num
  · exfalso; exact absurd hmod' (by decide)
  · exfalso; exact absurd hmod' (by decide)
  · right; norm_num
  · exfalso; exact absurd hmod' (by decide)
  · exfalso; exact absurd hmod' (by decide)
  · exfalso
    have htop : F = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hE]
      exact hd.symm
    have hg1 : g = 1 := by
      ext x
      show g x = x
      have hx : x ∈ F := by rw [htop]; trivial
      change g x = x at hx
      exact hx
    rw [hg1, orderOf_one] at hg
    norm_num at hg

theorem eq_zero_of_fixed_seven_sq (hE : Module.finrank (ZMod 2) E = 6)
    (R : Subgroup (E ≃ₗ[ZMod 2] E)) (hR : Nat.card R = 49)
    (hord : ∀ g ∈ R, g ≠ 1 → orderOf g = 7) {e : E} (he : ∀ g ∈ R, g e = e) : e = 0 := by
  classical
  by_contra he0
  have hcardE : Nat.card E = 2 ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod, hE]
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcardE]; norm_num)
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  haveI : Fintype R := Fintype.ofFinite R
  have hcardR : Fintype.card R = 49 := by
    rw [Fintype.card_eq_nat_card, hR]
  have hfix1 : Fintype.card (MulAction.fixedBy E (1 : R)) = 64 := by
    have h : MulAction.fixedBy E (1 : R) = Set.univ := by
      ext x; simp [MulAction.fixedBy]
    calc
      Fintype.card (MulAction.fixedBy E (1 : R))
          = Fintype.card (Set.univ : Set E) := Fintype.card_congr (Set.equivOfEq h)
      _ = Fintype.card E := Fintype.card_congr (Equiv.Set.univ E)
      _ = 64 := by rw [Fintype.card_eq_nat_card, hcardE]; norm_num
  have hfix_other : ∀ g : R, g ≠ 1 → Fintype.card (MulAction.fixedBy E g) = 8 := by
    intro g hg
    have hg' : (g : E ≃ₗ[ZMod 2] E) ≠ 1 := fun h => hg (Subtype.ext h)
    have hset : MulAction.fixedBy E g = {x : E | (g : E ≃ₗ[ZMod 2] E) x = x} := by
      ext x
      simp [MulAction.fixedBy, Subgroup.smul_def]
    have hcard : Fintype.card (MulAction.fixedBy E g) =
        Nat.card {x : E // (g : E ≃ₗ[ZMod 2] E) x = x} := by
      rw [← Fintype.card_eq_nat_card]
      exact Fintype.card_congr (Set.equivOfEq hset)
    rw [hcard]
    rcases card_fixed_of_orderOf_seven hE (hord (g : E ≃ₗ[ZMod 2] E) g.2 hg') with h1 | h8
    · exfalso
      have h2 : 2 ≤ Nat.card {x : E // (g : E ≃ₗ[ZMod 2] E) x = x} := by
        haveI : Nontrivial {x : E // (g : E ≃ₗ[ZMod 2] E) x = x} :=
          ⟨⟨0, by simp⟩, ⟨e, he (g : E ≃ₗ[ZMod 2] E) g.2⟩, by
            intro h
            exact he0 (Subtype.ext_iff.mp h).symm⟩
        have hlt := Fintype.one_lt_card (α := {x : E // (g : E ≃ₗ[ZMod 2] E) x = x})
        rw [Nat.card_eq_fintype_card]
        omega
      omega
    · exact h8
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group R E
  have hsum : (∑ g : R, Fintype.card (MulAction.fixedBy E g)) = 448 := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset R)
      (fun g => Fintype.card (MulAction.fixedBy E g)) (Finset.mem_univ (1 : R)), hfix1]
    have hconst : (∑ g ∈ (Finset.univ : Finset R).erase (1 : R),
        Fintype.card (MulAction.fixedBy E g)) =
        ((Finset.univ : Finset R).erase (1 : R)).card * 8 := by
      apply Finset.sum_const_nat (m := 8)
      intro g hg
      exact hfix_other g (Finset.mem_erase.mp hg).1
    rw [hconst, Finset.card_erase_of_mem (Finset.mem_univ (1 : R)), Finset.card_univ, hcardR]
  rw [hsum, hcardR] at hburn
  have hdiv : 49 ∣ 448 := by
    rw [hburn]
    exact dvd_mul_left 49 _
  norm_num at hdiv

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
