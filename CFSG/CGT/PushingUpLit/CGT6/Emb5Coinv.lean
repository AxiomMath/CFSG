module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

section Coinv

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_top_of_sup_commV_eq_top (hV : ∀ v : V, v ^ 2 = 1) {T : Subgroup (MulAut V)}
    (hT : IsPGroup 2 ↥T) {W : Subgroup V} (hW : ∀ t ∈ T, ∀ w ∈ W, t w ∈ W)
    (h : W ⊔ commV T = ⊤) : W = ⊤ := by
  classical
  by_contra hWtop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, ⟨hWM, hMtop, hMinv⟩, hmax⟩ := (wellFounded_gt (α := Subgroup V)).has_min
    {M : Subgroup V | W ≤ M ∧ M ≠ ⊤ ∧ ∀ t ∈ T, ∀ m ∈ M, t m ∈ M} ⟨W, le_rfl, hWtop, hW⟩
  let _ : MulAction ↥T (V ⧸ M) :=
    { smul := fun t => QuotientGroup.map M M (t.1 : MulAut V).toMonoidHom
        (fun m hm => hMinv t t.2 m hm)
      one_smul := fun x => by
        induction x using QuotientGroup.induction_on with
        | H v => rfl
      mul_smul := fun s t x => by
        induction x using QuotientGroup.induction_on with
        | H v => rfl }
  have hsmul : ∀ (t : ↥T) (v : V), t • (v : V ⧸ M) = ((t.1 v : V) : V ⧸ M) := fun t v => rfl
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by simpa using hV v⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ M.index_dvd_card)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hMtop (Subgroup.index_eq_one.mp (by simpa using hj))
  have hmod := hT.card_modEq_card_fixedPoints (V ⧸ M)
  have hcardX : Nat.card (V ⧸ M) = 2 ^ j := hj
  rw [hcardX] at hmod
  have heven : Even (Nat.card ↥(MulAction.fixedPoints ↥T (V ⧸ M))) := by
    have h1 : 2 ^ j % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hj0)
    have h2 : Nat.card ↥(MulAction.fixedPoints ↥T (V ⧸ M)) % 2 = 0 := by
      rw [← hmod]
      exact h1
    exact Nat.even_iff.mpr h2
  obtain ⟨f, hf1, hfix⟩ : ∃ f : V ⧸ M, f ≠ 1 ∧ ∀ t : ↥T, t • f = f := by
    by_contra hno
    have hone : (1 : V ⧸ M) ∈ MulAction.fixedPoints ↥T (V ⧸ M) := fun t => by
      show t • ((1 : V) : V ⧸ M) = ((1 : V) : V ⧸ M)
      rw [hsmul]
      simp
    have hall : ∀ a : ↥(MulAction.fixedPoints ↥T (V ⧸ M)), (a : V ⧸ M) = 1 := fun a => by
      by_contra hne
      exact hno ⟨a, hne, fun t => a.2 t⟩
    have hcard : Nat.card ↥(MulAction.fixedPoints ↥T (V ⧸ M)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hall a).trans (hall b).symm)⟩, ⟨⟨1, hone⟩⟩⟩
    rw [hcard] at heven
    exact absurd heven (by decide)
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective f
  have hvM : v ∉ M := fun hv => hf1 ((QuotientGroup.eq_one_iff v).mpr hv)
  have htv : ∀ t ∈ T, t v / v ∈ M := fun t ht => by
    have h1 := hfix ⟨t, ht⟩
    rw [hsmul] at h1
    have h2 := M.inv_mem (QuotientGroup.eq.mp h1)
    rw [div_eq_inv_mul]
    simpa using h2
  have hM'inv : ∀ t ∈ T, ∀ x ∈ M ⊔ Subgroup.zpowers v, t x ∈ M ⊔ Subgroup.zpowers v := by
    intro t ht x hx
    obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_mul, map_zpow]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hMinv t ht m hm)) ?_
    have e : t v = (t v / v) * v := by simp
    rw [e, mul_zpow]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (M.zpow_mem (htv t ht) i))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers v i))
  have hM'top : M ⊔ Subgroup.zpowers v = ⊤ := by
    by_contra hne
    exact hmax _ ⟨hWM.trans le_sup_left, hne, hM'inv⟩
      (lt_of_le_of_ne le_sup_left fun e => hvM (e ▸ Subgroup.mem_sup_right
        (Subgroup.mem_zpowers v)))
  have hcomm : commV T ≤ M := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨t, ht, x, rfl⟩
    have hx : x ∈ M ⊔ Subgroup.zpowers v := by
      rw [hM'top]
      exact Subgroup.mem_top x
    obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have e : t (m * v ^ i) * (m * v ^ i)⁻¹ = (t m / m) * (t v / v) ^ i := by
      rw [map_mul, map_zpow, ← div_eq_mul_inv, mul_div_mul_comm, div_zpow]
    show t (m * v ^ i) * (m * v ^ i)⁻¹ ∈ (M : Set V)
    rw [e]
    have h1 : t m / m ∈ M := by
      rw [div_eq_mul_inv]
      exact Subgroup.mul_mem _ (hMinv t ht m hm) (M.inv_mem hm)
    exact Subgroup.mul_mem _ h1 (M.zpow_mem (htv t ht) i)
  exact hMtop (top_le_iff.mp (h ▸ sup_le hWM hcomm))

end Coinv

end CFSG.CGT.PushingUpLit.CGT6
