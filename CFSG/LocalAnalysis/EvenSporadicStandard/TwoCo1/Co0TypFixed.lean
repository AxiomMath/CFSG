module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypStab

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts

theorem fix_block (R : Subgroup (Equiv.Perm (Fin 24))) (hR : IsPGroup 2 R)
    (t : Equiv.Perm (Fin 24))
    (hn : ∀ k : ℕ, ∀ r ∈ R, t ^ k * r * (t ^ k)⁻¹ ∈ R ∧ (t ^ k)⁻¹ * r * t ^ k ∈ R)
    (B : Finset (Fin 24)) (hB : B.card = 12) (f : Fin 24) (hf : f ∈ B) (htf : t f = f)
    (hBinv : ∀ r ∈ R, ∀ i, i ∈ B ↔ r i ∈ B)
    (htr : ∀ x ∈ B.erase f, ∀ y ∈ B.erase f, ∃ k : ℕ, (t ^ k) x = y) :
    ∀ r ∈ R, ∀ i ∈ B, r i = i := by
  have htk : ∀ k : ℕ, (t ^ k) f = f := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, htf, ih]
  have htk' : ∀ k : ℕ, (t ^ k)⁻¹ f = f := fun k => by
    rw [Equiv.Perm.inv_eq_iff_eq, htk k]
  have hfix : ∀ r ∈ R, r f = f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r₀, hr₀, hne⟩ := hcon
    have hxZ : r₀ f ∈ B.erase f := Finset.mem_erase.2 ⟨hne, (hBinv r₀ hr₀ f).1 hf⟩
    have horb : MulAction.orbit R f = (B : Set (Fin 24)) := by
      ext y
      constructor
      · rintro ⟨r, rfl⟩
        exact (hBinv r r.2 f).1 hf
      · intro hy
        by_cases hyf : y = f
        · exact ⟨1, by simp [hyf]⟩
        · obtain ⟨k, hk⟩ := htr (r₀ f) hxZ y (Finset.mem_erase.2 ⟨hyf, hy⟩)
          refine ⟨⟨t ^ k * r₀ * (t ^ k)⁻¹, (hn k r₀ hr₀).1⟩, ?_⟩
          show (t ^ k * r₀ * (t ^ k)⁻¹) f = y
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htk' k, hk]
    obtain ⟨n, hn2⟩ := hR.card_orbit f
    rw [horb, Nat.card_coe_set_eq, Set.ncard_coe_finset, hB] at hn2
    have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn2]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hZinv : ∀ r ∈ R, ∀ i ∈ B.erase f, r i ∈ B.erase f := by
    intro r hr i hi
    obtain ⟨hif, hiB⟩ := Finset.mem_erase.1 hi
    exact Finset.mem_erase.2 ⟨fun h => hif (r.injective (h.trans (hfix r hr).symm)),
      (hBinv r hr i).1 hiB⟩
  let S : SubMulAction R (Fin 24) :=
    { carrier := ↑(B.erase f)
      smul_mem' := fun r i hi => hZinv r r.2 i hi }
  have hcard : Nat.card S = 11 := by
    show Nat.card ↥(↑(B.erase f) : Set (Fin 24)) = 11
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_erase_of_mem hf, hB]
  obtain ⟨x₀, hx₀⟩ : ∃ x : S, x ∈ MulAction.fixedPoints R S := by
    by_contra hnone
    push Not at hnone
    have h0 : Nat.card (MulAction.fixedPoints R S) = 0 := by
      have : IsEmpty (MulAction.fixedPoints R S) := ⟨fun x => hnone x.1 x.2⟩
      exact Nat.card_of_isEmpty
    have hmod := hR.card_modEq_card_fixedPoints S
    rw [hcard, h0] at hmod
    exact absurd hmod (by decide)
  have hZfix : ∀ r ∈ R, ∀ z ∈ B.erase f, r z = z := by
    intro r hr z hz
    obtain ⟨k, hk⟩ := htr x₀.1 x₀.2 z hz
    have hfx : ((t ^ k)⁻¹ * r * t ^ k) x₀.1 = x₀.1 :=
      congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx₀ ⟨_, (hn k r hr).2⟩)
    calc r z = r ((t ^ k) x₀.1) := by rw [hk]
      _ = (t ^ k) (((t ^ k)⁻¹ * r * t ^ k) x₀.1) := by simp [Equiv.Perm.mul_apply]
      _ = (t ^ k) x₀.1 := by rw [hfx]
      _ = z := hk
  intro r hr i hi
  by_cases hif : i = f
  · rw [hif]
    exact hfix r hr
  · exact hZfix r hr i (Finset.mem_erase.2 ⟨hif, hi⟩)

@[expose] def dodSupp : Finset (Fin 24) := {1, 2, 4, 6, 8, 9, 10, 11, 12, 13, 16, 17}

theorem mem_dodSupp_iff (i : Fin 24) : i ∈ dodSupp ↔ (dod₂ : Fin 24 → ZMod 2) i ≠ 0 := by
  revert i
  decide

theorem dod₂_permC_apply {p : AutPerm} (hp : p ∈ stabC dod₂) (i : Fin 24) :
    (dod₂ : Fin 24 → ZMod 2) ((p : Equiv.Perm (Fin 24)) i) = (dod₂ : Fin 24 → ZMod 2) i := by
  have h1 := congrFun (congrArg Subtype.val (mem_stabC.1 hp)) ((p : Equiv.Perm (Fin 24)) i)
  rw [coe_permC, permWord_apply] at h1
  exact h1.symm

private theorem tEl_cycle_supp : ∀ x ∈ dodSupp.erase 16, ∀ y ∈ dodSupp.erase 16,
    ∃ k < 11, (tEl ^ k) x = y := by decide

private theorem tEl_cycle_compl : ∀ x ∈ (dodSuppᶜ).erase 21, ∀ y ∈ (dodSuppᶜ).erase 21,
    ∃ k < 11, (tEl ^ k) x = y := by decide

theorem stab_normal_two_trivial (R : Subgroup AutPerm) (hR : IsPGroup 2 R)
    (hRs : R ≤ stabC dod₂) (hn : ∀ h ∈ stabC dod₂, ∀ r ∈ R, h * r * h⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  have hR'p : IsPGroup 2 (R.map AutPerm.subtype) :=
    hR.of_equiv (R.equivMapOfInjective _ Subtype.val_injective)
  let tA : AutPerm := ⟨tEl, tEl_mem⟩
  have htA : tA ∈ stabC dod₂ := mem_stabC.2 (Subtype.ext permWord_tEl_dod₂)
  have hn' : ∀ k : ℕ, ∀ r ∈ R.map AutPerm.subtype,
      tEl ^ k * r * (tEl ^ k)⁻¹ ∈ R.map AutPerm.subtype ∧
        (tEl ^ k)⁻¹ * r * tEl ^ k ∈ R.map AutPerm.subtype := by
    rintro k _ ⟨r, hr, rfl⟩
    have h1 := hn (tA ^ k) ((stabC dod₂).pow_mem htA k) r hr
    have h2 := hn (tA ^ k)⁻¹ ((stabC dod₂).inv_mem ((stabC dod₂).pow_mem htA k)) r hr
    rw [inv_inv] at h2
    exact ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
  have hD : ∀ r ∈ R.map AutPerm.subtype, ∀ i, i ∈ dodSupp ↔ r i ∈ dodSupp := by
    rintro _ ⟨p, hp, rfl⟩ i
    rw [mem_dodSupp_iff, mem_dodSupp_iff]
    show _ ↔ (dod₂ : Fin 24 → ZMod 2) ((p : Equiv.Perm (Fin 24)) i) ≠ 0
    rw [dod₂_permC_apply (hRs hp) i]
  have hall : ∀ r ∈ R.map AutPerm.subtype, ∀ i, r i = i := by
    intro r hr i
    by_cases hi : i ∈ dodSupp
    · exact fix_block _ hR'p tEl hn' dodSupp (by decide) 16 (by decide) (by decide) hD
        (fun x hx y hy => (tEl_cycle_supp x hx y hy).imp fun _ h => h.2) r hr i hi
    · exact fix_block _ hR'p tEl hn' dodSuppᶜ (by decide) 21 (by decide) (by decide)
        (fun r hr i => by simpa using not_congr (hD r hr i))
        (fun x hx y hy => (tEl_cycle_compl x hx y hy).imp fun _ h => h.2) r hr i
        (Finset.mem_compl.2 hi)
  intro r hr
  exact Subtype.ext (Equiv.ext fun i => hall _ ⟨r, hr, rfl⟩ i)

end CFSG.EvenSporadicStandard.TwoCo1
