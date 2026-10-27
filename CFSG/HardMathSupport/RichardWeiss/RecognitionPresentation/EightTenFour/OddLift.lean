module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.OddCentral

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG.Open
open scoped commutatorElement

theorem perfect_center_of_simple {Ã : Type} [Group Ã] {Ht : Subgroup Ã} (hs : IsSimpleGroup ↥Ht)
    (hnon : ∃ a ∈ Ht, ∃ b ∈ Ht, a * b ≠ b * a) :
    ⁅Ht, Ht⁆ = Ht ∧ Subgroup.center ↥Ht = ⊥ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnon
  constructor
  · rcases Subgroup.Normal.eq_bot_or_eq_top (commutator ↥Ht) with h | h
    · exfalso
      apply hab
      have h1 : ⁅(⟨a, ha⟩ : ↥Ht), (⟨b, hb⟩ : ↥Ht)⁆ ∈ commutator ↥Ht :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact congrArg Subtype.val h1
    · have : (commutator ↥Ht).map Ht.subtype = ⁅Ht, Ht⁆ := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      rw [← this, h, Subgroup.map_top, Subgroup.range_subtype]
  · rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥Ht) with h | h
    · exact h
    · exfalso
      apply hab
      have h1 : (⟨a, ha⟩ : ↥Ht) ∈ Subgroup.center ↥Ht := by rw [h]; exact Subgroup.mem_top _
      have := Subgroup.mem_center_iff.1 h1 ⟨b, hb⟩
      exact (congrArg Subtype.val this).symm

theorem commutatorElement_mul_central {B : Type*} [Group B] {z z' : B}
    (hz : z ∈ Subgroup.center B) (hz' : z' ∈ Subgroup.center B) (y y' : B) :
    ⁅y * z, y' * z'⁆ = ⁅y, y'⁆ := by
  have hz1 : ∀ w, z * w * z⁻¹ = w := fun w => by
    rw [mul_inv_eq_iff_eq_mul]; exact (Subgroup.mem_center_iff.1 hz w).symm
  have hz1' : ∀ w, z' * w * z'⁻¹ = w := fun w => by
    rw [mul_inv_eq_iff_eq_mul]; exact (Subgroup.mem_center_iff.1 hz' w).symm
  have e1 : ⁅y * z, y' * z'⁆ = y * (z * (y' * z') * z⁻¹) * y⁻¹ * (y' * z')⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  have e2 : z * (y' * z') * z⁻¹ = y' * z' := hz1 _
  have e3 : y' * z' * y⁻¹ * (y' * z')⁻¹ = y' * y⁻¹ * y'⁻¹ := by
    have : z' * y⁻¹ * z'⁻¹ = y⁻¹ := hz1' _
    calc y' * z' * y⁻¹ * (y' * z')⁻¹ = y' * (z' * y⁻¹ * z'⁻¹) * y'⁻¹ := by group
      _ = y' * y⁻¹ * y'⁻¹ := by rw [this]
  rw [e1, e2]
  calc y * (y' * z') * y⁻¹ * (y' * z')⁻¹ = y * (y' * z' * y⁻¹ * (y' * z')⁻¹) := by group
    _ = ⁅y, y'⁆ := by rw [e3]; simp only [commutatorElement_def]; group

theorem commutator_sup_central_le {B : Type*} [Group B] {H K : Subgroup B}
    (hK : K ≤ Subgroup.center B) : ⁅H ⊔ K, H ⊔ K⁆ ≤ ⁅H, H⁆ := by
  have hKn : K.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by
      rw [mul_inv_eq_iff_eq_mul]; exact (Subgroup.mem_center_iff.1 (hK hn) g)
    rwa [this]⟩
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg1
  obtain ⟨y', hy', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg2
  rw [commutatorElement_mul_central (hK hz) (hK hz')]
  exact Subgroup.commutator_mem_commutator hy hy'

section Lift

variable {B Ã : Type} [Group B] [Finite B] [Group Ã] [Finite Ã]

omit [Finite B] in
theorem commutator_le_self' (H : Subgroup B) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun g1 hg1 g2 hg2 => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg1 hg2) (H.inv_mem hg1)) (H.inv_mem hg2)

omit [Finite Ã] in
theorem exists_lift (φ : B →* Ã) (hker : φ.ker ≤ Subgroup.center B)
    (hodd : Odd (Nat.card φ.ker)) (hsurj : Function.Surjective φ) {P : Subgroup B}
    (hP2 : IsPGroup 2 ↥P) {Ht : Subgroup Ã} (hs : IsSimpleGroup ↥Ht)
    (hnon : ∃ a ∈ Ht, ∃ b ∈ Ht, a * b ≠ b * a) (hle : P.map φ ≤ Ht)
    (hidx : ¬ 2 ∣ ((P.map φ).subgroupOf Ht).index) :
    ∃ H : Subgroup B, ⁅H, H⁆ = H ∧ P ≤ H ∧ ¬ 2 ∣ (P.subgroupOf H).index ∧
      Odd (Nat.card (Subgroup.center ↥H)) ∧ CFSG.Open.IsQuasisimple ↥H := by
  classical
  obtain ⟨hperf, hcen⟩ := perfect_center_of_simple hs hnon
  set Hh : Subgroup B := Ht.comap φ with hHh
  set H : Subgroup B := ⁅Hh, Hh⁆ with hH
  have hmapHh : Hh.map φ = Ht := Subgroup.map_comap_eq_self_of_surjective hsurj Ht
  have hmapH : H.map φ = Ht := by
    rw [hH, Subgroup.map_commutator, hmapHh, hperf]
  have hHhH : Hh = H ⊔ φ.ker := by
    rw [← Subgroup.comap_map_eq, hmapH]
  have hHperf : ⁅H, H⁆ = H := by
    refine le_antisymm (commutator_le_self' H) ?_
    have h1 : ⁅H ⊔ φ.ker, H ⊔ φ.ker⁆ ≤ ⁅H, H⁆ := commutator_sup_central_le hker
    rw [← hHhH] at h1
    exact h1
  have hPH : P ≤ H := by
    intro p hp
    have hpHh : p ∈ Hh := hle ⟨p, hp, rfl⟩
    rw [hHhH] at hpHh
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hpHh
    have hcomm : Commute y z := Subgroup.mem_center_iff.1 (hker hz) y
    have hzo : z ^ Nat.card φ.ker = 1 := by
      have : (⟨z, hz⟩ : φ.ker) ^ Nat.card φ.ker = 1 := pow_card_eq_one'
      exact congrArg Subtype.val this
    have hpo : (y * z) ^ Nat.card φ.ker = y ^ Nat.card φ.ker := by
      rw [hcomm.mul_pow, hzo, mul_one]
    obtain ⟨m, hm⟩ := hP2 ⟨y * z, hp⟩
    have hm' : (y * z) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hcop : Nat.gcd (Nat.card φ.ker) (2 ^ m) = 1 :=
      Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
    have hbez := Nat.gcd_eq_gcd_ab (Nat.card φ.ker) (2 ^ m)
    rw [hcop] at hbez
    have hmem : (y * z) ^ (Nat.card φ.ker : ℤ) ∈ H := by
      rw [zpow_natCast, hpo]; exact H.pow_mem hy _
    have key : y * z = ((y * z) ^ (Nat.card φ.ker : ℤ)) ^ (Nat.gcdA (Nat.card φ.ker) (2 ^ m)) := by
      have h1 : (y * z) ^ (1 : ℤ) = ((y * z) ^ (Nat.card φ.ker : ℤ)) ^
          (Nat.gcdA (Nat.card φ.ker) (2 ^ m)) * ((y * z) ^ (2 ^ m : ℤ)) ^
          (Nat.gcdB (Nat.card φ.ker) (2 ^ m)) := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add]
        congr 1
      have h2 : (y * z) ^ (2 ^ m : ℤ) = 1 := by
        have : (2 ^ m : ℤ) = ((2 ^ m : ℕ) : ℤ) := by push_cast; rfl
        rw [this, zpow_natCast, hm']
      rw [h2, one_zpow, mul_one, zpow_one] at h1
      exact h1
    rw [key]
    exact H.zpow_mem hmem _
  have hPc : Nat.card ↥(P.map φ) = Nat.card ↥P := card_map_of_isPGroup φ hodd hP2
  have hH1 : Nat.card ↥Ht * Nat.card ↥(φ.ker ⊓ H : Subgroup B) = Nat.card ↥H := by
    have h1 := Subgroup.relIndex_mul_card (H := φ.ker) (K := H)
    rwa [Subgroup.relIndex_ker, hmapH] at h1
  have hH2 : P.relIndex H * Nat.card ↥P = Nat.card ↥H := by
    have h1 := Subgroup.relIndex_mul_card (H := P) (K := H)
    rwa [inf_eq_left.mpr hPH] at h1
  have hH3 : (P.map φ).relIndex Ht * Nat.card ↥(P.map φ) = Nat.card ↥Ht := by
    have h1 := Subgroup.relIndex_mul_card (H := P.map φ) (K := Ht)
    rwa [inf_eq_left.mpr hle] at h1
  have hrel : P.relIndex H = (P.map φ).relIndex Ht * Nat.card ↥(φ.ker ⊓ H : Subgroup B) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥P))
    rw [hH2, ← hH1, ← hH3, hPc]
    ring
  have hcodd : Odd (Nat.card ↥(φ.ker ⊓ H : Subgroup B)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  let ψ : ↥H →* ↥Ht := (φ.comp H.subtype).codRestrict Ht (fun x => by
    have : φ x ∈ H.map φ := ⟨x, x.2, rfl⟩
    rwa [hmapH] at this)
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    have : y ∈ H.map φ := by rwa [hmapH]
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hψker : ψ.ker = Subgroup.center ↥H := by
    ext x
    constructor
    · intro hx
      have hx1 : φ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (show (x : B) ∈ φ.ker from hx1)) g)
    · intro hx
      have hc : ψ x ∈ Subgroup.center ↥Ht := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨g, rfl⟩ := hψs y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g]
      rw [hcen, Subgroup.mem_bot] at hc
      exact hc
  refine ⟨H, hHperf, hPH, ?_, ?_, ?_⟩
  · show ¬ 2 ∣ P.relIndex H
    rw [hrel]
    intro h2
    rcases Nat.prime_two.dvd_mul.1 h2 with h | h
    · exact hidx h
    · exact (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr h)
  · have hle' : (Subgroup.center ↥H).map H.subtype ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← hψker] at hx
      exact congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h1 : Nat.card ↥((Subgroup.center ↥H).map H.subtype) = Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h1]
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle')
  · refine ⟨?_, ?_⟩
    · have e : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      apply Subgroup.map_injective H.subtype_injective
      rw [e, hHperf, Subgroup.map_top, Subgroup.range_subtype]
    · exact MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))

end Lift

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
