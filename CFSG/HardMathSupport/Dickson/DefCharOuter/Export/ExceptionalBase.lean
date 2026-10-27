module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

section Transport

variable {p : ℕ} {S : Type} [Group S]

theorem commute_pow_of_mul_eq {β w : MulAut S} (h : w * β = β * w) (r : ℕ) :
    w * β ^ r = β ^ r * w :=
  (Commute.pow_right (show Commute w β from h) r).eq

theorem OuterCentData.of_pow {β : MulAut S} (r : ℕ) (h : OuterCentData p (β ^ r))
    (hfix : fixSubgroup (β ^ r) = fixSubgroup β) : OuterCentData p β where
  unique I J hI hJ := h.unique I J (hfix ▸ hI) (hfix ▸ hJ)
  chev I hI := h.chev I (hfix ▸ hI)
  core hexc := hfix ▸ h.core hexc
  cent hexc w hw hwβ hfixw :=
    h.cent hexc w hw (commute_pow_of_mul_eq hwβ r) (fun x hx => hfixw x (hfix ▸ hx))
  noHatSix hp3 I hI := h.noHatSix hp3 I (hfix ▸ hI)
  l227 hp3 I hI hL β' hβ3 hββ' hmap :=
    h.l227 hp3 I (hfix ▸ hI) hL β' hβ3
      (by
        have := commute_pow_of_mul_eq hββ' r
        exact this) hmap

theorem OuterCentData.of_conj_aut (hp : p.Prime) [Finite S] {β : MulAut S} (δ : MulAut S)
    (h : OuterCentData p (δ * β * δ⁻¹)) : OuterCentData p β := by
  refine OuterCentData.of_congr hp (δ : S ≃* S) ?_
  have : MulAut.congr (δ : S ≃* S) β = δ * β * δ⁻¹ := by
    ext x
    simp [MulAut.congr_apply]
  rw [this]
  exact h

end Transport

section Stabilizer

variable {p : ℕ} {T : Type} [Group T] [Finite T]

theorem cent_of_stabilizer (hp : p.Prime) {α : MulAut T} (hα : orderOf α = p) {M : Subgroup T}
    (hle : M ≤ fixSubgroup α)
    (hstab : ∀ w : MulAut T, w * α = α * w → (∀ x ∈ M, w x = x) → w ∈ Subgroup.zpowers α) :
    ∀ w : MulAut T, Nat.Coprime p (orderOf w) → w * α = α * w →
      (∀ x ∈ fixSubgroup α, w x = x) → w ∈ innerAut T := by
  intro w hw hwα hfixw
  have hmem := hstab w hwα fun x hx => hfixw x (hle hx)
  have hdvd : orderOf w ∣ p := hα ▸ orderOf_dvd_of_mem_zpowers hmem
  have hone : orderOf w = 1 := (Nat.Coprime.symm hw).eq_one_of_dvd hdvd
  rw [orderOf_eq_one_iff] at hone
  rw [hone]
  exact (innerAut T).one_mem

theorem eq_one_of_conj_mem_zpowers (hp : p.Prime) {α : MulAut T} (hα : orderOf α = p)
    (hout : α ∉ innerAut T) (hZ : Subgroup.center T = ⊥) {x : T}
    (hx : MulAut.conj x ∈ Subgroup.zpowers α) : x = 1 := by
  by_contra hx1
  have hne : MulAut.conj x ≠ 1 := by
    intro h
    apply hx1
    have : x ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut T => f y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rwa [hZ, Subgroup.mem_bot] at this
  have hdvd : orderOf (MulAut.conj x) ∣ p := hα ▸ orderOf_dvd_of_mem_zpowers hx
  have hord : orderOf (MulAut.conj x) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have hle : Subgroup.zpowers (MulAut.conj x) ≤ Subgroup.zpowers α := Subgroup.zpowers_le.2 hx
  have hcard : Nat.card (Subgroup.zpowers α) ≤ Nat.card (Subgroup.zpowers (MulAut.conj x)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hα]
  have heq : Subgroup.zpowers (MulAut.conj x) = Subgroup.zpowers α :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hαm : α ∈ Subgroup.zpowers (MulAut.conj x) := by
    rw [heq]
    exact Subgroup.mem_zpowers α
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hαm
  apply hout
  refine ⟨x ^ k, ?_⟩
  rw [map_zpow]
  exact hk

theorem OuterCentData.ofStabilizer (hp : p.Prime) {α : MulAut T} (hα : orderOf α = p)
    (hout : α ∉ innerAut T) (hZ : Subgroup.center T = ⊥) {M : Subgroup T}
    (hle : M ≤ fixSubgroup α) (hn : (M.subgroupOf (fixSubgroup α)).Normal)
    (hs : IsSimpleGroup ↥M) (hnab : ∃ a b : ↥M, a * b ≠ b * a)
    (hsol : Group.IsSolvable (↥(fixSubgroup α) ⧸ M.subgroupOf (fixSubgroup α)))
    (hstab : ∀ w : MulAut T, w * α = α * w → (∀ x ∈ M, w x = x) → w ∈ Subgroup.zpowers α)
    (hchev : IsChevSimple p ↥M) (hdvd : p ∣ Nat.card ↥M)
    (hL27 : p = 3 → ¬ IsLTwoTwentySeven ↥M) : OuterCentData p α := by
  have hcent : ∀ x ∈ fixSubgroup α, (∀ m ∈ M, x * m = m * x) → x = 1 := by
    intro x hxfix hx
    refine eq_one_of_conj_mem_zpowers hp hα hout hZ (hstab _ ?_ fun m hm => ?_)
    · ext y
      have hx' : α x = x := hxfix
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hx']
    · rw [MulAut.conj_apply, hx m hm]
      group
  exact OuterCentData.ofSimpleNormal hp
    ⟨hle, hn, hs, hnab, hsol, hcent, hchev, hdvd⟩
    (fun _ => cent_of_stabilizer hp hα hle hstab)
    (fun h3 hL => absurd hL (hL27 h3))

end Stabilizer

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
