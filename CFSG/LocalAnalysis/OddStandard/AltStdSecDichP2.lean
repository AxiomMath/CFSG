module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

theorem exists_orderOf_three {m : ℕ} (hm : 3 ≤ m) :
    ∃ x : alternatingGroup (Fin m), orderOf x = 3 := by
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  refine ⟨⟨cyc3 a b c, mem_alt_cyc3 hab hbc⟩, ?_⟩
  have h3 : cyc3 a b c * cyc3 a b c * cyc3 a b c = 1 := by
    ext i
    simp only [cyc3, Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq]
    grind
  have h1 : cyc3 a b c ≠ 1 := by
    intro h
    have := congrArg (fun f : Perm (Fin m) => f a) h
    simp only [cyc3, Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq] at this
    grind
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext (by simpa [pow_succ] using h3)
  · exact fun h => h1 (congrArg Subtype.val h)

section P2

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

omit [Finite X] in
theorem inf_centralizer_le_zpowers (h : ExactShape t A m) (hm : 5 ≤ m) {P : Subgroup X}
    [P.Normal] (hP : IsPGroup 2 P) : P ⊓ centralizer ({t} : Set X) ≤ zpowers t := by
  obtain ⟨e⟩ := h.iso
  have hsimple : IsSimpleGroup A := isSimpleGroup_of_alt hm e
  set W : Subgroup X := P ⊓ centralizer ({t} : Set X) with hW
  have hnormal : ((A ⊓ W).subgroupOf A).Normal := by
    refine ⟨fun n hn a => ?_⟩
    have hn' : (n : X) ∈ A ⊓ W := hn
    obtain ⟨hnA, hnW⟩ := Subgroup.mem_inf.1 hn'
    obtain ⟨hnP, hnC⟩ := Subgroup.mem_inf.1 hnW
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem a.2 hnA) (inv_mem a.2),
      Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · exact (inferInstance : P.Normal).conj_mem _ hnP _
    · exact mul_mem (mul_mem (h.le_cent a.2) hnC) (inv_mem (h.le_cent a.2))
  have hAW : A ⊓ W = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ((A ⊓ W).subgroupOf A) with hD | hD
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxA, hxW⟩ := Subgroup.mem_inf.1 hx
      have : (⟨x, hxA⟩ : A) ∈ (A ⊓ W).subgroupOf A := hx
      rw [hD] at this
      have h1 : (⟨x, hxA⟩ : A) = 1 := this
      simpa using congrArg Subtype.val h1
    · exfalso
      obtain ⟨x, hx3⟩ := exists_orderOf_three (by omega : 3 ≤ m)
      have hxW : ((e.symm x : A) : X) ∈ W := by
        have : e.symm x ∈ (A ⊓ W).subgroupOf A := by rw [hD]; trivial
        exact (Subgroup.mem_inf.1 this).2
      have hxP : ((e.symm x : A) : X) ∈ P := (Subgroup.mem_inf.1 hxW).1
      have hord : orderOf ((e.symm x : A) : X) = 3 := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx3]
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨((e.symm x : A) : X), hxP⟩
      rw [Subgroup.orderOf_mk, hord] at hk
      rcases k with _ | k
      · simp at hk
      · rw [pow_succ] at hk
        omega
  intro w hw
  have hwC : w ∈ centralizer ({t} : Set X) := (Subgroup.mem_inf.1 hw).2
  have hwcent : w ∈ centralizer (A : Set X) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hwN : w ∈ normalizer (A : Set X) := h.cent_le_norm hwC
    have h1 : w * a * w⁻¹ * a⁻¹ ∈ A := by
      have := mul_mem ((mem_normalizer_iff.1 hwN a).1 ha) (inv_mem ha)
      simpa [mul_assoc] using this
    have h2 : w * a * w⁻¹ * a⁻¹ ∈ W := by
      have haw : a * w⁻¹ * a⁻¹ ∈ W := by
        refine Subgroup.mem_inf.2
          ⟨(inferInstance : P.Normal).conj_mem _ (inv_mem (Subgroup.mem_inf.1 hw).1) _, ?_⟩
        exact mul_mem (mul_mem (h.le_cent ha) (inv_mem hwC)) (inv_mem (h.le_cent ha))
      have := mul_mem hw haw
      simpa [mul_assoc] using this
    have h3 : w * a * w⁻¹ * a⁻¹ ∈ A ⊓ W := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [hAW] at h3
    have h4 : w * a * w⁻¹ * a⁻¹ = 1 := h3
    calc a * w = (w * a * w⁻¹ * a⁻¹)⁻¹ * (w * a) := by group
      _ = w * a := by rw [h4]; group
  rw [← h.cent_cent]
  exact Subgroup.mem_inf.2 ⟨hwcent, hwC⟩

theorem mem_center_of_pCore_ne_bot (h : ExactShape t A m) (hm : 5 ≤ m)
    (hP : CFSG.pCore 2 X ≠ ⊥) : t ∈ center X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 X with hPdef
  have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hW := inf_centralizer_le_zpowers h hm hPp
  have ht2 : t * t = 1 := by rw [← sq, ← h.order]; exact pow_orderOf_eq_one t
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have key : ∀ x ∈ zpowers t, x ≠ 1 → x = t := by
    intro x hx hx1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · exfalso
      apply hx1
      rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul]
      have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
      rw [this]; simp
    · rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul]
      have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
      rw [this]; simp
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hP
  have hZnt : Nontrivial (center ↥P) := IsPGroup.center_nontrivial hPp
  have hZp : IsPGroup 2 (center ↥P) := hPp.to_subgroup _
  have hZd : 2 ∣ Nat.card (center ↥P) := by
    rcases hZp.card_eq_or_dvd with h1 | h1
    · exfalso
      have := Nat.card_eq_one_iff_unique.1 h1
      exact not_subsingleton _ this.1
    · exact h1
  by_cases htP : t ∈ P
  ·
    obtain ⟨z₀, hz₀⟩ := exists_ne (1 : center ↥P)
    have hz₀t : ((z₀ : P) : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.1 z₀.2 ⟨t, htP⟩
      exact congrArg Subtype.val this.symm
    have hz₀ne : ((z₀ : P) : X) ≠ 1 := by
      intro h1
      apply hz₀
      exact Subtype.ext (Subtype.ext h1)
    have hzt : ((z₀ : P) : X) = t :=
      key _ (hW (Subgroup.mem_inf.2 ⟨(z₀ : P).2, hz₀t⟩)) hz₀ne
    have htcent : ∀ x ∈ P, x * t = t * x := by
      intro x hx
      have := Subgroup.mem_center_iff.1 z₀.2 ⟨x, hx⟩
      have h2 : x * ((z₀ : P) : X) = ((z₀ : P) : X) * x := congrArg Subtype.val this
      rw [hzt] at h2
      exact h2
    have hPle : ∀ x ∈ P, x ∈ zpowers t := fun x hx =>
      hW (Subgroup.mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 (htcent x hx)⟩)
    rw [mem_center_iff]
    intro g
    have hgt : g * t * g⁻¹ ∈ zpowers t := hPle _ ((inferInstance : P.Normal).conj_mem t htP g)
    have hord : orderOf (g * t * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.order
    have heq : g * t * g⁻¹ = t :=
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.eq_of_orderOf_eq_two_of_isCyclic
        (inferInstance : IsCyclic (zpowers t)) hgt (mem_zpowers t) hord h.order
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [heq]
  · exfalso
    have hbot : ∀ x ∈ P, x ∈ centralizer ({t} : Set X) → x = 1 := by
      intro x hxP hxC
      by_contra hx1
      exact htP (key x (hW (Subgroup.mem_inf.2 ⟨hxP, hxC⟩)) hx1 ▸ hxP)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := center ↥P) 2 hZd
    have huc : ∀ x : P, x * (u : P) = (u : P) * x := fun x => Subgroup.mem_center_iff.1 u.2 x
    set u0 : X := ((u : P) : X) with hu0
    have hu0P : u0 ∈ P := (u : P).2
    have hu0ord : orderOf u0 = 2 := by
      have h1 : orderOf (u : P) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact hu
      rw [hu0, Subgroup.orderOf_coe, h1]
    have hu0sq : u0 * u0 = 1 := by rw [← sq, ← hu0ord]; exact pow_orderOf_eq_one u0
    set u1 : X := t * u0 * t⁻¹ with hu1
    have hu1P : u1 ∈ P := (inferInstance : P.Normal).conj_mem u0 hu0P t
    have hcomm : u0 * u1 = u1 * u0 := by
      have := huc ⟨u1, hu1P⟩
      exact (congrArg Subtype.val this).symm
    have e1 : u1 * t = t * u0 := by rw [hu1]; group
    have e2 : t * u1 = u0 * t := by
      rw [hu1]
      calc t * (t * u0 * t⁻¹) = (t * t) * u0 * t⁻¹ := by group
        _ = u0 * t := by rw [ht2, ht1]; group
    have hv : u0 * u1 = 1 := by
      apply hbot _ (mul_mem hu0P hu1P)
      rw [mem_centralizer_singleton_iff]
      calc u0 * u1 * t = u0 * (u1 * t) := by group
        _ = u0 * (t * u0) := by rw [e1]
        _ = (u0 * t) * u0 := by group
        _ = (t * u1) * u0 := by rw [e2]
        _ = t * (u1 * u0) := by group
        _ = t * (u0 * u1) := by rw [hcomm]
    have hu10 : u1 = u0 := by
      have := eq_inv_of_mul_eq_one_right hv
      rwa [inv_eq_of_mul_eq_one_right hu0sq] at this
    have hu0C : u0 ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      rw [hu10] at e1
      exact e1
    have := hbot u0 hu0P hu0C
    rw [this, orderOf_one] at hu0ord
    omega

end P2

end CFSG.OddStandard.AltStdSec
