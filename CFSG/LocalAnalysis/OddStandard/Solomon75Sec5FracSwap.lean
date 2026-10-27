module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracEnd
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracDiag

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

omit [Finite X] in
theorem frac_map_conj_subgroupOf {C₀ : Subgroup X} {r : X} (hr : r ∈ C₀) (A : Subgroup X) :
    (A.subgroupOf C₀).map (MulAut.conj (⟨r, hr⟩ : ↥C₀)).toMonoidHom =
      (A.map (MulAut.conj r).toMonoidHom).subgroupOf C₀ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : X), hy, by simp [MulAut.conj_apply]⟩
  · rintro ⟨a, ha, hax⟩
    have hxC : (x : X) ∈ C₀ := x.2
    have haC : a ∈ C₀ := by
      have hax' : r * a * r⁻¹ = (x : X) := by simpa [MulAut.conj_apply] using hax
      have : a = r⁻¹ * (x : X) * r := by
        rw [← hax']
        group
      rw [this]
      exact C₀.mul_mem (C₀.mul_mem (C₀.inv_mem hr) hxC) hr
    refine ⟨⟨a, haC⟩, ha, ?_⟩
    apply Subtype.ext
    simpa [MulAut.conj_apply] using hax

omit [Finite X] in
theorem eq_one_or_eq_of_mem_zpowers {u x : X} (hu : u * u = 1) (hx : x ∈ Subgroup.zpowers u) :
    x = 1 ∨ x = u := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hu2 : u ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hu
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m
  · left
    rw [hk, zpow_mul, hu2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hu2, one_zpow, one_mul, zpow_one]

theorem swap_witness_eq (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {A A' : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hA' : Sec5Comp X n (normalizer (Z : Set X)) A') (hne : A ≠ A')
    (hAs : A.map (MulAut.conj s).toMonoidHom = A') {u : X}
    (hu : IsIntrinsicIn X (normalizer (Z : Set X)) A u) (huZ : u ∈ Z) (hu1 : u ≠ 1) :
    s * u * s⁻¹ = u := by
  classical
  by_contra hne'
  have hs2 : s * s = 1 := hs.sq
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  set u' : X := s * u * s⁻¹ with hu'def
  have hsN : s ∈ normalizer (Z : Set X) := hs.mem
  have hu'Z : u' ∈ Z := (Subgroup.mem_normalizer_iff.1 hsN u).1 huZ
  have hu'2 : u' * u' = 1 := h.Z_sq_eq_one hu'Z
  have hcommZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b) * (a * b) = 1 := h.Z_sq_eq_one (Z.mul_mem ha hb)
    have h2 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (h.Z_sq_eq_one ha),
      inv_eq_of_mul_eq_one_right (h.Z_sq_eq_one hb)]
  set w : X := u * u' with hwdef
  have hwZ : w ∈ Z := Z.mul_mem huZ hu'Z
  have hw2 : w * w = 1 := h.Z_sq_eq_one hwZ
  have hw2' : w ^ 2 = 1 := by
    rw [sq]
    exact hw2
  have hw1 : w ≠ 1 := by
    intro hw1
    apply hne'
    have h1 : u' = u⁻¹ := eq_inv_of_mul_eq_one_right hw1
    rw [h1, inv_eq_of_mul_eq_one_right hu2]
  have hwo : orderOf w = 2 := orderOf_eq_prime hw2' hw1
  have hu'1 : u' ≠ 1 := by
    intro h1
    apply hu1
    have h2 : u = s⁻¹ * u' * s := by
      simp only [hu'def]
      group
    rw [h2, h1]
    group
  have hsu' : s * u' * s⁻¹ = u := by
    calc s * u' * s⁻¹ = (s * s) * u * (s * s)⁻¹ := by
          simp only [hu'def]
          group
      _ = u := by
          rw [hs2]
          group
  have hws' : s * w * s⁻¹ = w := by
    calc s * w * s⁻¹ = (s * u * s⁻¹) * (s * u' * s⁻¹) := by
          simp only [hwdef]
          group
      _ = u' * u := by rw [hsu']
      _ = w := hcommZ u' hu'Z u huZ
  have hws : w * s = s * w := by
    calc w * s = (s * w * s⁻¹) * s := by rw [hws']
      _ = s * w := by group
  have hu'A' : u' ∈ A' := by
    rw [← hAs]
    exact ⟨u, hu.2.1, by simp [hu'def, MulAut.conj_apply]⟩
  have hu'N : u' ∈ normalizer ((normalizer (Z : Set X) : Subgroup X) : Set X) :=
    Subgroup.le_normalizer (Subgroup.le_normalizer hu'Z)
  have hu'sec : u' ∈ centralizerSection A (pPrimeCoreOf 2 A) :=
    normalizes_isPCompIn_of_comm_mem hA.isPCompIn hu'N (fun l hl =>
      commutator_mem_oddCoreOf_of_ne hA.isPCompIn hA'.isPCompIn hne hl hu'A')
  have hwsec : w ∈ centralizerSection A (pPrimeCoreOf 2 A) :=
    (centralizerSection A (pPrimeCoreOf 2 A)).mul_mem hu.mem_zStar.2 hu'sec
  have huC : u ∈ centralizer ({w} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hwdef]
    calc u * (u * u') = (u * u) * u' := by group
      _ = u' := by rw [hu2, one_mul]
      _ = u * (u' * u) := by
          rw [hcommZ u' hu'Z u huZ, ← mul_assoc, hu2, one_mul]
      _ = u * u' * u := by group
  obtain ⟨hd1, hd2, -⟩ := hu.descend_singleton hA.2 hw2' hwsec huC
  obtain ⟨B, hB, hBn, -⟩ := exists_isIntrinsicIn_centralizer h.hypA h.maxdeg (s := w) hwo
    (inf_le_right : normalizer (Z : Set X) ⊓ centralizer ({w} : Set X) ≤
      centralizer ({w} : Set X)) hd1 hd2
  have hBc : Sec5Comp X n (centralizer ({w} : Set X)) B := ⟨⟨u, hB⟩, hBn⟩
  have hsCw : s ∈ centralizer ({w} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hws.symm
  have hBs : B.map (MulAut.conj s).toMonoidHom ≠ B := by
    intro hBeq
    have hCw : (centralizer ({w} : Set X)).map (MulAut.conj s).toMonoidHom =
        centralizer ({w} : Set X) :=
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hsCw)
    have hB' : IsIntrinsicIn X (centralizer ({w} : Set X)) B u' := by
      have h1 := hB.map_mulEquiv (MulAut.conj s)
      rw [hCw, hBeq] at h1
      exact h1
    have hwz : w ∈ zStar B := (zStar B).mul_mem hB.mem_zStar hB'.mem_zStar
    have hwsup := hB.zStar_le_sup_zpowers hBn hwz
    have hnorm : Subgroup.zpowers u ≤ normalizer (pPrimeCoreOf 2 B : Set X) := by
      rw [Subgroup.zpowers_le]
      exact le_normalizer_oddCoreOf B hB.2.1
    obtain ⟨o, ho, k, hk, hok⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing
      (pPrimeCoreOf 2 B) (Subgroup.zpowers u) (fun x hx => hnorm hx) w).1 hwsup
    have hkZ : k ∈ Z := (Subgroup.zpowers_le.2 huZ) hk
    have hoZ : o ∈ Z := by
      have : o = w * k⁻¹ := by rw [← hok]; group
      rw [this]
      exact Z.mul_mem hwZ (Z.inv_mem hkZ)
    have ho1 : o = 1 :=
      eq_one_of_mem_of_mem_odd (oddCoreOf B) Z (odd_card_oddCoreOf B) h.isPGroup_Z hoZ ho
    rw [ho1, one_mul] at hok
    rcases eq_one_or_eq_of_mem_zpowers hu2 hk with hk1 | hk1
    · exact hw1 (hok.symm.trans hk1)
    · have : u' = 1 := by
        have h2 : u * u' = u := hok.symm.trans hk1
        have h3 : u * u' = u * 1 := by rw [h2, mul_one]
        exact mul_left_cancel h3
      exact hu'1 this
  set Cw : Subgroup X := centralizer ({w} : Set X) with hCw
  have huCw : u ∈ Cw := huC
  have hBCw : B ≤ Cw := hBc.isPCompIn.1
  have hB'c : Sec5Comp X n Cw (B.map (MulAut.conj s).toMonoidHom) :=
    hBc.map_conj (Subgroup.le_normalizer hsCw)
  have hB'Cw : B.map (MulAut.conj s).toMonoidHom ≤ Cw := hB'c.isPCompIn.1
  set tC : ↥Cw := ⟨s, hsCw⟩ with htC
  have htC2 : tC * tC = 1 := Subtype.ext hs2
  have hBpc : IsPComponent 2 (B.subgroupOf Cw) := hBc.isPCompIn.2
  have hneC : (B.subgroupOf Cw).map (MulAut.conj tC).toMonoidHom ≠ B.subgroupOf Cw := by
    rw [frac_map_conj_subgroupOf hsCw B]
    intro heq
    apply hBs
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hB'Cw, inf_of_le_left hBCw] at heq
    exact heq
  have huB : (⟨u, huCw⟩ : ↥Cw) ∈ B.subgroupOf Cw := hB.2.1
  have hwCw : w ∈ Cw := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hwdefC : (⟨w, hwCw⟩ : ↥Cw) = ⟨u, huCw⟩ * (tC * ⟨u, huCw⟩ * tC⁻¹) := rfl
  have hwc : ∀ c : ↥Cw, c * ⟨w, hwCw⟩ = ⟨w, hwCw⟩ * c := fun c =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  have hw2C : (⟨w, hwCw⟩ : ↥Cw) * ⟨w, hwCw⟩ = 1 := Subtype.ext hw2
  obtain ⟨Δ, hΔt, hΔpc, hwΔ⟩ := exists_diag_piece hBpc htC2 hneC huB hwdefC hwc hw2C
  set ΔX : Subgroup X := Δ.map Cw.subtype with hΔX
  have hΔXw : ΔX ≤ Cw := Subgroup.map_subtype_le Δ
  have hΔXs : ΔX ≤ centralizer ({s} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hΔt hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hcenmap : (centralizer ({tC} : Set ↥Cw)).map Cw.subtype =
      Cw ⊓ centralizer ({s} : Set X) := by
    rw [centralizer_singleton_subgroup hsCw, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hΔXpc : IsPCompIn 2 (Cw ⊓ centralizer ({s} : Set X)) ΔX := by
    refine ⟨le_inf hΔXw hΔXs, ?_⟩
    have h1 := (isPComponent_subgroupOf_map_iff 2 Cw.subtype Cw.subtype_injective hΔt).2 hΔpc
    rwa [hcenmap] at h1
  have hwΔX : w ∈ ΔX := ⟨⟨w, hwCw⟩, hwΔ, rfl⟩
  exact false_of_piece h hs hwZ hw1 hws hΔXpc hwΔX

theorem zStar_sup_eq_of_swap (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {A A' : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hA' : Sec5Comp X n (normalizer (Z : Set X)) A') (hne : A ≠ A')
    (hAs : A.map (MulAut.conj s).toMonoidHom = A') :
    zStar A ⊔ oddCoreOf (K0 X n (normalizer (Z : Set X))) =
      zStar A' ⊔ oddCoreOf (K0 X n (normalizer (Z : Set X))) := by
  classical
  obtain ⟨u, hu⟩ := hA.1
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu.1, sq] at this
    exact this
  have hu1 : u ≠ 1 := by
    intro h1
    have := hu.1
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have huZ : u ∈ Z := h.mem_Z_of_comm_mem hA hu.2.1 hu2 (fun a ha => hu.comm_mem a ha)
  have hcomm : s * u * s⁻¹ = u := swap_witness_eq h hs hA hA' hne hAs hu huZ hu1
  have hu' : IsIntrinsicIn X (normalizer (Z : Set X)) A' u := by
    have h1 := hu.map_mulEquiv (MulAut.conj s)
    rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hs.mem), hAs] at h1
    simpa [MulAut.conj_apply, hcomm] using h1
  have hOA : pPrimeCoreOf 2 A ≤ oddCoreOf (K0 X n (normalizer (Z : Set X))) := by
    have hLK := hu.isPCompIn_K0 hA.2
    exact pPrimeCoreOf_le_oddCoreOf hLK.1 (isPComponent_two_iff.1 hLK.2).1
  have hOA' : pPrimeCoreOf 2 A' ≤ oddCoreOf (K0 X n (normalizer (Z : Set X))) := by
    have hLK := hu'.isPCompIn_K0 hA'.2
    exact pPrimeCoreOf_le_oddCoreOf hLK.1 (isPComponent_two_iff.1 hLK.2).1
  have hzA := hu.zStar_le_sup_zpowers hA.2
  have hzA' := hu'.zStar_le_sup_zpowers hA'.2
  have huzA : u ∈ zStar A := hu.mem_zStar
  have huzA' : u ∈ zStar A' := hu'.mem_zStar
  apply le_antisymm
  · refine sup_le ((hzA.trans (sup_le ?_ ?_))) le_sup_right
    · exact hOA.trans le_sup_right
    · exact (Subgroup.zpowers_le.2 huzA').trans le_sup_left
  · refine sup_le ((hzA'.trans (sup_le ?_ ?_))) le_sup_right
    · exact hOA'.trans le_sup_right
    · exact (Subgroup.zpowers_le.2 huzA).trans le_sup_left

end CFSG.OddStandard.Solomon75
