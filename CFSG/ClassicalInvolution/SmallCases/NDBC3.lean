module

public import CFSG.ClassicalInvolution.SmallCases.NDBC2
import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace Cover

section Comp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

omit [Finite G] in
theorem zbar_comm (y : OddQuot z) :
    oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ * y = y * oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have hc : z * (c : G) = (c : G) * z := (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  have e : (⟨z, Asc77.XCtx.hzC z⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * c =
      c * ⟨z, Asc77.XCtx.hzC z⟩ := Subtype.ext hc
  show oddQuotMk z _ * oddQuotMk z c = oddQuotMk z c * oddQuotMk z _
  rw [← map_mul, ← map_mul, e]

theorem exists_member_of_meets (C : Asc77.XCtx p f Ω z) (j : Fin C.D.card) :
    ∃ R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D, ∃ N ∈ tqMembers Ω z,
      modOdd z (exactCore z N) = R.map (C.psi j) := by
  obtain ⟨R, hR, hmem⟩ := C.D.meets j
  have h : R.map (C.psi j) ∈ memberImages (exactFamily Ω z) z := by
    rw [← map_sectionQuotientHom_family C.hs.normalizes]
    exact ⟨_, hmem, Subgroup.map_map _ _ _⟩
  obtain ⟨M, hM, hMR⟩ := h
  obtain ⟨N, hN, rfl⟩ := hM.1
  exact ⟨R, hR, N, hN, hMR⟩

theorem exists_not_commute (C : Asc77.XCtx p f Ω z) {j : Fin C.D.card}
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) {x : OddQuot z}
    (hx : x ∈ R.map (C.psi j)) (hx1 : x ≠ 1) : ∃ y ∈ (C.psi j).range, x * y ≠ y * x := by
  obtain ⟨r, hr, rfl⟩ := hx
  by_contra hcon
  push Not at hcon
  have h1 : r = 1 := RouteD.Gaps.fundNoncentral p (C.D.tag j) (C.D.rank j) (C.D.exp j)
    (C.D.isFundTag j) (C.D.admissible j) hj R hR r hr fun y => by
      apply C.psi_ker j
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        hcon (C.psi j y) ⟨y, rfl⟩]
      group
  exact hx1 (by rw [h1, map_one])

theorem eq_or_mul_eq (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ∈ tqMembers Ω z) (h₂ : N₂ ∈ tqMembers Ω z) {n₁ n₂ : G}
    (hn₁ : IsClassicalMember p f N₁ n₁) (hn₂ : IsClassicalMember p f N₂ n₂)
    (hcomm : ∀ x ∈ modOdd z (exactCore z N₁), ∀ y ∈ modOdd z (exactCore z N₂), x * y = y * x)
    (h1z : oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ ≠
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩)
    (h2z : oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ ≠
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) :
    oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ =
        oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ ∨
      oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ *
          oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ =
        oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hA⟩ := exists_fuzzyFrameOn_of_commute C h₁ h₂ hn₁ hn₂ hcomm h1z h2z hcon.1 hcon.2
  exact hnoF A hA

theorem false_of_two_nonA1 (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {i j : Fin C.D.card}
    (hij : i ≠ j) (hi : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2))
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) : False := by
  obtain ⟨Ri, hRi, Ni, hNi, hNiR⟩ := exists_member_of_meets C i
  obtain ⟨Rj, hRj, Nj, hNj, hNjR⟩ := exists_member_of_meets C j
  obtain ⟨ni, hni⟩ := C.hΩ.classical Ni hNi.1
  obtain ⟨nj, hnj⟩ := C.hΩ.classical Nj hNj.1
  have hxi : oddQuotMk z ⟨ni, C.involution_mem_centralizer hNi hni⟩ ∈ Ri.map (C.psi i) :=
    hNiR ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore hNi hni) _
  have hxj : oddQuotMk z ⟨nj, C.involution_mem_centralizer hNj hnj⟩ ∈ Rj.map (C.psi j) :=
    hNjR ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore hNj hnj) _
  obtain ⟨yi, hyi, hxyi⟩ :=
    exists_not_commute C hi hRi hxi (C.isUniqueInvolution_modOdd hNi hni).ne_one
  obtain ⟨yj, -, hxyj⟩ :=
    exists_not_commute C hj hRj hxj (C.isUniqueInvolution_modOdd hNj hnj).ne_one
  have hiz : oddQuotMk z ⟨ni, C.involution_mem_centralizer hNi hni⟩ ≠
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := fun h => hxyi (by rw [h]; exact zbar_comm yi)
  have hjz : oddQuotMk z ⟨nj, C.involution_mem_centralizer hNj hnj⟩ ≠
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := fun h => hxyj (by rw [h]; exact zbar_comm yj)
  have hcomm : ∀ x ∈ modOdd z (exactCore z Ni), ∀ y ∈ modOdd z (exactCore z Nj),
      x * y = y * x := by
    rw [hNiR, hNjR]
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact C.psi_commute hij a b
  have hxjc : ∀ y ∈ (C.psi i).range,
      oddQuotMk z ⟨nj, C.involution_mem_centralizer hNj hnj⟩ * y =
        y * oddQuotMk z ⟨nj, C.involution_mem_centralizer hNj hnj⟩ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, -, hb⟩ := hxj
    rw [← hb]
    exact (C.psi_commute hij a b).symm
  have hxj2 := (C.isUniqueInvolution_modOdd hNj hnj).sq
  rcases eq_or_mul_eq C hnoF hNi hNj hni hnj hcomm hiz hjz with h | h
  · exact hxyi (by rw [h]; exact hxjc yi hyi)
  · apply hxyi
    set xi := oddQuotMk z ⟨ni, C.involution_mem_centralizer hNi hni⟩
    set xj := oddQuotMk z ⟨nj, C.involution_mem_centralizer hNj hnj⟩
    set zb := oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩
    have e : xi = zb * xj := by
      calc xi = xi * (xj * xj) := by rw [hxj2, mul_one]
        _ = zb * xj := by rw [← mul_assoc, h]
    calc xi * yi = zb * (xj * yi) := by rw [e, mul_assoc]
      _ = zb * (yi * xj) := by rw [hxjc yi hyi]
      _ = (zb * yi) * xj := by rw [mul_assoc]
      _ = (yi * zb) * xj := by rw [zbar_comm yi]
      _ = yi * xi := by rw [e, mul_assoc]

theorem eq_z_of_le_A1 (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {i₁ : Fin C.D.card}
    (hQ : ¬ (C.D.tag i₁ = .PSL ∧ C.D.rank i₁ = 2)) {N : Subgroup G} (hN : N ∈ tqMembers Ω z)
    {n : G} (hn : IsClassicalMember p f N n) {i : Fin C.D.card}
    (hi : C.D.tag i = .PSL ∧ C.D.rank i = 2)
    (hNi : modOdd z (exactCore z N) ≤ (C.psi i).range) : n = z := by
  have hii₁ : i ≠ i₁ := by
    rintro rfl
    exact hQ hi
  obtain ⟨R, hR, M, hM, hMR⟩ := exists_member_of_meets C i₁
  obtain ⟨m, hm⟩ := C.hΩ.classical M hM.1
  have hnC := C.involution_mem_centralizer hN hn
  have hxm : oddQuotMk z ⟨m, C.involution_mem_centralizer hM hm⟩ ∈ R.map (C.psi i₁) :=
    hMR ▸ oddQuotMk_mem_modOdd (C.involution_mem_exactCore hM hm) _
  obtain ⟨y, hy, hxy⟩ :=
    exists_not_commute C hQ hR hxm (C.isUniqueInvolution_modOdd hM hm).ne_one
  have hmz : oddQuotMk z ⟨m, C.involution_mem_centralizer hM hm⟩ ≠
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := fun h => hxy (by rw [h]; exact zbar_comm y)
  have hx : oddQuotMk z ⟨n, hnC⟩ ∈ (C.psi i).range :=
    hNi (oddQuotMk_mem_modOdd (C.involution_mem_exactCore hN hn) _)
  have hxc : ∀ y ∈ (C.psi i₁).range, oddQuotMk z ⟨n, hnC⟩ * y = y * oddQuotMk z ⟨n, hnC⟩ := by
    obtain ⟨a, ha⟩ := hx
    rintro _ ⟨b, rfl⟩
    rw [← ha]
    exact C.psi_commute hii₁ a b
  have hcomm : ∀ u ∈ modOdd z (exactCore z N), ∀ v ∈ modOdd z (exactCore z M),
      u * v = v * u := by
    intro u hu v hv
    obtain ⟨a, ha⟩ := hNi hu
    rw [hMR] at hv
    obtain ⟨b, -, rfl⟩ := hv
    rw [← ha]
    exact C.psi_commute hii₁ a b
  by_contra hnz
  have hxz : oddQuotMk z ⟨n, hnC⟩ ≠ oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := fun h =>
    hnz (Asc77.eq_of_oddQuotMk_eq' hnC (Asc77.XCtx.hzC z) hn.isCentralInvolution.sq C.hKz.sq
      (Subgroup.mem_centralizer_singleton_iff.mp hnC) h)
  rcases eq_or_mul_eq C hnoF hN hM hn hm hcomm hxz hmz with h | h
  · exact hxy (by rw [← h]; exact hxc y hy)
  · apply hxy
    set x := oddQuotMk z ⟨n, hnC⟩
    set xm := oddQuotMk z ⟨m, C.involution_mem_centralizer hM hm⟩
    set zb := oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩
    have hx2 : x * x = 1 := (C.isUniqueInvolution_modOdd hN hn).sq
    have e : xm = x * zb := by
      calc xm = (x * x) * xm := by rw [hx2, one_mul]
        _ = x * zb := by rw [mul_assoc, h]
    calc xm * y = x * (zb * y) := by rw [e, mul_assoc]
      _ = x * (y * zb) := by rw [zbar_comm y]
      _ = (x * y) * zb := by rw [mul_assoc]
      _ = (y * x) * zb := by rw [hxc y hy]
      _ = y * xm := by rw [e, mul_assoc]

end Comp

end Cover

end CFSG.ClassicalInvolution.NDB
