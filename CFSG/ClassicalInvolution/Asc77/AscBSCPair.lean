module

public import CFSG.ClassicalInvolution.Asc77.AscBSCModel
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootCtx
public import CFSG.ClassicalInvolution.SmallCases.NDBC2
import CFSG.ClassicalInvolution.Asc77.WP3SCSModel

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD
  (CommFamilyConnected ModelFund le_centralizer_of_isClassicalMember)

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}


structure CompMem (C : XCtx p f Ω z) (j : Fin C.D.card) where
  N : Subgroup G
  n : G
  R : Subgroup (compModel C.D j).K
  hN : N ∈ tqMembers Ω z
  hn : IsClassicalMember p f N n
  hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D
  himg : modOdd z (exactCore z N) = R.map (C.psi j)

namespace CompMem

variable {C : XCtx p f Ω z} {j : Fin C.D.card} (m : CompMem C j)

noncomputable def nbar : OddQuot z := oddQuotMk z ⟨m.n, C.involution_mem_centralizer m.hN m.hn⟩

theorem nbar_mem : m.nbar ∈ m.R.map (C.psi j) := by
  have h := oddQuotMk_mem_modOdd (C.involution_mem_exactCore m.hN m.hn)
    (C.involution_mem_centralizer m.hN m.hn)
  rw [m.himg] at h
  exact h

theorem nbar_sq : m.nbar * m.nbar = 1 := by
  unfold nbar
  rw [← map_mul]
  have : (⟨m.n, C.involution_mem_centralizer m.hN m.hn⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
      ⟨m.n, C.involution_mem_centralizer m.hN m.hn⟩ = 1 :=
    Subtype.ext (isCentralInvolution_of_isClassicalMember m.hn).sq
  rw [this, map_one]

theorem nbar_ne_one : m.nbar ≠ 1 := fun h =>
  (isCentralInvolution_of_isClassicalMember m.hn).ne_one
    (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one
      (Subtype.ext (isCentralInvolution_of_isClassicalMember m.hn).sq) h))

end CompMem

noncomputable abbrev zbar (z : G) : OddQuot z := oddQuotMk z ⟨z, XCtx.hzC z⟩

section Comp

variable (C : XCtx p f Ω z)

include C

theorem exists_compMem (j : Fin C.D.card) : Nonempty (CompMem C j) := by
  obtain ⟨R, hR, hmem⟩ := C.D.meets j
  have hmem' : R.map (secComponentHom C.hs.normalizes C.D j) ∈
      memberImages (exactFamily Ω z) z := by
    rw [← map_sectionQuotientHom_family C.hs.normalizes]
    exact ⟨_, hmem, Subgroup.map_map _ _ _⟩
  obtain ⟨M, hM, hMR⟩ := hmem'
  obtain ⟨N, hN, rfl⟩ := hM.1
  have hex := C.hΩ.classical N hN.1
  obtain ⟨n, hn⟩ := hex
  exact ⟨{ N := N, n := n, R := R, hN := hN, hn := hn, hR := hR, himg := hMR }⟩

theorem eq_one_of_comm (j : Fin C.D.card) (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) {r : (compModel C.D j).K}
    (hrR : r ∈ R)
    (hcomm : ∀ y : (compModel C.D j).K, C.psi j r * C.psi j y = C.psi j y * C.psi j r) :
    r = 1 := by
  refine CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p (C.D.tag j) (C.D.rank j)
    (C.D.exp j) (C.D.isFundTag j) (C.D.admissible j) hj R hR r hrR fun y => C.psi_ker j ?_
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
  calc C.psi j r * C.psi j y * (C.psi j r)⁻¹ * (C.psi j y)⁻¹
      = (C.psi j y * C.psi j r) * (C.psi j r)⁻¹ * (C.psi j y)⁻¹ := by rw [hcomm y]
    _ = 1 := by group

theorem zbar_not_mem (j : Fin C.D.card) (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) :
    zbar z ∉ R.map (C.psi j) := by
  rintro ⟨r, hrR, hr⟩
  have hr1 : r = 1 := by
    refine eq_one_of_comm C j hj hR hrR fun y => ?_
    rw [hr]
    exact oddQuotMk_central (XCtx.hzC z) (C.psi j y)
  rw [hr1, map_one] at hr
  exact C.hKz.ne_one (congrArg Subtype.val
    (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) hr.symm))

theorem comm_mem_ker (j : Fin C.D.card) {x : (compModel C.D j).K} (hx : C.psi j x = zbar z)
    (y : (compModel C.D j).K) : x * y * x⁻¹ * y⁻¹ ∈ (C.psi j).ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hx]
  have hc := oddQuotMk_central (XCtx.hzC z) (C.psi j y)
  calc zbar z * C.psi j y * (zbar z)⁻¹ * (C.psi j y)⁻¹
      = (C.psi j y * zbar z) * (zbar z)⁻¹ * (C.psi j y)⁻¹ := by rw [hc]
    _ = 1 := by group

end Comp

section Frames

variable (C : XCtx p f Ω z)

theorem exists_fuzzyFrame_of_components {j₁ j₂ : Fin C.D.card} (hne : j₁ ≠ j₂)
    (hj₂ : ¬ (C.D.tag j₂ = .PSL ∧ C.D.rank j₂ = 2)) (m₁ : CompMem C j₁) (m₂ : CompMem C j₂)
    (h1z : m₁.nbar ≠ zbar z) : ∃ A : Subgroup G, Theorem5.FuzzyFrameOn p f Ω A := by
  have hcomm : ∀ x ∈ modOdd z (exactCore z m₁.N), ∀ y ∈ modOdd z (exactCore z m₂.N),
      x * y = y * x := by
    intro x hx y hy
    rw [m₁.himg] at hx
    rw [m₂.himg] at hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    exact C.psi_commute hne a b
  have h2z : m₂.nbar ≠ zbar z := fun h => zbar_not_mem C j₂ hj₂ m₂.hR (h ▸ m₂.nbar_mem)
  obtain ⟨r, hrR, hr⟩ := m₂.nbar_mem
  obtain ⟨a, -, ha⟩ := m₁.nbar_mem
  have h12 : m₁.nbar ≠ m₂.nbar := by
    intro h
    have hr1 : r = 1 := by
      refine eq_one_of_comm C j₂ hj₂ m₂.hR hrR fun y => ?_
      rw [hr, ← h, ← ha]
      exact C.psi_commute hne a y
    rw [hr1, map_one] at hr
    exact m₂.nbar_ne_one hr.symm
  have h12z : m₁.nbar * m₂.nbar ≠ zbar z := by
    intro h
    have hn2 : m₂.nbar = m₁.nbar * zbar z := by
      calc m₂.nbar = m₁.nbar * (m₁.nbar * m₂.nbar) := by
            rw [← mul_assoc, m₁.nbar_sq, one_mul]
        _ = m₁.nbar * zbar z := by rw [h]
    have hr1 : r = 1 := by
      refine eq_one_of_comm C j₂ hj₂ m₂.hR hrR fun y => ?_
      have hc := oddQuotMk_central (XCtx.hzC z) (C.psi j₂ y)
      have ha' := C.psi_commute hne a y
      calc C.psi j₂ r * C.psi j₂ y = (C.psi j₁ a * zbar z) * C.psi j₂ y := by
            rw [hr, hn2, ← ha]
        _ = C.psi j₁ a * (zbar z * C.psi j₂ y) := by rw [mul_assoc]
        _ = C.psi j₁ a * (C.psi j₂ y * zbar z) := by rw [hc]
        _ = (C.psi j₁ a * C.psi j₂ y) * zbar z := by rw [mul_assoc]
        _ = (C.psi j₂ y * C.psi j₁ a) * zbar z := by rw [ha']
        _ = C.psi j₂ y * (C.psi j₁ a * zbar z) := by rw [mul_assoc]
        _ = C.psi j₂ y * C.psi j₂ r := by rw [hr, hn2, ← ha]
    rw [hr1, map_one] at hr
    exact m₂.nbar_ne_one hr.symm
  exact NDB.Cover.exists_fuzzyFrameOn_of_commute C m₁.hN m₂.hN m₁.hn m₂.hn hcomm h1z h2z h12 h12z

theorem exists_fuzzyFrame_of_pair (j : Fin C.D.card)
    (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2)) (hG2 : C.D.tag j ≠ .G2)
    (hD4 : C.D.tag j ≠ .trialityD4)
    (hconn : CommFamilyConnected (ModelFund p (C.D.tag j) (C.D.rank j) (C.D.exp j))) :
    ∃ A : Subgroup G, Theorem5.FuzzyFrameOn p f Ω A := by
  obtain ⟨m₀⟩ := exists_compMem C j
  have hq : 5 ≤ p ^ C.D.exp j := by
    rw [C.exp_eq j hD4]
    exact C.hq
  have hK : CFSG.Open.IsQuasisimple (compModel C.D j).K :=
    (ModelFacts.modelClauseZero _ _ _ _ _ (C.D.isFundTag j) (C.D.admissible j)).1
  obtain ⟨R, hR, S, hS, hRS, hpair⟩ := exists_commuting_pair_ne C.hp hq (C.D.isFundTag j)
    (C.D.admissible j) hG2 hD4 hj hconn m₀.hR
  obtain ⟨N₁, hN₁, hmod₁⟩ := C.exists_member_of_fund j (C.single j hG2 hD4) hR
  obtain ⟨N₂, hN₂, hmod₂⟩ := C.exists_member_of_fund j (C.single j hG2 hD4) hS
  obtain ⟨n₁, hn₁⟩ := C.hΩ.classical N₁ hN₁.1
  obtain ⟨n₂, hn₂⟩ := C.hΩ.classical N₂ hN₂.1
  let m₁ : CompMem C j := ⟨N₁, n₁, R, hN₁, hn₁, hR, hmod₁⟩
  let m₂ : CompMem C j := ⟨N₂, n₂, S, hN₂, hn₂, hS, hmod₂⟩
  have hcomm : ∀ x ∈ modOdd z (exactCore z N₁), ∀ y ∈ modOdd z (exactCore z N₂),
      x * y = y * x := by
    intro x hx y hy
    rw [hmod₁] at hx
    rw [hmod₂] at hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hRS a ha b hb]
  have h1z : m₁.nbar ≠ zbar z := fun h => zbar_not_mem C j hj hR (h ▸ m₁.nbar_mem)
  have h2z : m₂.nbar ≠ zbar z := fun h => zbar_not_mem C j hj hS (h ▸ m₂.nbar_mem)
  obtain ⟨r, hrR, hr⟩ := m₁.nbar_mem
  obtain ⟨s, hsS, hs⟩ := m₂.nbar_mem
  have hr2 : r * r ∈ Subgroup.center (compModel C.D j).K :=
    C.psi_ker j (by rw [MonoidHom.mem_ker, map_mul, hr, m₁.nbar_sq])
  have hs2 : s * s ∈ Subgroup.center (compModel C.D j).K :=
    C.psi_ker j (by rw [MonoidHom.mem_ker, map_mul, hs, m₂.nbar_sq])
  have hrZ : r ∉ Subgroup.center (compModel C.D j).K := by
    intro h
    have h1 := eq_one_of_mem_center (C.D.isFundTag j) (C.D.admissible j) hj hR hrR h
    rw [h1, map_one] at hr
    exact m₁.nbar_ne_one hr.symm
  have hsZ : s ∉ Subgroup.center (compModel C.D j).K := by
    intro h
    have h1 := eq_one_of_mem_center (C.D.isFundTag j) (C.D.admissible j) hj hS hsS h
    rw [h1, map_one] at hs
    exact m₂.nbar_ne_one hs.symm
  have hnc := hpair r hrR s hsS hr2 hs2 hrZ hsZ
  have h12 : m₁.nbar ≠ m₂.nbar := by
    intro h
    apply hnc
    refine C.psi_ker j ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr, hs, h, mul_inv_cancel]
  have h12z : m₁.nbar * m₂.nbar ≠ zbar z := by
    intro h
    apply hnc
    have hz : C.psi j (r * s) = zbar z := by rw [map_mul, hr, hs, h]
    have hrs : r * s ∈ Subgroup.center (compModel C.D j).K :=
      ModelFacts.mem_center_of_commutators_mem_center hK fun y =>
        C.psi_ker j (comm_mem_ker C j hz y)
    have e : r * s⁻¹ = (r * s) * (s * s)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hrs (Subgroup.inv_mem _ hs2)
  exact NDB.Cover.exists_fuzzyFrameOn_of_commute C hN₁ hN₂ hn₁ hn₂ hcomm h1z h2z h12 h12z

theorem classical_of_nbar_eq {j : Fin C.D.card} (hj : C.D.tag j = .PSL ∧ C.D.rank j = 2)
    (m : CompMem C j) (h : m.nbar = zbar z) :
    IsClassicalMember p f m.N z ∧ modOdd z m.N = (C.psi j).range := by
  have hmod : modOdd z (exactCore z m.N) = (C.psi j).range := by
    rw [m.himg, C.fund_eq_top j hj m.hR, Subgroup.map_top]
  have hz : zbar z ∈ (C.psi j).range := by
    rw [← h]
    exact Subgroup.map_le_range _ _ m.nbar_mem
  have hw : m.n = z := C.classical_of_range m.hN m.hn hmod hz
  have hcl : IsClassicalMember p f m.N z := by
    have h0 := m.hn
    rwa [hw] at h0
  refine ⟨hcl, ?_⟩
  rw [← hmod, exactCore_eq_self hcl.perfect (le_centralizer_of_isClassicalMember hcl)]

end Frames

end CFSG.ClassicalInvolution.Asc77.BSC
