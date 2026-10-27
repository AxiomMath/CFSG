module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameModel
public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha
public import CFSG.ClassicalInvolution.Asc77.WP3FrameData

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

structure ChainCtx (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (z : G) where
  K : Subgroup G
  hK : K ∈ Ω
  hKz : IsUniqueInvolution K z
  hΩ : HypOmegaMod p f Ω
  hp : p ≠ 2
  hq : 5 ≤ p ^ f
  D : LocalLieSystemAt p f (exactFamily Ω z) z
  card_eq : D.card = 2
  i₀ : Fin D.card
  i₁ : Fin D.card
  ne : i₀ ≠ i₁
  tag₁ : D.tag i₁ = .PSL ∨ D.tag i₁ = .PSU
  tag₀ : D.tag i₀ = .PSL
  rank₀ : D.rank i₀ = 2
  pair : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D)

namespace ChainCtx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  (C : ChainCtx p f Ω z)

include C

theorem hz2 : z * z = 1 := C.hKz.sq

theorem hc2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_sq_eq_one C.hz2

theorem hKtq : z ∈ trivialOnQuot C.K :=
  trivialOnQuot_of_isUniqueInvolution C.hp C.hq C.hΩ C.hK C.hKz

theorem hne : (tqMembers Ω z).Nonempty := ⟨C.K, C.hK, C.hKtq⟩

theorem hs : SecData p f z (exactFamily Ω z) :=
  secData_exactFamily C.hΩ.conjInvariant C.hΩ.classical C.hc2 C.hne

noncomputable abbrev psi (j : Fin C.D.card) : (compModel C.D j).K →* OddQuot z :=
  secComponentHom C.hs.normalizes C.D j

theorem psi_ker (j : Fin C.D.card) : (C.psi j).ker ≤ Subgroup.center (compModel C.D j).K :=
  secComponentHom_ker_le_center C.hs.normalizes C.D j

theorem eq_i₀_or_i₁ (j : Fin C.D.card) : j = C.i₀ ∨ j = C.i₁ := by
  have h := C.card_eq
  have hj := j.2
  have h0 := C.i₀.2
  have h1 := C.i₁.2
  have hne : C.i₀.val ≠ C.i₁.val := fun e => C.ne (Fin.ext e)
  by_contra hcon
  push Not at hcon
  have a1 : j.val ≠ C.i₀.val := fun e => hcon.1 (Fin.ext e)
  have a2 : j.val ≠ C.i₁.val := fun e => hcon.2 (Fin.ext e)
  omega

theorem exp_eq (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∨ C.D.tag j = .PSU) :
    C.D.exp j = f := by
  rcases C.D.exp_eq j with h | ⟨h, -⟩
  · exact h
  · rcases hj with h' | h' <;> rw [h'] at h <;> cases h

theorem four_le (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∨ C.D.tag j = .PSU) :
    4 ≤ p ^ C.D.exp j := by
  rw [C.exp_eq j hj]
  have := C.hq
  omega

theorem single (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∨ C.D.tag j = .PSU) :
    FundamentalSingleClass (C.D.tag j) (compModel C.D j).D := by
  refine ModelFacts.fundamentalSingleClass (C.D.tag j) (C.D.rank j) p (C.D.exp j) Fact.out
    (C.D.isFundTag j) (C.D.admissible j) ?_ ?_ <;> rcases hj with h | h <;> rw [h] <;> decide

theorem fund_perfect (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∨ C.D.tag j = .PSU)
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) : ⁅R, R⁆ = R :=
  commutator_self_eq_of_le (ModelFacts.fundPerfect_core (C.D.tag j) (C.D.rank j) p (C.D.exp j)
    C.hp (C.D.isFundTag j) (C.D.admissible j) (C.four_le j hj) R hR)

theorem exists_fund_of_mem {N : Subgroup G} (hN : N ∈ tqMembers Ω z) :
    ∃ j : Fin C.D.card, ∃ R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D,
      R.map (C.psi j) = modOdd z (exactCore z N) := by
  have hM : exactCore z N ∈ centMembers (exactFamily Ω z) z :=
    ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer z N⟩
  have hMY : exactCore z N ≤ centralizingLayer (exactFamily Ω z) {z} := le_centralizingLayer hM
  have hMfam : modOddIn (centralizingLayer (exactFamily Ω z) {z}) (exactCore z N) ∈
      localFamily (exactFamily Ω z) z := ⟨(exactCore z N).subgroupOf _, ⟨_, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := C.D.fundamental _ hMfam
  refine ⟨i, R, hR, ?_⟩
  have h1 : (R.map (C.D.hom i)).map (sectionQuotientHom C.hs.normalizes) =
      R.map (C.psi i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn C.hs.normalizes hM

theorem exists_member_of_fund (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∨ C.D.tag j = .PSU)
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) :
    ∃ N ∈ tqMembers Ω z, modOdd z (exactCore z N) = R.map (C.psi j) := by
  obtain ⟨M, hM, hMR⟩ := map_secComponentHom_mem_memberImages C.hs C.D j (C.single j hj) hR
  obtain ⟨N, hN, rfl⟩ := hM.1
  exact ⟨N, hN, hMR⟩

theorem involution_mem_exactCore {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) : w ∈ exactCore z N :=
  mem_exactCore hw C.hc2 hN.2

theorem involution_mem_centralizer {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) : w ∈ Subgroup.centralizer ({z} : Set G) :=
  exactCore_le_centralizer z N (C.involution_mem_exactCore hN hw)

theorem oddQuotMk_involution {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) (j : Fin C.D.card)
    (hj : C.D.tag j = .PSL ∨ C.D.tag j = .PSU) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    {τ : (compModel C.D j).K} (hτ : ∀ c ∈ R, (∀ r ∈ R, c * r = r * c) → c = 1 ∨ c = τ)
    (hmod : modOdd z (exactCore z N) = R.map (C.psi j)) :
    oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩ = C.psi j τ := by
  have hwE := C.involution_mem_exactCore hN hw
  have hwC := C.involution_mem_centralizer hN hw
  have hmem : oddQuotMk z ⟨w, hwC⟩ ∈ R.map (C.psi j) := hmod ▸ oddQuotMk_mem_modOdd hwE hwC
  obtain ⟨r, hrR, hr⟩ := hmem
  have hcw := isCentralInvolution_of_isClassicalMember hw
  have hcent : ∀ s ∈ R, C.psi j r * C.psi j s = C.psi j s * C.psi j r := by
    intro s hs
    have hsm : C.psi j s ∈ modOdd z (exactCore z N) := hmod ▸ ⟨s, hs, rfl⟩
    obtain ⟨k, hk, hks⟩ := hsm
    rw [hr, ← hks, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk z) (Subtype.ext (hcw.central _ (exactCore_le_left z N hk)))
  have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr (C.fund_perfect j hj hR)
  have hrc : ∀ s ∈ R, r * s = s * r := by
    have key : (⟨r, hrR⟩ : ↥R) ∈ Subgroup.center ↥R :=
      FrameVertex.mem_center_of_commutators_central fun t => by
        rw [Subgroup.mem_center_iff]
        intro u
        have h1 : C.psi j (r * (t : (compModel C.D j).K) * r⁻¹ *
            (t : (compModel C.D j).K)⁻¹) = 1 := by
          have := hcent t t.2
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, this]
          group
        have h2 : r * (t : (compModel C.D j).K) * r⁻¹ * (t : (compModel C.D j).K)⁻¹ ∈
            Subgroup.center (compModel C.D j).K :=
          C.psi_ker j (MonoidHom.mem_ker.mpr h1)
        apply Subtype.ext
        have := Subgroup.mem_center_iff.mp h2 u
        simpa [commutatorElement_def] using this
    intro s hs
    have := Subgroup.mem_center_iff.mp key ⟨s, hs⟩
    exact congrArg Subtype.val this.symm
  rcases hτ r hrR hrc with rfl | rfl
  · exfalso
    rw [map_one] at hr
    have h1 : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      eq_one_of_oddQuotMk_eq_one (Subtype.ext hcw.sq) hr.symm
    exact hcw.ne_one (congrArg Subtype.val h1)
  · exact hr.symm

end ChainCtx

end CFSG.ClassicalInvolution.Asc77
