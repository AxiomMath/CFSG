module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha
public import CFSG.ClassicalInvolution.Asc77.WP3Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

structure VertexCtx (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (c : G) where
  hΩ : HypOmegaMod p f Ω
  hp : p ≠ 2
  hq : 5 ≤ p ^ f
  hc2 : IsPGroup 2 (Subgroup.zpowers c)
  hne : (tqMembers Ω c).Nonempty
  D : LocalLieSystemAt p f (exactFamily Ω c) c

namespace VertexCtx

variable (C : VertexCtx p f Ω c)

include C

theorem hs : SecData p f c (exactFamily Ω c) :=
  secData_exactFamily C.hΩ.conjInvariant C.hΩ.classical C.hc2 C.hne

noncomputable abbrev psi (j : Fin C.D.card) : (compModel C.D j).K →* OddQuot c :=
  secComponentHom C.hs.normalizes C.D j

theorem psi_ker (j : Fin C.D.card) : (C.psi j).ker ≤ Subgroup.center (compModel C.D j).K :=
  secComponentHom_ker_le_center C.hs.normalizes C.D j

theorem exists_fund_of_mem {N : Subgroup G} (hN : N ∈ tqMembers Ω c) :
    ∃ j : Fin C.D.card, ∃ R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D,
      R.map (C.psi j) = modOdd c (exactCore c N) := by
  have hM : exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  have hMY : exactCore c N ≤ centralizingLayer (exactFamily Ω c) {c} := le_centralizingLayer hM
  have hMfam : modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c N) ∈
      localFamily (exactFamily Ω c) c := ⟨(exactCore c N).subgroupOf _, ⟨_, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := C.D.fundamental _ hMfam
  refine ⟨i, R, hR, ?_⟩
  have h1 : (R.map (C.D.hom i)).map (sectionQuotientHom C.hs.normalizes) =
      R.map (C.psi i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn C.hs.normalizes hM

theorem involution_mem_exactCore {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω c)
    (hw : IsClassicalMember p f N w) : w ∈ exactCore c N :=
  mem_exactCore hw C.hc2 hN.2

theorem involution_mem_centralizer {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω c)
    (hw : IsClassicalMember p f N w) : w ∈ Subgroup.centralizer ({c} : Set G) :=
  exactCore_le_centralizer c N (C.involution_mem_exactCore hN hw)

theorem isUniqueInvolution_modOdd {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω c)
    (hw : IsClassicalMember p f N w) :
    IsUniqueInvolution (modOdd c (exactCore c N))
      (oddQuotMk c ⟨w, C.involution_mem_centralizer hN hw⟩) := by
  have hwE := C.involution_mem_exactCore hN hw
  have hwC := C.involution_mem_centralizer hN hw
  have hcw := isCentralInvolution_of_isClassicalMember hw
  set Cz : Subgroup G := Subgroup.centralizer ({c} : Set G) with hCz
  set E' : Subgroup ↥Cz := (exactCore c N).subgroupOf Cz with hE'
  have hU : IsUniqueInvolution E' ⟨w, hwC⟩ := by
    refine ⟨hwE, fun h => hcw.ne_one (congrArg Subtype.val h), Subtype.ext hcw.sq, ?_⟩
    intro y hy hy2
    rcases eq_one_or_eq_of_mem_exactCore hw C.hp C.hq hy (congrArg Subtype.val hy2) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hodd : Odd (Nat.card ↥(componentClassificationOddCore ↥Cz ⊓ E')) :=
    (OddCore.odd_card ↥Cz).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact isUniqueInvolution_map_mk_of_odd hodd hU

theorem psi_mem_memberJoin (j : Fin C.D.card) (k : (compModel C.D j).K) :
    C.psi j k ∈ memberJoin (exactFamily Ω c) c := by
  rw [← range_sectionQuotientHom C.hs.normalizes]
  exact ⟨C.D.hom j k, rfl⟩

theorem psi_commute {i j : Fin C.D.card} (hij : i ≠ j) (x : (compModel C.D i).K)
    (y : (compModel C.D j).K) : C.psi i x * C.psi j y = C.psi j y * C.psi i x := by
  have h1 := map_mul (sectionQuotientHom C.hs.normalizes) (C.D.hom i x) (C.D.hom j y)
  have h2 := map_mul (sectionQuotientHom C.hs.normalizes) (C.D.hom j y) (C.D.hom i x)
  have h3 := congrArg (sectionQuotientHom C.hs.normalizes) (C.D.commute i j hij x y)
  exact h1.symm.trans (h3.trans h2)

theorem conj_psi_range (j : Fin C.D.card) {y : OddQuot c}
    (hy : y ∈ memberJoin (exactFamily Ω c) c) :
    ∀ n ∈ (C.psi j).range, y * n * y⁻¹ ∈ (C.psi j).range := by
  rw [← range_sectionQuotientHom C.hs.normalizes] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : x ∈ ⨆ i, (C.D.hom i).range := by
    rw [C.D.generate]
    exact Subgroup.mem_top x
  induction hx using Subgroup.iSup_induction' with
  | hp k y hy =>
    intro n hn
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hn
    have h2 : sectionQuotientHom C.hs.normalizes (C.D.hom k a) = C.psi k a := rfl
    rw [h2]
    by_cases hkj : k = j
    · subst hkj
      refine ⟨a * b * a⁻¹, ?_⟩
      simp
    · rw [C.psi_commute hkj a b, mul_assoc, mul_inv_cancel, mul_one]
      exact ⟨b, rfl⟩
  | h1 =>
    intro n hn
    rw [map_one, one_mul, inv_one, mul_one]
    exact hn
  | hmul a b _ _ ha hb =>
    intro n hn
    rw [map_mul]
    have e : ∀ u v : OddQuot c, u * v * n * (u * v)⁻¹ = u * (v * n * v⁻¹) * u⁻¹ :=
      fun u v => by group
    rw [e]
    exact ha _ (hb n hn)

theorem isComponentOf_range (j : Fin C.D.card) : IsComponentOf (C.psi j).range ⊤ := by
  have hJ : (memberJoin (exactFamily Ω c) c).Normal :=
    memberJoin_normal_of_normalizes C.hs.normalizes
  have hle : (C.psi j).range ≤ memberJoin (exactFamily Ω c) c := by
    rintro _ ⟨k, rfl⟩
    exact C.psi_mem_memberJoin j k
  refine ⟨le_top, ?_, ?_⟩
  · refine IsSubnormal.step hle ?_ ?_
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using C.conj_psi_range j g.2 _ hn
    · exact isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  · have hK : CFSG.Open.IsQuasisimple
        (modelUniv (C.D.tag j) (C.D.rank j) p (C.D.exp j) Fact.out).K :=
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (C.D.isFundTag j)
        (C.D.admissible j)).1
    have hq : CFSG.Open.IsQuasisimple ↥((⊤ : Subgroup (compModel C.D j).K).map (C.psi j)) :=
      isQuasisimple_map_of_ker_le_center _ (C.psi_ker j)
        (Components.quasisimple_of_equiv Subgroup.topEquiv hK)
    rwa [Subgroup.map_top] at hq

theorem isComponent_range (j : Fin C.D.card) : CFSG.IsComponent (C.psi j).range :=
  (CFSG.isComponent_iff_open _).mpr (C.isComponentOf_range j)

theorem exp_eq (j : Fin C.D.card) (hj : C.D.tag j ≠ .trialityD4) : C.D.exp j = f := by
  rcases C.D.exp_eq j with h | ⟨h, -⟩
  · exact h
  · exact absurd h hj

theorem four_le (j : Fin C.D.card) (hj : C.D.tag j ≠ .trialityD4) : 4 ≤ p ^ C.D.exp j := by
  rw [C.exp_eq j hj]
  have := C.hq
  omega

theorem fund_perfect (j : Fin C.D.card) (hj : C.D.tag j ≠ .trialityD4)
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) : ⁅R, R⁆ = R :=
  commutator_self_eq_of_le (ModelFacts.fundPerfect_core (C.D.tag j) (C.D.rank j) p (C.D.exp j)
    C.hp (C.D.isFundTag j) (C.D.admissible j) (C.four_le j hj) R hR)

theorem exists_central_lift {N : Subgroup G} {w : G}
    (hN : N ∈ tqMembers Ω c) (hw : IsClassicalMember p f N w) (j : Fin C.D.card)
    (hj : C.D.tag j ≠ .trialityD4) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hmod : modOdd c (exactCore c N) = R.map (C.psi j)) :
    ∃ r ∈ R, (∀ s ∈ R, r * s = s * r) ∧ r ≠ 1 ∧
      oddQuotMk c ⟨w, C.involution_mem_centralizer hN hw⟩ = C.psi j r := by
  have hwE := C.involution_mem_exactCore hN hw
  have hwC := C.involution_mem_centralizer hN hw
  have hmem : oddQuotMk c ⟨w, hwC⟩ ∈ R.map (C.psi j) := hmod ▸ oddQuotMk_mem_modOdd hwE hwC
  obtain ⟨r, hrR, hr⟩ := hmem
  have hcw := isCentralInvolution_of_isClassicalMember hw
  have hcent : ∀ s ∈ R, C.psi j r * C.psi j s = C.psi j s * C.psi j r := by
    intro s hs
    have hsm : C.psi j s ∈ modOdd c (exactCore c N) := hmod ▸ ⟨s, hs, rfl⟩
    obtain ⟨k, hk, hks⟩ := hsm
    rw [hr, ← hks, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk c) (Subtype.ext (hcw.central _ (exactCore_le_left c N hk)))
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
  refine ⟨r, hrR, hrc, fun hr1 => ?_, hr.symm⟩
  rw [hr1, map_one] at hr
  have h1 : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
    eq_one_of_oddQuotMk_eq_one (Subtype.ext hcw.sq) hr.symm
  exact hcw.ne_one (congrArg Subtype.val h1)

end VertexCtx

end Ctx

end CFSG.ClassicalInvolution.Asc77
