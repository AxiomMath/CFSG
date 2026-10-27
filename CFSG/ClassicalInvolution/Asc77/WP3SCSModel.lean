module

public import CFSG.ClassicalInvolution.Asc77.WP3SCSShape
public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open CFSG.ClassicalInvolution.RouteD.TwinY
open scoped commutatorElement

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem XCtx.fund_perfect (C : XCtx p f Ω z) (j : Fin C.D.card) (hj : C.D.tag j ≠ .trialityD4)
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) : ⁅R, R⁆ = R :=
  commutator_self_eq_of_le (ModelFacts.fundPerfect_core (C.D.tag j) (C.D.rank j) p (C.D.exp j)
    C.hp (C.D.isFundTag j) (C.D.admissible j) (C.four_le j hj) R hR)

theorem XCtx.classical_of_range (C : XCtx p f Ω z) {N : Subgroup G} (hN : N ∈ tqMembers Ω z)
    {w : G} (hw : IsClassicalMember p f N w) {j : Fin C.D.card}
    (hmod : modOdd z (exactCore z N) = (C.psi j).range)
    (hz : oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi j).range) : w = z := by
  have hzC := XCtx.hzC z
  have hU := C.isUniqueInvolution_modOdd hN hw
  rw [hmod] at hU
  have hzsq : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨z, hzC⟩ = 1 :=
      Subtype.ext C.hKz.sq
    rw [this, map_one]
  have hz1 : oddQuotMk z ⟨z, hzC⟩ ≠ 1 := fun h =>
    C.hKz.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h))
  have heq : oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩ = oddQuotMk z ⟨z, hzC⟩ :=
    ((hU.unique _ hz hzsq).resolve_left hz1).symm
  have hwY : w ∈ exactLayer Ω z :=
    exactCore_le_exactLayer hN (C.involution_mem_exactCore hN hw)
  obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY C.z_mem_exactLayer
    (isCentralInvolution_of_isClassicalMember hw).sq C.hKz.sq heq
  rw [hwo]
  exact conj_eq_of_mem_centralizer_singleton
    (exactLayer_le_centralizer Ω z (oddCoreIn_le _ ho))

theorem XCtx.exists_central_lift (C : XCtx p f Ω z) {N : Subgroup G} {w : G}
    (hN : N ∈ tqMembers Ω z) (hw : IsClassicalMember p f N w) (j : Fin C.D.card)
    (hj : C.D.tag j ≠ .trialityD4) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hmod : modOdd z (exactCore z N) = R.map (C.psi j)) :
    ∃ r ∈ R, (∀ s ∈ R, r * s = s * r) ∧ r ≠ 1 ∧
      oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩ = C.psi j r := by
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
  refine ⟨r, hrR, hrc, fun hr1 => ?_, hr.symm⟩
  rw [hr1, map_one] at hr
  have h1 : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
    eq_one_of_oddQuotMk_eq_one (Subtype.ext hcw.sq) hr.symm
  exact hcw.ne_one (congrArg Subtype.val h1)

end Basic

section Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

structure TwinVertex (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (z : G) where
  M : Subgroup G
  M' : Subgroup G
  a : G
  x : G
  y : G
  hM : M ∈ tqMembers Ω z
  hM' : M' ∈ tqMembers Ω z
  hMM' : M ≠ M'
  hMa : IsClassicalMember p f M a
  hM'a : IsClassicalMember p f M' a
  haz : a ≠ z
  hx : x ∈ exactCore z M
  hy : y ∈ exactCore z M'
  hxx : x * x = a
  hyy : y * y = a
  hxy : x * y = y * x

namespace TwinVertex

variable (V : TwinVertex p f Ω z)

theorem x_mem : V.x ∈ Subgroup.centralizer ({z} : Set G) := exactCore_le_centralizer z V.M V.hx

theorem y_mem : V.y ∈ Subgroup.centralizer ({z} : Set G) := exactCore_le_centralizer z V.M' V.hy

theorem a_mem : V.a ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [← V.hxx]
  exact mul_mem V.x_mem V.x_mem

theorem u_mem : V.x * V.y ∈ Subgroup.centralizer ({z} : Set G) := mul_mem V.x_mem V.y_mem

end TwinVertex

end Datum

section ModelDatum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem XCtx.commute_of_twin_cores (C : XCtx p f Ω z) {M M' : Subgroup G} {a : G}
    (hM : M ∈ tqMembers Ω z) (hM' : M' ∈ tqMembers Ω z) (hne : M ≠ M')
    (hMa : IsClassicalMember p f M a) (hM'a : IsClassicalMember p f M' a)
    (hquasi : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z M))) {e : G}
    (he : e ∈ exactCore z M') (heC : e ∈ Subgroup.centralizer ({z} : Set G)) :
    ∀ y ∈ modOdd z (exactCore z M), oddQuotMk z ⟨e, heC⟩ * y = y * oddQuotMk z ⟨e, heC⟩ := by
  have hUa := ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hMa
  have hUa' := ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hM'a
  have hnorm : M' ≤ Subgroup.normalizer (M : Set G) :=
    C.hΩ.le_normalizer_of_twin hM'.1 hM.1 hne.symm hUa' hUa
  have hc := C.hΩ.comm_le_oddCore_of_twin hM'.1 hM.1 hne.symm hUa' hUa
  have heM' : e ∈ M' := exactCore_le_left z M' he
  have htq : e ∈ trivialOnQuot M :=
    ⟨hnorm heM', fun x hx => (hc (Subgroup.commutator_mem_commutator heM' hx)).2⟩
  exact oddQuotMk_centralizes_modOdd_exactCore hMa C.hc2 hM.2 htq heC hquasi

theorem XCtx.exists_big_fund (C : XCtx p f Ω z) (a₁ : Fin C.D.card)
    (hothers : ∀ j, j ≠ a₁ → (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    (hzA1 : ∀ j, (C.D.tag j = .PSL ∧ C.D.rank j = 2) →
      oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi j).range)
    {N : Subgroup G} (hN : N ∈ tqMembers Ω z) {w : G} (hw : IsClassicalMember p f N w)
    (hwz : w ≠ z) :
    ∃ R ∈ fundamentalSubgroups (C.D.tag a₁) (compModel C.D a₁).D,
      modOdd z (exactCore z N) = R.map (C.psi a₁) := by
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hN
  by_cases hj : j = a₁
  · subst hj
    exact ⟨R, hR, hmod.symm⟩
  · exfalso
    have hA := hothers j hj
    have hRtop : R = ⊤ := C.fund_eq_top j hA hR
    have hmod' : modOdd z (exactCore z N) = (C.psi j).range := by
      rw [← hmod, hRtop, Subgroup.map_top]
    exact hwz (C.classical_of_range hN hw hmod' (hzA1 j hA))

theorem XCtx.exists_modelDatum (C : XCtx p f Ω z) (a₁ : Fin C.D.card)
    (hD4 : C.D.tag a₁ ≠ .trialityD4)
    (hothers : ∀ j, j ≠ a₁ → (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    (hzA1 : ∀ j, (C.D.tag j = .PSL ∧ C.D.rank j = 2) →
      oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi j).range)
    (V : TwinVertex p f Ω z) :
    ∃ (R R' : Subgroup (compModel C.D a₁).K) (x x' ã ã' : (compModel C.D a₁).K),
      TwinDatum p (C.D.exp a₁) (C.D.tag a₁) (C.D.rank a₁) R R' x x' ∧ ã ∈ R ∧ ã' ∈ R' ∧
      ã * ã * x⁻¹ ∈ Subgroup.center (compModel C.D a₁).K ∧
      ã' * ã' * x'⁻¹ ∈ Subgroup.center (compModel C.D a₁).K ∧
      C.psi a₁ x = oddQuotMk z ⟨V.a, V.a_mem⟩ ∧ C.psi a₁ x' = oddQuotMk z ⟨V.a, V.a_mem⟩ ∧
      C.psi a₁ (ã * ã') = oddQuotMk z ⟨V.x * V.y, V.u_mem⟩ := by
  classical
  obtain ⟨R, hR, hmodM⟩ := C.exists_big_fund a₁ hothers hzA1 V.hM V.hMa V.haz
  obtain ⟨R', hR', hmodM'⟩ := C.exists_big_fund a₁ hothers hzA1 V.hM' V.hM'a V.haz
  have hRp := C.fund_perfect a₁ hD4 hR
  have hR'p := C.fund_perfect a₁ hD4 hR'
  have hquasi : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z V.M)) := by
    rw [hmodM]
    exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker a₁)
      (fundQuasisimple_core C.hp (C.D.isFundTag a₁) (C.D.admissible a₁) (C.four_le a₁ hD4) R hR)
  have himg : ∀ r ∈ R, ∀ r' ∈ R', C.psi a₁ r' * C.psi a₁ r = C.psi a₁ r * C.psi a₁ r' := by
    intro r hr r' hr'
    have h1 : C.psi a₁ r ∈ modOdd z (exactCore z V.M) := hmodM ▸ Subgroup.mem_map_of_mem _ hr
    have h2 : C.psi a₁ r' ∈ modOdd z (exactCore z V.M') :=
      hmodM' ▸ Subgroup.mem_map_of_mem _ hr'
    obtain ⟨e, he, hee⟩ := (mem_modOdd_iff).mp h2
    rw [← hee]
    exact C.commute_of_twin_cores V.hM V.hM' V.hMM' V.hMa V.hM'a hquasi he e.2 _ h1
  have hcomm : Commutes R R' := by
    intro r hr r' hr'
    refine RouteD.Gaps.commute_of_commutator_central hRp (b := r') (fun a ha => ?_) r hr
    refine C.psi_ker a₁ (MonoidHom.mem_ker.mpr ?_)
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (himg a ha r' hr').symm
  obtain ⟨x, hxR, hxc, hx1, hxψ⟩ := C.exists_central_lift V.hM V.hMa a₁ hD4 hR hmodM
  obtain ⟨x', hx'R, hx'c, hx'1, hx'ψ⟩ := C.exists_central_lift V.hM' V.hM'a a₁ hD4 hR' hmodM'
  have hne : R ≠ R' := by
    intro h
    subst h
    have hbot : ⁅R, R⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm a ha b hb
    have hx_top : x ∈ ⁅R, R⁆ := by rw [hRp]; exact hxR
    rw [hbot, Subgroup.mem_bot] at hx_top
    exact hx1 hx_top
  have hxmem : oddQuotMk z ⟨V.x, V.x_mem⟩ ∈ R.map (C.psi a₁) :=
    hmodM ▸ oddQuotMk_mem_modOdd V.hx V.x_mem
  have hymem : oddQuotMk z ⟨V.y, V.y_mem⟩ ∈ R'.map (C.psi a₁) :=
    hmodM' ▸ oddQuotMk_mem_modOdd V.hy V.y_mem
  obtain ⟨ã, hãR, hã⟩ := hxmem
  obtain ⟨ã', hã'R, hã'⟩ := hymem
  have hsqx : (⟨V.x, V.x_mem⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨V.x, V.x_mem⟩ =
      ⟨V.a, V.a_mem⟩ := Subtype.ext V.hxx
  have hsqy : (⟨V.y, V.y_mem⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨V.y, V.y_mem⟩ =
      ⟨V.a, V.a_mem⟩ := Subtype.ext V.hyy
  have hcen1 : ã * ã * x⁻¹ ∈ Subgroup.center (compModel C.D a₁).K := by
    refine C.psi_ker a₁ (MonoidHom.mem_ker.mpr ?_)
    rw [map_mul, map_mul, map_inv, hã, ← hxψ, ← map_mul, hsqx, mul_inv_cancel]
  have hcen2 : ã' * ã' * x'⁻¹ ∈ Subgroup.center (compModel C.D a₁).K := by
    refine C.psi_ker a₁ (MonoidHom.mem_ker.mpr ?_)
    rw [map_mul, map_mul, map_inv, hã', ← hx'ψ, ← map_mul, hsqy, mul_inv_cancel]
  have hsame : x * x'⁻¹ ∈ Subgroup.center (compModel C.D a₁).K := by
    refine C.psi_ker a₁ (MonoidHom.mem_ker.mpr ?_)
    rw [map_mul, map_inv, ← hxψ, ← hx'ψ, mul_inv_cancel]
  refine ⟨R, R', x, x', ã, ã', ?_, hãR, hã'R, hcen1, hcen2, hxψ.symm, hx'ψ.symm, ?_⟩
  · exact
      { mem := hR
        mem' := hR'
        ne := hne
        comm := hcomm
        hx := hxR
        hx' := hx'R
        cx := hxc
        cx' := hx'c
        nx := hx1
        nx' := hx'1
        same := hsame }
  · rw [map_mul, hã, hã', ← map_mul]
    rfl

end ModelDatum

end CFSG.ClassicalInvolution.Asc77
