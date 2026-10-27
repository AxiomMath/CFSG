module

public import CFSG.ClassicalInvolution.Asc77.AscBSCMain

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (ModelFund)

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

theorem pos_exp_of_five_le {p f : ℕ} (hq : 5 ≤ p ^ f) : 0 < f := by
  refine Nat.pos_of_ne_zero ?_
  rintro rfl
  simp at hq

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


section Conj

variable (C : XCtx p f (𝒞 K) z)

theorem exists_conj_of_compMem {j : Fin C.D.card} (m : CompMem C j) :
    ∃ g : G, conjSub g C.K = m.N ∧ m.n = g * z * g⁻¹ := by
  obtain ⟨g₁, hg₁⟩ := m.hN.1
  obtain ⟨g₂, hg₂⟩ := C.hK
  have hg₁' : conjSub g₁ K = m.N := hg₁
  have hg₂' : conjSub g₂ K = C.K := hg₂
  have hN : conjSub (g₁ * g₂⁻¹) C.K = m.N := by
    rw [conjSub_mul, ← hg₂', conjSub_inv_conjSub, hg₁']
  refine ⟨g₁ * g₂⁻¹, hN, ?_⟩
  have h1 : IsClassicalMember p f m.N (g₁ * g₂⁻¹ * z * (g₁ * g₂⁻¹)⁻¹) := by
    rw [← hN]
    exact C.K_cl.conj (g₁ * g₂⁻¹)
  exact (m.hn.eq_of_isCentralInvolution C.hp (pos_exp_of_five_le C.hq)
    (isCentralInvolution_of_isClassicalMember h1)).symm

variable {C}

@[expose] noncomputable def nb {j : Fin C.D.card} (m : CompMem C j) : OddQuot z :=
  oddQuotMk z ⟨m.n, C.involution_mem_centralizer m.hN m.hn⟩

theorem nb_mem {j : Fin C.D.card} (m : CompMem C j) : nb m ∈ m.R.map (C.psi j) := by
  have h := oddQuotMk_mem_modOdd (C.involution_mem_exactCore m.hN m.hn)
    (C.involution_mem_centralizer m.hN m.hn)
  rw [m.himg] at h
  exact h

theorem nb_ne_zbar {j : Fin C.D.card} (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    (m : CompMem C j) : nb m ≠ zbar z := fun h =>
  zbar_not_mem C j hj m.hR (h ▸ nb_mem m)

theorem involution_ne {j : Fin C.D.card} (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    (m : CompMem C j) : m.n ≠ z := by
  intro h
  refine nb_ne_zbar hj m ?_
  have : (⟨m.n, C.involution_mem_centralizer m.hN m.hn⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨z, XCtx.hzC z⟩ := Subtype.ext h
  exact congrArg (oddQuotMk z) this

theorem compMem_ne_K {j : Fin C.D.card} (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    (m : CompMem C j) : m.N ≠ C.K := by
  intro h
  have hn := m.hn
  rw [h] at hn
  exact involution_ne hj m
    (hn.eq_of_isCentralInvolution C.hp (pos_exp_of_five_le C.hq)
      (isCentralInvolution_of_isClassicalMember C.K_cl)).symm

theorem nb_comm_of_range {b j : Fin C.D.card} (hjb : j ≠ b) (mb : CompMem C b) {y : OddQuot z}
    (hy : y ∈ (C.psi j).range) : nb mb * y = y * nb mb := by
  obtain ⟨r, -, hr⟩ := nb_mem mb
  obtain ⟨a, rfl⟩ := hy
  rw [← hr]
  exact C.psi_commute (Ne.symm hjb) r a

theorem isInvIn_of_psi_eq {j : Fin C.D.card} (hj : ¬ (C.D.tag j = .PSL ∧ C.D.rank j = 2))
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    {r : (compModel C.D j).K} (hrR : r ∈ R) {w : G}
    (hwC : w ∈ Subgroup.centralizer ({z} : Set G)) (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hr : C.psi j r = oddQuotMk z ⟨w, hwC⟩) : IsInvIn R r := by
  have hsq : r * r ∈ Subgroup.center (compModel C.D j).K := by
    refine C.psi_ker j ?_
    rw [MonoidHom.mem_ker, map_mul, hr, ← map_mul]
    have : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨w, hwC⟩ = 1 := Subtype.ext hw2
    rw [this, map_one]
  refine ⟨hrR, ?_, ?_⟩
  · exact eq_one_of_mem_center (C.D.isFundTag j) (C.D.admissible j) hj hR (R.mul_mem hrR hrR) hsq
  · rintro rfl
    rw [map_one] at hr
    exact hw1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hw2) hr.symm))

theorem exists_fund_conj_twin (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    {b : Fin C.D.card} (hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2)) (mb : CompMem C b) {g : G}
    (hg : mb.n = g * z * g⁻¹) {T : Subgroup G} (hT : T ∈ 𝒞 K) (hTz : IsClassicalMember p f T z)
    (hcomm : ∀ y ∈ modOdd z T, nb mb * y = y * nb mb) :
    conjSub g⁻¹ T ∈ tqMembers (𝒞 K) z ∧ IsClassicalMember p f (conjSub g⁻¹ T) (g⁻¹ * z * g) ∧
      ∃ R ∈ fundamentalSubgroups (C.D.tag b) (compModel C.D b).D,
        modOdd z (exactCore z (conjSub g⁻¹ T)) = R.map (C.psi b) ∧
        ∃ r ∈ R, ∃ hm : g⁻¹ * z * g ∈ Subgroup.centralizer ({z} : Set G),
          C.psi b r = oddQuotMk z ⟨g⁻¹ * z * g, hm⟩ := by
  have hnC := C.involution_mem_centralizer mb.hN mb.hn
  have htq : mb.n ∈ trivialOnQuot T :=
    mem_trivialOnQuot_of_centralizes_modOdd hTz (isCanonical_of_isClassicalMember hTz) hnC hcomm
  have hT'Ω : conjSub g⁻¹ T ∈ 𝒞 K := C.hΩ.conjInvariant g⁻¹ T hT
  have htq' : z ∈ trivialOnQuot (conjSub g⁻¹ T) := by
    have h1 := Theorem5.mem_trivialOnQuot_conj_of_mem htq g⁻¹
    have e : g⁻¹ * mb.n * g⁻¹⁻¹ = z := by rw [hg]; group
    rwa [e] at h1
  have hT'tq : conjSub g⁻¹ T ∈ tqMembers (𝒞 K) z := ⟨hT'Ω, htq'⟩
  have hT'cl : IsClassicalMember p f (conjSub g⁻¹ T) (g⁻¹ * z * g) := by
    have h := hTz.conj g⁻¹
    rwa [inv_inv] at h
  refine ⟨hT'tq, hT'cl, ?_⟩
  obtain ⟨j, R, hR, himg⟩ := C.exists_fund_of_mem hT'tq
  have hmC := C.involution_mem_centralizer hT'tq hT'cl
  have hmE := C.involution_mem_exactCore hT'tq hT'cl
  have hjb : j = b := by
    by_contra hjb
    obtain ⟨hj, hall⟩ := nbar_eq_of_A1 C hno hb hjb
    let m' : CompMem C j := ⟨conjSub g⁻¹ T, g⁻¹ * z * g, R, hT'tq, hT'cl, hR, himg.symm⟩
    obtain ⟨hcl, -⟩ := classical_of_nbar_eq C hj m' (hall m')
    have hzz : g⁻¹ * z * g = z :=
      hcl.eq_of_isCentralInvolution C.hp (pos_exp_of_five_le C.hq)
        (isCentralInvolution_of_isClassicalMember hT'cl)
    refine involution_ne hb mb ?_
    have e : z * g = g * z := by
      calc z * g = (g * (g⁻¹ * z * g)) := by group
        _ = g * z := by rw [hzz]
    rw [hg, ← e]
    group
  subst hjb
  refine ⟨R, hR, himg.symm, ?_⟩
  have hmem := oddQuotMk_mem_modOdd hmE hmC
  rw [← himg] at hmem
  obtain ⟨r, hrR, hr⟩ := hmem
  exact ⟨r, hrR, hmC, hr⟩

theorem eq_of_fund_eq {T₁ T₂ : Subgroup G} {m : G} (hz : z * z = 1)
    (h₁ : T₁ ∈ tqMembers (𝒞 K) z) (h₂ : T₂ ∈ tqMembers (𝒞 K) z)
    (c₁ : IsClassicalMember p f T₁ m) (c₂ : IsClassicalMember p f T₂ m)
    (himg : modOdd z (exactCore z T₁) = modOdd z (exactCore z T₂)) : T₁ = T₂ :=
  NDB.Cover.eq_of_modOdd_exactCore_eq c₁ c₂ (isPGroup_zpowers_of_sq_eq_one hz) h₁.2 h₂.2 himg

end Conj

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
