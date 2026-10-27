module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentURho
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsLabels

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem yBar_conj_quasiBar : d.yBar * quasiBar u * d.yBar⁻¹ = quasiBar u ∨
    d.yBar * quasiBar u * d.yBar⁻¹ = quasiBar u * quasiCentral u := by
  rw [yBar, ← map_inv, ← map_mul, ← map_mul, ← d.quasiMk_centralElt, ← map_mul]
  rcases d.caseC3BCD.conj_self with h | h
  · exact Or.inl (congrArg (quasiMk u) (Subtype.ext h))
  · exact Or.inr (congrArg (quasiMk u) (Subtype.ext h))

theorem yBar_conj_mBar : d.yBar * d.mBar * d.yBar⁻¹ = quasiBar u * d.mBar ∨
    d.yBar * d.mBar * d.yBar⁻¹ = quasiBar u * d.mBar * quasiCentral u := by
  rw [yBar, mBar, ← map_inv, ← map_mul, ← map_mul, ← d.quasiMk_centralElt, ← map_mul, ← map_mul]
  rcases d.caseC3BCD.toCaseC3.conj_moved d.caseC3BCD.m_mem d.caseC3BCD.m_moved
      d.caseC3BCD.m_moved' with h | h
  · exact Or.inl (congrArg (quasiMk u) (Subtype.ext h))
  · exact Or.inr (congrArg (quasiMk u) (Subtype.ext h))

@[expose] noncomputable def lyGroup : Subgroup (QuasiQuotient u) := L ⊔ Subgroup.zpowers d.yBar

theorem le_lyGroup : L ≤ d.lyGroup := le_sup_left

theorem yBar_mem_lyGroup : d.yBar ∈ d.lyGroup := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem mem_lyGroup_iff {g : QuasiQuotient u} : g ∈ d.lyGroup ↔ g ∈ L ∨ g * d.yBar⁻¹ ∈ L := by
  have := d.oneComponent.normal
  constructor
  · intro hg
    obtain ⟨l, hl, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hy2 : d.yBar ^ (2 : ℤ) ∈ L := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, d.yBar_mul_self]
      exact d.quasiCentral_mem
    have hsplit : d.yBar ^ j = (d.yBar ^ (2 : ℤ)) ^ (j / 2) * d.yBar ^ (j % 2) := by
      rw [← zpow_mul, ← zpow_add, Int.mul_ediv_add_emod]
    have hpow : (d.yBar ^ (2 : ℤ)) ^ (j / 2) ∈ L := L.zpow_mem hy2 _
    rcases Int.emod_two_eq_zero_or_one j with h | h
    · left
      rw [hsplit, h, zpow_zero, mul_one]
      exact L.mul_mem hl hpow
    · right
      rw [hsplit, h, zpow_one, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
      exact L.mul_mem hl hpow
  · rintro (h | h)
    · exact d.le_lyGroup h
    · rw [show g = g * d.yBar⁻¹ * d.yBar by group]
      exact Subgroup.mul_mem _ (d.le_lyGroup h) d.yBar_mem_lyGroup

theorem eq_of_mem_centralizer_of_mem_lyGroup {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) (hkH : k ∈ d.lyGroup) :
    k = 1 ∨ k = quasiCentral u := by
  rcases d.mem_lyGroup_iff.mp hkH with h | h
  · exact d.eq_of_mem_of_mem_centralizer h hk
  · exfalso
    apply d.yBar_not_mem
    rw [show d.yBar = (k * d.yBar⁻¹)⁻¹ * k by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem h)) (Subgroup.mem_sup_right hk)

theorem exists_mem_centralizer_inv_mul_mem (g : QuasiQuotient u) :
    ∃ k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)), k⁻¹ * g ∈ d.lyGroup := by
  have := d.oneComponent.centralizer_normal
  rcases d.mem_sup_or_mul_inv_mem_sup g with h | h
  · obtain ⟨l, hl, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp h
    refine ⟨k, hk, ?_⟩
    rw [show k⁻¹ * (l * k) = l by rw [Subgroup.mem_centralizer_iff.mp hk l hl]; group]
    exact d.le_lyGroup hl
  · obtain ⟨l, hl, k, hk, hlk⟩ := Subgroup.mem_sup_of_normal_right.mp h
    refine ⟨k, hk, d.mem_lyGroup_iff.mpr (Or.inr ?_)⟩
    rw [show k⁻¹ * g * d.yBar⁻¹ = k⁻¹ * (g * d.yBar⁻¹) by group, ← hlk,
      show k⁻¹ * (l * k) = l by rw [Subgroup.mem_centralizer_iff.mp hk l hl]; group]
    exact hl

@[expose] noncomputable def kappa : Fin 4 → QuasiQuotient u :=
  ![1, quasiBar u, d.mBar, quasiBar u * d.mBar]

@[expose] noncomputable def kappaX : Fin 4 → quasiNormalizer u :=
  ![1, quasiSelf u, ⟨m, d.m_mem⟩, quasiSelf u * ⟨m, d.m_mem⟩]

@[expose] def kappaWord : Fin 4 → Fin 64 := ![0, 32, 16, 48]

theorem quasiMk_kappaX (i : Fin 4) : quasiMk u (d.kappaX i) = d.kappa i := by
  fin_cases i
  · exact map_one _
  · rfl
  · rfl
  · exact map_mul _ _ _

theorem kappaX_mem (i : Fin 4) : d.kappaX i ∈ (T : Subgroup (quasiNormalizer u)) := by
  have hu := d.quasiSelf_mem_sylow
  have hm := mem_sylow_of_mem_partCSylow (partCRight_le d.caseC3BCD.m_mem)
  fin_cases i
  · exact Subgroup.one_mem _
  · exact hu
  · exact hm
  · exact Subgroup.mul_mem _ hu hm

theorem mk_kappaX (i : Fin 4) : (((d.kappaX i : quasiNormalizer u) : J) : J ⧸ Subgroup.center J) =
    caseC3Word (Subgroup.center J) u m y x (kappaWord i) := by
  fin_cases i
  · exact (CaseC3BCD.caseC3Word_zero (Z := Subgroup.center J) (u := u) (m := m) (y := y)
      (x := x)).symm
  · exact (CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (u := u) (m := m) (y := y)
      (x := x)).symm
  · exact (CaseC3BCD.caseC3Word_sixteen (Z := Subgroup.center J) (u := u) (m := m) (y := y)
      (x := x)).symm
  · change ((u * m : J) : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 48
    rw [show (48 : Fin 64) = c3Mul 32 16 by decide, ← d.caseC3BCD.caseC3Word_mul,
      CaseC3BCD.caseC3Word_thirtytwo, CaseC3BCD.caseC3Word_sixteen, QuotientGroup.mk_mul]

theorem kappa_mem (i : Fin 4) : d.kappa i ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  fin_cases i
  · exact Subgroup.one_mem _
  · exact d.quasiBar_mem_centralizer
  · exact d.mBar_mem_centralizer
  · exact Subgroup.mul_mem _ d.quasiBar_mem_centralizer d.mBar_mem_centralizer

theorem exists_kappa {k : QuasiQuotient u}
    (hk : k ∈ Subgroup.centralizer (L : Set (QuasiQuotient u))) :
    ∃ i, k = d.kappa i ∨ k = d.kappa i * quasiCentral u := by
  rcases d.mem_centralizer_cases hk with h | h | h | h | h | h | h | h
  · exact ⟨0, Or.inl h⟩
  · exact ⟨0, Or.inr (by rw [h]; exact (one_mul _).symm)⟩
  · exact ⟨1, Or.inl h⟩
  · exact ⟨1, Or.inr h⟩
  · exact ⟨2, Or.inl h⟩
  · exact ⟨2, Or.inr h⟩
  · exact ⟨3, Or.inl h⟩
  · exact ⟨3, Or.inr h⟩

theorem eq_of_kappa_inv_mul_mem {i j : Fin 4} (h : (d.kappa i)⁻¹ * d.kappa j ∈ d.lyGroup) :
    i = j := by
  have hK : (d.kappa i)⁻¹ * d.kappa j ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (d.kappa_mem i)) (d.kappa_mem j)
  set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
  obtain ⟨ε, hεT, hεJ, hε⟩ : ∃ ε : quasiNormalizer u, ε ∈ (T : Subgroup (quasiNormalizer u)) ∧
      ((ε : J) : J ⧸ Subgroup.center J) = 1 ∧ quasiMk u ε = (d.kappa i)⁻¹ * d.kappa j := by
    rcases d.eq_of_mem_centralizer_of_mem_lyGroup hK h with h1 | h1
    · exact ⟨1, Subgroup.one_mem _, QuotientGroup.mk_one _, by rw [map_one, h1]⟩
    · exact ⟨e₀, d.centralElt_mem_sylow,
        (QuotientGroup.eq_one_iff _).mpr d.setting.centralElt_mem_center,
        by rw [d.quasiMk_centralElt, h1]⟩
  have hX : d.kappaX j = d.kappaX i * ε := quasiMk_injOn_twoGroup u T.isPGroup' (d.kappaX_mem j)
    (Subgroup.mul_mem _ (d.kappaX_mem i) hεT)
    (by rw [map_mul, hε, d.quasiMk_kappaX, d.quasiMk_kappaX, mul_inv_cancel_left])
  have hw : caseC3Word (Subgroup.center J) u m y x (kappaWord j) =
      caseC3Word (Subgroup.center J) u m y x (kappaWord i) := by
    rw [← d.mk_kappaX, ← d.mk_kappaX, hX, Subgroup.coe_mul, QuotientGroup.mk_mul, hεJ, mul_one]
  have hw' := d.caseC3BCD.caseC3Word_inj.mp hw
  revert hw'
  fin_cases i <;> fin_cases j <;> decide

@[expose] noncomputable def cosetEquiv : Fin 4 ≃ QuasiQuotient u ⧸ d.lyGroup :=
  Equiv.ofBijective (fun i => (d.kappa i : QuasiQuotient u ⧸ d.lyGroup)) ⟨fun i j h =>
    d.eq_of_kappa_inv_mul_mem (QuotientGroup.eq.mp h), fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, hkg⟩ := d.exists_mem_centralizer_inv_mul_mem g
    obtain ⟨i, hi⟩ := d.exists_kappa hk
    refine ⟨i, QuotientGroup.eq.mpr ?_⟩
    rw [show (d.kappa i)⁻¹ * g = ((d.kappa i)⁻¹ * k) * (k⁻¹ * g) by group]
    refine Subgroup.mul_mem _ (d.le_lyGroup ?_) hkg
    rcases hi with rfl | rfl
    · rw [inv_mul_cancel]
      exact L.one_mem
    · rw [inv_mul_cancel_left]
      exact d.quasiCentral_mem⟩

theorem cosetEquiv_apply (i : Fin 4) :
    d.cosetEquiv i = (d.kappa i : QuasiQuotient u ⧸ d.lyGroup) := rfl

@[expose] noncomputable def rho4 : QuasiQuotient u →* Perm (Fin 4) :=
  d.cosetEquiv.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (QuasiQuotient u) (QuasiQuotient u ⧸ d.lyGroup))

theorem rho4_apply_eq_iff (g : QuasiQuotient u) (i j : Fin 4) :
    d.rho4 g i = j ↔ (d.kappa j)⁻¹ * (g * d.kappa i) ∈ d.lyGroup := by
  change d.cosetEquiv.symm (g • d.cosetEquiv i) = j ↔ _
  rw [Equiv.symm_apply_eq, cosetEquiv_apply, cosetEquiv_apply, MulAction.Quotient.smul_mk,
    QuotientGroup.eq, ← Subgroup.inv_mem_iff]
  simp

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
