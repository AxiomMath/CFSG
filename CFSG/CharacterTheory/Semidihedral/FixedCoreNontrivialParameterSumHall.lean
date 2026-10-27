module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumClauses

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

namespace CaseIData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {q : ℕ}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
  (h : CaseIData G t s₀ d d₁ J q F' φ)
include h

theorem psl2_orderOf_ne (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F') {m : ℕ}
    (hm : 3 ≤ m) (hx : orderOf x = m * Nat.card (torusU G t s₀ d)) : False := by
  classical
  obtain ⟨p', f', hp', -, hf', hq'⟩ := h.isOddPrimePower_card_F'
  have : Fact p'.Prime := ⟨hp'⟩
  have hU5 := h.five_le_card_U
  have h2U := h.two_mul_card_U_int
  have h11 := h.eleven_le_card_F'
  have hodd := h.card_F'_odd
  have hcases : 2 * Nat.card (torusU G t s₀ d) = Nat.card F' + 1 ∨
      2 * Nat.card (torusU G t s₀ d) + 1 = Nat.card F' := by
    by_cases h4 : Nat.card F' % 4 = 1
    · left
      have : 2 * (Nat.card (torusU G t s₀ d) : ℤ) = Nat.card F' + 1 := by simpa [h4] using h2U
      exact_mod_cast this
    · right
      have : 2 * (Nat.card (torusU G t s₀ d) : ℤ) = Nat.card F' + -1 := by simpa [h4] using h2U
      have : 2 * (Nat.card (torusU G t s₀ d) : ℤ) + 1 = Nat.card F' := by linarith
      exact_mod_cast this
  have hx1 : x ≠ 1 := by
    intro hx1
    rw [hx1, orderOf_one] at hx
    have : 3 * 5 ≤ m * Nat.card (torusU G t s₀ d) := Nat.mul_le_mul hm hU5
    omega
  obtain ⟨U₀, S₀, -, hU₀, -, hS₀, hpart⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_5_a_psl2_cover hq'
      (default : Sylow p' (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F'))
  have hgcd : Nat.gcd (Nat.card F' - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  rw [hgcd] at hU₀ hS₀
  have hmU : 3 * Nat.card (torusU G t s₀ d) ≤ m * Nat.card (torusU G t s₀ d) :=
    Nat.mul_le_mul_right _ hm
  obtain ⟨T, ⟨hxT, hfam⟩, -⟩ := hpart x hx1
  rcases hfam with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  ·
    obtain ⟨y, hy, rfl⟩ := hxT
    have hyord : orderOf ((MulAut.conj g).toMonoidHom y) = orderOf y := MulEquiv.orderOf_eq _ y
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp
      (default : Sylow p' (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F')).isPGroup') ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hj
    rw [hyord, hj] at hx
    have hUdvd : Nat.card (torusU G t s₀ d) ∣ p' ^ j := ⟨m, by rw [hx]; ring⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp').mp hUdvd
    have hi1 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hi
      omega
    have hpU : p' ∣ Nat.card (torusU G t s₀ d) := by
      rw [hi]
      exact dvd_pow_self p' hi1
    have hpq : p' ∣ Nat.card F' := by
      rw [hq']
      exact dvd_pow_self p' (by omega)
    rcases hcases with hc | hc
    · have h1 : p' ∣ Nat.card F' + 1 := hc ▸ dvd_mul_of_dvd_right hpU 2
      exact hp'.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp h1))
    · have h1 : p' ∣ 2 * Nat.card (torusU G t s₀ d) + 1 := hc ▸ hpq
      exact hp'.one_lt.ne'
        (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpU 2)).mp h1))
  ·
    obtain ⟨y, hy, rfl⟩ := hxT
    have hyord : orderOf ((MulAut.conj g).toMonoidHom y) = orderOf y := MulEquiv.orderOf_eq _ y
    have hdvd : orderOf y ∣ Nat.card U₀ := Subgroup.orderOf_dvd_natCard U₀ hy
    rw [← hyord, hx, hU₀] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    have : (Nat.card F' - 1) / 2 ≤ (Nat.card F' + 1) / 2 := by omega
    rcases hcases with hc | hc <;> omega
  ·
    obtain ⟨y, hy, rfl⟩ := hxT
    have hyord : orderOf ((MulAut.conj g).toMonoidHom y) = orderOf y := MulEquiv.orderOf_eq _ y
    have hdvd : orderOf y ∣ Nat.card S₀ := Subgroup.orderOf_dvd_natCard S₀ hy
    rw [← hyord, hx, hS₀] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    rcases hcases with hc | hc <;> omega

theorem coprime_relIndex_inf_torusH_of_coprime
    (hcop : Nat.Coprime (Nat.card (torusU G t s₀ d)) (Nat.card (torusW G t s₀)))
    (R : Subgroup G) (hRU : R ≤ Subgroup.centralizer (torusU G t s₀ d : Set G))
    (hR : Odd (Nat.card R)) (hWR : torusW G t s₀ ≤ R) :
    Nat.Coprime (Nat.card (torusW G t s₀)) ((torusW G t s₀).relIndex (R ⊓ torusH G t s₀)) := by
  classical
  have : Finite (CFSG.GorensteinWalter.PGL2 F') :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  by_contra hcop'
  obtain ⟨r, hr, hrW, hrI⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop'
  have : Fact r.Prime := ⟨hr⟩
  have hr3 : 3 ≤ r := by
    have h2 := hr.two_le
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr (odd_card_W (G := G) (t := t) (s₀ := s₀)))
        (even_iff_two_dvd.mpr hrW)
    omega
  have hWL : torusW G t s₀ ≤ R ⊓ torusH G t s₀ := le_inf hWR h.W_le_H
  have hWLn : ((torusW G t s₀).subgroupOf (R ⊓ torusH G t s₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mpr inf_le_right
  let Q : Sylow r ↥(R ⊓ torusH G t s₀) := default
  have hπ := QuotientGroup.mk'_surjective ((torusW G t s₀).subgroupOf (R ⊓ torusH G t s₀))
  have hQ' := Sylow.ne_bot_of_dvd_card (Q.mapSurjective hπ) hrI
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ'
  obtain ⟨y, hyQ, hyz⟩ := z.2
  have hyW : (y : G) ∉ torusW G t s₀ := by
    intro hyW
    apply hz
    apply Subtype.ext
    rw [← hyz]
    exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hyW)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨y, hyQ⟩
  rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at hk
  have hyR : (y : G) ∈ R := y.2.1
  have hyH : (y : G) ∈ torusH G t s₀ := y.2.2
  have hyodd : Odd (orderOf (y : G)) := by
    have h1 := Subgroup.orderOf_dvd_natCard R hyR
    exact hR.of_dvd_nat h1
  have hyK : (y : G) ∈ torusK G t s₀ := by
    have h1 := mem_of_index_two_of_odd h.relIndex_K_H
      (x := (⟨_, hyH⟩ : torusH G t s₀)) (by rwa [Subgroup.orderOf_mk])
    exact Subgroup.mem_subgroupOf.mp h1
  set ybar := torusPsi φ ⟨_, hyH⟩ with hybar
  have hy1 : ybar ≠ 1 := by
    rw [hybar, ne_eq, h.torusPsi_eq_one_iff]
    exact hyW
  have hyR' : ybar ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range :=
    (h.torusPsi_mem_range_iff _).mpr hyK
  obtain ⟨a, ha⟩ : ∃ a : ℕ, orderOf ybar = r ^ a := by
    have h1 : orderOf ybar ∣ r ^ k := by
      rw [← hk, hybar, ← Subgroup.orderOf_mk (ha := hyH)]
      exact orderOf_map_dvd _ _
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hr).mp h1
    exact ⟨a, ha⟩
  have ha1 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at ha
    exact hy1 ha
  have hUc := h.U_cyclic
  obtain ⟨u₁, hu₁⟩ := IsCyclic.exists_generator (α := torusU G t s₀ d)
  have hu₁ord : orderOf u₁ = Nat.card (torusU G t s₀ d) := orderOf_eq_card_of_forall_mem_zpowers hu₁
  have hu₁H : (u₁ : G) ∈ torusH G t s₀ := U_le_H u₁.2
  set ubar := torusPsi φ ⟨_, hu₁H⟩ with hubar
  have hubarord : orderOf ubar = Nat.card (torusU G t s₀ d) := by
    rw [← hu₁ord]
    apply le_antisymm
    · apply Nat.le_of_dvd (orderOf_pos _)
      rw [hubar, ← Subgroup.orderOf_coe u₁, ← Subgroup.orderOf_mk (ha := hu₁H)]
      exact orderOf_map_dvd _ _
    · apply Nat.le_of_dvd (orderOf_pos _)
      apply orderOf_dvd_of_pow_eq_one
      have h1 : torusPsi φ (⟨_, hu₁H⟩ ^ orderOf ubar) = 1 := by
        rw [map_pow, ← hubar, pow_orderOf_eq_one]
      have hv : ((⟨_, hu₁H⟩ ^ orderOf ubar : torusH G t s₀) : G) * (s₀ * d) =
          s₀ * d * ((⟨_, hu₁H⟩ ^ orderOf ubar : torusH G t s₀) : G) := by
        rw [Subgroup.coe_pow]
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (U_le_centralizer (Subgroup.pow_mem _ u₁.2 _))
      have h2 := h.eq_of_torusPsi_eq hv
        (show ((1 : torusH G t s₀) : G) * (s₀ * d) = s₀ * d * ((1 : torusH G t s₀) : G) by
          simp) (by rw [h1, map_one])
      apply Subtype.ext
      have := congrArg Subtype.val h2
      simpa using this
  have hu₁R' : ubar ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range :=
    (h.torusPsi_mem_range_iff _).mpr (h.U_le_K u₁.2)
  have hcomm : Commute ybar ubar := by
    rw [hybar, hubar, Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp (hRU hyR)) _ u₁.2).symm
  have hcopyu : Nat.Coprime (orderOf ybar) (orderOf ubar) := by
    rw [ha, hubarord]
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hr]
    intro hrU
    exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hrU hrW)
  have hord := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcopyu
  rw [ha, hubarord] at hord
  obtain ⟨x, hx⟩ := Subgroup.mul_mem _ hyR' hu₁R'
  have hxord : orderOf x = r ^ a * Nat.card (torusU G t s₀ d) := by
    rw [← hord, ← hx]
    exact (orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective x).symm
  have hra : 3 ≤ r ^ a :=
    hr3.trans (Nat.le_self_pow ha1 r)
  exact h.psl2_orderOf_ne x hra hxord

end CaseIData

end CFSG.Semidihedral.FixedCoreNontrivial
