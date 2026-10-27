module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterTorusBasic
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusDickson
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

section Helpers

variable (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
include h

theorem two_mul_card_W_cases :
    (p ^ f % 4 = 1 → 2 * Nat.card (torusW G t s₀) = p ^ f + 1) ∧
      (p ^ f % 4 = 3 → 2 * Nat.card (torusW G t s₀) + 1 = p ^ f) := by
  have h2 := h.card_W_int'
  obtain ⟨k, hk⟩ := h.q_odd'
  have hq : ((p ^ f : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  refine ⟨fun h4 => ?_, fun h4 => ?_⟩
  · have h2' : (Nat.card (torusW G t s₀) : ℤ) = (((p ^ f : ℕ) : ℤ) + 1) / 2 := by
      simpa [h4] using h2
    have : 2 * (Nat.card (torusW G t s₀) : ℤ) = ((p ^ f : ℕ) : ℤ) + 1 := by omega
    exact_mod_cast this
  · have h4' : ¬ p ^ f % 4 = 1 := by omega
    have h2' : (Nat.card (torusW G t s₀) : ℤ) = (((p ^ f : ℕ) : ℤ) + -1) / 2 := by
      simpa [h4'] using h2
    have : 2 * (Nat.card (torusW G t s₀) : ℤ) + 1 = ((p ^ f : ℕ) : ℤ) := by omega
    exact_mod_cast this

theorem four_mul_card_B_cases :
    (p ^ f % 4 = 1 → 4 * Nat.card ((N t).map (C t).subtype) + 1 = p ^ f) ∧
      (p ^ f % 4 = 3 → 4 * Nat.card ((N t).map (C t).subtype) = p ^ f + 1) := by
  have h2 := h.card_B_int'
  rw [h.card_F'] at h2
  refine ⟨fun h4 => ?_, fun h4 => ?_⟩
  · have h2' : 4 * (Nat.card ((N t).map (C t).subtype) : ℤ) = ((p ^ f : ℕ) : ℤ) - 1 := by
      simpa [h4] using h2
    have : 4 * (Nat.card ((N t).map (C t).subtype) : ℤ) + 1 = ((p ^ f : ℕ) : ℤ) := by omega
    exact_mod_cast this
  · have h4' : ¬ p ^ f % 4 = 1 := by omega
    have h2' : 4 * (Nat.card ((N t).map (C t).subtype) : ℤ) = ((p ^ f : ℕ) : ℤ) - -1 := by
      simpa [h4'] using h2
    have : 4 * (Nat.card ((N t).map (C t).subtype) : ℤ) = ((p ^ f : ℕ) : ℤ) + 1 := by omega
    exact_mod_cast this

theorem q_mod_four : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
  obtain ⟨k, hk⟩ := h.q_odd'
  omega

theorem not_dvd_card_W : ¬ p ∣ Nat.card (torusW G t s₀) := by
  intro hpW
  have hpq : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
  obtain ⟨h1, h3⟩ := h.two_mul_card_W_cases
  rcases h.q_mod_four with h4 | h4
  · have h5 : p ∣ p ^ f + 1 := (h1 h4) ▸ dvd_mul_of_dvd_right hpW 2
    exact h.prime.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp h5))
  · have h5 : p ∣ 2 * Nat.card (torusW G t s₀) + 1 := (h3 h4) ▸ hpq
    exact h.prime.one_lt.ne'
      (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpW 2)).mp h5))

theorem factorization_card_H : (Nat.card (torusH G t s₀)).factorization p = f := by
  have hp := h.prime
  have hq1 : 1 ≤ (p ^ f) ^ 2 - 1 := by
    have : 9 < p ^ f := h.q_gt
    have : 81 < (p ^ f) ^ 2 := by nlinarith
    omega
  have hW0 : Nat.card (torusW G t s₀) ≠ 0 := Nat.card_pos.ne'
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hnot : ¬ p ∣ (p ^ f) ^ 2 - 1 := by
    intro hdvd
    have h2 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by have := h.one_le; omega)) two_ne_zero
    have h3 : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub h2 hdvd
    rw [show (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) = 1 by omega] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  rw [h.card_H, Nat.factorization_mul hW0 (mul_ne_zero hq0 (by omega)),
    Nat.factorization_mul hq0 (by omega), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h.not_dvd_card_W,
    Nat.factorization_eq_zero_of_not_dvd hnot, hp.factorization_pow, Finsupp.single_eq_same]
  ring

theorem card_map_torusPsiD {X : Subgroup G} (hXH : X ≤ torusH G t s₀)
    (hXW : X ⊓ torusW G t s₀ = ⊥) :
    Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) = Nat.card X := by
  have hinj : Function.Injective ((torusPsiD φ).comp (X.subgroupOf (torusH G t s₀)).subtype) := by
    intro a b hab
    have h1 := h.mul_inv_mem_W_of_torusPsiD_eq hab
    have h2 : (((a : torusH G t s₀) * (b : torusH G t s₀)⁻¹ : torusH G t s₀) : G) ∈ X := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact X.mul_mem (Subgroup.mem_subgroupOf.mp a.2) (X.inv_mem (Subgroup.mem_subgroupOf.mp b.2))
    have h3 : (((a : torusH G t s₀) * (b : torusH G t s₀)⁻¹ : torusH G t s₀) : G) ∈
        X ⊓ torusW G t s₀ := ⟨h2, h1⟩
    rw [hXW, Subgroup.mem_bot] at h3
    have h4 : (a : torusH G t s₀) * (b : torusH G t s₀)⁻¹ = 1 := Subtype.ext h3
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  rw [show (X.subgroupOf (torusH G t s₀)).map (torusPsiD φ) =
      ((torusPsiD φ).comp (X.subgroupOf (torusH G t s₀)).subtype).range by
    rw [MonoidHom.range_comp, Subgroup.range_subtype],
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]

theorem inf_W_eq_bot_of_isPGroup {X : Subgroup G} (hX : IsPGroup p X) :
    X ⊓ torusW G t s₀ = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  rw [eq_bot_iff]
  intro x ⟨hxX, hxW⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨x, hxX⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf x ∣ Nat.card (torusW G t s₀) := Subgroup.orderOf_dvd_natCard _ hxW
  rw [hk] at h1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact Subgroup.mem_bot.mpr hk
  · exact absurd ((dvd_pow_self p hk0.ne').trans h1) h.not_dvd_card_W

omit [Finite G] [Field F] [Finite F] h in
theorem card_map_torusPsiD_dvd {X : Subgroup G} (hXH : X ≤ torusH G t s₀) :
    Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) ∣ Nat.card X := by
  have h1 := Subgroup.card_map_dvd (X.subgroupOf (torusH G t s₀)) (torusPsiD φ)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv] at h1

omit [Finite G] h in
theorem map_torusPsiD_le_coordinateD (X : Subgroup G) :
    (X.subgroupOf (torusH G t s₀)).map (torusPsiD φ) ≤ coordinateD F' := by
  rintro _ ⟨y, -, rfl⟩
  exact torusPsiD_mem_coordinateD y

theorem le_of_map_torusPsiD_le {X Y : Subgroup G} (hXH : X ≤ torusH G t s₀)
    (hWY : torusW G t s₀ ≤ Y)
    (hle : (X.subgroupOf (torusH G t s₀)).map (torusPsiD φ) ≤
      (Y.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) : X ≤ Y := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hle ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have h1 := h.mul_inv_mem_W_of_torusPsiD_eq hyx.symm
  have h2 : x = ((⟨x, hXH hx⟩ * y⁻¹ : torusH G t s₀) : G) * (y : G) := by simp
  rw [h2]
  exact Y.mul_mem (hWY h1) (Subgroup.mem_subgroupOf.mp hy)

end Helpers

theorem sylow_H_facts (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {P : Subgroup G}
    (hP : IsSylowOf p P (torusH G t s₀)) :
    Nat.card P = p ^ f ∧ P ≤ torusK G t s₀ ∧
      torusH G t s₀ ⊓ Subgroup.centralizer (P : Set G) = P ⊔ torusW G t s₀ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hPH := hP.le
  have hPp := hP.isPGroup
  have hcard : Nat.card P = p ^ f := by rw [hP.card_eq, h.factorization_card_H]
  have hPK : P ≤ torusK G t s₀ := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    have hodd : Odd (orderOf (⟨x, hPH hx⟩ : torusH G t s₀)) := by
      rw [Subgroup.orderOf_mk, hk]
      exact h.odd.pow
    exact Subgroup.mem_subgroupOf.mp (mem_of_index_two_of_odd h.relIndex_K_H' hodd)
  have hPW := h.inf_W_eq_bot_of_isPGroup hPp
  have hXD := map_torusPsiD_le_coordinateD (φ := φ) P
  have hXp : IsPGroup p ((P.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) :=
    hPp.comap_subtype.map _
  have hXcard : Nat.card ((P.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) = p ^ f :=
    (h.card_map_torusPsiD hPH hPW).trans hcard
  have hcent := coordinateD_inf_centralizer_eq_of_isPGroup h.prime h.odd h.card_F' hXD hXp hXcard
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have hXc : ∀ z ∈ (P.subgroupOf (torusH G t s₀)).map (torusPsiD φ),
        z ∈ Subgroup.centralizer (((P.subgroupOf (torusH G t s₀)).map (torusPsiD φ) :
          Subgroup (Equiv.Perm (Omega F'))) : Set (Equiv.Perm (Omega F'))) := by
      intro z hz
      have hmem : z ∈ coordinateD F' ⊓ Subgroup.centralizer
          (((P.subgroupOf (torusH G t s₀)).map (torusPsiD φ) :
            Subgroup (Equiv.Perm (Omega F'))) : Set (Equiv.Perm (Omega F'))) := by
        rw [hcent]
        exact hz
      exact hmem.2
    have h1 := Subgroup.mem_centralizer_iff.mp
      (hXc _ ⟨⟨b, hPH hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩) _
      ⟨⟨a, hPH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have h2 : torusPsiD φ (⟨a, hPH ha⟩ * ⟨b, hPH hb⟩) =
        torusPsiD φ (⟨b, hPH hb⟩ * ⟨a, hPH ha⟩) := by
      rw [map_mul, map_mul]
      exact h1
    have h3 := h.mul_inv_mem_W_of_torusPsiD_eq h2
    have h4 : (((⟨a, hPH ha⟩ * ⟨b, hPH hb⟩ : torusH G t s₀) *
        (⟨b, hPH hb⟩ * ⟨a, hPH ha⟩ : torusH G t s₀)⁻¹ : torusH G t s₀) : G) ∈ P := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact P.mul_mem (P.mul_mem ha hb) (P.inv_mem (P.mul_mem hb ha))
    have h5 : (((⟨a, hPH ha⟩ * ⟨b, hPH hb⟩ : torusH G t s₀) *
        (⟨b, hPH hb⟩ * ⟨a, hPH ha⟩ : torusH G t s₀)⁻¹ : torusH G t s₀) : G) ∈
        P ⊓ torusW G t s₀ := ⟨h4, h3⟩
    rw [hPW, Subgroup.mem_bot] at h5
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
    exact mul_inv_eq_one.mp h5
  refine ⟨hcard, hPK, le_antisymm ?_ ?_⟩
  · rintro y ⟨hyH, hyC⟩
    have hyC' : y ∈ Subgroup.centralizer (P : Set G) := hyC
    have hΨy : torusPsiD φ ⟨y, hyH⟩ ∈ coordinateD F' ⊓
        Subgroup.centralizer (((P.subgroupOf (torusH G t s₀)).map (torusPsiD φ) :
          Subgroup (Equiv.Perm (Omega F'))) : Set (Equiv.Perm (Omega F'))) := by
      refine ⟨torusPsiD_mem_coordinateD _, ?_⟩
      show _ ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hyC') _ (Subgroup.mem_subgroupOf.mp hz)
    rw [hcent] at hΨy
    obtain ⟨z, hz, hzy⟩ := hΨy
    have h1 := h.mul_inv_mem_W_of_torusPsiD_eq hzy.symm
    have h2 : y = ((⟨y, hyH⟩ * z⁻¹ : torusH G t s₀) : G) * (z : G) := by simp
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hz))
  · apply sup_le
    · intro x hx
      refine ⟨hPH hx, ?_⟩
      show x ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hPab y hy x hx
    · intro w hw
      refine ⟨h.W_le_H' hw, ?_⟩
      show w ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact ((Subgroup.mem_centralizer_iff.mp (hPK hx)) w hw).symm

theorem odd_subgroup_H_eq_of_mod_four_eq_three
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 3) {X : Subgroup G}
    (hXH : X ≤ torusH G t s₀) (hX : Odd (Nat.card X))
    (hWBX : torusW G t s₀ ⊔ (N t).map (C t).subtype ≤ X) :
    X = torusW G t s₀ ⊔ (N t).map (C t).subtype := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hB4 := h.four_mul_card_B_cases.2 he
  have hBodd := CaseIData.odd_card_B (G := G) (t := t)
  have hB1 : Nat.card ((N t).map (C t).subtype) ≠ 1 := by
    intro h1
    exact h.B_ne_bot (Subgroup.card_eq_one.mp h1)
  have hBX : (N t).map (C t).subtype ≤ X := le_sup_right.trans hWBX
  have hBbX : ((N t).map (C t).subtype).subgroupOf (torusH G t s₀) ≤ X.subgroupOf (torusH G t s₀) :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (hBX (Subgroup.mem_subgroupOf.mp hx))
  have hBbX' := Subgroup.map_mono (f := torusPsiD φ) hBbX
  have hXbD := map_torusPsiD_le_coordinateD (φ := φ) X
  have hXbodd : Odd (Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ))) :=
    hX.of_dvd_nat (card_map_torusPsiD_dvd hXH)
  have hBW : (N t).map (C t).subtype ⊓ torusW G t s₀ = ⊥ := by
    rw [inf_comm]
    exact h.W_inf_B
  have hBbcard := h.card_map_torusPsiD h.B_le_H' hBW
  obtain ⟨ℓ, hℓ, hℓB⟩ := Nat.exists_prime_and_dvd hB1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card'
    (G := (((N t).map (C t).subtype).subgroupOf (torusH G t s₀)).map (torusPsiD φ)) ℓ
    (hBbcard ▸ hℓB)
  have hbD : (b : Equiv.Perm (Omega F')) ∈ coordinateD F' :=
    map_torusPsiD_le_coordinateD _ b.2
  have hbord : orderOf (b : Equiv.Perm (Omega F')) = ℓ := by rw [Subgroup.orderOf_coe, hb]
  have hb1 : (b : Equiv.Perm (Omega F')) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbord
    exact hℓ.one_lt.ne hbord
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := hℓ.two_le
    have : ℓ ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hBodd) (even_iff_two_dvd.mpr hℓB)
    omega
  have hfix : ∀ x : Omega F', (b : Equiv.Perm (Omega F')) x ≠ x := by
    intro x hx
    have h1 := card_fixed_modEq (K := F') hbord
    have h2 := card_fixed_le_two hbD hb1
    have hℓq : ℓ ∣ Nat.card F' + 1 := by
      rw [h.card_F', ← hB4]
      exact dvd_mul_of_dvd_right hℓB 4
    have h3 : ℓ ∣ Nat.card {y : Omega F' // (b : Equiv.Perm (Omega F')) y = y} :=
      Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr hℓq))
    have h4 : 0 < Nat.card {y : Omega F' // (b : Equiv.Perm (Omega F')) y = y} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
    have h5 := Nat.le_of_dvd h4 h3
    omega
  rcases odd_subgroup_fixes_point_or_cyclic h.prime h.odd h.card_F' _ hXbD hXbodd with
    ⟨x, hx⟩ | ⟨-, hdvd⟩
  · exact absurd (hx _ (hBbX' b.2)) (hfix x)
  · have h1 : Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) ∣
        2 * Nat.card ((N t).map (C t).subtype) := by
      rw [h.card_F'] at hdvd
      have : (p ^ f + 1) / 2 = 2 * Nat.card ((N t).map (C t).subtype) := by omega
      rwa [this] at hdvd
    have h2 : Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) ∣
        Nat.card ((N t).map (C t).subtype) :=
      (Nat.Coprime.dvd_of_dvd_mul_left hXbodd.coprime_two_right h1)
    have hXbB : (X.subgroupOf (torusH G t s₀)).map (torusPsiD φ) =
        (((N t).map (C t).subtype).subgroupOf (torusH G t s₀)).map (torusPsiD φ) :=
      (Subgroup.eq_of_le_of_card_ge hBbX'
        (by rw [hBbcard]; exact Nat.le_of_dvd Nat.card_pos h2)).symm
    apply le_antisymm _ hWBX
    have hle := h.le_of_map_torusPsiD_le hXH (le_sup_left : torusW G t s₀ ≤
      torusW G t s₀ ⊔ (N t).map (C t).subtype) (by
        rw [hXbB]
        exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))))
    exact hle

section Split

variable (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
include h

theorem Bd_le_H : (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤ torusH G t s₀ :=
  sup_le h.B_le_H' (Subgroup.zpowers_le.mpr h.d_mem_H)

theorem Bd_comm : ∀ a ∈ (N t).map (C t).subtype, ∀ b ∈ Subgroup.zpowers d, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_right (h.d_comm_B a ha).symm k).eq

theorem Bd_le_centralizer {b : G} (hb : b ∈ (N t).map (C t).subtype) :
    (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer {b} := by
  have hL := h.localData
  apply sup_le
  · intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hL.B_comm a ha b hb
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact h.d_comm_B b hb

theorem mem_B_of_mem_Bd_of_odd {x : G} (hx : x ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers d)
    (hodd : Odd (orderOf x)) : x ∈ (N t).map (C t).subtype := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup h.Bd_comm hx
  have hcomm : Commute a b := h.Bd_comm a ha b hb
  have hbodd : Odd (orderOf b) := by
    have h1 : b = a⁻¹ * (a * b) := by group
    rw [h1]
    exact odd_orderOf_mul_of_commute ((Commute.refl a).mul_right hcomm).inv_left
      (by rw [orderOf_inv]; exact h.localData.B_odd a ha) hodd
  have hd2 : IsPGroup 2 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, h.d_orderOf]; norm_num)
  rw [eq_one_of_mem_of_odd hd2 hb hbodd, mul_one]
  exact ha

theorem Bd_inf_W : ((N t).map (C t).subtype ⊔ Subgroup.zpowers d) ⊓ torusW G t s₀ = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hxBd, hxW⟩
  have hxB := h.mem_B_of_mem_Bd_of_odd hxBd (CaseIData.odd_orderOf_of_mem_W hxW)
  have : x ∈ torusW G t s₀ ⊓ (N t).map (C t).subtype := ⟨hxW, hxB⟩
  rwa [h.W_inf_B] at this

theorem card_Bd : Nat.card ((N t).map (C t).subtype ⊔ Subgroup.zpowers d : Subgroup G) =
    Nat.card ((N t).map (C t).subtype) * 4 := by
  have hnorm : Subgroup.zpowers d ≤ Subgroup.normalizer
      (((N t).map (C t).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_conj_mem
    intro x hx
    rw [h.d_comm_B x hx, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hdisj : Disjoint ((N t).map (C t).subtype) (Subgroup.zpowers d) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [Nat.card_zpowers, h.d_orderOf]
    have hodd := CaseIData.odd_card_B (G := G) (t := t)
    have := Nat.Coprime.pow_right 2 hodd.coprime_two_right
    simpa using this
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, h.d_orderOf]

theorem exists_two_point_of_mod_four_eq_one (he : p ^ f % 4 = 1) :
    ∃ x y : Omega F', x ≠ y ∧ ∀ c : torusH G t s₀,
      (c : G) ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers d →
        torusPsiD φ c x = x ∧ torusPsiD φ c y = y := by
  classical
  have hL := h.localData
  have hB4 := h.four_mul_card_B_cases.1 he
  have hBodd := CaseIData.odd_card_B (G := G) (t := t)
  have hB1 : Nat.card ((N t).map (C t).subtype) ≠ 1 := by
    intro h1
    exact h.B_ne_bot (Subgroup.card_eq_one.mp h1)
  obtain ⟨ℓ, hℓ, hℓB⟩ := Nat.exists_prime_and_dvd hB1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := (N t).map (C t).subtype) ℓ hℓB
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hBodd) (even_iff_two_dvd.mpr hℓB)
  set b' : torusH G t s₀ := ⟨(b : G), h.B_le_H' b.2⟩ with hb'
  have hbW : (b : G) ∉ torusW G t s₀ := by
    intro hbW
    have h1 : (b : G) ∈ torusW G t s₀ ⊓ (N t).map (C t).subtype := ⟨hbW, b.2⟩
    rw [h.W_inf_B, Subgroup.mem_bot] at h1
    have h2 : b = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hb
    exact hℓ.one_lt.ne hb
  have hbord : orderOf (torusPsiD φ b') = ℓ := by
    have h1 : orderOf (torusPsiD φ b') ∣ ℓ := by
      have := orderOf_map_dvd (torusPsiD φ) b'
      rwa [hb', Subgroup.orderOf_mk, Subgroup.orderOf_coe, hb] at this
    rcases (Nat.dvd_prime hℓ).mp h1 with h2 | h2
    · exfalso
      rw [orderOf_eq_one_iff, h.torusPsiD_eq_one_iff] at h2
      exact hbW h2
    · exact h2
  have hℓq : ℓ ∣ p ^ f - 1 := by
    rw [← hB4, Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_right hℓB 4
  obtain ⟨x, y, hxy, hx, hy⟩ := fixes_two_of_prime_dvd h.card_F'
    (torusPsiD_mem_coordinateD b') hℓ hℓ2 hbord hℓq
  refine ⟨x, y, hxy, ?_⟩
  set E : Subgroup (Equiv.Perm (Omega F')) := Subgroup.zpowers (torusPsiD φ b') with hE
  have hED : E ≤ coordinateD F' := Subgroup.zpowers_le.mpr (torusPsiD_mem_coordinateD b')
  have hfixE : ∀ z : Omega F', torusPsiD φ b' z = z → ∀ e ∈ E, e z = z := by
    intro z hz e he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he'
    have : (torusPsiD φ b') • z = z := hz
    exact (MulAction.mem_stabilizer_iff.mp
      (Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.mpr this) k) :)
  have hE1 : E ≠ ⊥ := by
    intro hbot
    have : torusPsiD φ b' ∈ E := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hbord
    exact hℓ.one_lt.ne hbord
  have hnorm : ∀ c : torusH G t s₀, (c : G) ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers d →
      torusPsiD φ c ∈ Subgroup.normalizer (E : Set (Equiv.Perm (Omega F'))) := by
    intro c hc
    have hcb : c * b' = b' * c := Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (h.Bd_le_centralizer b.2 hc))
    have hcomm : torusPsiD φ c * torusPsiD φ b' = torusPsiD φ b' * torusPsiD φ c := by
      rw [← map_mul, ← map_mul, hcb]
    have : Finite (Equiv.Perm (Omega F')) := inferInstance
    apply mem_normalizer_of_conj_mem
    intro e he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he'
    have h1 : torusPsiD φ c * torusPsiD φ b' ^ k * (torusPsiD φ c)⁻¹ = torusPsiD φ b' ^ k := by
      rw [(Commute.zpow_right hcomm k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  set T : Subgroup (Equiv.Perm (Omega F')) := coordinateD F' ⊓
    MulAction.stabilizer (Equiv.Perm (Omega F')) x ⊓
      MulAction.stabilizer (Equiv.Perm (Omega F')) y with hT
  have hpre : (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤
      (T.comap (torusPsiD φ)).map (torusH G t s₀).subtype := by
    apply sup_le
    · intro a ha
      refine ⟨⟨a, h.B_le_H' ha⟩, ?_, rfl⟩
      have hpair := mem_pair_of_mem_normalizer hxy hED (hfixE x hx) (hfixE y hy) hE1
        (hnorm ⟨a, h.B_le_H' ha⟩ (Subgroup.mem_sup_left ha))
      have hodd : Odd (orderOf (torusPsiD φ ⟨a, h.B_le_H' ha⟩)) := by
        have h1 := orderOf_map_dvd (torusPsiD φ) ⟨a, h.B_le_H' ha⟩
        rw [Subgroup.orderOf_mk] at h1
        exact (hL.B_odd a ha).of_dvd_nat h1
      obtain ⟨h1, h2⟩ := fixes_of_odd_of_pair hxy hodd hpair
      exact ⟨⟨torusPsiD_mem_coordinateD _, h1⟩, h2⟩
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨d, h.d_mem_H⟩, ?_, rfl⟩
      have hpair := mem_pair_of_mem_normalizer hxy hED (hfixE x hx) (hfixE y hy) hE1
        (hnorm ⟨d, h.d_mem_H⟩ (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨torusPsiD_mem_coordinateD _, h1⟩, h2⟩
      · exfalso
        have h3 := mul_self_eq_one_of_swap hxy (torusPsiD_mem_coordinateD _) h1 h2
        rw [← map_mul, h.torusPsiD_eq_one_iff] at h3
        have h4 : ((⟨d, h.d_mem_H⟩ * ⟨d, h.d_mem_H⟩ : torusH G t s₀) : G) = t := by
          rw [Subgroup.coe_mul, ← pow_two, h.d_sq]
        rw [h4] at h3
        have := CaseIData.odd_orderOf_of_mem_W h3
        rw [hL.t_orderOf] at this
        exact absurd this (by decide)
  intro c hc
  obtain ⟨c', hc', hcc'⟩ := hpre hc
  have : c' = c := Subtype.ext hcc'
  subst this
  exact ⟨hc'.1.2, hc'.2⟩

theorem exists_sylow_fixing (x : Omega F') :
    ∃ P : Subgroup G, IsSylowOf p P (torusH G t s₀) ∧
      ∀ z : torusH G t s₀, (z : G) ∈ P → torusPsiD φ z x = x := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P₀, hP₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (torusH G t s₀)
  obtain ⟨hP₀card, -, -⟩ := h.sylow_H_facts hP₀
  have hP₀H := hP₀.le
  have hP₀W := h.inf_W_eq_bot_of_isPGroup hP₀.isPGroup
  have hXD := map_torusPsiD_le_coordinateD (φ := φ) P₀
  have hXp : IsPGroup p ((P₀.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) :=
    hP₀.isPGroup.comap_subtype.map _
  have hXcard := (h.card_map_torusPsiD hP₀H hP₀W).trans hP₀card
  have hX1 : (P₀.subgroupOf (torusH G t s₀)).map (torusPsiD φ) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXcard
    have : 9 < p ^ f := h.q_gt
    omega
  obtain ⟨x₀, hx₀, -⟩ := existsUnique_fixed_of_isPGroup h.prime h.odd h.card_F' hXD hXp hX1
  obtain ⟨g, hg⟩ := coordinateG_transitive F' x₀ x
  obtain ⟨h₀, hh₀⟩ := exists_torusPsiD_eq (φ := φ) (coordinateG_le_D F' g.2)
  refine ⟨P₀.map (MulAut.conj (h₀ : G)).toMonoidHom, ?_, ?_⟩
  · have hle : P₀.map (MulAut.conj (h₀ : G)).toMonoidHom ≤ torusH G t s₀ := by
      rintro _ ⟨z, hz, rfl⟩
      exact (torusH G t s₀).mul_mem ((torusH G t s₀).mul_mem h₀.2 (hP₀H hz))
        ((torusH G t s₀).inv_mem h₀.2)
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (h₀ : G)).injective, hP₀.card_eq]
  · intro z hz
    obtain ⟨z₀, hz₀, hzz₀⟩ := hz
    have hz₀' : z = h₀ * ⟨z₀, hP₀H hz₀⟩ * h₀⁻¹ := by
      apply Subtype.ext
      rw [← hzz₀]
      simp
    have hfix₀ : torusPsiD φ ⟨z₀, hP₀H hz₀⟩ x₀ = x₀ :=
      hx₀ _ ⟨⟨z₀, hP₀H hz₀⟩, Subgroup.mem_subgroupOf.mpr hz₀, rfl⟩
    have hg' : (g : Equiv.Perm (Omega F'))⁻¹ x = x₀ := by
      rw [← hg, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    rw [hz₀', map_mul, map_mul, map_inv, hh₀, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg',
      hfix₀, hg]

theorem mem_of_torusPsiD_eq_of_pow {P : Subgroup G} (hPK : P ≤ torusK G t s₀)
    (hPcard : Nat.card P = p ^ f) {z' z'' : torusH G t s₀} (hz' : (z' : G) ^ p ^ f = 1)
    (hz'' : (z'' : G) ∈ P) (heq : torusPsiD φ z' = torusPsiD φ z'') : (z' : G) ∈ P := by
  have hw := h.mul_inv_mem_W_of_torusPsiD_eq heq
  set w : G := ((z' * z''⁻¹ : torusH G t s₀) : G) with hwdef
  have hwz : Commute w (z'' : G) :=
    (Subgroup.mem_centralizer_iff.mp (hPK hz'')) w hw
  have hzz : Commute (z' : G) ((z'' : G)⁻¹) := by
    have h1 : (z' : G) = w * (z'' : G) := by rw [hwdef]; simp
    rw [h1]
    exact (hwz.mul_left (Commute.refl _)).inv_right
  have hz''p : (z'' : G) ^ p ^ f = 1 := by
    rw [← hPcard]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hz'')
  have hwp : w ^ p ^ f = 1 := by
    have : w = (z' : G) * (z'' : G)⁻¹ := by rw [hwdef]; simp
    rw [this, hzz.mul_pow, hz', inv_pow, hz''p, inv_one, one_mul]
  have hcop : Nat.Coprime (p ^ f) (Nat.card (torusW G t s₀)) :=
    Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.not_dvd_card_W)
  have hw1 : w = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hwp
    have h2 := Subgroup.orderOf_dvd_natCard (torusW G t s₀) hw
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have : (z' : G) = (z'' : G) := by
    have h1 : (z' : G) = w * (z'' : G) := by rw [hwdef]; simp
    rw [h1, hw1, one_mul]
  rw [this]
  exact hz''

end Split


theorem exists_split_torus_sylow
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 1) :
    ∃ P : Subgroup G, IsSylowOf p P (torusH G t s₀) ∧
      (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤ Subgroup.normalizer (P : Set G) ∧
      IsCyclic ((N t).map (C t).subtype ⊔ Subgroup.zpowers d : Subgroup G) ∧
      Nat.card ((N t).map (C t).subtype ⊔ Subgroup.zpowers d : Subgroup G) = p ^ f - 1 ∧
      (∀ x ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers d, x ≠ 1 →
        P ⊓ Subgroup.centralizer {x} = ⊥) ∧
      Nat.card (P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
        p ^ f * Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) ∧
      ∀ X : Subgroup G, X ≤ torusH G t s₀ → Odd (Nat.card X) →
        P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ≤ X →
        X = P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hB4 := h.four_mul_card_B_cases.1 he
  have hW2 := h.two_mul_card_W_cases.1 he
  have hBdH := h.Bd_le_H
  have hBdW := h.Bd_inf_W
  have hBdcard : Nat.card ((N t).map (C t).subtype ⊔ Subgroup.zpowers d : Subgroup G) =
      p ^ f - 1 := by
    rw [h.card_Bd]
    omega
  obtain ⟨x, y, hxy, hfix⟩ := h.exists_two_point_of_mod_four_eq_one he
  obtain ⟨hTc, hTcard⟩ := two_point_stabilizer h.prime h.odd h.card_F' hxy
  have himg_le : (((N t).map (C t).subtype ⊔ Subgroup.zpowers d).subgroupOf
      (torusH G t s₀)).map (torusPsiD φ) ≤ coordinateD F' ⊓
        MulAction.stabilizer (Equiv.Perm (Omega F')) x ⊓
          MulAction.stabilizer (Equiv.Perm (Omega F')) y := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨h1, h2⟩ := hfix c (Subgroup.mem_subgroupOf.mp hc)
    exact ⟨⟨torusPsiD_mem_coordinateD c, h1⟩, h2⟩
  have himg_card := h.card_map_torusPsiD hBdH hBdW
  have hcyc : IsCyclic ((N t).map (C t).subtype ⊔ Subgroup.zpowers d : Subgroup G) := by
    have : IsCyclic (coordinateD F' ⊓ MulAction.stabilizer (Equiv.Perm (Omega F')) x ⊓
        MulAction.stabilizer (Equiv.Perm (Omega F')) y : Subgroup (Equiv.Perm (Omega F'))) := hTc
    let fT : (((N t).map (C t).subtype ⊔ Subgroup.zpowers d).subgroupOf (torusH G t s₀)) →*
        (coordinateD F' ⊓ MulAction.stabilizer (Equiv.Perm (Omega F')) x ⊓
          MulAction.stabilizer (Equiv.Perm (Omega F')) y : Subgroup (Equiv.Perm (Omega F'))) :=
      ((torusPsiD φ).comp (((N t).map (C t).subtype ⊔ Subgroup.zpowers d).subgroupOf
        (torusH G t s₀)).subtype).codRestrict _ (fun c => himg_le ⟨c, c.2, rfl⟩)
    have hfT : Function.Injective fT := by
      intro a b hab
      have hab'' := congrArg Subtype.val hab
      have hab' : torusPsiD φ (a : torusH G t s₀) = torusPsiD φ (b : torusH G t s₀) := hab''
      have h1 := h.mul_inv_mem_W_of_torusPsiD_eq hab'
      have h2 : (((a : torusH G t s₀) * (b : torusH G t s₀)⁻¹ : torusH G t s₀) : G) ∈
          ((N t).map (C t).subtype ⊔ Subgroup.zpowers d) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp a.2)
          (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp b.2))
      have h3 : (((a : torusH G t s₀) * (b : torusH G t s₀)⁻¹ : torusH G t s₀) : G) ∈
          ((N t).map (C t).subtype ⊔ Subgroup.zpowers d) ⊓ torusW G t s₀ := ⟨h2, h1⟩
      rw [hBdW, Subgroup.mem_bot] at h3
      have h4 : (a : torusH G t s₀) * (b : torusH G t s₀)⁻¹ = 1 := Subtype.ext h3
      exact Subtype.ext (mul_inv_eq_one.mp h4)
    have h1 := isCyclic_of_injective fT hfT
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hBdH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBdH).symm.injective
  obtain ⟨P, hP, hPx⟩ := h.exists_sylow_fixing x
  obtain ⟨hPcard, hPK, -⟩ := h.sylow_H_facts hP
  have hPH := hP.le
  have hPW := h.inf_W_eq_bot_of_isPGroup hP.isPGroup
  have hXD := map_torusPsiD_le_coordinateD (φ := φ) P
  have hXp : IsPGroup p ((P.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) :=
    hP.isPGroup.comap_subtype.map _
  have hXcard := (h.card_map_torusPsiD hPH hPW).trans hPcard
  have hXfix : ∀ u ∈ (P.subgroupOf (torusH G t s₀)).map (torusPsiD φ), u x = x := by
    rintro _ ⟨z, hz, rfl⟩
    exact hPx z (Subgroup.mem_subgroupOf.mp hz)
  have hpow : ∀ z ∈ P, z ^ p ^ f = 1 := by
    intro z hz
    rw [← hPcard]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard P hz)
  have hBdN : (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤
      Subgroup.normalizer (P : Set G) := by
    intro c hc
    apply mem_normalizer_of_conj_mem
    intro z hz
    set cH : torusH G t s₀ := ⟨c, hBdH hc⟩
    set zH : torusH G t s₀ := ⟨z, hPH hz⟩
    have hcN : torusPsiD φ cH ∈ Subgroup.normalizer
        (((P.subgroupOf (torusH G t s₀)).map (torusPsiD φ) : Subgroup (Equiv.Perm (Omega F'))) :
          Set (Equiv.Perm (Omega F'))) :=
      mem_normalizer_of_fixes h.prime h.card_F' hXD hXp hXcard hXfix
        (torusPsiD_mem_coordinateD cH) (hfix cH hc).1
    have h1 : torusPsiD φ cH * torusPsiD φ zH * (torusPsiD φ cH)⁻¹ ∈
        (P.subgroupOf (torusH G t s₀)).map (torusPsiD φ) :=
      (Subgroup.mem_normalizer_iff.mp hcN _).mp
        ⟨zH, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    obtain ⟨z'', hz'', hz''eq⟩ := h1
    have h2 := h.mem_of_torusPsiD_eq_of_pow hPK hPcard (z' := cH * zH * cH⁻¹) (z'' := z'')
      (by
        change (c * z * c⁻¹) ^ p ^ f = 1
        rw [conj_pow, hpow z hz]
        group)
      (Subgroup.mem_subgroupOf.mp hz'') (by rw [map_mul, map_mul, map_inv, hz''eq])
    exact h2
  have hfree : ∀ c ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers d, c ≠ 1 →
      P ⊓ Subgroup.centralizer {c} = ⊥ := by
    intro c hc hc1
    rw [eq_bot_iff]
    rintro z ⟨hzP, hzc⟩
    set cH : torusH G t s₀ := ⟨c, hBdH hc⟩
    set zH : torusH G t s₀ := ⟨z, hPH hzP⟩
    have hw1 : torusPsiD φ cH ≠ 1 := by
      intro h1
      rw [h.torusPsiD_eq_one_iff] at h1
      have h2 : c ∈ ((N t).map (C t).subtype ⊔ Subgroup.zpowers d) ⊓ torusW G t s₀ := ⟨hc, h1⟩
      rw [hBdW, Subgroup.mem_bot] at h2
      exact hc1 h2
    have hcomm : torusPsiD φ cH * torusPsiD φ zH = torusPsiD φ zH * torusPsiD φ cH := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp hzc).symm
    have hu := eq_one_of_commute_two_point h.prime h.card_F' hxy
      (torusPsiD_mem_coordinateD cH) (hfix cH hc).1 (hfix cH hc).2 hw1
      (torusPsiD_mem_coordinateD zH) (hPx zH hzP) (k := f)
      (by rw [← map_pow]; rw [show zH ^ p ^ f = 1 from Subtype.ext (hpow z hzP), map_one]) hcomm
    rw [h.torusPsiD_eq_one_iff] at hu
    have h3 : z ∈ P ⊓ torusW G t s₀ := ⟨hzP, hu⟩
    rwa [hPW] at h3
  have hpB : ¬ p ∣ Nat.card ((N t).map (C t).subtype) := by
    intro hpB
    have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    have h2 : p ∣ 4 * Nat.card ((N t).map (C t).subtype) + 1 := hB4 ▸ h1
    exact h.prime.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpB 4)).mp
      h2))
  have hWB : Nat.Coprime (Nat.card (torusW G t s₀)) (Nat.card ((N t).map (C t).subtype)) := by
    have h1 : Nat.card (torusW G t s₀) = 2 * Nat.card ((N t).map (C t).subtype) + 1 := by omega
    rw [h1, add_comm, mul_comm]
    exact (Nat.coprime_add_mul_left_left 1 _ 2).mpr (Nat.coprime_one_left _)
  have hcardWB : Nat.card (torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
      Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ h.B_le_H'
      (disjoint_iff.mpr h.W_inf_B)
  have hWN : torusW G t s₀ ≤ Subgroup.normalizer (P : Set G) := by
    intro w hw
    apply mem_normalizer_of_conj_mem
    intro z hz
    have h1 : w * z = z * w := ((Subgroup.mem_centralizer_iff.mp (hPK hz)) w hw)
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hBN : (N t).map (C t).subtype ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_left.trans hBdN
  have hPdisj : Disjoint P (torusW G t s₀ ⊔ (N t).map (C t).subtype) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hPcard, hcardWB]
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd h.prime]
    intro hdvd
    rcases (Nat.Prime.dvd_mul h.prime).mp hdvd with h1 | h1
    · exact h.not_dvd_card_W h1
    · exact hpB h1
  have hcardPWB : Nat.card (P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
      p ^ f * Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) := by
    rw [sup_assoc, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (sup_le hWN hBN) hPdisj, hPcard, hcardWB, mul_assoc]
  refine ⟨P, hP, hBdN, hcyc, hBdcard, hfree, hcardPWB, ?_⟩
  intro X hXH hX hPWBX
  have hPBdisj : Disjoint P ((N t).map (C t).subtype) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hPcard]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hpB)
  have hcardPB : Nat.card (P ⊔ (N t).map (C t).subtype : Subgroup G) =
      p ^ f * Nat.card ((N t).map (C t).subtype) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hBN hPBdisj,
      hPcard]
  have hPBH : P ⊔ (N t).map (C t).subtype ≤ torusH G t s₀ := sup_le hPH h.B_le_H'
  have hPBW : (P ⊔ (N t).map (C t).subtype) ⊓ torusW G t s₀ = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hcardPB]
    apply Nat.coprime_comm.mp
    apply Nat.Coprime.mul_right
    · exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr
        h.not_dvd_card_W)).symm
    · exact hWB
  have hPBX : P ⊔ (N t).map (C t).subtype ≤ X :=
    sup_le (le_sup_left.trans (le_sup_left.trans hPWBX)) (le_sup_right.trans hPWBX)
  have himgPB := h.card_map_torusPsiD hPBH hPBW
  have himgle : ((P ⊔ (N t).map (C t).subtype).subgroupOf (torusH G t s₀)).map (torusPsiD φ) ≤
      (X.subgroupOf (torusH G t s₀)).map (torusPsiD φ) :=
    Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
      (hPBX (Subgroup.mem_subgroupOf.mp hz)))
  have hXbD := map_torusPsiD_le_coordinateD (φ := φ) X
  have hXbodd : Odd (Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ))) :=
    hX.of_dvd_nat (card_map_torusPsiD_dvd hXH)
  have hqdvd : p ^ f ∣ Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) := by
    rw [← hXcard]
    apply Subgroup.card_dvd_of_le
    exact Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
      (le_sup_left.trans (le_sup_left.trans hPWBX) (Subgroup.mem_subgroupOf.mp hz)))
  have hle : Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ)) ≤
      p ^ f * Nat.card ((N t).map (C t).subtype) := by
    rcases odd_subgroup_fixes_point_or_cyclic h.prime h.odd h.card_F' _ hXbD hXbodd with
      ⟨z, hz⟩ | ⟨-, hdvd⟩
    · have hXbz : (X.subgroupOf (torusH G t s₀)).map (torusPsiD φ) ≤
          coordinateD F' ⊓ MulAction.stabilizer (Equiv.Perm (Omega F')) z :=
        fun u hu => ⟨hXbD hu, hz u hu⟩
      have h1 := Subgroup.card_dvd_of_le hXbz
      rw [card_coordinateD_inf_stabilizer, h.card_F'] at h1
      have h2 : p ^ f * (p ^ f - 1) = (p ^ f * Nat.card ((N t).map (C t).subtype)) * 4 := by
        rw [show p ^ f - 1 = 4 * Nat.card ((N t).map (C t).subtype) by omega]
        ring
      rw [h2] at h1
      have h3 : Nat.Coprime (Nat.card ((X.subgroupOf (torusH G t s₀)).map (torusPsiD φ))) 4 := by
        have := Nat.Coprime.pow_right 2 hXbodd.coprime_two_right
        simpa using this
      exact Nat.le_of_dvd (by
        have := h.q_gt
        have : 0 < Nat.card ((N t).map (C t).subtype) := Nat.card_pos
        positivity) (h3.dvd_of_dvd_mul_right h1)
    · exfalso
      rw [h.card_F'] at hdvd
      have h1 := Nat.le_of_dvd (by omega) (hqdvd.trans hdvd)
      have := h.q_gt
      omega
  have hXbeq : (X.subgroupOf (torusH G t s₀)).map (torusPsiD φ) =
      ((P ⊔ (N t).map (C t).subtype).subgroupOf (torusH G t s₀)).map (torusPsiD φ) :=
    (Subgroup.eq_of_le_of_card_ge himgle (by rw [himgPB, hcardPB]; exact hle)).symm
  apply le_antisymm _ hPWBX
  refine h.le_of_map_torusPsiD_le hXH (le_sup_right.trans le_sup_left) ?_
  rw [hXbeq]
  have hPBle : P ⊔ (N t).map (C t).subtype ≤ P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  exact Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
    (hPBle (Subgroup.mem_subgroupOf.mp hz)))

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
