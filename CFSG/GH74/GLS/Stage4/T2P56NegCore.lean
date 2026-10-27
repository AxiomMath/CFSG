module

public import CFSG.GH74.GLS.Stage4.T2P56Core
public import CFSG.GH74.GLS.Stage4.T2P56NegLift
public import CFSG.GH74.GLS.Stage4.T2P56NegExcl
public import CFSG.GH74.GLS.Stage4.T2P56NegSyl
public import CFSG.GH74.GLS.Stage4.T2P56NegStar

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Core

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem exists_J_core_neg_of_shape (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) (hStd : Std G)
    (hSet : Ch6Setup G Gs q q z K₁ K₂ F₁ F₂)
    (hnormK : ∀ c : G, c * z = z * c →
      (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂))
    {p : ℕ} (hNum : Ch6NumD p q q) {u : G} {H : Subgroup G} {w₁ w₂ a : G}
    (cfg : Ch6NegCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z u K₁ K₂ H w₁ w₂)
    (ha1 : a⁻¹ * z * a = u) (ha2 : a⁻¹ * u * a = z * u) {y : G} (hyH : y ∈ H ⊓ K₁)
    (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y)) (hya : a * y * a⁻¹ = y)
    (hshape : (q % 4 = 1 ∧ HasSDSylow ↥(centralizer ({y} : Set G))) ∨
      (q % 4 = 3 ∧ HasWreathedSylow ↥(centralizer ({y} : Set G)))) :
    ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
      (IsSLnEps 3 ↥J (-1) q ∨ IsLnEps 3 ↥J (-1) q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hSet.finite₁
  have := hSet.finite₂
  have hp := hNum.prime
  have hp2 := hNum.p_ne_two
  obtain ⟨n, hn⟩ := hNum.q₂_pow
  have hq₂odd : Odd q := hSet.odd₂
  have h5 : 5 ≤ q := hSet.five
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyp
    exact Nat.not_prime_one hyp
  have hy2 : y * y ≠ 1 := by
    intro h
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
    · exact hy1 (orderOf_eq_one_iff.1 h3)
    · rw [h3] at hyodd
      exact absurd hyodd (by decide)
  have hyH' : y ∈ H := hyH.1
  have hyK₁ : y ∈ K₁ := hyH.2
  have hzz : z * z = 1 := cfg.zz
  have hz1 : z ≠ 1 := cfg.z_ne
  have hu2 : u * u = 1 := cfg.uu
  have hu1 : u ≠ 1 := cfg.u_ne
  have hHc := cfg.H_comm
  have hzu : z * u = u * z := cfg.zu_comm
  have hay : a * y = y * a := by
    calc a * y = (a * y * a⁻¹) * a := by group
      _ = y * a := by rw [hya]
  have hX : centralizer ({y} : Set G) ≠ ⊤ := by
    intro htop
    have hy : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ centralizer ({y} : Set G) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have hsimple : IsSimpleGroup G := hStd.kps.1
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · rw [h0] at hy
      exact hy1 (Subgroup.mem_bot.1 hy)
    · obtain ⟨b, c, hbc⟩ := hStd.kps.2.1
      apply hbc
      have := Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) b
      exact this
  have hKX := hStd.kps.isKGroupNative_of_ne_top hX
  set X : Subgroup G := centralizer ({y} : Set G) with hXdef
  have hmemX : ∀ x : G, x * y = y * x → x ∈ X := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 hx
  have hXy : ∀ x ∈ X, x * y = y * x := fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx
  have hcomm : ∀ x ∈ H, x * y = y * x := fun x hx => hHc x hx y hyH'
  have hzX : z ∈ X := hmemX _ (hcomm _ cfg.z_mem_H)
  have huX : u ∈ X := hmemX _ (hcomm _ cfg.u_mem_H)
  have haX : a ∈ X := hmemX _ hay
  have hK₂X : K₂ ≤ X := fun x hx => hmemX x (hSet.comm y hyK₁ x hx).symm
  have hFodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hq₂odd
  obtain ⟨e₂⟩ := hSet.iso₂
  have hS : HasSDOrWreathedSylow ↥X := by
    rcases hshape with ⟨-, h⟩ | ⟨-, h⟩
    · exact hasSDOrWreathedSylow_iff.2 (Or.inl h)
    · exact hasSDOrWreathedSylow_iff.2 (Or.inr h)
  let z' : ↥X := ⟨z, hzX⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hz'2 : orderOf z' = 2 := by
    rw [← hz2]
    exact Subgroup.orderOf_mk _ hzX
  have hzK' : z' ∈ K₂.subgroupOf X := cfg.z_mem_K₂
  have hSL₂ : HasSL2Model ↥K₂ (fun q' => q' = p ^ n) :=
    ⟨F₂, inferInstance, hSet.finite₂, hSet.card₂.trans hn,
      ⟨e₂.trans (specialLinearGroupEquivStatedSL 2 F₂)⟩⟩
  have hK' := hasSL2Model_subgroupOf hK₂X hSL₂
  have hCK' : ∀ c : ↥X, c * z' = z' * c → ∀ k ∈ K₂.subgroupOf X, c * k * c⁻¹ ∈ K₂.subgroupOf X :=
    fun c hc k hk => (hnormK (c : G) (congrArg Subtype.val hc)).2 (k : G) hk
  have hfus' : ∃ a' : ↥X, a' * z' * a'⁻¹ ≠ z' ∧ (a' * z' * a'⁻¹) * z' = z' * (a' * z' * a'⁻¹) := by
    obtain ⟨hau', haz', hazu'⟩ := cycle_facts hzz ha1 ha2
    refine ⟨⟨a, haX⟩, ?_, ?_⟩
    · intro h
      have h' : a * z * a⁻¹ = z := congrArg Subtype.val h
      rw [haz'] at h'
      apply hu1
      have h5' : u * z = 1 * z := by rw [one_mul]; exact h'
      exact mul_right_cancel h5'
    · apply Subtype.ext
      show (a * z * a⁻¹) * z = z * (a * z * a⁻¹)
      rw [haz']
      calc u * z * z = u * (z * z) := by group
        _ = u := by rw [hzz, mul_one]
        _ = z * (u * z) := by
            calc u = u * (z * z) := by rw [hzz, mul_one]
              _ = (u * z) * z := by group
              _ = (z * u) * z := by rw [hzu]
              _ = z * (u * z) := by group
  have hq₂pn : 3 ≤ p ^ n := by rw [← hn]; omega
  obtain ⟨E, hEn, hKE, hEodd, hE⟩ :=
    layer_of_quotient hL hKX hS hp hp2 hq₂pn hz'2 hzK' hK' hCK' hfus'
  have := hEn
  obtain ⟨ε, hε, hEε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 ↥E ε (p ^ n) := by
    rcases hE with h | ⟨h3, -⟩
    · exact h
    · exfalso; rw [← hn] at h3; omega
  have hshape' : (p ^ n % 4 = 1 ∧ HasSDSylow ↥X) ∨ (p ^ n % 4 = 3 ∧ HasWreathedSylow ↥X) := by
    rw [← hn]; exact hshape
  have hε1 : ε = -1 := eps_eq_neg_one_of_layer hp hp2 hε E hEodd hEε hshape'
  subst hε1
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥X)) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥X)
    rwa [Nat.coprime_two_left] at hcop
  have : (pPrimeCore 2 ↥X).Normal := pPrimeCore_normal
  have hloc : ∀ B : Subgroup G, (∀ b ∈ B, b * y = y * b) →
      (∀ g : G, g * y = y * g → ∀ b ∈ B, g * b * g⁻¹ ∈ B) → Odd (Nat.card B) →
        ∀ b ∈ B, b * z = z * b → b * u = u * b := by
    intro B hBy hBn hBodd
    exact star_local_neg (z := z) (u := u) (y := y) (K₁ := K₁) (K₂ := K₂) (H := H)
      (C₁ := oPrimeResidualOf 2 (centralizer ({z} : Set G))) hz1 hu2 hSet.comm cfg.z_mem_K₁
      cfg.z_mem_K₂ e₂ hFodd₂ (by rw [hSet.card₂]; omega) hHc cfg.z_mem_H cfg.u_mem_H hyH' hyK₁
      cfg.H₁_cent hy2 (fun f hf _ x hx => (hnormK f hf).2 x hx)
      (fun c hc x hx => t2C_oPrimeResidualOf_conj 2
        (Subgroup.mem_centralizer_singleton_iff.2 hc) hx)
      cfg.u_mem_C cfg.C_idx B hBy hBn hBodd
  have hstar := hstar_of_local X hzX huX hXy hmemX hloc (pPrimeCore 2 ↥X) hNodd
  have hperf : ⁅K₂.subgroupOf X, K₂.subgroupOf X⁆ = K₂.subgroupOf X :=
    perfect_of_sl2 ((Subgroup.subgroupOfEquivOfLe hK₂X).trans e₂)
      (by rw [hSet.card₂]; omega)
  have hz'2' : z' * z' = 1 := Subtype.ext (by simpa using hzz)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hu'2 : (⟨u, huX⟩ : ↥X) * ⟨u, huX⟩ = 1 := Subtype.ext (by simpa using hu2)
  have hzu' : z' * (⟨u, huX⟩ : ↥X) = ⟨u, huX⟩ * z' := Subtype.ext hzu
  obtain ⟨P, hKP, hP⟩ := lift_core_neg (pPrimeCore 2 ↥X) E hL3 hNodd hp hp2 (by rw [← hn]; exact h5)
    hEε (K := K₂.subgroupOf X) hperf hKE (z := z') (u := ⟨u, huX⟩) (a := ⟨a, haX⟩) hz'2' hz'1 hu'2
    (fun h => cfg.zu_ne (congrArg Subtype.val h)) hzu' hzK' (Subtype.ext ha1)
    (Subtype.ext ha2) hstar
  refine ⟨P.map X.subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · intro x hx
    have : (⟨x, hK₂X hx⟩ : ↥X) ∈ P := hKP (Subgroup.mem_subgroupOf.2 hx)
    exact ⟨⟨x, hK₂X hx⟩, this, rfl⟩
  · have e := Subgroup.equivMapOfInjective P X.subtype X.subtype_injective
    rw [hn]
    rcases hP with h | h
    · exact Or.inl (isSLnEps_of_equiv e h)
    · exact Or.inr (isLnEps_of_equiv e h)

theorem exists_J_core_neg_one (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) (hStd : Std G)
    (hSet : Ch6Setup G Gs q q z K₁ K₂ F₁ F₂)
    (hnormK : ∀ c : G, c * z = z * c →
      (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂))
    {p : ℕ} (hNum : Ch6NumD p q q) (hq4 : q % 4 = 1) {u : G} {H : Subgroup G} {w₁ w₂ a : G}
    (cfg : Ch6NegCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z u K₁ K₂ H w₁ w₂)
    (ha1 : a⁻¹ * z * a = u) (ha2 : a⁻¹ * u * a = z * u) {y : G} (hyH : y ∈ H ⊓ K₁)
    (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y)) (hya : a * y * a⁻¹ = y) :
    ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
      (IsSLnEps 3 ↥J (-1) q ∨ IsLnEps 3 ↥J (-1) q) := by
  have := hSet.finite₂
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyp
    exact Nat.not_prime_one hyp
  have hFodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  obtain ⟨e₂⟩ := hSet.iso₂
  refine exists_J_core_neg_of_shape hL hL3 hStd hSet hnormK hNum cfg ha1 ha2 hyH hyp hyodd hya
    (Or.inl ⟨hq4, ?_⟩)
  exact hasSDSylow_neg cfg hq4 (fun g hg h2 => twoElt_mem_residual hg h2) hyH.1 hy1 hyodd
    (Kj := K₂) (fun x hx => (hSet.comm y hyH.2 x hx).symm) hFodd₂ e₂

end Core

end CFSG.GH74.GLS.Stage4.Rest
