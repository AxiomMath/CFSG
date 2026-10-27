module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerShape
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerNorm
public import CFSG.GH74.GLS.Stage4.T2P56NegStar
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLayerCfg
public import CFSG.GH74.GLS.Stage4.T2P56Core

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Core

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem exists_J_core_mix (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hStd : Std G) (hr : pRank 2 G = 3)
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn' : ∃ n : ℕ, q₂ = p ^ n) (hmod' : q₁ % 4 ≠ q₂ % 4) (h5 : 5 ≤ q₂)
    {N : T2N3 G} {u : G}
    (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁) (hq₂ : N.q₂ = q₂)
    (hSec : Ch6Sec5M N u) {y : G} (hyH : y ∈ N.H ⊓ N.K₁) (hyz : y ∉ Subgroup.zpowers N.z)
    (hyp : (orderOf y).Prime) (hyodd : Odd (orderOf y)) (hya : N.a * y * N.a⁻¹ = y) :
    ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
      (IsSLnEps 3 ↥J 1 q₂ ∨ IsLnEps 3 ↥J 1 q₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hz hK₁ hK₂ hq₁ hq₂
  have hLoc : Ch6Loc5M N.toT2N2.toT2N1 u := hSec.loc
  have hLocW : Ch6Loc5W N.toT2N2.toT2N1 u := hLoc.toCh6Loc5W
  have hW := hSec.weyl
  have ctx := t2Ctx_ofW hSet hRem hLocW rfl rfl rfl rfl rfl
  have cfg := Ch6Loc5M.toMixCfg hSet hRem hLoc rfl rfl rfl rfl rfl
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨n, hn⟩ := hn'
  have hq₂odd : Odd N.q₂ := hSet.odd₂
  have hq₁odd : Odd N.q₁ := hSet.odd₁
  have hmod : N.q₁ % 4 ≠ N.q₂ % 4 := hmod'
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
  have hyH' : y ∈ N.H := hyH.1
  have hyK₁ : y ∈ N.K₁ := hyH.2
  have hu : N.u = u := hSec.u_eq
  have haz : N.a⁻¹ * N.z * N.a = u := hu
  have hau : N.a⁻¹ * u * N.a = N.z * u := by
    have := hW.a_cycle
    rwa [hu] at this
  have hz2 : orderOf N.z = 2 := hLoc.z_ord
  have hzz : N.z * N.z = 1 := by
    have h := pow_orderOf_eq_one N.z
    rw [hz2, sq] at h
    exact h
  have hz1 : N.z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hHc := hLoc.H_comm
  have hzu : N.z * u = u * N.z := hHc _ hLoc.z_mem_H u hLoc.u_mem_H
  have hay : N.a * y = y * N.a := by
    calc N.a * y = (N.a * y * N.a⁻¹) * N.a := by group
      _ = y * N.a := by rw [hya]
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
  have hcomm : ∀ x ∈ N.H, x * y = y * x := fun x hx => hHc x hx y hyH'
  have hzX : N.z ∈ X := hmemX _ (hcomm _ hLoc.z_mem_H)
  have huX : u ∈ X := hmemX _ (hcomm _ hLoc.u_mem_H)
  have haX : N.a ∈ X := hmemX _ hay
  have hK₂X : N.K₂ ≤ X := fun x hx => hmemX x (hSet.comm y hyK₁ x hx).symm
  have hq₂4 : N.q₂ % 4 = 1 ∨ N.q₂ % 4 = 3 := by obtain ⟨k, hk⟩ := hq₂odd; omega
  have hq₁4 : N.q₁ % 4 = 1 ∨ N.q₁ % 4 = 3 := by obtain ⟨k, hk⟩ := hq₁odd; omega
  have hFodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hq₂odd
  obtain ⟨e₂⟩ := hSet.iso₂
  have hshape : (N.q₂ % 4 = 3 ∧ HasSDSylow ↥X) ∨ (N.q₂ % 4 = 1 ∧ HasWreathedSylow ↥X) := by
    rcases hq₂4 with h1 | h3
    · right
      refine ⟨h1, ?_⟩
      have hq₁3 : N.q₁ % 4 = 3 := by omega
      obtain ⟨h₀, hh₀, hwa⟩ := hW.w₂_a
      exact hasWreathedSylow_mix hr cfg hq₁3 (fun g hg h2 => twoElt_mem_residual hg h2) hyH' hy1 hyodd
        (a := N.a) (w := N.w₂) (h₀ := h₀) hW.a_normH hW.a_cube haz hau hay
        (hSet.comm y hyK₁ N.w₂ hLoc.w₂_mem).symm hLoc.w₂_normH hLoc.w₂_sq hLoc.w₂_u hh₀ hwa
    · left
      refine ⟨h3, ?_⟩
      have hq₁1 : N.q₁ % 4 = 1 := by omega
      exact hasSDSylow_mix cfg hq₁1 h3 (fun g hg h2 => twoElt_mem_residual hg h2) hyH' hy1 hyodd
        (Kj := N.K₂) (fun x hx => (hSet.comm y hyK₁ x hx).symm) hFodd₂ e₂
  have hS : HasSDOrWreathedSylow ↥X := by
    rcases hshape with ⟨-, h⟩ | ⟨-, h⟩
    · exact hasSDOrWreathedSylow_iff.2 (Or.inl h)
    · exact hasSDOrWreathedSylow_iff.2 (Or.inr h)
  let z' : ↥X := ⟨N.z, hzX⟩
  have hz'2 : orderOf z' = 2 := by rw [← hz2]; exact Subgroup.orderOf_mk _ hzX
  have hzK' : z' ∈ N.K₂.subgroupOf X := hLoc.z_mem_K₂
  have hSL₂ : HasSL2Model ↥N.K₂ (fun q => q = p ^ n) :=
    ⟨F₂, inferInstance, hSet.finite₂, hSet.card₂.trans hn,
      ⟨e₂.trans (specialLinearGroupEquivStatedSL 2 F₂)⟩⟩
  have hK' := hasSL2Model_subgroupOf hK₂X hSL₂
  have hCK' : ∀ c : ↥X, c * z' = z' * c → ∀ k ∈ N.K₂.subgroupOf X, c * k * c⁻¹ ∈ N.K₂.subgroupOf X :=
    fun c hc k hk => (t2Ctx_all_normKW hSet hRem hLocW rfl rfl rfl rfl rfl (congrArg Subtype.val hc)).2
      (k : G) hk
  have hfus' : ∃ a' : ↥X, a' * z' * a'⁻¹ ≠ z' ∧ (a' * z' * a'⁻¹) * z' = z' * (a' * z' * a'⁻¹) := by
    obtain ⟨hau', haz', hazu'⟩ := cycle_facts hzz haz hau
    refine ⟨⟨N.a, haX⟩, ?_, ?_⟩
    · intro h
      have h' : N.a * N.z * N.a⁻¹ = N.z := congrArg Subtype.val h
      rw [haz'] at h'
      apply hu1
      have h5 : u * N.z = 1 * N.z := by rw [one_mul]; exact h'
      exact mul_right_cancel h5
    · apply Subtype.ext
      show (N.a * N.z * N.a⁻¹) * N.z = N.z * (N.a * N.z * N.a⁻¹)
      rw [haz']
      calc u * N.z * N.z = u * (N.z * N.z) := by group
        _ = u := by rw [hzz, mul_one]
        _ = N.z * (u * N.z) := by
            calc u = u * (N.z * N.z) := by rw [hzz, mul_one]
              _ = (u * N.z) * N.z := by group
              _ = (N.z * u) * N.z := by rw [hzu]
              _ = N.z * (u * N.z) := by group
  have hq₂pn : 3 ≤ p ^ n := by rw [← hn]; omega
  obtain ⟨E, hEn, hKE, hEodd, hE⟩ := layer_of_quotient hL hKX hS hp hp2 hq₂pn hz'2 hzK' hK' hCK' hfus'
  have := hEn
  obtain ⟨ε, hε, hEε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 ↥E ε (p ^ n) := by
    rcases hE with h | ⟨h3, -⟩
    · exact h
    · exfalso; rw [← hn] at h3; omega
  have hshape' : (p ^ n % 4 = 3 ∧ HasSDSylow ↥X) ∨ (p ^ n % 4 = 1 ∧ HasWreathedSylow ↥X) := by
    rw [← hn]; exact hshape
  have hε1 : ε = 1 := eps_eq_one_of_layer hp hp2 hε E hEodd hEε hshape'
  subst hε1
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥X)) := by
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥X)
    rwa [Nat.coprime_two_left] at hcop
  have : (pPrimeCore 2 ↥X).Normal := pPrimeCore_normal
  have hloc : ∀ B : Subgroup G, (∀ b ∈ B, b * y = y * b) →
      (∀ g : G, g * y = y * g → ∀ b ∈ B, g * b * g⁻¹ ∈ B) → Odd (Nat.card B) →
        ∀ b ∈ B, b * N.z = N.z * b → b * u = u * b := by
    intro B hBy hBn hBodd
    exact star_local_neg (z := N.z) (u := u) (y := y) (K₁ := N.K₁) (K₂ := N.K₂) (H := N.H)
      (C₁ := oPrimeResidualOf 2 (centralizer ({N.z} : Set G))) hz1 hu2 hSet.comm hLoc.z_mem_K₁
      hLoc.z_mem_K₂ e₂ hFodd₂ (by rw [hSet.card₂]; have := hLoc.q₂_ge; omega) hHc hLoc.z_mem_H
      hLoc.u_mem_H hyH' hyK₁ hLoc.H₁_cent hy2
      (fun f hf hodd x hx => (t2Ctx_odd_normK ctx hf hodd).2 x hx)
      (fun c hc x hx => ctx.C₁norm c (Subgroup.mem_centralizer_singleton_iff.2 hc) x hx)
      (ctx.SC₁ hLoc.u_mem_S) hSet.index_two B hBy hBn hBodd
  have hstar := hstar_of_local X hzX huX hXy hmemX hloc (pPrimeCore 2 ↥X) hNodd
  have hperf : ⁅N.K₂.subgroupOf X, N.K₂.subgroupOf X⁆ = N.K₂.subgroupOf X :=
    perfect_of_sl2 ((Subgroup.subgroupOfEquivOfLe hK₂X).trans e₂)
      (by rw [hSet.card₂]; omega)
  have hz'2' : z' * z' = 1 := Subtype.ext (by simpa using hzz)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hu'2 : (⟨u, huX⟩ : ↥X) * ⟨u, huX⟩ = 1 := Subtype.ext (by simpa using hu2)
  have hzu' : z' * (⟨u, huX⟩ : ↥X) = ⟨u, huX⟩ * z' := Subtype.ext hzu
  obtain ⟨P, hKP, hP⟩ := lift_core (pPrimeCore 2 ↥X) E hL3 hNodd hp hp2 (by rw [← hn]; exact h5) hEε
    (K := N.K₂.subgroupOf X) hperf hKE (z := z') (u := ⟨u, huX⟩) (a := ⟨N.a, haX⟩) hz'2' hz'1 hu'2
    (fun h => hLoc.u_ne.symm (congrArg Subtype.val h)) hzu' hzK' (Subtype.ext haz) (Subtype.ext hau)
    hstar
  refine ⟨P.map X.subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · intro x hx
    have : (⟨x, hK₂X hx⟩ : ↥X) ∈ P := hKP (Subgroup.mem_subgroupOf.2 hx)
    exact ⟨⟨x, hK₂X hx⟩, this, rfl⟩
  · have e := Subgroup.equivMapOfInjective P X.subtype X.subtype_injective
    rw [hn]
    rcases hP with h | h
    · exact Or.inl (isSLnEps_of_equiv e h)
    · exact Or.inr (isLnEps_of_equiv e h)

end Core

end CFSG.GH74.GLS.Stage4.Rest
