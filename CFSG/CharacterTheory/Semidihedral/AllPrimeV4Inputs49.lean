module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts
public import CFSG.LocalAnalysis.ABGTheoremB.V4Inputs
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.Semidihedral.AllPrime

noncomputable section

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.AllPrime.QDTI
open CFSG.Wreathed.OriginalAllPrime.TIFacts CFSG.QuasiDihedralFusion
open Matrix CFSG.Semidihedral.MatrixCoverData
open scoped Pointwise

section Matrix

variable {F : Type} [Field F]

private theorem qd49_rootGroup_inf_neg (h2 : (2 : F) ≠ 0) {l : F} (hl0 : l ≠ 0) :
    rootGroup l ⊓ rootGroup (-l) = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨hX, hX'⟩
  rw [Subgroup.mem_bot]
  obtain ⟨h0, h1⟩ := (mem_rootGroup_iff l X).mp hX
  obtain ⟨h0', h1'⟩ := (mem_rootGroup_iff (-l) X).mp hX'
  have h2l : (2 : F) * l ≠ 0 := mul_ne_zero h2 hl0
  have e00 : X.1 0 0 = 1 := by
    have : (2 * l) * (X.1 0 0 - 1) = 0 := by linear_combination h0 - h0'
    have := (mul_eq_zero.mp this).resolve_left h2l
    linear_combination this
  have e10 : X.1 1 0 = 0 := by
    have : (2 * l) * X.1 1 0 = 0 := by linear_combination h1 - h1'
    exact (mul_eq_zero.mp this).resolve_left h2l
  have e01 : X.1 0 1 = 0 := by linear_combination h0 - l * e00
  have e11 : X.1 1 1 = 1 := by linear_combination h1 - l * e10
  apply sl_ext <;> simp [sl_one_val, e00, e10, e01, e11]

private theorem qd49_inf_le_Wsl [Finite F] (hodd : Odd (Nat.card F)) (a : Fˣ) {p : ℕ}
    [CharP F p] (hp : p.Prime) (hpW : ¬ p ∣ Nat.card (Wsl a)) {l : F}
    (hl : l ^ 2 = -(a : F)) :
    (Wsl a ⊔ rootGroup l) ⊓ (Wsl a ⊔ rootGroup (-l)) ≤ Wsl a := by
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hl.symm)
  have hl' : (-l) ^ 2 = -(a : F) := by rw [neg_sq]; exact hl
  have hnorm : ∀ l' : F, l' ^ 2 = -(a : F) →
      Wsl a ≤ Subgroup.normalizer (rootGroup l' : Set (SL F)) := by
    intro l' hl'' w hw
    apply Subgroup.mem_normalizer_fintype
    intro X hX
    exact torus_conj_mem_rootGroup a hl'' (Wsl_le_torus a hw) hX
  have hdec : ∀ l' : F, l' ^ 2 = -(a : F) → ∀ x ∈ Wsl a ⊔ rootGroup l',
      ∃ k ∈ rootGroup l', ∃ w ∈ Wsl a, x = k * w := by
    intro l' hl'' x hx
    have hx' : x ∈ ((rootGroup l' ⊔ Wsl a : Subgroup (SL F)) : Set (SL F)) := by
      rw [sup_comm]
      exact hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hnorm l' hl'')] at hx'
    obtain ⟨k, hk, w, hw, rfl⟩ := hx'
    exact ⟨k, hk, w, hw, rfl⟩
  rintro x ⟨hx₁, hx₂⟩
  obtain ⟨k₁, hk₁, w₁, hw₁, rfl⟩ := hdec l hl x hx₁
  have hk₁' : k₁ ∈ Wsl a ⊔ rootGroup (-l) := by
    have := (Wsl a ⊔ rootGroup (-l)).mul_mem hx₂
      ((Wsl a ⊔ rootGroup (-l)).inv_mem (Subgroup.mem_sup_left hw₁))
    simpa using this
  obtain ⟨k₂, hk₂, w₂, hw₂, hk₁eq⟩ := hdec (-l) hl' k₁ hk₁'
  have hpow : ∀ m : ℕ, ∃ k ∈ rootGroup (-l), (k₂ * w₂) ^ m = k * w₂ ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, (rootGroup (-l)).one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨k, hk, hkm⟩ := ih
      refine ⟨k * (w₂ ^ m * k₂ * (w₂ ^ m)⁻¹), (rootGroup (-l)).mul_mem hk
        (torus_conj_mem_rootGroup a hl' ((Torus F a).pow_mem (Wsl_le_torus a hw₂) m) hk₂), ?_⟩
      rw [pow_succ, hkm]
      group
  obtain ⟨k, hk, hkp⟩ := hpow p
  have hk₁p : k₁ ^ p = 1 := rootGroup_pow_char p hk₁
  rw [← hk₁eq, hk₁p] at hkp
  have hw₂p1 : w₂ ^ p = 1 := by
    have hw₂p : w₂ ^ p = k⁻¹ := eq_inv_of_mul_eq_one_right hkp.symm
    have hmem : w₂ ^ p ∈ rootGroup (-l) ⊓ Torus F a :=
      ⟨hw₂p ▸ (rootGroup (-l)).inv_mem hk, (Torus F a).pow_mem (Wsl_le_torus a hw₂) p⟩
    rwa [rootGroup_inf_torus a h2 hl', Subgroup.mem_bot] at hmem
  have hw₂1 : w₂ = 1 := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hw₂p1) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      apply hpW
      rw [← h]
      exact Subgroup.orderOf_dvd_natCard _ hw₂
  rw [hw₂1, mul_one] at hk₁eq
  have hk₁1 : k₁ = 1 := by
    have hmem : k₁ ∈ rootGroup l ⊓ rootGroup (-l) := ⟨hk₁, hk₁eq ▸ hk₂⟩
    rwa [qd49_rootGroup_inf_neg h2 hl0, Subgroup.mem_bot] at hmem
  rw [hk₁1, one_mul]
  exact hw₁

end Matrix

section Model

variable {F : Type} [Field F] {a : Fˣ} {A : Subgroup (F ≃+* F)}
  {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a}

private def qd49_actOnHom (m : OriginalH F a A hfix) : SL F →* SL F where
  toFun := actOn m
  map_one' := by
    apply slIn_injective (a := a) (A := A) (hfix := hfix)
    rw [← conj_slIn, map_one, mul_one, mul_inv_cancel]
  map_mul' x y := by
    apply slIn_injective (a := a) (A := A) (hfix := hfix)
    rw [map_mul, ← conj_slIn, ← conj_slIn, ← conj_slIn, map_mul]
    group

private theorem qd49_actOnHom_apply (m : OriginalH F a A hfix) (X : SL F) :
    qd49_actOnHom m X = actOn m X := rfl

private theorem qd49_actOn_mem_Wsl [Finite F] (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    {m : OriginalH F a A hfix} (hm : ∀ c ∈ cenU F a A hfix, m * c * m⁻¹ ∈ cenU F a A hfix)
    {X : SL F} (hX : X ∈ Wsl a) : actOn m X ∈ Wsl a := by
  obtain ⟨hXT, hXo⟩ := (mem_Wsl_iff hodd a ha X).mp hX
  have hC : originalSlInH F a A hfix (actOn m X) ∈ cenU F a A hfix := by
    rw [← conj_slIn]
    exact hm _ ((slIn_mem_cenU_iff X).mpr hXT)
  refine (mem_Wsl_iff hodd a ha _).mpr ⟨(slIn_mem_cenU_iff _).mp hC, ?_⟩
  have h1 : orderOf (originalSlInH F a A hfix (actOn m X)) = orderOf X := by
    rw [← conj_slIn, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
      orderOf_injective _ slIn_injective]
  rw [orderOf_injective _ slIn_injective] at h1
  rw [h1]
  exact hXo

private theorem qd49_le_cenU [Finite F] (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hq : 7 ≤ Nat.card F) (hA : Odd (Nat.card A)) {p : ℕ} [CharP F p] (hp : p.Prime)
    (hpW : ¬ p ∣ Nat.card (Wsl a))
    (hz : ∀ m : OriginalH F a A hfix, m * originalZ F a A hfix = originalZ F a A hfix * m)
    {Y : Subgroup (OriginalH F a A hfix)} (hYodd : Odd (Nat.card Y))
    (huY : originalU F a A hfix ∈ Subgroup.normalizer (Y : Set (OriginalH F a A hfix)))
    {h : OriginalH F a A hfix} (hhY : h ∈ Subgroup.normalizer (Y : Set (OriginalH F a A hfix)))
    (hh : h * originalU F a A hfix * h⁻¹ = originalZ F a A hfix * originalU F a A hfix)
    (hWY : (Wsl a).map (originalSlInH F a A hfix) ≤ Y) : Y ≤ cenU F a A hfix := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hzz : originalZ F a A hfix * originalZ F a A hfix = 1 := by
    have h1 := pow_orderOf_eq_one (originalZ F a A hfix)
    rwa [ActualFourGroupAlignment.originalZ_order F a A hfix hodd, pow_two] at h1
  have hzinv : (originalZ F a A hfix)⁻¹ = originalZ F a A hfix :=
    inv_eq_of_mul_eq_one_right hzz
  have hYn : ∀ g ∈ Subgroup.normalizer (Y : Set (OriginalH F a A hfix)), ∀ m ∈ Y,
      g * m * g⁻¹ ∈ Y := fun g hg m hm => (Subgroup.mem_normalizer_iff.mp hg m).mp hm
  set R : Subgroup (SL F) := Y.comap (originalSlInH F a A hfix) with hR
  have hRodd : Odd (Nat.card R) := by
    have hle : R.map (originalSlInH F a A hfix) ≤ Y := Subgroup.map_comap_le _ _
    rw [← Subgroup.card_map_of_injective (f := originalSlInH F a A hfix) slIn_injective]
    exact hYodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hWR : Wsl a ≤ R := fun X hX => hWY ⟨X, hX, rfl⟩
  have hβR : ∀ x ∈ R, beta F a x ∈ R := by
    intro x hx
    change originalSlInH F a A hfix (beta F a x) ∈ Y
    rw [← conj_u_slIn]
    exact hYn _ huY _ hx
  have hhC : ∀ c ∈ cenU F a A hfix, h * c * h⁻¹ ∈ cenU F a A hfix := by
    intro c hc
    rw [cenU, Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have h1 : (h * c * h⁻¹) * (originalZ F a A hfix * originalU F a A hfix) =
        (originalZ F a A hfix * originalU F a A hfix) * (h * c * h⁻¹) := by
      rw [← hh]
      calc h * c * h⁻¹ * (h * originalU F a A hfix * h⁻¹) =
          h * (c * originalU F a A hfix) * h⁻¹ := by group
        _ = h * (originalU F a A hfix * c) * h⁻¹ := by rw [hc]
        _ = h * originalU F a A hfix * h⁻¹ * (h * c * h⁻¹) := by group
    have h3 : originalZ F a A hfix * ((h * c * h⁻¹) * originalU F a A hfix) =
        originalZ F a A hfix * (originalU F a A hfix * (h * c * h⁻¹)) := by
      calc originalZ F a A hfix * ((h * c * h⁻¹) * originalU F a A hfix) =
          (h * c * h⁻¹) * (originalZ F a A hfix * originalU F a A hfix) := by
            rw [← mul_assoc, ← hz (h * c * h⁻¹), mul_assoc]
        _ = (originalZ F a A hfix * originalU F a A hfix) * (h * c * h⁻¹) := h1
        _ = originalZ F a A hfix * (originalU F a A hfix * (h * c * h⁻¹)) := by
            rw [mul_assoc]
    exact mul_left_cancel h3
  have hRW : R ≤ Wsl a := by
    rcases odd_subgroup_structure hodd a ha hq hRodd hWR hβR with hle | ⟨l, hl, hle⟩
    · exact hle
    · have hmap : Wsl a ⊔ rootGroup l ≤
          (Wsl a ⊔ rootGroup (-l)).comap (qd49_actOnHom h) := by
        refine sup_le (fun w hw => ?_) (fun k hk => ?_)
        · exact Subgroup.mem_sup_left (qd49_actOn_mem_Wsl hodd ha hhC hw)
        · refine Subgroup.mem_sup_right ?_
          have hmem : originalSlInH F a A hfix (actOn h k) ∈ rootM F a A hfix (-l) := by
            rw [← conjSub_rootM hA hl hh, ← conj_slIn]
            exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
          obtain ⟨k', hk', hk'eq⟩ := hmem
          rw [qd49_actOnHom_apply, ← slIn_injective hk'eq]
          exact hk'
      have hle' : R ≤ Wsl a ⊔ rootGroup (-l) := by
        intro x hx
        have hx' : actOn h⁻¹ x ∈ R := by
          change originalSlInH F a A hfix (actOn h⁻¹ x) ∈ Y
          rw [← conj_slIn]
          exact hYn h⁻¹ ((Subgroup.normalizer _).inv_mem hhY) _ hx
        have hxx : actOn h (actOn h⁻¹ x) = x := by
          apply slIn_injective (a := a) (A := A) (hfix := hfix)
          rw [← conj_slIn, ← conj_slIn]
          group
        have := hmap (hle hx')
        rwa [Subgroup.mem_comap, qd49_actOnHom_apply, hxx] at this
      exact (le_inf hle hle').trans (qd49_inf_le_Wsl hodd a hp hpW hl)
  have hWcard : 3 ≤ Nat.card (Wsl a) := by
    rw [card_Wsl hodd a ha]
    exact torusSize_half_ge_three hq
  have hW1 : Wsl a ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hWcard
    omega
  obtain ⟨⟨w₀, hw₀⟩, hw₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
  have hw₀1 : w₀ ≠ 1 := fun h => hw₀ne (Subtype.ext h)
  obtain ⟨hw₀T, -⟩ := (mem_Wsl_iff hodd a ha w₀).mp hw₀
  intro m hm
  obtain ⟨k, hk, hmk⟩ := exists_cenU_factor m
  obtain ⟨X, hX⟩ : ∃ X, X = m.left.left := ⟨_, rfl⟩
  rw [← hX] at hmk
  have hw₀'T : actOn k w₀ ∈ Torus F a := by
    rw [← slIn_mem_cenU_iff (hfix := hfix), ← conj_slIn]
    exact (cenU F a A hfix).mul_mem ((cenU F a A hfix).mul_mem hk
      ((slIn_mem_cenU_iff w₀).mpr hw₀T)) ((cenU F a A hfix).inv_mem hk)
  have hx₁R : actOn m w₀ ∈ R := by
    change originalSlInH F a A hfix (actOn m w₀) ∈ Y
    rw [← conj_slIn]
    exact Y.mul_mem (Y.mul_mem hm (hWR hw₀)) (Y.inv_mem hm)
  obtain ⟨hx₁T, hx₁o⟩ := (mem_Wsl_iff hodd a ha _).mp (hRW hx₁R)
  have hx₁1 : actOn m w₀ ≠ 1 := by
    intro h1
    apply hw₀1
    apply slIn_injective (a := a) (A := A) (hfix := hfix)
    have e := conj_slIn m w₀
    rw [h1, map_one] at e
    rw [map_one]
    calc originalSlInH F a A hfix w₀ =
        m⁻¹ * (m * originalSlInH F a A hfix w₀ * m⁻¹) * m := by group
      _ = 1 := by rw [e]; group
  have hx₁10 : (actOn m w₀).1 1 0 ≠ 0 := fun h0 =>
    torus_entries_ne_zero_of_odd a hx₁T hx₁o hx₁1 (by rw [h0, mul_zero])
  have hconj : X * actOn k w₀ = actOn m w₀ * X := by
    apply slIn_injective (a := a) (A := A) (hfix := hfix)
    rw [map_mul, map_mul, ← conj_slIn, ← conj_slIn, hmk]
    group
  rcases torus_or_anticomm_of_conj a h2 hx₁T hw₀'T hx₁10 hconj with hXT | hXA
  · rw [hmk]
    exact (cenU F a A hfix).mul_mem ((slIn_mem_cenU_iff X).mpr hXT) hk
  ·
    have hβX : beta F a X = OddFieldSL2.minusIdentity F * X := (beta_eq_neg_iff a X).mpr hXA
    have h1 : originalU F a A hfix * originalSlInH F a A hfix X * (originalU F a A hfix)⁻¹ =
        originalZ F a A hfix * originalSlInH F a A hfix X := by
      rw [conj_u_slIn, hβX, map_mul, originalZ_eq]
    have hzu : originalSlInH F a A hfix X * originalU F a A hfix *
        (originalSlInH F a A hfix X)⁻¹ = originalZ F a A hfix * originalU F a A hfix := by
      calc originalSlInH F a A hfix X * originalU F a A hfix *
            (originalSlInH F a A hfix X)⁻¹ =
          (originalZ F a A hfix)⁻¹ * (originalZ F a A hfix * originalSlInH F a A hfix X) *
            originalU F a A hfix * (originalSlInH F a A hfix X)⁻¹ := by group
        _ = (originalZ F a A hfix)⁻¹ * (originalU F a A hfix * originalSlInH F a A hfix X *
            (originalU F a A hfix)⁻¹) * originalU F a A hfix *
            (originalSlInH F a A hfix X)⁻¹ := by rw [h1]
        _ = (originalZ F a A hfix)⁻¹ * originalU F a A hfix := by group
        _ = originalZ F a A hfix * originalU F a A hfix := by rw [hzinv]
    have hku : k * originalU F a A hfix = originalU F a A hfix * k :=
      Subgroup.mem_centralizer_singleton_iff.mp hk
    have hmu : m * originalU F a A hfix * m⁻¹ =
        originalZ F a A hfix * originalU F a A hfix := by
      rw [hmk]
      calc originalSlInH F a A hfix X * k * originalU F a A hfix *
            (originalSlInH F a A hfix X * k)⁻¹ =
          originalSlInH F a A hfix X * (k * originalU F a A hfix) * k⁻¹ *
            (originalSlInH F a A hfix X)⁻¹ := by group
        _ = originalSlInH F a A hfix X * (originalU F a A hfix * k) * k⁻¹ *
            (originalSlInH F a A hfix X)⁻¹ := by rw [hku]
        _ = originalSlInH F a A hfix X * originalU F a A hfix *
            (originalSlInH F a A hfix X)⁻¹ := by group
        _ = originalZ F a A hfix * originalU F a A hfix := hzu
    have hmz : m * originalZ F a A hfix * m⁻¹ = originalZ F a A hfix := by
      rw [hz m, mul_inv_cancel_right]
    have hm2 : m ^ 2 ∈ cenU F a A hfix := by
      rw [cenU, Subgroup.mem_centralizer_singleton_iff]
      have e : m ^ 2 * originalU F a A hfix * (m ^ 2)⁻¹ = originalU F a A hfix := by
        calc m ^ 2 * originalU F a A hfix * (m ^ 2)⁻¹ =
            m * (m * originalU F a A hfix * m⁻¹) * m⁻¹ := by rw [pow_two]; group
          _ = m * (originalZ F a A hfix * originalU F a A hfix) * m⁻¹ := by rw [hmu]
          _ = (m * originalZ F a A hfix * m⁻¹) * (m * originalU F a A hfix * m⁻¹) := by
              group
          _ = originalZ F a A hfix * (originalZ F a A hfix * originalU F a A hfix) := by
              rw [hmz, hmu]
          _ = originalU F a A hfix := by rw [← mul_assoc, hzz, one_mul]
      calc m ^ 2 * originalU F a A hfix =
          m ^ 2 * originalU F a A hfix * (m ^ 2)⁻¹ * m ^ 2 := (inv_mul_cancel_right _ _).symm
        _ = originalU F a A hfix * m ^ 2 := by rw [e]
    have hmo : Odd (orderOf m) := by
      have h1 := orderOf_dvd_natCard (⟨m, hm⟩ : Y)
      rw [Subgroup.orderOf_mk] at h1
      exact hYodd.of_dvd_nat h1
    obtain ⟨c, hc⟩ := hmo
    have hmpow : m = (m ^ 2) ^ (c + 1) := by
      rw [← pow_mul, show 2 * (c + 1) = orderOf m + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hmpow]
    exact (cenU F a A hfix).pow_mem hm2 _

end Model

section Transport

variable {G : Type} [Group G] [Finite G]

private theorem qd49_odd_card_of_forall {H : Subgroup G} (hH : ∀ x ∈ H, Odd (orderOf x)) :
    Odd (Nat.card H) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card H := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have h1 := hH x x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact absurd h1 (by decide)

private theorem qd49_Wsl_le_map_W {σ : Setting G} {F : Type} [Field F] [Finite F]
    {A : Subgroup (F ≃+* F)} {a : Fˣ} {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a}
    {φ : σ.N →* OriginalH F a A hfix}
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix))
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) {J : Subgroup G} (hJ : σ.IsV21Layer J)
    {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    (Wsl a).map (originalSlInH F a A hfix) ≤ (W.subgroupOf σ.N).map φ := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hJN : J ≤ σ.N := hJ.le.trans hφ.L₀_le
  have hpON : pCoreIn σ.p σ.N ≤ σ.ON := hJ.inf_eq ▸ inf_le_right
  have hpbot : ((pCoreIn σ.p σ.N).subgroupOf σ.N).map φ = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [hφ.ker_eq]; exact subgroupOf_mono_of_le hpON _)
  have hmapW : (W.subgroupOf σ.N).map φ =
      ((oddCoreIn σ.C ⊓ J : Subgroup G).subgroupOf σ.N).map φ := by
    have h1 : ((W ⊔ pCoreIn σ.p σ.N : Subgroup G).subgroupOf σ.N).map φ =
        (W.subgroupOf σ.N).map φ := by
      rw [Subgroup.subgroupOf_sup (hW.1.trans hJN) (hpON.trans σ.ON_le_N), Subgroup.map_sup,
        hpbot, sup_bot_eq]
    have h2 : (((oddCoreIn σ.C ⊓ J) ⊔ pCoreIn σ.p σ.N : Subgroup G).subgroupOf σ.N).map φ =
        ((oddCoreIn σ.C ⊓ J : Subgroup G).subgroupOf σ.N).map φ := by
      rw [Subgroup.subgroupOf_sup (inf_le_right.trans hJN) (hpON.trans σ.ON_le_N),
        Subgroup.map_sup, hpbot, sup_bot_eq]
    rw [← h1, hW.2.2.2, h2]
  have hmapJ : (J.subgroupOf σ.N).map φ = layerM F a A hfix := by
    rw [← hφ.map_L₀, hJ.sup_eq, Subgroup.subgroupOf_sup hJN σ.ON_le_N, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq hφ.ker_eq.symm), sup_bot_eq]
  rw [hmapW]
  rintro _ ⟨X, hX, rfl⟩
  have hXT : X ∈ Torus F a := Wsl_le_torus a hX
  have hXM : originalSlInH F a A hfix X ∈ (J.subgroupOf σ.N).map φ := by
    rw [hmapJ]
    exact ⟨X, rfl⟩
  obtain ⟨g, hg, hgX⟩ := hXM
  have hx₂ : (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N) * ⟨σ.x₂, hφ.x₂_mem⟩ = 1 := Subtype.ext hφ.x₂_mul_self
  have hU : ∀ v ∈ J.subgroupOf σ.N,
      (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N) * v * (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)⁻¹ ∈ J.subgroupOf σ.N := by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hJ.normal hφ.x₂_mem) v).mp hv
    simpa using this
  have hc : φ g * φ ⟨σ.x₂, hφ.x₂_mem⟩ = φ ⟨σ.x₂, hφ.x₂_mem⟩ * φ g := by
    rw [hφ.map_x₂, hgX]
    exact Subgroup.mem_centralizer_singleton_iff.mp ((slIn_mem_cenU_iff X).mpr hXT)
  obtain ⟨v, hvJ, hvφ, hvc⟩ := exists_commute_lift φ hφ.odd_card_ker hx₂ hU hg hc
  have hvC : (v : G) ∈ σ.C := (mem_C_iff σ v.2).mpr (congrArg Subtype.val hvc)
  set K₀ : Subgroup G := (((σ.C ⊓ J).subgroupOf σ.N) ⊓
    ((Wsl a).map (originalSlInH F a A hfix)).comap φ).map σ.N.subtype with hK₀
  have hK₀C : K₀ ≤ σ.C := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp hk.1).1
  have hK₀n : σ.C ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro c hcC
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨k, hk, rfl⟩
    have hcN : c ∈ σ.N := C_le_N σ hcC
    obtain ⟨hk1, hk2⟩ := hk
    have hkCJ : (k : G) ∈ σ.C ⊓ J := Subgroup.mem_subgroupOf.mp hk1
    have hmem1 : (⟨c, hcN⟩ * k * (⟨c, hcN⟩ : σ.N)⁻¹ : σ.N) ∈ (σ.C ⊓ J).subgroupOf σ.N := by
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨σ.C.mul_mem (σ.C.mul_mem hcC hkCJ.1) (σ.C.inv_mem hcC),
        (Subgroup.mem_normalizer_iff.mp (hJ.normal hcN) k).mp hkCJ.2⟩
    have hmem2 : (⟨c, hcN⟩ * k * (⟨c, hcN⟩ : σ.N)⁻¹ : σ.N) ∈
        ((Wsl a).map (originalSlInH F a A hfix)).comap φ := by
      have hcU : φ ⟨c, hcN⟩ ∈ cenU F a A hfix := by
        rw [cenU, ← hφ.map_C]
        exact ⟨⟨c, hcN⟩, hcC, rfl⟩
      obtain ⟨Y, hY, hYk⟩ := hk2
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, ← hYk, conj_slIn]
      exact ⟨_, qd49_actOn_mem_Wsl hodd ha (fun c' hc' => (cenU F a A hfix).mul_mem
        ((cenU F a A hfix).mul_mem hcU hc') ((cenU F a A hfix).inv_mem hcU)) hY, rfl⟩
    exact ⟨_, ⟨hmem1, hmem2⟩, by simp⟩
  have hK₀odd : Odd (Nat.card K₀) := by
    apply qd49_odd_card_of_forall
    rintro _ ⟨k, ⟨-, Y, hY, hYk⟩, rfl⟩
    obtain ⟨-, hYo⟩ := (mem_Wsl_iff hodd a ha Y).mp hY
    have hφk : orderOf (φ k) = orderOf Y := by
      rw [← hYk, orderOf_injective _ slIn_injective]
    have hker : k ^ orderOf Y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hφk, pow_orderOf_eq_one]
    rw [hφ.ker_eq, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hker
    have hko : Odd (orderOf ((k : G) ^ orderOf Y)) :=
      (odd_card_oddCoreIn σ.N).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hker)
    have hdvd : orderOf (k : G) ∣ orderOf Y * orderOf ((k : G) ^ orderOf Y) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    exact (hYo.mul hko).of_dvd_nat hdvd
  have hvO : (v : G) ∈ oddCoreIn σ.C :=
    le_oddCoreIn hK₀C hK₀n hK₀odd ⟨v, ⟨Subgroup.mem_subgroupOf.mpr
      ⟨hvC, Subgroup.mem_subgroupOf.mp hvJ⟩, X, hX, (hvφ.trans hgX).symm⟩, rfl⟩
  exact ⟨v, Subgroup.mem_subgroupOf.mpr ⟨hvO, Subgroup.mem_subgroupOf.mp hvJ⟩, hvφ.trans hgX⟩

private theorem qd49_lemmaII49Input_of_modelMap {σ : Setting G} (hσv : σ.IsValid) {F : Type}
    [Field F] [Finite F] {A : Subgroup (F ≃+* F)} {a : Fˣ}
    {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a} {φ : σ.N →* OriginalH F a A hfix}
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix))
    (hcard : Nat.card F = σ.p ^ σ.f) (hA : Odd (Nat.card A)) (ha : ¬IsSquare a)
    (hz : φ ⟨σ.x, σ.x_mem_N⟩ = originalZ F a A hfix)
    (hd : ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x * σ.x₂)
    {J : Subgroup G} (hJ : σ.IsV21Layer J) : V4.LemmaII49Input σ J := by
  intro W hW Y hYN hYodd hDY hWY
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hp := hσv.p_prime
  have hp2 := hσv.p_ne_two
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have : CharP F σ.p := qdti_charP hp hcard
  have hq7 : 7 ≤ Nat.card F := by
    have h5 := hσv.five_lt_q
    have hq : Nat.card F = σ.q := hcard
    rcases hodd with ⟨k, hk⟩
    omega
  have hpW : ¬ σ.p ∣ Nat.card (Wsl a) := by
    rw [card_Wsl hodd a ha]
    intro hdvd
    have hdvd' : σ.p ∣ torusSize (Nat.card F) :=
      hdvd.trans (Nat.div_dvd_of_dvd ⟨_, torusSize_two_mul_half hodd⟩)
    have hpq : σ.p ∣ Nat.card F := by
      rw [hcard]
      exact dvd_pow_self _ (by have := hσv.one_le_f; omega)
    unfold torusSize at hdvd'
    split_ifs at hdvd' with h4
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp hdvd'))
    · have hq1 : 1 ≤ Nat.card F := Nat.card_pos
      have h1 := Nat.dvd_sub hpq hdvd'
      rw [Nat.sub_sub_self hq1] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hzc : ∀ m : OriginalH F a A hfix,
      m * originalZ F a A hfix = originalZ F a A hfix * m := by
    intro m
    obtain ⟨g, rfl⟩ := hφ.surjective m
    rw [← hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((σ.mem_N_iff g).mp g.2)
  obtain ⟨d, hdD, hdx⟩ := hd
  have hDN : σ.D ≤ σ.N := σ.D_le_N hσv
  set Yb := (Y.subgroupOf σ.N).map φ with hYb
  have hYbodd : Odd (Nat.card Yb) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ φ)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv]
  have hDYb : (σ.D.subgroupOf σ.N).map φ ≤
      Subgroup.normalizer (Yb : Set (OriginalH F a A hfix)) :=
    hφ.le_normalizer_map hYN hDY
  have huY : originalU F a A hfix ∈ Subgroup.normalizer (Yb : Set (OriginalH F a A hfix)) := by
    rw [← hφ.map_x₂]
    exact hDYb ⟨⟨σ.x₂, hφ.x₂_mem⟩, Subgroup.mem_subgroupOf.mpr (σ.T_le_D hσv σ.x₂_mem_T), rfl⟩
  have hhY : φ ⟨d, hDN hdD⟩ ∈ Subgroup.normalizer (Yb : Set (OriginalH F a A hfix)) :=
    hDYb ⟨⟨d, hDN hdD⟩, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩
  have hh : φ ⟨d, hDN hdD⟩ * originalU F a A hfix * (φ ⟨d, hDN hdD⟩)⁻¹ =
      originalZ F a A hfix * originalU F a A hfix := by
    have e : (⟨d, hDN hdD⟩ * ⟨σ.x₂, hφ.x₂_mem⟩ * (⟨d, hDN hdD⟩ : σ.N)⁻¹ : σ.N) =
        ⟨σ.x, σ.x_mem_N⟩ * ⟨σ.x₂, hφ.x₂_mem⟩ := Subtype.ext (by simpa using hdx)
    have h1 := congrArg φ e
    simp only [map_mul, map_inv, hφ.map_x₂, hz] at h1
    exact h1
  have hWYb : (Wsl a).map (originalSlInH F a A hfix) ≤ Yb :=
    (qd49_Wsl_le_map_W hφ hodd ha hJ hW).trans (Subgroup.map_mono (subgroupOf_mono_of_le hWY _))
  have hYbC := qd49_le_cenU hodd ha hq7 hA hp hpW hzc hYbodd huY hhY hh hWYb
  intro y hy
  have hyN := hYN hy
  have hmem : φ ⟨y, hyN⟩ ∈ (σ.C.subgroupOf σ.N).map φ := by
    rw [hφ.map_C]
    exact hYbC ⟨⟨y, hyN⟩, hy, rfl⟩
  obtain ⟨c, hc, hcy⟩ := hmem
  have hk : c⁻¹ * ⟨y, hyN⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel]
  rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hk
  have hyc : y = (c : G) * ((c⁻¹ * ⟨y, hyN⟩ : σ.N) : G) := by simp
  rw [hyc]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hc) hk

end Transport

private theorem qd49_exists_D_conj {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    ∃ d ∈ (frontierSetting S fS t p f).D,
      d * (frontierSetting S fS t p f).x₂ * d⁻¹ =
        (frontierSetting S fS t p f).x * (frontierSetting S fS t p f).x₂ := by
  set ι := FocalFusion.ambientHom n (S : Subgroup G) fS with hι
  have := sdFourSubgroup_isKleinFour hn
  refine ⟨ι (r n ^ 2 ^ (n - 3)), ?_, ?_⟩
  · rw [frontierSetting_D hn S fS t ht p f]
    exact Subgroup.mem_map_of_mem _ (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.1
  · change ι (r n ^ 2 ^ (n - 3)) * ι (s n) * (ι (r n ^ 2 ^ (n - 3)))⁻¹ = t * ι (s n)
    have hconj := sd_s_conj_quarter hn
    have e : r n ^ 2 ^ (n - 2) = r n ^ 2 ^ (n - 3) * r n ^ 2 ^ (n - 3) := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      congr 2
      omega
    have hw : r n ^ 2 ^ (n - 3) * s n * (r n ^ 2 ^ (n - 3))⁻¹ = r n ^ 2 ^ (n - 2) * s n := by
      calc r n ^ 2 ^ (n - 3) * s n * (r n ^ 2 ^ (n - 3))⁻¹
          = r n ^ 2 ^ (n - 3) * (s n * r n ^ 2 ^ (n - 3) * (s n)⁻¹)⁻¹ * s n := by group
        _ = r n ^ 2 ^ (n - 2) * s n := by rw [hconj, inv_inv, e]
    rw [← map_inv, ← map_mul, ← map_mul, hw, map_mul, map_pow, ht]
    rfl

theorem frontier_lemmaII49Input {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, (frontierSetting S fS t p f).IsV21Layer J →
      V4.LemmaII49Input (frontierSetting S fS t p f) J := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, hA, -, ha, hPsiZ, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hσv := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  have hz : frontierModelMap S fS t p f Psi ⟨(frontierSetting S fS t p f).x,
      (frontierSetting S fS t p f).x_mem_N⟩ = originalZ F a A hfix := by
    change Psi.symm (nu t ⟨t, _⟩) = originalZ F a A hfix
    rw [MulEquiv.symm_apply_eq, hPsiZ]
    rfl
  intro J hJ
  exact qd49_lemmaII49Input_of_modelMap hσv hφ hcard hA ha hz
    (qd49_exists_D_conj hn S fS t ht p f) hJ

end

end CFSG.Semidihedral.AllPrime
