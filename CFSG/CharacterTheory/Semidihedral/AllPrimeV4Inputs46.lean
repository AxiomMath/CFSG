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
open scoped Pointwise commutatorElement

private theorem qd46_le_normalizer_commutator {G₀ : Type*} [Group G₀] [Finite G₀]
    (H₁ H₂ : Subgroup G₀) : H₂ ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G₀) : Set G₀) := by
  intro t ht
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have key : ⁅H₁, H₂⁆ ≤ (⁅H₁, H₂⁆ : Subgroup G₀).comap (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    change t * ⁅h, k⁆ * t⁻¹ ∈ ⁅H₁, H₂⁆
    have e : t * ⁅h, k⁆ * t⁻¹ = ⁅h, t⁆⁻¹ * ⁅h, t * k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hh ht))
      (Subgroup.commutator_mem_commutator hh (H₂.mul_mem ht hk))
  exact key hx

private theorem qd46_commutator_subgroupOf {G₀ : Type*} [Group G₀] {H₁ H₂ K : Subgroup G₀}
    (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) :
    ⁅H₁.subgroupOf K, H₂.subgroupOf K⁆ = (⁅H₁, H₂⁆ : Subgroup G₀).subgroupOf K := by
  have hc : ⁅H₁, H₂⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (h₁ hx) (h₂ hy)) (K.inv_mem (h₁ hx))) (K.inv_mem (h₂ hy))
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left h₁, inf_of_le_left h₂, inf_of_le_left hc]

section Matrix

variable {F : Type} [Field F]

private theorem qd46_odd_subgroup_decomp [Finite F] (hodd : Odd (Nat.card F)) (a : Fˣ)
    (ha : ¬IsSquare a) {R : Subgroup (SL F)} (hRodd : Odd (Nat.card R))
    (hRW : R ⊓ Wsl a ≠ ⊥) (hβ : ∀ x ∈ R, beta F a x ∈ R) :
    R ≤ Wsl a ∨ ∃ l : F, l ^ 2 = -(a : F) ∧
      ∀ x ∈ R, ∃ k ∈ rootGroup l, ∃ w ∈ Wsl a, x = k * w := by
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  set W₁ := R ⊓ Wsl a with hW₁
  by_cases hRW₁ : R ≤ W₁
  · exact Or.inl (hRW₁.trans inf_le_right)
  right
  have hRo : ∀ x ∈ R, Odd (orderOf x) := by
    intro x hx
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : R)
    rw [Subgroup.orderOf_mk] at h
    exact hRodd.of_dvd_nat h
  obtain ⟨⟨w₀, hw₀⟩, hw₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRW
  have hw₀1 : w₀ ≠ 1 := fun h => hw₀ne (Subtype.ext h)
  obtain ⟨hw₀T, hw₀o⟩ := (mem_Wsl_iff hodd a ha w₀).mp hw₀.2
  have hw₀xy := torus_entries_ne_zero_of_odd a hw₀T hw₀o hw₀1
  have hfrob : ∀ g ∈ R, g ∉ W₁ → ∀ x ∈ W₁, g⁻¹ * x * g ∈ W₁ → x = 1 := by
    intro g hg hgW x hx hgx
    by_contra hx1
    obtain ⟨hxT, hxo⟩ := (mem_Wsl_iff hodd a ha x).mp hx.2
    have hx10 : x.1 1 0 ≠ 0 := fun h =>
      torus_entries_ne_zero_of_odd a hxT hxo hx1 (by rw [h, mul_zero])
    obtain ⟨hgxT, -⟩ := (mem_Wsl_iff hodd a ha _).mp hgx.2
    have hcomm : g * (g⁻¹ * x * g) = x * g := by group
    rcases torus_or_anticomm_of_conj a h2 hxT hgxT hx10 hcomm with hgT | hgA
    · exact hgW ⟨hg, (mem_Wsl_iff hodd a ha g).mpr ⟨hgT, hRo g hg⟩⟩
    · exact not_odd_orderOf_of_sq_eq_neg_one h2 (sq_eq_neg_one_of_anticomm a hgA) (hRo g hg)
  have hW₁1 : W₁ ≠ ⊥ := hRW
  obtain ⟨K, hKR, hKn, hKW, hdec, hKmem⟩ :=
    frobenius_kernel_subgroup (inf_le_left : W₁ ≤ R) hW₁1 hRW₁ hfrob
  have hβW : ∀ w ∈ W₁, beta F a w = w := fun w hw =>
    (beta_fixed_iff F a w).mpr (Wsl_le_torus a hw.2)
  have hKβ : ∀ k ∈ K, beta F a k ∈ K := by
    intro k hk
    have hkR := hKR hk
    rw [hKmem _ (hβ k hkR)]
    rcases (hKmem k hkR).mp hk with h1 | h
    · left
      rw [h1, map_one]
    · right
      intro g hg hgW
      apply h (beta F a g) (hβ g hg)
      have : beta F a (g⁻¹ * beta F a k * g) = (beta F a g)⁻¹ * k * beta F a g := by
        simp only [map_mul, map_inv, beta_beta]
      rw [← this, hβW _ hgW]
      exact hgW
  have hKfix : ∀ k ∈ K, beta F a k = k → k = 1 := by
    intro k hk hfix
    have hkW : k ∈ W₁ :=
      ⟨hKR hk, (mem_Wsl_iff hodd a ha k).mpr ⟨(beta_fixed_iff F a k).mp hfix, hRo k (hKR hk)⟩⟩
    have : k ∈ K ⊓ W₁ := ⟨hk, hkW⟩
    rwa [hKW, Subgroup.mem_bot] at this
  let βK : K →* K :=
    { toFun := fun k => ⟨beta F a k, hKβ k k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hfree : MonoidHom.FixedPointFree βK := by
    intro k hk
    exact Subtype.ext (hKfix k k.2 (congrArg Subtype.val hk))
  have hinvol : Function.Involutive βK := fun k => Subtype.ext (beta_beta a k)
  have hinvK : ∀ k ∈ K, beta F a k = k⁻¹ := by
    intro k hk
    have h := congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨k, hk⟩
    exact congrArg Subtype.val h
  have hcommK : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k := by
    intro k hk k' hk'
    have h := hfree.commute_all_of_involutive hinvol ⟨k, hk⟩ ⟨k', hk'⟩
    exact congrArg Subtype.val h.eq
  have hroot : ∀ k ∈ K, k ≠ 1 → ∃ l : F, l ^ 2 = -(a : F) ∧ k ∈ rootGroup l := by
    intro k hk hk1
    have hk' := hKn w₀ hw₀.1 k hk
    exact inverted_odd_mem_rootGroup a h2 (hinvK k hk) hk1 (hRo k (hKR hk)) hw₀T hw₀xy
      (hcommK k hk _ hk')
  have hK1 : ∃ k ∈ K, k ≠ 1 := by
    by_contra hcon
    apply hRW₁
    intro x hx
    obtain ⟨k, hk, w, hw, rfl⟩ := hdec x hx
    have hk1 : k = 1 := by
      by_contra hk1
      exact hcon ⟨k, hk, hk1⟩
    rw [hk1, one_mul]
    exact hw
  obtain ⟨k₀, hk₀, hk₀1⟩ := hK1
  obtain ⟨b, hb, -⟩ := hroot k₀ hk₀ hk₀1
  have hor : ∀ k ∈ K, k ∈ rootGroup b ∨ k ∈ rootGroup (-b) := by
    intro k hk
    by_cases hk1 : k = 1
    · left
      rw [hk1]
      exact Subgroup.one_mem _
    obtain ⟨l, hl, hkl⟩ := hroot k hk hk1
    have : (l - b) * (l + b) = 0 := by linear_combination hl - hb
    rcases mul_eq_zero.mp this with h | h
    · left
      rwa [show l = b by linear_combination h] at hkl
    · right
      rwa [show l = -b by linear_combination h] at hkl
  have hfin : ∀ l : F, K ≤ rootGroup l → ∀ x ∈ R, ∃ k ∈ rootGroup l, ∃ w ∈ Wsl a,
      x = k * w := by
    intro l hKl x hx
    obtain ⟨k, hk, w, hw, rfl⟩ := hdec x hx
    exact ⟨k, hKl hk, w, hw.2, rfl⟩
  rcases le_or_le_of_forall_mem_or_mem hor with hKb | hKb
  · exact ⟨b, hb, hfin b hKb⟩
  · exact ⟨-b, by rw [neg_sq]; exact hb, hfin (-b) hKb⟩

private theorem qd46_inv_mul_beta_mem_rootGroup (a : Fˣ) {l : F} (hl : l ^ 2 = -(a : F))
    {k w : SL F} (hk : k ∈ rootGroup l) (hw : w ∈ Torus F a) :
    (k * w)⁻¹ * beta F a (k * w) ∈ rootGroup l := by
  have hβw : beta F a w = w := (beta_fixed_iff F a w).mpr hw
  have hw' : w⁻¹ ∈ Torus F a := (Torus F a).inv_mem hw
  have h1 : k⁻¹ * beta F a k ∈ rootGroup l :=
    (rootGroup l).mul_mem ((rootGroup l).inv_mem hk) (beta_mem_rootGroup a hl hk)
  have h2 := torus_conj_mem_rootGroup a hl hw' h1
  rw [inv_inv] at h2
  rw [map_mul, hβw]
  convert h2 using 1
  group

end Matrix

variable {G : Type} [Group G] [Finite G]

private theorem qd46_right_eq_one_of_mem_L {σ : Setting G} (hσv : σ.IsValid) {F : Type}
    [Field F] {A : Subgroup (F ≃+* F)} {a : Fˣ} {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a}
    {φ : σ.N →* OriginalH F a A hfix}
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix)) (hA : Odd (Nat.card A))
    {g : σ.N} (hg : (g : G) ∈ σ.L) : (φ g).right = 1 := by
  set K : Subgroup G :=
    ((SemidirectProduct.rightHom : OriginalH F a A hfix →* A).comp φ).ker.map σ.N.subtype
    with hK
  have hL₀K : σ.L₀ ≤ K := by
    intro x hx
    have hxN := hφ.L₀_le hx
    have hmem : φ ⟨x, hxN⟩ ∈ layerM F a A hfix := by
      rw [← hφ.map_L₀]
      exact ⟨⟨x, hxN⟩, hx, rfl⟩
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply,
      SemidirectProduct.rightHom_eq_right]
    exact ((mem_layerM_iff _).mp hmem).2
  have hSK : (σ.S : Subgroup G) ≤ K := by
    intro x hx
    have hxN := σ.S_le_N hσv hx
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply,
      SemidirectProduct.rightHom_eq_right]
    obtain ⟨k, hk⟩ := σ.S.isPGroup' ⟨x, hx⟩
    have hk' : (⟨x, hxN⟩ : σ.N) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hpow : (φ ⟨x, hxN⟩).right ^ (2 ^ k) = 1 := by
      rw [← SemidirectProduct.rightHom_eq_right, ← map_pow, ← map_pow, hk', map_one, map_one]
    have h1 := orderOf_dvd_of_pow_eq_one hpow
    have h2 : Odd (orderOf (φ ⟨x, hxN⟩).right) := hA.of_dvd_nat (orderOf_dvd_natCard _)
    have hcop : Nat.Coprime (orderOf (φ ⟨x, hxN⟩).right) (2 ^ k) :=
      (Nat.coprime_two_right.mpr h2).pow_right k
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h1)
  obtain ⟨g', hg', hgg'⟩ := (sup_le hL₀K hSK : σ.L ≤ K) hg
  have hg'g : g' = g := Subtype.ext hgg'
  rw [hg'g, SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply,
    SemidirectProduct.rightHom_eq_right] at hg'
  exact hg'

private theorem qd46_lemmaII46Input_of_modelMap {σ : Setting G} (hσv : σ.IsValid) {F : Type}
    [Field F] [Finite F] {A : Subgroup (F ≃+* F)} {a : Fˣ}
    {hfix : ∀ τ : A, (τ : F ≃+* F) (a : F) = a} {φ : σ.N →* OriginalH F a A hfix}
    (hφ : IsModelMap σ φ (layerM F a A hfix) (originalU F a A hfix))
    (hcard : Nat.card F = σ.p ^ σ.f) (hA : Odd (Nat.card A)) (ha : ¬IsSquare a)
    {J : Subgroup G} (hJ : σ.IsV21Layer J) : V4.LemmaII46Input σ J := by
  intro W hW r hr hrW W₀ hW₀ hW₀O Y hYN hYr hYT hYO
  by_contra hev
  have hBodd : Odd (Nat.card (W₀ ⊔ Y ⊔ σ.ON : Subgroup G)) := Nat.not_even_iff_odd.mp hev
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hp := hσv.p_prime
  have hp2 := hσv.p_ne_two
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have : CharP F σ.p := qdti_charP hp hcard
  have : Fact r.Prime := ⟨hr⟩
  have hJN : J ≤ σ.N := hJ.le.trans hφ.L₀_le
  have hpON : pCoreIn σ.p σ.N ≤ σ.ON := hJ.inf_eq ▸ inf_le_right
  have hu : originalU F a A hfix ∈ (σ.T.subgroupOf σ.N).map φ := by
    rw [← hφ.map_x₂]
    exact ⟨⟨σ.x₂, hφ.x₂_mem⟩, Subgroup.mem_subgroupOf.mpr σ.x₂_mem_T, rfl⟩
  have hC : (σ.C.subgroupOf σ.N).map φ = cenU F a A hfix := hφ.map_C
  have hWJ : W ≤ J := hW.1
  have hWN : W ≤ σ.N := hWJ.trans hJN
  have hWON : W ⊓ σ.ON = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxO⟩
    have hx : x ∈ W ⊓ pCoreIn σ.p σ.N := ⟨hxW, hJ.inf_eq ▸ ⟨hWJ hxW, hxO⟩⟩
    rwa [hW.2.2.1] at hx
  obtain ⟨⟨w, hwW⟩, hwr⟩ := exists_prime_orderOf_dvd_card' (G := W) r hrW
  rw [Subgroup.orderOf_mk] at hwr
  have hφw : orderOf (φ ⟨w, hWN hwW⟩) = r := by
    have hdvd : orderOf (φ ⟨w, hWN hwW⟩) ∣ r := by
      have h := orderOf_map_dvd φ ⟨w, hWN hwW⟩
      rwa [Subgroup.orderOf_mk, hwr] at h
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      have hk : (⟨w, hWN hwW⟩ : σ.N) ∈ φ.ker := h
      rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hk
      have hw1 : w ∈ W ⊓ σ.ON := ⟨hwW, hk⟩
      rw [hWON, Subgroup.mem_bot] at hw1
      rw [hw1, orderOf_one] at hwr
      exact hr.one_lt.ne hwr
    · exact h
  have hwC : w ∈ ((oddCoreIn σ.C ⊓ J) ⊔ pCoreIn σ.p σ.N : Subgroup G) := by
    rw [← hW.2.2.2]
    exact Subgroup.mem_sup_left hwW
  have hmapW : ((((oddCoreIn σ.C ⊓ J) ⊔ pCoreIn σ.p σ.N : Subgroup G)).subgroupOf σ.N).map φ =
      (((oddCoreIn σ.C ⊓ J : Subgroup G)).subgroupOf σ.N).map φ := by
    have hpbot : ((pCoreIn σ.p σ.N).subgroupOf σ.N).map φ = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by rw [hφ.ker_eq]; exact subgroupOf_mono_of_le hpON _)
    rw [Subgroup.subgroupOf_sup (inf_le_right.trans hJN) (hpON.trans σ.ON_le_N), Subgroup.map_sup,
      hpbot, sup_bot_eq]
  have hwimg : φ ⟨w, hWN hwW⟩ ∈ (((oddCoreIn σ.C ⊓ J : Subgroup G)).subgroupOf σ.N).map φ := by
    rw [← hmapW]
    exact ⟨⟨w, hWN hwW⟩, hwC, rfl⟩
  obtain ⟨c, hc, hcw⟩ := hwimg
  have hc' : (c : G) ∈ oddCoreIn σ.C ⊓ J := Subgroup.mem_subgroupOf.mp hc
  have hφc : orderOf (φ c) = r := by rw [hcw, hφw]
  have hr2 : r ≠ 2 := by
    intro h2r
    have hco : Odd (orderOf (φ c)) := (odd_card_oddCoreIn σ.C).of_dvd_nat
      ((orderOf_map_dvd φ c).trans (by
        rw [← Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard _ hc'.1))
    rw [hφc, h2r] at hco
    exact absurd hco (by decide)
  have hrp : r ≠ σ.p := by
    intro hrp
    have hcM : φ c ∈ layerM F a A hfix := by
      rw [← hφ.map_L₀]
      exact ⟨c, Subgroup.mem_subgroupOf.mpr (hJ.le hc'.2), rfl⟩
    have hcC : φ c ∈ cenU F a A hfix := by
      rw [← hC]
      exact ⟨c, Subgroup.mem_subgroupOf.mpr ((oddCoreIn_le σ.C) hc'.1), rfl⟩
    have hmem : φ c ∈ layerM F a A hfix ⊓ cenU F a A hfix := ⟨hcM, hcC⟩
    rw [layerM_inf_cenU] at hmem
    obtain ⟨X, hXT, hX⟩ := hmem
    have hXr : orderOf X = r := by
      rw [← orderOf_injective (originalSlInH F a A hfix) slIn_injective X, hX, hφc]
    have hdvd : σ.p ∣ torusSize (Nat.card F) := by
      rw [← torus_card F a hodd ha, ← hrp, ← hXr]
      exact Subgroup.orderOf_dvd_natCard _ hXT
    have hpq : σ.p ∣ Nat.card F := by
      rw [hcard]
      exact dvd_pow_self _ (by have := hσv.one_le_f; omega)
    unfold torusSize at hdvd
    split_ifs at hdvd with h4
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp hdvd))
    · have hq1 : 1 ≤ Nat.card F := Nat.card_pos
      have h1 := Nat.dvd_sub hpq hdvd
      rw [Nat.sub_sub_self hq1] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hTN : σ.T ≤ σ.N := σ.T_le_N hσv
  have hTL : σ.T ≤ σ.L := (σ.T_le_S hσv).trans le_sup_right
  set Yb := (Y.subgroupOf σ.N).map φ with hYb
  set Tb := (σ.T.subgroupOf σ.N).map φ with hTb
  have hYTb : ⁅Yb, Tb⁆ = Yb := by
    rw [hYb, hTb, ← Subgroup.map_commutator, qd46_commutator_subgroupOf hYN hTN, hYT]
  have hTnY : σ.T ≤ Subgroup.normalizer (Y : Set G) := by
    have h := qd46_le_normalizer_commutator Y σ.T
    rwa [hYT] at h
  have hTnYb : Tb ≤ Subgroup.normalizer (Yb : Set (OriginalH F a A hfix)) :=
    hφ.le_normalizer_map hYN hTnY
  have hTright : Tb ≤ (SemidirectProduct.rightHom : OriginalH F a A hfix →* A).ker := by
    rintro _ ⟨g, hg, rfl⟩
    rw [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right]
    exact qd46_right_eq_one_of_mem_L hσv hφ hA (hTL (Subgroup.mem_subgroupOf.mp hg))
  have hYright : Yb ≤ (SemidirectProduct.rightHom : OriginalH F a A hfix →* A).ker := by
    rw [← hYTb]
    exact (Subgroup.commutator_mono le_rfl hTright).trans (Subgroup.commutator_le_right _ _)
  have hYbp : IsPGroup r Yb := (hYr.of_equiv (Subgroup.subgroupOfEquivOfLe hYN).symm).map φ
  have hYbM : Yb ≤ layerM F a A hfix := by
    intro y hy
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hYbp) ⟨y, hy⟩
    apply mem_layerM_of_odd y
    · rw [← Subgroup.orderOf_mk y hy, hk]
      exact hrodd.pow
    · have h := hYright hy
      rwa [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right] at h
  have hYb1 : Yb ≠ ⊥ := by
    intro h
    apply hYO
    intro g hg
    have h1 : φ ⟨g, hYN hg⟩ = 1 := by
      have : φ ⟨g, hYN hg⟩ ∈ Yb := ⟨⟨g, hYN hg⟩, hg, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    have hk : (⟨g, hYN hg⟩ : σ.N) ∈ φ.ker := h1
    rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hW₀N : W₀ ≤ σ.N := hW₀.trans (inf_le_left.trans ((oddCoreIn_le σ.C).trans σ.C_le_N))
  set W₀b := (W₀.subgroupOf σ.N).map φ with hW₀b
  have hW₀W : ∀ m ∈ W₀b, ∃ X ∈ Wsl a, originalSlInH F a A hfix X = m := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ oddCoreIn σ.C ⊓ σ.L := hW₀ (Subgroup.mem_subgroupOf.mp hg)
    have hright := qd46_right_eq_one_of_mem_L hσv hφ hA hg'.2
    have hgo : Odd (orderOf (φ g)) := (odd_card_oddCoreIn σ.C).of_dvd_nat
      ((orderOf_map_dvd φ g).trans (by
        rw [← Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard _ hg'.1))
    have hgM := mem_layerM_of_odd (φ g) hgo hright
    have hgC : φ g ∈ cenU F a A hfix := by
      rw [← hC]
      exact ⟨g, Subgroup.mem_subgroupOf.mpr ((oddCoreIn_le σ.C) hg'.1), rfl⟩
    have hmem : φ g ∈ layerM F a A hfix ⊓ cenU F a A hfix := ⟨hgM, hgC⟩
    rw [layerM_inf_cenU] at hmem
    obtain ⟨X, hXT, hX⟩ := hmem
    refine ⟨X, (mem_Wsl_iff hodd a ha X).mpr ⟨hXT, ?_⟩, hX⟩
    rwa [← orderOf_injective (originalSlInH F a A hfix) slIn_injective X, hX]
  have hW₀b1 : W₀b ≠ ⊥ := by
    intro h
    apply hW₀O
    intro g hg
    have h1 : φ ⟨g, hW₀N hg⟩ = 1 := by
      have : φ ⟨g, hW₀N hg⟩ ∈ W₀b := ⟨⟨g, hW₀N hg⟩, hg, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    have hk : (⟨g, hW₀N hg⟩ : σ.N) ∈ φ.ker := h1
    rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hW₀bM : W₀b ≤ layerM F a A hfix := by
    intro m hm
    obtain ⟨X, -, hX⟩ := hW₀W m hm
    exact ⟨X, hX⟩
  have hRodd : Odd (Nat.card (W₀b ⊔ Yb : Subgroup (OriginalH F a A hfix))) := by
    have hBN : W₀ ⊔ Y ⊔ σ.ON ≤ σ.N := sup_le (sup_le hW₀N hYN) σ.ON_le_N
    have hle : W₀b ⊔ Yb ≤ ((W₀ ⊔ Y ⊔ σ.ON : Subgroup G).subgroupOf σ.N).map φ :=
      sup_le (Subgroup.map_mono (subgroupOf_mono_of_le (le_sup_left.trans le_sup_left) _))
        (Subgroup.map_mono (subgroupOf_mono_of_le (le_sup_right.trans le_sup_left) _))
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le hle)
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ φ)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv]
  have hu_norm : ∀ m ∈ W₀b ⊔ Yb,
      originalU F a A hfix * m * (originalU F a A hfix)⁻¹ ∈ W₀b ⊔ Yb := by
    have key : W₀b ⊔ Yb ≤
        (W₀b ⊔ Yb).comap (MulAut.conj (originalU F a A hfix)).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro m hm
        change originalU F a A hfix * m * (originalU F a A hfix)⁻¹ ∈ W₀b ⊔ Yb
        obtain ⟨X, hX, rfl⟩ := hW₀W m hm
        have hc : originalSlInH F a A hfix X ∈ cenU F a A hfix :=
          (slIn_mem_cenU_iff X).mpr (Wsl_le_torus a hX)
        have hXu := Subgroup.mem_centralizer_singleton_iff.mp hc
        rw [← hXu, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left hm
      · intro m hm
        change originalU F a A hfix * m * (originalU F a A hfix)⁻¹ ∈ W₀b ⊔ Yb
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hTnYb hu) m).mp hm)
    exact fun m hm => key hm
  set R' := (W₀b ⊔ Yb).comap (originalSlInH F a A hfix) with hR'
  have hR'map : R'.map (originalSlInH F a A hfix) = W₀b ⊔ Yb :=
    Subgroup.map_comap_eq_self (sup_le hW₀bM hYbM)
  have hR'odd : Odd (Nat.card R') := by
    rw [← Subgroup.card_map_of_injective (f := originalSlInH F a A hfix) slIn_injective, hR'map]
    exact hRodd
  have hβR' : ∀ x ∈ R', beta F a x ∈ R' := by
    intro x hx
    change originalSlInH F a A hfix (beta F a x) ∈ W₀b ⊔ Yb
    rw [← conj_u_slIn]
    exact hu_norm _ hx
  have hR'W : R' ⊓ Wsl a ≠ ⊥ := by
    obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW₀b1
    obtain ⟨X, hXW, hX⟩ := hW₀W m hm
    have hXR : X ∈ R' := by
      change originalSlInH F a A hfix X ∈ W₀b ⊔ Yb
      rw [hX]
      exact Subgroup.mem_sup_left hm
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨X, hXR, hXW⟩, fun h => hm1 ?_⟩
    have hX1 : X = 1 := congrArg Subtype.val h
    apply Subtype.ext
    change m = 1
    rw [← hX, hX1, map_one]
  have hYtorus : ∀ y : SL F, originalSlInH F a A hfix y ∈ Yb → y ∈ Torus F a := by
    intro y hy
    have hyR : y ∈ R' := Subgroup.mem_sup_right hy
    rcases qd46_odd_subgroup_decomp hodd a ha hR'odd hR'W hβR' with hle | ⟨l, hl, hdec⟩
    · exact Wsl_le_torus a (hle hyR)
    · obtain ⟨k, hk, w', hw', hkw⟩ := hdec y hyR
      have hg := qd46_inv_mul_beta_mem_rootGroup a hl hk (Wsl_le_torus a hw')
      rw [← hkw] at hg
      have hgY : originalSlInH F a A hfix (y⁻¹ * beta F a y) ∈ Yb := by
        rw [map_mul, map_inv, ← conj_u_slIn]
        exact Yb.mul_mem (Yb.inv_mem hy) ((Subgroup.mem_normalizer_iff.mp (hTnYb hu) _).mp hy)
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hYbp) ⟨_, hgY⟩
      have hgp := rootGroup_pow_char σ.p hg
      have h1 : orderOf (y⁻¹ * beta F a y) ∣ σ.p := orderOf_dvd_of_pow_eq_one hgp
      have h2 : orderOf (y⁻¹ * beta F a y) ∣ r ^ m := by
        rw [← hm, Subgroup.orderOf_mk, orderOf_injective (originalSlInH F a A hfix) slIn_injective]
      have hcop : Nat.Coprime σ.p (r ^ m) :=
        ((Nat.coprime_primes hp hr).mpr hrp.symm).pow_right m
      have hg1 : y⁻¹ * beta F a y = 1 :=
        orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
      exact (beta_fixed_iff F a y).mp (inv_mul_eq_one.mp hg1).symm
  have hYcen : ∀ m ∈ Yb, m * originalU F a A hfix = originalU F a A hfix * m := by
    intro m hm
    obtain ⟨y, rfl⟩ := hYbM hm
    exact Subgroup.mem_centralizer_singleton_iff.mp ((slIn_mem_cenU_iff y).mpr (hYtorus y hm))
  have hTcen : Tb ≤ Subgroup.centralizer (Yb : Set (OriginalH F a A hfix)) := by
    have hK : σ.T ≤
        ((Subgroup.centralizer (Yb : Set (OriginalH F a A hfix))).comap φ).map σ.N.subtype := by
      rw [Setting.T, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · refine ⟨⟨σ.x, σ.x_mem_N⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        rintro _ ⟨h, -, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext ((σ.mem_N_iff h).mp h.2)
      · refine ⟨⟨σ.x₂, hφ.x₂_mem⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, hφ.map_x₂, Subgroup.mem_centralizer_iff]
        exact hYcen
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hK (Subgroup.mem_subgroupOf.mp hg)
    have hg'g : g' = g := Subtype.ext hgg'
    rw [← hg'g]
    exact hg'
  apply hYb1
  rw [← hYTb, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hTcen

variable [IsSimpleGroup G]

theorem frontier_lemmaII46Input
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
      V4.LemmaII46Input (frontierSetting S fS t p f) J := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, hA, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hσv := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  intro J hJ
  exact qd46_lemmaII46Input_of_modelMap hσv hφ hcard hA ha hJ

end

end CFSG.Semidihedral.AllPrime
