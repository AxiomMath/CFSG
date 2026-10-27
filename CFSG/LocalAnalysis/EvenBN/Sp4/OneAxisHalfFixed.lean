module

public import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisClassSlice
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCSeriesCoset
public import CFSG.LocalAnalysis.SteinbergSFFieldInvolutionRepresentative
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_12_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_13_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_d
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_e
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_6_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.theorem_11_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_c_2

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard CFSG.LocalAnalysis.ComponentInitial
open GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisSecondAxis OneAxisWeakClosure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD

section Coord

variable {G : Type*} [Group G] {K : Type*} [Field K]

structure IsCoord (W W' : Subgroup G) (a : G) (σ : K →+* K) (f : G → K) : Prop where
  map_mul : ∀ x ∈ W, ∀ y ∈ W, f (x * y) = f x + f y
  ker : ∀ x ∈ W, f x = 0 ↔ x ∈ W'
  surj : ∀ k : K, ∃ y ∈ W, f y = k
  equiv : ∀ x ∈ W, f (a⁻¹ * x * a) = σ (f x)

variable [CharP K 2] {W W' : Subgroup G} {a : G} {σ : K →+* K} {f : G → K}

theorem IsCoord.map_inv (hf : IsCoord W W' a σ f) {x : G} (hx : x ∈ W) : f x⁻¹ = f x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 := hf.map_mul 1 (one_mem _) 1 (one_mem _)
  rw [one_mul] at h1
  have h3 := hf.map_mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel] at h3
  linear_combination (-1 : K) * h1 + (-1 : K) * h3 + (-(f x)) * h2

theorem IsCoord.map_comm (hf : IsCoord W W' a σ f) (haW : a ∈ normalizer (W : Set G)) {x : G}
    (hx : x ∈ W) : f (x⁻¹ * (a⁻¹ * x * a)) = f x + σ (f x) := by
  rw [hf.map_mul _ (inv_mem hx) _ (inv_mul_mul_mem_of_mem_normalizer haW hx), hf.map_inv hx,
    hf.equiv x hx]

theorem IsCoord.isElementaryAbelian [hN : (W'.subgroupOf W).Normal] (hf : IsCoord W W' a σ f) :
    IsElementaryAbelian 2 (W ⧸ W'.subgroupOf W) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : ∀ q : W ⧸ W'.subgroupOf W, q ^ 2 = 1 := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, pow_two,
      Subgroup.coe_mul, ← hf.ker _ (mul_mem hx hx), hf.map_mul x hx x hx]
    linear_combination f x * h2
  exact { is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
            (fun g => orderOf_dvd_of_pow_eq_one (hsq g)) a b).eq⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

theorem IsCoord.fixed_eq_range [hN : (W'.subgroupOf W).Normal] (hf : IsCoord W W' a σ f)
    (haW : a ∈ normalizer (W : Set G)) (haW' : a ∈ normalizer (W' : Set G))
    (hσ : ∀ x, σ (σ x) = x) {ρ : K} (hρ : ρ + σ ρ = 1) :
    {q | sectionRightConj haW haW' q = q} =
      Set.range fun q : W ⧸ W'.subgroupOf W => q⁻¹ * sectionRightConj haW haW' q := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hconj : ∀ x ∈ W, a⁻¹ * x * a ∈ W := fun x hx => inv_mul_mul_mem_of_mem_normalizer haW hx
  apply le_antisymm
  · rintro q hq
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hfix := (sectionRightConj_mk_eq_iff haW haW' ⟨x, hx⟩).mp hq
    have e1 := (hf.ker _ (mul_mem (hconj _ (inv_mem hx)) hx)).mpr hfix
    rw [hf.map_mul _ (hconj _ (inv_mem hx)) _ hx, hf.equiv _ (inv_mem hx), hf.map_inv hx] at e1
    obtain ⟨y, hy, hfy⟩ := hf.surj (ρ * f x)
    refine ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
    dsimp only
    rw [sectionRightConj_mk haW haW' ⟨y, hy⟩ ⟨a⁻¹ * y * a, hconj y hy⟩ rfl,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have hz : y⁻¹ * (a⁻¹ * y * a) ∈ W := mul_mem (inv_mem hy) (hconj y hy)
    change (y⁻¹ * (a⁻¹ * y * a))⁻¹ * x ∈ W'
    rw [← hf.ker _ (mul_mem (inv_mem hz) hx), hf.map_mul _ (inv_mem hz) _ hx, hf.map_inv hz,
      hf.map_comm haW hy, hfy, _root_.map_mul σ]
    linear_combination σ ρ * e1 + f x * hρ + f x * (1 - σ ρ) * h2
  · rintro _ ⟨q, rfl⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hz : y⁻¹ * (a⁻¹ * y * a) ∈ W := mul_mem (inv_mem hy) (hconj y hy)
    change sectionRightConj haW haW' _ = _
    dsimp only
    rw [sectionRightConj_mk haW haW' ⟨y, hy⟩ ⟨a⁻¹ * y * a, hconj y hy⟩ rfl,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    refine (sectionRightConj_mk_eq_iff haW haW' ⟨_, hz⟩).mpr ?_
    change a⁻¹ * (y⁻¹ * (a⁻¹ * y * a))⁻¹ * a * (y⁻¹ * (a⁻¹ * y * a)) ∈ W'
    rw [← hf.ker _ (mul_mem (hconj _ (inv_mem hz)) hz), hf.map_mul _ (hconj _ (inv_mem hz)) _ hz,
      hf.equiv _ (inv_mem hz), hf.map_inv hz, hf.map_comm haW hy, map_add, hσ]
    linear_combination (f y + σ (f y)) * h2

end Coord

section Coordinates

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

open scoped Classical in
noncomputable def lcoord (φ : L ≃* antiSp K) (i j : Fin 4) (x : G) : K :=
  if hx : x ∈ L then mat (φ ⟨x, hx⟩) i j else 0

omit [CharP K 2] in
theorem lcoord_symm (φ : L ≃* antiSp K) (i j : Fin 4) (g : antiSp K) :
    lcoord φ i j ((φ.symm g : L) : G) = mat g i j := by
  rw [lcoord, dite_eq_left (φ.symm g).2]
  simp

theorem lcoord_uElt (φ : L ≃* antiSp K) (a b c d : K) :
    lcoord φ 0 1 ((φ.symm (uElt a b c d) : L) : G) = a ∧
      lcoord φ 0 2 ((φ.symm (uElt a b c d) : L) : G) = b ∧
      lcoord φ 0 3 ((φ.symm (uElt a b c d) : L) : G) = c := by
  rw [lcoord_symm, lcoord_symm, lcoord_symm]
  exact ⟨rfl, rfl, rfl⟩

open scoped Classical in
noncomputable def heisParam (φ : L ≃* antiSp K) (t g : G) : K × K × K :=
  if hg : ∃ p : K × K × K, HAct φ t g p.1 p.2.1 p.2.2 then hg.choose else 0

theorem heisParam_eq {n : ℕ} {φ : L ≃* antiSp K} {t : G} (hS : TwoCoreSetup L K n t) {g : G}
    {x y d : K} (h : HAct φ t g x y d) : heisParam φ t g = (x, y, d) := by
  have hex : ∃ p : K × K × K, HAct φ t g p.1 p.2.1 p.2.2 := ⟨(x, y, d), h⟩
  rw [heisParam, dite_eq_left hex]
  obtain ⟨h1, h2, h3⟩ := HAct.unique hS hex.choose_spec h
  exact Prod.ext h1 (Prod.ext h2 h3)

end Coordinates

section Frob

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]

theorem frobAut_pow_aElt (m : ℕ) (v : Fin 2 → K) (c : K) :
    (frobAut K ^ m) (aElt v c) = aElt (fun i => v i ^ 2 ^ m) (c ^ 2 ^ m) := by
  rw [aElt, aElt, FieldInvolution.frobAut_pow_uElt, zero_pow (pow_ne_zero _ two_ne_zero)]

structure FrobeniusInvolution (φ : L ≃* antiSp K) (t : G) (m : ℕ) (v₀ : G) : Prop where
  mul_self : v₀ * v₀ = 1
  comm : v₀ * t = t * v₀
  frob : ∀ l : L, ((φ.symm ((frobAut K ^ m) (φ l)) : L) : G) = v₀ * l * v₀⁻¹

namespace FrobeniusInvolution

variable {φ : L ≃* antiSp K} {t : G} {m : ℕ} {v₀ : G}

theorem inv_eq (hv : FrobeniusInvolution φ t m v₀) : v₀⁻¹ = v₀ :=
  inv_eq_of_mul_eq_one_right hv.mul_self

theorem conj_symm (hv : FrobeniusInvolution φ t m v₀) (g : antiSp K) :
    v₀⁻¹ * ((φ.symm g : L) : G) * v₀ = ((φ.symm ((frobAut K ^ m) g) : L) : G) := by
  have e := hv.frob (φ.symm g)
  rw [MulEquiv.apply_symm_apply] at e
  rw [e, hv.inv_eq]

theorem mem_normalizer_pull (hv : FrobeniusInvolution φ t m v₀) {S : Subgroup (antiSp K)}
    (hS : ∀ s ∈ S, (frobAut K ^ m) s ∈ S) : v₀ ∈ normalizer (pull φ S : Set G) := by
  have hfwd : ∀ x ∈ pull φ S, v₀⁻¹ * x * v₀ ∈ pull φ S := fun x hx => by
    obtain ⟨g, hg, rfl⟩ := exists_eq_symm_of_mem_pull hx
    rw [hv.conj_symm]
    exact symm_mem_pull.mpr (hS g hg)
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have := hfwd x hx
    rw [hv.inv_eq] at this ⊢
    exact this
  · have := hfwd _ hx
    rwa [show v₀⁻¹ * (v₀ * x * v₀⁻¹) * v₀ = x by group] at this

theorem lcoord_conj (hv : FrobeniusInvolution φ t m v₀) (i j : Fin 4) {x : G} (hx : x ∈ L) :
    lcoord φ i j (v₀⁻¹ * x * v₀) = lcoord φ i j x ^ 2 ^ m := by
  obtain ⟨g, rfl⟩ : ∃ g : antiSp K, ((φ.symm g : L) : G) = x := ⟨φ ⟨x, hx⟩, by simp⟩
  rw [hv.conj_symm, lcoord_symm, lcoord_symm, FieldInvolution.mat_frobAut_pow, Matrix.map_apply]

theorem hAct_conj (hv : FrobeniusInvolution φ t m v₀) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ m)
    (hσσ : ∀ c, σ (σ c) = c) {g : G} {x y d : K} (h : HAct φ t g x y d) :
    HAct φ t (v₀⁻¹ * g * v₀) (σ x) (σ y) (σ d) := by
  have hvt : v₀⁻¹ * t = t * v₀⁻¹ := by
    rw [hv.inv_eq]
    exact hv.comm
  have hκ : ∀ w : Fin 2 → K, v₀⁻¹ * coord φ t (qgPoint w) * v₀ =
      coord φ t (qgPoint fun i => σ (w i)) := by
    intro w
    have e : ∀ z : G, v₀⁻¹ * (t * z) * v₀ = t * (v₀⁻¹ * z * v₀) := fun z => by
      rw [← mul_assoc, hvt]
      group
    rw [coord_qgPoint, coord_qgPoint, e, hv.conj_symm, frobAut_pow_aElt]
    simp only [hσ, zero_pow (pow_ne_zero _ two_ne_zero)]
  intro w
  have e1 : v₀ * coord φ t (qgPoint w) * v₀⁻¹ = coord φ t (qgPoint fun i => σ (w i)) := by
    have := hκ w
    rw [hv.inv_eq] at this ⊢
    exact this
  calc v₀⁻¹ * g * v₀ * coord φ t (qgPoint w) * (v₀⁻¹ * g * v₀)⁻¹
      = v₀⁻¹ * (g * (v₀ * coord φ t (qgPoint w) * v₀⁻¹) * g⁻¹) * v₀ := by group
    _ = v₀⁻¹ * coord φ t (qgPoint ![σ (w 0) + d * σ (w 1) + y, σ (w 1) + x]) * v₀ := by
        rw [e1, h]
    _ = coord φ t (qgPoint fun i =>
          σ ((![σ (w 0) + d * σ (w 1) + y, σ (w 1) + x] : Fin 2 → K) i)) := hκ _
    _ = coord φ t (qgPoint ![w 0 + σ d * w 1 + σ y, w 1 + σ x]) := by
        congr 2
        ext i
        fin_cases i <;> simp [hσσ]

end FrobeniusInvolution

end Frob

section Factors

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]
  {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G} {m : ℕ} {v₀ : G}
  {σ : K →+* K}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐔₁" => pull φ (rootU K Axis.one)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₁" => pull φ (rootA K Axis.one)
local notation "𝐀₂" => pull φ (rootA K Axis.two)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐒" => (pull φ (antiUnipotent K) ⊔ TG ⊔ (CFSG.pCore 2 (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔
  pull φ (rootA K Axis.two) : Subgroup G) : Set G)).subtype : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₂" =>
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄" => (M ⊔ pull φ (antiUnipotent K) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐕" => (M ⊔ pull φ (rootA K Axis.one) ⊔
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom) : Subgroup G)

omit [Finite K] in
theorem lcoord_mul_uElt (i j : Fin 4) (a b c d a' b' c' d' : K) :
    lcoord φ i j (((φ.symm (uElt a b c d) : L) : G) * ((φ.symm (uElt a' b' c' d') : L) : G)) =
      uMat (a + a') (b + b' + a * d') (c + c' + a * b' + a * a' * d' + b * a') (d + d') i j := by
  rw [← Subgroup.coe_mul, ← map_mul, uElt_mul, lcoord_symm]
  rfl

theorem isCoord_U₂ (hv : FrobeniusInvolution φ t m v₀) (hσ : ∀ c, σ c = c ^ 2 ^ m) :
    IsCoord 𝐔₂ ⊥ v₀ σ (lcoord φ 0 3) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun k => ⟨_, symm_mem_pull.mpr ⟨k, rfl⟩,
    (lcoord_uElt φ 0 0 k 0).2.2⟩, fun x hx => ?_⟩
  · obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
    obtain ⟨_, ⟨c', rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hy
    rw [lcoord_mul_uElt, (lcoord_uElt φ 0 0 c 0).2.2, (lcoord_uElt φ 0 0 c' 0).2.2]
    change c + c' + 0 * 0 + 0 * 0 * 0 + 0 * 0 = c + c'
    ring
  · obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
    rw [(lcoord_uElt φ 0 0 c 0).2.2, mem_bot]
    constructor
    · rintro rfl
      rw [uElt_zero_eq_one, map_one, OneMemClass.coe_one]
    · intro h1
      have h2 : uElt (0 : K) 0 c 0 = uElt 0 0 0 0 := by
        rw [uElt_zero_eq_one]
        exact φ.symm.map_eq_one_iff.mp (Subtype.ext h1)
      exact (uElt_inj h2).2.2.1
  · rw [hv.lcoord_conj 0 3 (pull_le φ _ hx), hσ]

theorem isCoord_ZP (hv : FrobeniusInvolution φ t m v₀) (hσ : ∀ c, σ c = c ^ 2 ^ m) :
    IsCoord 𝐙 𝐔₂ v₀ σ (lcoord φ 0 2) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun k => ⟨_, symm_mem_pull.mpr ⟨k, 0, rfl⟩,
    (lcoord_uElt φ 0 k 0 0).2.1⟩, fun x hx => ?_⟩
  · obtain ⟨_, ⟨b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
    obtain ⟨_, ⟨b', c', rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hy
    rw [lcoord_mul_uElt, (lcoord_uElt φ 0 b c 0).2.1, (lcoord_uElt φ 0 b' c' 0).2.1]
    change b + b' + 0 * 0 = b + b'
    ring
  · obtain ⟨_, ⟨b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
    rw [(lcoord_uElt φ 0 b c 0).2.1]
    constructor
    · rintro rfl
      exact symm_mem_pull.mpr ⟨c, rfl⟩
    · intro h1
      obtain ⟨_, ⟨c', hc'⟩, he⟩ := exists_eq_symm_of_mem_pull h1
      have h2 : uElt (0 : K) b c 0 = uElt 0 0 c' 0 := by
        rw [← hc']
        exact φ.symm.injective (Subtype.ext he.symm)
      exact (uElt_inj h2).2.1
  · rw [hv.lcoord_conj 0 2 (pull_le φ _ hx), hσ]

namespace OneAxisData

theorem M_inf_centralizer [Finite G] (h : OneAxisData L K n φ TG t M) :
    M ⊓ 𝐂 = 𝐙 := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf h.ZP_le fun z hz => h.heis.sec.two.L_le (pull_le φ _ hz))
  obtain ⟨hxM, hxC⟩ := mem_inf.mp hx
  have hxA : x ∈ 𝐀₁ := by
    rw [← h.M₁_inf_centralizer]
    exact mem_inf.mpr ⟨mem_sup_left hxM, hxC⟩
  rw [← h.M_inf_P]
  exact mem_inf.mpr ⟨hxM, pull_mono φ radA1_le_antiUnipotent hxA⟩

theorem isCoord_M [Finite G] (h : OneAxisData L K n φ TG t M) (hv : FrobeniusInvolution φ t m v₀)
    (hσ : ∀ c, σ c = c ^ 2 ^ m) :
    IsCoord M 𝐙 v₀ σ (fun x => lcoord φ 0 2 (t⁻¹ * (x⁻¹ * t * x))) := by
  have hU : ∀ x ∈ M, t⁻¹ * (x⁻¹ * t * x) ∈ 𝐔₁ := fun x hx => h.heis.conj₁ x (h.le_D₁ hx)
  have hb : ∀ u ∈ 𝐔₁, ∃ b : K, u = ((φ.symm (uElt 0 b 0 0) : L) : G) := fun u hu => by
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hu
    exact ⟨b, rfl⟩
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun k => ?_, fun x hx => ?_⟩
  · rw [h.heis.mul₁ x (h.le_D₁ hx) y (h.le_D₁ hy)]
    obtain ⟨b, hbx⟩ := hb _ (hU x hx)
    obtain ⟨b', hby⟩ := hb _ (hU y hy)
    rw [hbx, hby, lcoord_mul_uElt, (lcoord_uElt φ 0 b 0 0).2.1, (lcoord_uElt φ 0 b' 0 0).2.1]
    change b + b' + 0 * 0 = b + b'
    ring
  · obtain ⟨b, hbx⟩ := hb _ (hU x hx)
    rw [hbx, (lcoord_uElt φ 0 b 0 0).2.1, ← h.M_inf_centralizer, mem_inf,
      mem_centralizer_singleton_iff]
    have hiff : x * t = t * x ↔ t⁻¹ * (x⁻¹ * t * x) = 1 := by
      constructor
      · intro hxt
        rw [mul_assoc, ← hxt, inv_mul_cancel_left, inv_mul_cancel]
      · intro h1
        have h2 : x⁻¹ * t * x = t := by
          have := congrArg (t * ·) h1
          simpa using this
        calc x * t = x * (x⁻¹ * t * x) := by rw [h2]
          _ = t * x := by group
    rw [hiff, hbx]
    constructor
    · rintro rfl
      exact ⟨hx, by rw [uElt_zero_eq_one, map_one, OneMemClass.coe_one]⟩
    · rintro ⟨-, h1⟩
      have h2 : uElt (0 : K) b 0 0 = uElt 0 0 0 0 := by
        rw [uElt_zero_eq_one]
        exact φ.symm.map_eq_one_iff.mp (Subtype.ext h1)
      exact (uElt_inj h2).2.1
  · obtain ⟨m₁, hm₁, hm₁t⟩ := h.exists_mem_M₁_conj_eq (u := ((φ.symm (uElt 0 k 0 0) : L) : G))
      (symm_mem_pull.mpr ⟨k, rfl⟩)
    rw [← SetLike.mem_coe, ← h.coe_M₁] at hm₁
    obtain ⟨x, hx, a, ha, rfl⟩ := Set.mem_mul.mp hm₁
    have hax : x * a = a * x := elemAb_comm h.elemAb₁ (mem_sup_left hx) (mem_sup_right ha)
    refine ⟨x, hx, ?_⟩
    have e : x⁻¹ * t * x = t * ((φ.symm (uElt 0 k 0 0) : L) : G) := by
      rw [← hm₁t, hax]
      have hat : a * t = t * a := (h.comm_L (pull_le φ _ ha)).symm
      calc x⁻¹ * t * x = x⁻¹ * (a⁻¹ * (a * t)) * x := by group
        _ = (a * x)⁻¹ * t * (a * x) := by rw [hat]; group
    rw [e, inv_mul_cancel_left, (lcoord_uElt φ 0 k 0 0).2.1]
  · have hvt : v₀⁻¹ * t = t * v₀⁻¹ := by
      rw [hv.inv_eq]
      exact hv.comm
    have e : t⁻¹ * ((v₀⁻¹ * x * v₀)⁻¹ * t * (v₀⁻¹ * x * v₀)) =
        v₀⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * v₀ := by
      have hvt' : v₀ * t = t * v₀ := hv.comm
      have e1 : t⁻¹ * v₀⁻¹ = v₀⁻¹ * t⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hvt']
      calc t⁻¹ * ((v₀⁻¹ * x * v₀)⁻¹ * t * (v₀⁻¹ * x * v₀))
          = (t⁻¹ * v₀⁻¹) * x⁻¹ * (v₀ * t) * v₀⁻¹ * x * v₀ := by group
        _ = v₀⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * v₀ := by
          rw [e1, hvt']
          group
    rw [e, hv.lcoord_conj 0 2 (pull_le φ _ (hU x hx)), hσ]

theorem isCoord_M₁ [Finite G] (h : OneAxisData L K n φ TG t M)
    (hv : FrobeniusInvolution φ t m v₀) (hσ : ∀ c, σ c = c ^ 2 ^ m) (hσσ : ∀ c, σ (σ c) = c) :
    IsCoord 𝐌₁ M v₀ σ (fun x => (heisParam φ t x).2.2) := by
  have hS := h.heis.sec.two
  have hex : ∀ x ∈ 𝐌₁, ∃ a b d : K, HAct φ t x a b d := fun x hx => h.exists_hAct (h.M₁_le_S hx)
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun k => ⟨_, mem_sup_right (symm_mem_pull.mpr
    ⟨0, 0, k, rfl⟩), by rw [heisParam_eq hS (hAct_symm_uElt hS 0 0 0 k)]⟩, fun x hx => ?_⟩
  · obtain ⟨a, b, d, hx'⟩ := hex x hx
    obtain ⟨a', b', d', hy'⟩ := hex y hy
    rw [heisParam_eq hS (hx'.mul hy'), heisParam_eq hS hx', heisParam_eq hS hy']
  · obtain ⟨a, b, d, hx'⟩ := hex x hx
    rw [heisParam_eq hS hx', ← h.heis.mem_D₂_iff (h.M₁_le_S hx) hx', ← h.M₁_inf_D₂]
    exact ⟨fun hD => mem_inf.mpr ⟨hx, hD⟩, fun hM => (mem_inf.mp hM).2⟩
  · obtain ⟨a, b, d, hx'⟩ := hex x hx
    rw [heisParam_eq hS (hv.hAct_conj hσ hσσ hx'), heisParam_eq hS hx']

omit [Finite K] in
theorem comm_y₀_eq (h : OneAxisData L K n φ TG t M) {x : G} (hx : x ∈ M) (a b c d : K) :
    (x * ((φ.symm (uElt a b c d) : L) : G))⁻¹ * ((φ.symm (uElt 0 0 0 1) : L) : G)⁻¹ *
        (x * ((φ.symm (uElt a b c d) : L) : G)) * ((φ.symm (uElt 0 0 0 1) : L) : G) =
      ((φ.symm (uElt 0 a (a ^ 2) 0) : L) : G) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hy : ((φ.symm (uElt 0 0 0 1) : L) : G) ∈ 𝐌₁ :=
    mem_sup_right (symm_mem_pull.mpr ⟨0, 0, 1, rfl⟩)
  have hxy := elemAb_comm h.elemAb₁ (mem_sup_left hx) hy
  have e : uElt a (b + a * d) c d * uElt 0 (0 + 0 * 1) 0 1 * uElt a b c d * uElt 0 0 0 1 =
      uElt 0 a (a ^ 2) 0 := by
    rw [uElt_mul, uElt_mul, uElt_mul]
    congr 1
    all_goals first
      | ring1
      | linear_combination a * h2
      | linear_combination (b + a * d) * h2
      | linear_combination (c + a * b + a ^ 2 * d) * h2
      | linear_combination (d + 1) * h2
      | linear_combination (b + a * d + a) * h2
  rw [← e, map_mul, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    ← uElt_inv, ← uElt_inv, map_inv, map_inv, Subgroup.coe_inv, Subgroup.coe_inv]
  calc (x * ((φ.symm (uElt a b c d) : L) : G))⁻¹ * ((φ.symm (uElt 0 0 0 1) : L) : G)⁻¹ *
        (x * ((φ.symm (uElt a b c d) : L) : G)) * ((φ.symm (uElt 0 0 0 1) : L) : G)
      = ((φ.symm (uElt a b c d) : L) : G)⁻¹ *
          (x⁻¹ * (((φ.symm (uElt 0 0 0 1) : L) : G)⁻¹ * x)) *
          ((φ.symm (uElt a b c d) : L) : G) * ((φ.symm (uElt 0 0 0 1) : L) : G) := by group
    _ = _ := by
      have hxy' : ((φ.symm (uElt 0 0 0 1) : L) : G)⁻¹ * x =
          x * ((φ.symm (uElt 0 0 0 1) : L) : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hxy, mul_inv_cancel_right]
      rw [hxy', inv_mul_cancel_left]

theorem isCoord_E [Finite G] (h : OneAxisData L K n φ TG t M)
    (hv : FrobeniusInvolution φ t m v₀) (hσ : ∀ c, σ c = c ^ 2 ^ m)
    (hvM : v₀ ∈ normalizer (M : Set G)) :
    IsCoord 𝐄 𝐌₁ v₀ σ (fun x => lcoord φ 0 2 (x⁻¹ * ((φ.symm (uElt 0 0 0 1) : L) : G)⁻¹ * x *
      ((φ.symm (uElt 0 0 0 1) : L) : G))) := by
  have hcoord : ∀ x ∈ M, ∀ a b c d : K, lcoord φ 0 2 ((x * ((φ.symm (uElt a b c d) : L) : G))⁻¹ *
      ((φ.symm (uElt 0 0 0 1) : L) : G)⁻¹ * (x * ((φ.symm (uElt a b c d) : L) : G)) *
      ((φ.symm (uElt 0 0 0 1) : L) : G)) = a := fun x hx a b c d => by
    rw [h.comm_y₀_eq hx, (lcoord_uElt φ 0 a (a ^ 2) 0).2.1]
  have hdec : ∀ e ∈ 𝐄, ∃ x ∈ M, ∃ a b c d : K, e = x * ((φ.symm (uElt a b c d) : L) : G) := by
    intro e he
    rw [← SetLike.mem_coe, ← h.coe_E] at he
    obtain ⟨x, hx, p, hp, rfl⟩ := Set.mem_mul.mp he
    obtain ⟨_, ⟨a, b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp
    exact ⟨x, hx, a, b, c, d, rfl⟩
  refine ⟨fun e he e' he' => ?_, fun e he => ?_, fun k => ⟨((φ.symm (uElt k 0 0 0) : L) : G),
    mem_sup_right (symm_mem_pull.mpr ⟨k, 0, 0, 0, rfl⟩), ?_⟩, fun e he => ?_⟩
  · obtain ⟨x, hx, a, b, c, d, rfl⟩ := hdec e he
    obtain ⟨x', hx', a', b', c', d', rfl⟩ := hdec e' he'
    have hp : ((φ.symm (uElt a b c d) : L) : G) ∈ 𝐒 :=
      AxisHyp.P_le_S (symm_mem_pull.mpr ⟨a, b, c, d, rfl⟩)
    have hx'' : ((φ.symm (uElt a b c d) : L) : G) * x' *
        ((φ.symm (uElt a b c d) : L) : G)⁻¹ ∈ M := h.conj_mem hp hx'
    have e1 : x * ((φ.symm (uElt a b c d) : L) : G) * (x' * ((φ.symm (uElt a' b' c' d') : L) : G)) =
        (x * (((φ.symm (uElt a b c d) : L) : G) * x' * ((φ.symm (uElt a b c d) : L) : G)⁻¹)) *
          ((φ.symm (uElt a b c d * uElt a' b' c' d') : L) : G) := by
      rw [map_mul, Subgroup.coe_mul]
      group
    rw [e1, uElt_mul, hcoord _ (mul_mem hx hx''), hcoord x hx, hcoord x' hx']
  · obtain ⟨x, hx, a, b, c, d, rfl⟩ := hdec e he
    rw [hcoord x hx]
    constructor
    · rintro rfl
      exact mul_mem (mem_sup_left hx) (mem_sup_right (symm_mem_pull.mpr ⟨b, c, d, rfl⟩))
    · intro hM
      have hpM : ((φ.symm (uElt a b c d) : L) : G) ∈ 𝐌₁ := by
        have := mul_mem (inv_mem (mem_sup_left hx : x ∈ 𝐌₁)) hM
        rwa [inv_mul_cancel_left] at this
      rw [← SetLike.mem_coe, ← h.coe_M₁] at hpM
      obtain ⟨x', hx', a₁, ha₁, he⟩ := Set.mem_mul.mp hpM
      have hx'P : x' ∈ 𝐏 := by
        have hp : ((φ.symm (uElt a b c d) : L) : G) ∈ 𝐏 := symm_mem_pull.mpr ⟨a, b, c, d, rfl⟩
        have := mul_mem hp (inv_mem (pull_mono φ radA1_le_antiUnipotent ha₁))
        rwa [← he, mul_inv_cancel_right] at this
      have hx'A : x' ∈ 𝐀₁ := by
        have hZ : x' ∈ 𝐙 := by
          rw [← h.M_inf_P]
          exact mem_inf.mpr ⟨hx', hx'P⟩
        exact pull_mono φ (center_le_rootA Axis.one) hZ
      have hpA : ((φ.symm (uElt a b c d) : L) : G) ∈ 𝐀₁ := he ▸ mul_mem hx'A ha₁
      obtain ⟨b', c', d', hbcd⟩ := symm_mem_pull.mp hpA
      exact (uElt_inj hbcd).1
  · rw [show ((φ.symm (uElt k 0 0 0) : L) : G) = 1 * ((φ.symm (uElt k 0 0 0) : L) : G) by
      rw [one_mul], hcoord 1 (one_mem _)]
  · obtain ⟨x, hx, a, b, c, d, rfl⟩ := hdec e he
    have hxv : v₀⁻¹ * x * v₀ ∈ M := inv_mul_mul_mem_of_mem_normalizer hvM hx
    have e1 : v₀⁻¹ * (x * ((φ.symm (uElt a b c d) : L) : G)) * v₀ =
        (v₀⁻¹ * x * v₀) * ((φ.symm ((frobAut K ^ m) (uElt a b c d)) : L) : G) := by
      rw [← hv.conj_symm]
      group
    rw [e1, FieldInvolution.frobAut_pow_uElt, hcoord _ hxv, hcoord x hx, hσ]

theorem isCoord_V₁ [Finite G] (h : OneAxisData L K n φ TG t M)
    (hv : FrobeniusInvolution φ t m v₀) (hσ : ∀ c, σ c = c ^ 2 ^ m) (hσσ : ∀ c, σ (σ c) = c) :
    IsCoord 𝐕 𝐄 v₀ σ (fun x => (heisParam φ t x).1) := by
  have hS := h.heis.sec.two
  have hex : ∀ x ∈ 𝐕, ∃ a b d : K, HAct φ t x a b d := fun x hx => h.exists_hAct (h.V₁_le_T₁ hx)
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun k => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, d, hx'⟩ := hex x hx
    obtain ⟨a', b', d', hy'⟩ := hex y hy
    rw [heisParam_eq hS (hx'.mul hy'), heisParam_eq hS hx', heisParam_eq hS hy']
  · obtain ⟨a, b, d, hx'⟩ := hex x hx
    rw [heisParam_eq hS hx', ← h.heis.mem_R_iff (h.V₁_le_T₁ hx) hx', ← h.V_inf_R]
    exact ⟨fun hR => mem_inf.mpr ⟨hx, hR⟩, fun hE => (mem_inf.mp hE).2⟩
  · obtain ⟨y, hy, hyk⟩ := h.exists_mem_M₂_hAct k 0
    exact ⟨y, (le_sup_right : 𝐌₂ ≤ 𝐕) hy, by rw [heisParam_eq hS hyk]⟩
  · obtain ⟨a, b, d, hx'⟩ := hex x hx
    rw [heisParam_eq hS (hv.hAct_conj hσ hσσ hx'), heisParam_eq hS hx']

end OneAxisData

end Factors

section Chain

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]
  {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G} {m : ℕ} {v₀ : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐔₂" => pull φ (rootU K Axis.two)
local notation "𝐀₁" => pull φ (rootA K Axis.one)
set_option quotPrecheck false in
local notation "𝐌₁" => (M ⊔ pull φ (rootA K Axis.one) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐌₂" =>
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄" => (M ⊔ pull φ (antiUnipotent K) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐕" => (M ⊔ pull φ (rootA K Axis.one) ⊔
  (M ⊔ M.map (MulAut.conj ((φ.symm (sElt swapSL) : L) : G)⁻¹).toMonoidHom) : Subgroup G)

omit [Finite K] in
theorem normal_subgroupOf_of_conj {W W' : Subgroup G} (h : ∀ w ∈ W, ∀ x ∈ W', w * x * w⁻¹ ∈ W') :
    (W'.subgroupOf W).Normal :=
  ⟨fun x hx w => mem_subgroupOf.mpr (h w w.2 x (mem_subgroupOf.mp hx))⟩

theorem frob_mem_rootU₂ (m : ℕ) :
    ∀ s ∈ rootU K Axis.two, (frobAut K ^ m) s ∈ rootU K Axis.two := by
  rintro _ ⟨c, rfl⟩
  exact ⟨c ^ 2 ^ m, by rw [FieldInvolution.frobAut_pow_uElt, zero_pow (pow_ne_zero _ two_ne_zero)]⟩

theorem frob_mem_center (m : ℕ) :
    ∀ s ∈ antiUnipotentCenter K, (frobAut K ^ m) s ∈ antiUnipotentCenter K := by
  rintro _ ⟨b, c, rfl⟩
  exact ⟨b ^ 2 ^ m, c ^ 2 ^ m, by
    rw [FieldInvolution.frobAut_pow_uElt, zero_pow (pow_ne_zero _ two_ne_zero)]⟩

theorem frob_mem_unipotent (m : ℕ) :
    ∀ s ∈ antiUnipotent K, (frobAut K ^ m) s ∈ antiUnipotent K := by
  rintro _ ⟨a, b, c, d, rfl⟩
  rw [FieldInvolution.frobAut_pow_uElt]
  exact uElt_mem_antiUnipotent _ _ _ _

namespace OneAxisData

theorem mem_normalizer_of_mem_normalizer_V₁ [Finite G] (h : OneAxisData L K n φ TG t M) {g : G}
    (hg : g ∈ normalizer (h.V₁ : Set G)) :
    g ∈ normalizer (𝐌₁ : Set G) ∧ g ∈ normalizer (𝐌₂ : Set G) ∧ g ∈ normalizer (M : Set G) := by
  rw [normalizer_V h.toAxisHyp h.elemAb₁] at hg
  obtain ⟨h₁, h₂⟩ := mem_inf.mp hg
  refine ⟨h₁, h₂, ?_⟩
  rw [← h.M₁_inf_M₂]
  refine mem_normalizer_iff.mpr fun x => ?_
  rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp h₁ x, ← mem_normalizer_iff.mp h₂ x]

theorem not_mem_V₁ [Finite G] (h : OneAxisData L K n φ TG t M) (hv : FrobeniusInvolution φ t m v₀)
    (hm0 : m ≠ 0) (hmn : m < n) : v₀ ∉ h.V₁ := by
  intro hvV
  have hvP : v₀ ∈ 𝐏 := by
    rw [← h.V₁_inf_centralizer]
    exact mem_inf.mpr ⟨hvV, mem_centralizer_singleton_iff.mpr hv.comm⟩
  set l : L := ⟨v₀, pull_le φ _ hvP⟩
  have hconj : frobAut K ^ m = MulAut.conj (φ l) := by
    refine MulEquiv.ext fun x => ?_
    have e := hv.frob (φ.symm x)
    rw [MulEquiv.apply_symm_apply] at e
    have e' : φ.symm ((frobAut K ^ m) x) = l * φ.symm x * l⁻¹ := Subtype.ext (by simpa using e)
    rw [MulAut.conj_apply]
    simpa using congrArg φ e'
  exact FieldInvolution.conj_mul_frobAut_pow_ne_conj (by omega) h.heis.sec.two.card_K hm0 hmn 1
    (φ l) (by rw [map_one, one_mul, hconj])

end OneAxisData

end Chain

open OneAxisData

theorem one_axis_half_fixed_series {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}
    {M : Subgroup G} (h : OneAxisData L K n φ TG t M) (hn : Even n) {v₀ : G}
    (hv₀ : orderOf v₀ = 2) (hv₀C : v₀ ∈ centralizer ({t} : Set G))
    (hv₀V : v₀ ∈ normalizer (h.V₁ : Set G))
    (hFr : ∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) :
    {x : G | (∃ v ∈ h.V₁, x = v₀ * v) ∧ orderOf x = 2} = {x | ∃ v ∈ h.V₁, x = v⁻¹ * v₀ * v} ∧
      Nat.card (h.V₁ ⊓ centralizer ({v₀} : Set G) : Subgroup G) = (2 ^ n) ^ 3 := by
  set m := n / 2 with hm
  have hn2 : n = 2 * m := by
    obtain ⟨r, hr⟩ := hn
    omega
  have hm1 : 1 ≤ m := by
    have := h.heis.sec.two.two_le
    omega
  have hmn : m < n := by omega
  have hv : FrobeniusInvolution φ t m v₀ :=
    ⟨by rw [← pow_two, ← hv₀, pow_orderOf_eq_one], mem_centralizer_singleton_iff.mp hv₀C, hFr⟩
  have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm1, by rw [h.heis.sec.two.card_K, hn2]⟩
  have hσ : ∀ c, hU.bar c = c ^ 2 ^ m := hU.bar_apply
  have hσσ : ∀ c, hU.bar (hU.bar c) = c := hU.bar_bar
  obtain ⟨ρ, hρ'⟩ := (unitary_field_trace hU).1 1
  have hρ : ρ + hU.bar ρ = 1 := congrArg Subtype.val hρ'
  have hvU₂ : v₀ ∈ normalizer (pull φ (rootU K Axis.two) : Set G) :=
    hv.mem_normalizer_pull (frob_mem_rootU₂ m)
  have hvZ : v₀ ∈ normalizer (pull φ (antiUnipotentCenter K) : Set G) :=
    hv.mem_normalizer_pull (frob_mem_center m)
  have hvP : v₀ ∈ normalizer (pull φ (antiUnipotent K) : Set G) :=
    hv.mem_normalizer_pull (frob_mem_unipotent m)
  obtain ⟨hvM₁, -, hvM⟩ := h.mem_normalizer_of_mem_normalizer_V₁ hv₀V
  have hvE : v₀ ∈ normalizer ((M ⊔ pull φ (antiUnipotent K) : Subgroup G) : Set G) :=
    le_normalizer_sup (zpowers_le.mpr hvM) (zpowers_le.mpr hvP) (mem_zpowers v₀)
  have hvbot : v₀ ∈ normalizer ((⊥ : Subgroup G) : Set G) :=
    mem_normalizer_iff.mpr fun x => by
      rw [mem_bot, mem_bot]
      constructor
      · rintro rfl
        group
      · intro hx
        have e : x = v₀⁻¹ * (v₀ * x * v₀⁻¹) * v₀ := by group
        rw [e, hx]
        group
  have nbot : ∀ W : Subgroup G, ((⊥ : Subgroup G).subgroupOf W).Normal := fun W =>
    normal_subgroupOf_of_conj fun w _ x hx => by
      rw [mem_bot] at hx ⊢
      rw [hx, mul_one, mul_inv_cancel]
  have nU₂ : ((pull φ (rootU K Axis.two)).subgroupOf h.V₁).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => by
      rw [comm_U₂ h.heis (h.V_le_S hw) hx, mul_inv_cancel_right]
      exact hx
  have nU₂Z : ((pull φ (rootU K Axis.two)).subgroupOf (pull φ (antiUnipotentCenter K))).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => by
      rw [comm_U₂ h.heis ((le_sup_left.trans le_sup_left : pull φ (antiUnipotent K) ≤ h.T₁)
        (Setup.ZP_le_PG hw)) hx, mul_inv_cancel_right]
      exact hx
  have nZ : ((pull φ (antiUnipotentCenter K)).subgroupOf h.V₁).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => by
      have hc := comm_M_V h.toAxisHyp h.elemAb₁ (h.ZP_le hx) w hw
      have e : w * x * w⁻¹ = (x * w * x⁻¹ * w⁻¹)⁻¹ * x := by group
      rw [e]
      exact mul_mem (inv_mem ((pull_mono φ (rootU_le_center Axis.two)) hc)) hx
  have nZM : ((pull φ (antiUnipotentCenter K)).subgroupOf M).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => by
      rw [h.comm w hw x (h.ZP_le hx), mul_inv_cancel_right]
      exact hx
  have nM : (M.subgroupOf h.V₁).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => h.conj_mem (h.V_le_S hw) hx
  have nMM₁ : (M.subgroupOf (M ⊔ pull φ (rootA K Axis.one))).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => by
      rw [elemAb_comm h.elemAb₁ hw (mem_sup_left hx), mul_inv_cancel_right]
      exact hx
  have nM₁ : ((M ⊔ pull φ (rootA K Axis.one)).subgroupOf h.V₁).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => h.conj₁ w (h.V_le_S hw) x hx
  have nM₁E : ((M ⊔ pull φ (rootA K Axis.one)).subgroupOf
      (M ⊔ pull φ (antiUnipotent K))).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => h.conj₁ w (h.E_normal.1 hw) x hx
  have hEconj : ∀ w ∈ h.T₁, ∀ x ∈ M ⊔ pull φ (antiUnipotent K), w * x * w⁻¹ ∈
      M ⊔ pull φ (antiUnipotent K) := fun w hw x hx => by
    obtain ⟨hES, hEn⟩ := h.E_normal
    exact mem_subgroupOf.mp (hEn.conj_mem ⟨x, hES hx⟩ (mem_subgroupOf.mpr hx) ⟨w, hw⟩)
  have nE : ((M ⊔ pull φ (antiUnipotent K)).subgroupOf h.V₁).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => hEconj w (h.V_le_S hw) x hx
  have nV : (h.V₁.subgroupOf h.V₁).Normal :=
    normal_subgroupOf_of_conj fun w hw x hx => mul_mem (mul_mem hw hx) (inv_mem hw)
  let V : Fin 7 → Subgroup G := ![⊥, pull φ (rootU K Axis.two), pull φ (antiUnipotentCenter K),
    M, M ⊔ pull φ (rootA K Axis.one), M ⊔ pull φ (antiUnipotent K), h.V₁]
  have haV : ∀ i, v₀ ∈ normalizer (V i : Set G) := by
    intro i
    fin_cases i
    exacts [hvbot, hvU₂, hvZ, hvM, hvM₁, hvE, hv₀V]
  have hle : ∀ i : Fin 6, V i.castSucc ≤ V i.succ := by
    intro i
    fin_cases i
    exacts [bot_le, pull_mono φ (rootU_le_center Axis.two), h.ZP_le, le_sup_left, M₁_le_E,
      h.E_le_V]
  have hN : ∀ i : Fin 6, ((V i.castSucc).subgroupOf (V i.succ)).Normal := by
    intro i
    fin_cases i
    exacts [nbot _, nU₂Z, nZM, nMM₁, nM₁E, nE]
  have hcoord₁ := isCoord_U₂ (φ := φ) (t := t) hv hσ
  have hcoord₂ := isCoord_ZP (φ := φ) (t := t) hv hσ
  have hcoord₃ := h.isCoord_M hv hσ
  have hcoord₄ := h.isCoord_M₁ hv hσ hσσ
  have hcoord₅ := h.isCoord_E hv hσ hvM
  have hcoord₆ := h.isCoord_V₁ hv hσ hσσ
  have hEA : ∀ i : Fin 6,
      IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ)) := by
    intro i
    fin_cases i
    · exact hcoord₁.isElementaryAbelian (hN := hN 0)
    · exact hcoord₂.isElementaryAbelian (hN := hN 1)
    · exact hcoord₃.isElementaryAbelian (hN := hN 2)
    · exact hcoord₄.isElementaryAbelian (hN := hN 3)
    · exact hcoord₅.isElementaryAbelian (hN := hN 4)
    · exact hcoord₆.isElementaryAbelian (hN := hN 5)
  have hfix : ∀ i : Fin 6, {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x} =
      Set.range fun x => x⁻¹ * sectionRightConj (haV i.succ) (haV i.castSucc) x := by
    intro i
    fin_cases i
    · exact hcoord₁.fixed_eq_range (hN := hN 0) _ _ hσσ hρ
    · exact hcoord₂.fixed_eq_range (hN := hN 1) _ _ hσσ hρ
    · exact hcoord₃.fixed_eq_range (hN := hN 2) _ _ hσσ hρ
    · exact hcoord₄.fixed_eq_range (hN := hN 3) _ _ hσσ hρ
    · exact hcoord₅.fixed_eq_range (hN := hN 4) _ _ hσσ hρ
    · exact hcoord₆.fixed_eq_range (hN := hN 5) _ _ hσσ hρ
  have hVW : ∀ i, ((V i).subgroupOf h.V₁).Normal := by
    intro i
    fin_cases i
    exacts [nbot _, nU₂, nZ, nM, nM₁, nE, nV]
  have hpV : IsPGroup 2 h.V₁ := IsPGroup.of_card (h.card_V.trans (by rw [← pow_mul]))
  obtain ⟨hinv, -, hsq, -⟩ := elementary_series_involution_coset_conjugacy (W := h.V₁) hpV hv₀
    hv₀V (h.not_mem_V₁ hv (by omega) hmn) (r := 6) (by norm_num) V rfl rfl hle hVW haV hfix
  refine ⟨hinv, Nat.pow_left_injective (n := 2) (by norm_num) ?_⟩
  change Nat.card (h.V₁ ⊓ centralizer ({v₀} : Set G) : Subgroup G) ^ 2 = ((2 ^ n) ^ 3) ^ 2
  rw [hsq, h.card_V]
  ring

end CFSG.LocalAnalysis.EvenBN.Sp4
