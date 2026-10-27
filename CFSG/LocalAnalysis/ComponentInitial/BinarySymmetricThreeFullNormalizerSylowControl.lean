module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeAffineOrbitTwoGroup
public import CFSG.LocalAnalysis.ComponentInitial.EightPointEvenQuotientRankBound
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.GroupTheory.Perm.Cycle.Type
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix Module
open scoped Pointwise

namespace BinarySymThreeOrbit

theorem sign_eq_one_of_sq_eq_one {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h2 : σ ^ 2 = 1) (h4 : 4 ∣ σ.support.card) : Equiv.Perm.sign σ = 1 := by
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) h2
  have hsum := Equiv.Perm.sum_cycleType σ
  set k := Multiset.card σ.cycleType
  rw [hct, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [Equiv.Perm.sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul]
  obtain ⟨j, hj⟩ := h4
  have hk : k = 2 * j := by omega
  rw [hk, show 2 * j * 2 + 2 * j = 2 * (3 * j) by ring, pow_mul]
  simp

@[expose] noncomputable def matPerm (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hN : N.det ≠ 0) :
    Equiv.Perm (Fin 3 → ZMod 2) where
  toFun v := N *ᵥ v
  invFun v := N⁻¹ *ᵥ v
  left_inv v := by
    change N⁻¹ *ᵥ (N *ᵥ v) = v
    rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hN), one_mulVec]
  right_inv v := by
    change N *ᵥ (N⁻¹ *ᵥ v) = v
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN), one_mulVec]

theorem matPerm_apply (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hN : N.det ≠ 0)
    (v : Fin 3 → ZMod 2) : matPerm N hN v = N *ᵥ v :=
  rfl

theorem transvection_support_card (i j : Fin 3) (c : ZMod 2) :
    4 ∣ (Finset.univ.filter fun v : Fin 3 → ZMod 2 => transvection i j c *ᵥ v ≠ v).card := by
  revert i j c
  decide +kernel

theorem sign_eq_one_of_mulVec {N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hN : N.det ≠ 0)
    (τ : Equiv.Perm (Fin 3 → ZMod 2)) (hτ : ∀ v, τ v = N *ᵥ v) : Equiv.Perm.sign τ = 1 := by
  revert τ
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun N => ∀ τ : Equiv.Perm (Fin 3 → ZMod 2), (∀ v, τ v = N *ᵥ v) → Equiv.Perm.sign τ = 1)
    N hN (fun Dg hDg τ hτ => ?_) (fun t τ hτ => ?_) (fun A B hA hB hPA hPB τ hτ => ?_)
  · have hD1 : Dg = 1 := by
      funext i
      have hi : Dg i ≠ 0 := by
        rw [det_diagonal] at hDg
        exact Finset.prod_ne_zero_iff.mp hDg i (Finset.mem_univ i)
      rcases f2_cases (Dg i) with h | h
      · exact absurd h hi
      · exact h
    have hτ1 : τ = 1 := Equiv.ext fun v => by
      rw [hτ, hD1]
      change diagonal (fun _ => (1 : ZMod 2)) *ᵥ v = v
      rw [diagonal_one, one_mulVec]
    rw [hτ1, map_one]
  · have hsq : τ ^ 2 = 1 := Equiv.ext fun v => by
      rw [pow_two, Equiv.Perm.mul_apply, hτ, hτ, mulVec_mulVec, TransvectionStruct.toMatrix,
        transvection_mul_transvection_same _ _ t.hij, symThree_zmod_add_self, transvection_zero,
        one_mulVec]
      rfl
    refine sign_eq_one_of_sq_eq_one hsq ?_
    have hsupp : τ.support = Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
        transvection t.i t.j t.c *ᵥ v ≠ v := by
      ext v
      rw [Equiv.Perm.mem_support, Finset.mem_filter, hτ]
      exact ⟨fun h => ⟨Finset.mem_univ v, h⟩, fun h => h.2⟩
    rw [hsupp]
    exact transvection_support_card t.i t.j t.c
  · have hτ' : τ = matPerm A hA * matPerm B hB := Equiv.ext fun v => by
      rw [hτ, Equiv.Perm.mul_apply, matPerm_apply, matPerm_apply, mulVec_mulVec]
    rw [hτ', map_mul, hPA _ (matPerm_apply A hA), hPB _ (matPerm_apply B hB), mul_one]

theorem card_vec : Fintype.card (Fin 3 → ZMod 2) = 8 := by
  decide

theorem sign_addLeft (a : Fin 3 → ZMod 2) : Equiv.Perm.sign (Equiv.addLeft a) = 1 := by
  by_cases ha : a = 0
  · have h1 : Equiv.addLeft a = 1 := Equiv.ext fun v => by
      rw [ha]
      exact zero_add v
    rw [h1, map_one]
  · have hsq : Equiv.addLeft a ^ 2 = 1 := Equiv.ext fun v => by
      rw [pow_two, Equiv.Perm.mul_apply]
      change a + (a + v) = v
      rw [← add_assoc, show a + a = 0 from funext fun i => symThree_zmod_add_self (a i),
        zero_add]
    refine sign_eq_one_of_sq_eq_one hsq ?_
    have hsupp : (Equiv.addLeft a).support = Finset.univ := by
      ext v
      rw [Equiv.Perm.mem_support]
      simp only [Finset.mem_univ, iff_true]
      change a + v ≠ v
      intro h
      exact ha (by simpa using h)
    rw [hsupp, Finset.card_univ, card_vec]
    decide

theorem sign_of_mem_affinePerms {σ : Equiv.Perm (Fin 3 → ZMod 2)}
    (hσ : σ ∈ affinePerms (Fin 3 → ZMod 2)) : Equiv.Perm.sign σ = 1 := by
  obtain ⟨a, A, hA⟩ := hσ
  have hdet : (toGL A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).mp (toGL A).isUnit).ne_zero
  have hσ' : σ = Equiv.addLeft a * A.toEquiv := Equiv.ext fun v => by
    rw [hA, Equiv.Perm.mul_apply]
    rfl
  rw [hσ', map_mul, sign_addLeft,
    sign_eq_one_of_mulVec hdet A.toEquiv fun v => (toGL_mulVec A v).symm, mul_one]

@[expose] noncomputable def labelSum :
    ((Fin 3 → ZMod 2) → ZMod 2) →ₗ[ZMod 2] (binarySymMatrices 3 × ZMod 2) :=
  Fintype.linearCombination (ZMod 2) fun v => (label v, (1 : ZMod 2))

theorem labelSum_single (v : Fin 3 → ZMod 2) : labelSum (Pi.single v 1) = (label v, 1) := by
  rw [labelSum, Fintype.linearCombination_apply_single, one_smul]

theorem labelSum_surjective : Function.Surjective labelSum := by
  have h := prod_eq_top_of_label_mem (S := (LinearMap.range labelSum).toAddSubgroup)
    fun v => ⟨Pi.single v 1, labelSum_single v⟩
  intro x
  have hx : x ∈ (LinearMap.range labelSum).toAddSubgroup := by
    rw [h]
    exact AddSubgroup.mem_top x
  exact hx

theorem sum_vecMulVec_self : ∑ v : Fin 3 → ZMod 2, vecMulVec v v = 0 := by
  ext i j
  rw [Matrix.sum_apply, Matrix.zero_apply]
  simp only [vecMulVec_apply]
  revert i j
  decide

theorem labelSum_one : labelSum (1 : (Fin 3 → ZMod 2) → ZMod 2) = 0 := by
  rw [labelSum, Fintype.linearCombination_apply]
  simp only [Pi.one_apply, one_smul]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum, Prod.fst_zero]
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum, ZeroMemClass.coe_zero]
    exact sum_vecMulVec_self
  · rw [Prod.snd_sum, Prod.snd_zero, Finset.sum_const, Finset.card_univ, card_vec]
    rfl

theorem ker_labelSum : LinearMap.ker labelSum = Submodule.span (ZMod 2) {1} := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact labelSum_one
  · have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {(1 : (Fin 3 → ZMod 2) → ZMod 2)}) = 1 :=
      finrank_span_singleton one_ne_zero
    have hrn := LinearMap.finrank_range_add_finrank_ker labelSum
    rw [LinearMap.range_eq_top.mpr labelSum_surjective, finrank_top, finrank_symProd,
      Module.finrank_fintype_fun_eq_card, card_vec] at hrn
    rw [h1]
    omega

@[expose] noncomputable def quotEquiv :
    constQuot (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (binarySymMatrices 3 × ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ ker_labelSum.symm).trans
    (LinearMap.quotKerEquivOfSurjective labelSum labelSum_surjective)

theorem quotEquiv_mk (f : (Fin 3 → ZMod 2) → ZMod 2) :
    quotEquiv (Submodule.Quotient.mk f) = labelSum f :=
  rfl

theorem permFun_single (σ : Equiv.Perm (Fin 3 → ZMod 2)) (v : Fin 3 → ZMod 2) :
    CFSG.GroupActions.permFun (p := 2) σ (Pi.single v 1) = Pi.single (σ v) 1 := by
  funext x
  simp only [CFSG.GroupActions.permFun_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

section Equivariance

variable {G : Type*} [Group G] {R : Subgroup G}
  {θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)}

theorem conjAdd_symm_eq [R.Normal] (m : G) {r : G} (hr : r ∈ R) (hcomm : m * r = r * m) :
    conjAdd θ m (Multiplicative.toAdd (θ ⟨r, hr⟩)) = Multiplicative.toAdd (θ ⟨r, hr⟩) := by
  have h := conjAdd_spec θ m (Multiplicative.toAdd (θ ⟨r, hr⟩))
  rw [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
  change m * r * m⁻¹ = _ at h
  rw [hcomm, mul_inv_cancel_right] at h
  have h' : θ.symm (Multiplicative.ofAdd (conjAdd θ m (Multiplicative.toAdd (θ ⟨r, hr⟩)))) =
      ⟨r, hr⟩ := Subtype.ext h.symm
  have h2 := congrArg (fun y => Multiplicative.toAdd (θ y)) h'
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using h2

namespace IsAffineOrbit

variable (H : IsAffineOrbit θ) [R.Normal]
include H

theorem labelSum_permFun (m : G) (f : (Fin 3 → ZMod 2) → ZMod 2) :
    labelSum (CFSG.GroupActions.permFun (p := 2) (H.permHom m) f) = conjAdd θ m (labelSum f) := by
  have hlin : labelSum ∘ₗ CFSG.GroupActions.permFun (p := 2) (H.permHom m) =
      ((conjAdd θ m).toZModLinearMap 2) ∘ₗ labelSum := by
    refine LinearMap.pi_ext' fun v => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.single_apply]
    rw [permFun_single, labelSum_single, labelSum_single]
    exact (H.conjAdd_label m v).symm
  exact LinearMap.congr_fun hlin f

theorem quotEquiv_constQuotAct (m : G) (q : constQuot (Fin 3 → ZMod 2)) :
    quotEquiv (constQuotAct (H.permHom m) q) = conjAdd θ m (quotEquiv q) := by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [Submodule.mkQ_apply, constQuotAct, Submodule.mapQ_apply, quotEquiv_mk, quotEquiv_mk,
    H.labelSum_permFun]

theorem card_subgroupOf_le [Finite G] (F : Subgroup G)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    Nat.card (R.subgroupOf F) ≤ 2 ^ finrank (ZMod 2) (constQuotFixed (F.map H.permHom)) := by
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := constQuotFixed (F.map H.permHom))
  rw [Nat.card_zmod] at hcard
  rw [← hcard]
  let j : R.subgroupOf F → constQuotFixed (F.map H.permHom) := fun r =>
    ⟨quotEquiv.symm (Multiplicative.toAdd (θ ⟨((r : F) : G), r.2⟩)), fun σ hσ => by
      obtain ⟨m, hm, rfl⟩ := hσ
      apply quotEquiv.injective
      rw [H.quotEquiv_constQuotAct, LinearEquiv.apply_symm_apply]
      exact conjAdd_symm_eq m (r := ((r : F) : G)) r.2 (hcomm m hm _ (r : F).2)⟩
  have hj : Function.Injective j := by
    intro r s h
    have h1 := congrArg (fun x : constQuotFixed (F.map H.permHom) =>
      quotEquiv (x : constQuot (Fin 3 → ZMod 2))) h
    simp only [j, LinearEquiv.apply_symm_apply] at h1
    have h2 := θ.injective (Multiplicative.toAdd.injective h1)
    have h3 : ((r : F) : G) = ((s : F) : G) := congrArg (fun x : R => (x : G)) h2
    exact Subtype.ext (Subtype.ext h3)
  exact Nat.card_le_card_of_injective j hj

theorem card_le_sixtyFour [Finite G] {F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian 2 F)
    (hFR : ¬ F ≤ R) : Nat.card F ≤ 64 := by
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set U := F.map H.permHom with hUdef
  have hU : U ≠ ⊥ := by
    obtain ⟨m, hm, hmR⟩ := IsConcreteLE.not_le_iff_exists.mp hFR
    intro hbot
    have hmU : H.permHom m ∈ U := ⟨m, hm, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, H.ker_permHom] at hmU
    exact hmR hmU
  have hcommU : ∀ u ∈ U, ∀ w ∈ U, u * w = w * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hsqU : ∀ u ∈ U, u * u = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← pow_two, hF.2 x hx, map_one]
  have hevenU : ∀ u ∈ U, Equiv.Perm.sign u = 1 := by
    rintro _ ⟨x, -, rfl⟩
    refine sign_of_mem_affinePerms ?_
    rw [← H.range_permHom.1]
    exact ⟨x, rfl⟩
  have hFp : IsPGroup 2 F := fun x => ⟨1, Subtype.ext (by
    rw [SubgroupClass.coe_pow, pow_one, OneMemClass.coe_one]
    exact hF.2 x x.2)⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (hFp.map H.permHom)
  have hrank := eight_point_even_permutation_quotient_elementary_rank_bound card_vec U hU
    hcommU hsqU hevenU r hr
  have hFR' := H.card_subgroupOf_le F hcomm
  have hFcard : Nat.card F = Nat.card U * Nat.card (R.subgroupOf F) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.permHom.domRestrict F).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, H.ker_permHom] at h1
    exact h1
  calc Nat.card F = Nat.card U * Nat.card (R.subgroupOf F) := hFcard
    _ ≤ 2 ^ r * 2 ^ finrank (ZMod 2) (constQuotFixed U) := by
        rw [hr]
        exact Nat.mul_le_mul_left _ hFR'
    _ = 2 ^ (r + finrank (ZMod 2) (constQuotFixed U)) := (pow_add 2 _ _).symm
    _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hrank
    _ = 64 := by norm_num

end IsAffineOrbit

end Equivariance

section Elementary

variable {G : Type*} [Group G]

open CFSG.Assembly

theorem elemAbelian_comm {K : Subgroup G} (hK : IsElemAbelian 2 K) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hK hx hy

theorem isElemAbelian_map {K : Subgroup G} (hK : IsElemAbelian 2 K) {G' : Type*} [Group G']
    (f : G →* G') : IsElemAbelian 2 (K.map f) := CFSG.Open.IsElemAbelian.map hK _

theorem isElemAbelian_subgroupOf {K : Subgroup G} (hK : IsElemAbelian 2 K) (L : Subgroup G) :
    IsElemAbelian 2 (K.subgroupOf L) := CFSG.Open.IsElemAbelian.subgroupOf hK L

theorem isPGroup_of_isElemAbelian {K : Subgroup G} (hK : IsElemAbelian 2 K) : IsPGroup 2 K :=
  CFSG.Open.IsElemAbelian.isPGroup hK

theorem isElemAbelian_R {R : Subgroup G} (θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)) :
    IsElemAbelian 2 R :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_mem θ a.2 b.2)⟩⟩, fun _ hx => sq_eq_one_of_mem θ hx⟩

theorem mem_map_conj {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g⁻¹ * (g * y * g⁻¹) * g ∈ K
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem card_map_conj (K : Subgroup G) (g : G) :
    Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem map_conj_inv_eq {K L : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g⁻¹).toMonoidHom = L) : K = L.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj, ← h, mem_map_conj, inv_inv]
  constructor
  · intro hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  · intro hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hx

theorem map_conj_le_iff {K L : Subgroup G} {g : G} :
    K.map (MulAut.conj g⁻¹).toMonoidHom ≤ L ↔ K ≤ L.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro h x hx
    rw [mem_map_conj]
    have := h ⟨x, hx, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
  · rintro h _ ⟨x, hx, rfl⟩
    have := h hx
    rw [mem_map_conj] at this
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

end Elementary

section SylowControl

variable {G : Type*} [Group G] [Finite G] {R M : Subgroup G}

open CFSG.Assembly

theorem factorization_two : (2 ^ 13 * 21 : ℕ).factorization 2 = 13 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

omit [Finite G] in
theorem mem_of_mem_normalizer (hM : M = Subgroup.normalizer (R : Set G))
    (hRea : IsElemAbelian 2 R) (hR128 : Nat.card R = 128)
    (huniq : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → Nat.card F = 128 → F = R)
    {S : Subgroup G} (hRS : R ≤ S) (hSM : S ≤ M) {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) : g ∈ M := by
  have hle : R.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg r).mp (hRS hr)
  have hF := huniq _ (hle.trans hSM) (isElemAbelian_map hRea _)
    (by rw [card_map_conj, hR128])
  rw [hM, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hF]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hF, mem_map_conj] at hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at hh

theorem exists_sylow_eq_map (hM : M = Subgroup.normalizer (R : Set G))
    (hRea : IsElemAbelian 2 R) (hR128 : Nat.card R = 128)
    (huniq : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → Nat.card F = 128 → F = R)
    (S : Sylow 2 M) :
    R ≤ (S : Subgroup M).map M.subtype ∧
      ∃ Q : Sylow 2 G, (Q : Subgroup G) = (S : Subgroup M).map M.subtype := by
  have hRM : R ≤ M := hM ▸ Subgroup.le_normalizer
  have hR2 : IsPGroup 2 R := isPGroup_of_isElemAbelian hRea
  have hRnM : (R.subgroupOf M).Normal := hM ▸ Subgroup.normal_in_normalizer
  set SG := (S : Subgroup M).map M.subtype with hSGdef
  have hSGM : SG ≤ M := Subgroup.map_subtype_le _
  have hRSG : R ≤ SG := by
    have hR2' : IsPGroup 2 (R.subgroupOf M) :=
      hR2.comap_of_injective M.subtype M.subtype_injective
    have h1 : R.subgroupOf M ≤ S := hR2'.le_sylow_of_normal S
    have h2 := Subgroup.map_mono (f := M.subtype) h1
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hRM] at h2
  refine ⟨hRSG, ?_⟩
  have hSG2 : IsPGroup 2 SG := S.isPGroup'.map M.subtype
  obtain ⟨Q, hQ⟩ := hSG2.exists_le_sylow
  refine ⟨Q, le_antisymm ?_ hQ⟩
  have hT : (Q : Subgroup G) ⊓ Subgroup.normalizer (SG : Set G) ≤ SG := by
    have hTM : (Q : Subgroup G) ⊓ Subgroup.normalizer (SG : Set G) ≤ M := fun g hg =>
      mem_of_mem_normalizer hM hRea hR128 huniq hRSG hSGM hg.2
    have hST : (S : Subgroup M) ≤
        ((Q : Subgroup G) ⊓ Subgroup.normalizer (SG : Set G)).subgroupOf M := fun x hx =>
      ⟨hQ ⟨x, hx, rfl⟩, Subgroup.le_normalizer ⟨x, hx, rfl⟩⟩
    have hT2 : IsPGroup 2
        (((Q : Subgroup G) ⊓ Subgroup.normalizer (SG : Set G)).subgroupOf M) :=
      (Q.isPGroup'.to_le inf_le_left).comap_of_injective M.subtype M.subtype_injective
    have heq := S.is_maximal' hT2 hST
    intro g hg
    have hgM : (⟨g, hTM hg⟩ : M) ∈
        ((Q : Subgroup G) ⊓ Subgroup.normalizer (SG : Set G)).subgroupOf M := hg
    rw [heq] at hgM
    exact ⟨_, hgM, rfl⟩
  by_contra hne
  have hlt : SG.subgroupOf Q < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hne (Subgroup.subgroupOf_eq_top.mp h)
  have hnc := p_group_normalizer_condition Q.isPGroup' hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hQ] at hnc
  obtain ⟨x, hx, hxS⟩ := IsConcreteLE.exists_of_lt hnc
  exact hxS (hT ⟨x.2, hx⟩)

theorem sylow_control (hM : M = Subgroup.normalizer (R : Set G))
    (hRea : IsElemAbelian 2 R) (hR128 : Nat.card R = 128)
    (huniq : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → Nat.card F = 128 → F = R)
    (hbound : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → Nat.card F ≤ 128)
    (hcard : Nat.card M = 2 ^ 13 * 21) :
    (∀ S : Sylow 2 M, ∃ Q : Sylow 2 G, (Q : Subgroup G) = (S : Subgroup M).map M.subtype ∧
      Nat.card Q = 2 ^ 13 ∧ R ≤ Q ∧
      (∀ F : Subgroup G, F ≤ Q → IsElemAbelian 2 F → Nat.card F = 128 → F = R) ∧
      (R.subgroupOf Q).Characteristic) ∧
    Odd M.index ∧
    (∀ Q : Sylow 2 G, ∃! F : Subgroup G, F ≤ Q ∧ IsElemAbelian 2 F ∧ Nat.card F = 128) ∧
    (∀ F : Subgroup G, IsElemAbelian 2 F → Nat.card F = 128 →
      ∃ g : G, F = R.map (MulAut.conj g).toMonoidHom) ∧
    (∀ F : Subgroup G, IsElemAbelian 2 F → Nat.card F ≤ 128) := by
  have hSylow : ∀ S : Sylow 2 M, ∃ Q : Sylow 2 G,
      (Q : Subgroup G) = (S : Subgroup M).map M.subtype ∧ Nat.card Q = 2 ^ 13 ∧ R ≤ Q ∧
      (∀ F : Subgroup G, F ≤ Q → IsElemAbelian 2 F → Nat.card F = 128 → F = R) ∧
      (R.subgroupOf Q).Characteristic := by
    intro S
    obtain ⟨hRS, Q, hQ⟩ := exists_sylow_eq_map hM hRea hR128 huniq S
    have hQM : (Q : Subgroup G) ≤ M := hQ ▸ Subgroup.map_subtype_le _
    have hQuniq : ∀ F : Subgroup G, F ≤ Q → IsElemAbelian 2 F → Nat.card F = 128 → F = R :=
      fun F hF => huniq F (hF.trans hQM)
    refine ⟨Q, hQ, ?_, hQ ▸ hRS, hQuniq, ?_⟩
    · rw [hQ, Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity,
        hcard, factorization_two]
    · refine Subgroup.characteristic_iff_map_eq.mpr fun φ => ?_
      apply Subgroup.map_injective (Q : Subgroup G).subtype_injective
      have hRQ : R ≤ Q := hQ ▸ hRS
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hRQ]
      refine hQuniq _ (Subgroup.map_subtype_le _) ?_ ?_
      · exact isElemAbelian_map (isElemAbelian_map (isElemAbelian_subgroupOf hRea _) _) _
      · rw [Subgroup.card_map_of_injective (Q : Subgroup G).subtype_injective,
          Subgroup.card_map_of_injective φ.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRQ).toEquiv, hR128]
  obtain ⟨S₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 M))
  obtain ⟨Q₀, hQ₀, -, hRQ₀, hQ₀uniq, -⟩ := hSylow S₀
  have hQ₀M : (Q₀ : Subgroup G) ≤ M := hQ₀ ▸ Subgroup.map_subtype_le _
  have hodd : Odd M.index := by
    have h1 := Sylow.not_dvd_index Q₀
    rw [← Subgroup.relIndex_mul_index hQ₀M] at h1
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact fun h => h1 (Dvd.dvd.mul_left h _)
  have hconj : ∀ Q : Sylow 2 G, ∃ g : G, (Q : Subgroup G) =
      (Q₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := fun Q => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₀ Q
    refine ⟨g, ?_⟩
    rw [← hg]
    rfl
  refine ⟨hSylow, hodd, fun Q => ?_, fun F hF hF128 => ?_, fun F hF => ?_⟩
  · obtain ⟨g, hg⟩ := hconj Q
    refine ⟨R.map (MulAut.conj g).toMonoidHom, ⟨?_, isElemAbelian_map hRea _, ?_⟩, ?_⟩
    · rw [hg]
      exact Subgroup.map_mono hRQ₀
    · rw [card_map_conj, hR128]
    · rintro F ⟨hFQ, hF, hF128⟩
      have h1 : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q₀ := map_conj_le_iff.mpr (hg ▸ hFQ)
      exact map_conj_inv_eq
        (hQ₀uniq _ h1 (isElemAbelian_map hF _) (by rw [card_map_conj, hF128]))
  · obtain ⟨Q, hFQ⟩ := (isPGroup_of_isElemAbelian hF).exists_le_sylow
    obtain ⟨g, hg⟩ := hconj Q
    have h1 : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q₀ := map_conj_le_iff.mpr (hg ▸ hFQ)
    exact ⟨g, map_conj_inv_eq
      (hQ₀uniq _ h1 (isElemAbelian_map hF _) (by rw [card_map_conj, hF128]))⟩
  · obtain ⟨Q, hFQ⟩ := (isPGroup_of_isElemAbelian hF).exists_le_sylow
    obtain ⟨g, hg⟩ := hconj Q
    have h1 : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q₀ := map_conj_le_iff.mpr (hg ▸ hFQ)
    rw [← card_map_conj F g⁻¹]
    exact hbound _ (h1.trans hQ₀M) (isElemAbelian_map hF _)

end SylowControl

end BinarySymThreeOrbit

open BinarySymThreeOrbit CFSG.Assembly in
theorem binary_symmetric_three_full_normalizer_sylow_control {G : Type*} [Group G] [Finite G]
    (R : Subgroup G) (θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2))
    (M : Subgroup G) (hM : M = Subgroup.normalizer (R : Set G))
    (ℓ : (Fin 3 → ZMod 2) → G)
    (hℓ : ∀ v, ℓ v = θ.symm (.ofAdd
      (⟨vecMulVec v v, MatrixExtension.vecMulVec_self_mem_binarySymMatrices v⟩, 1)))
    (z : G) (hz : z = ℓ 0)
    (hΩ : ∀ m ∈ M, ∀ v, ∃ w, m⁻¹ * ℓ v * m = ℓ w)
    (hfaith : ∀ m ∈ M, (∀ v, m⁻¹ * ℓ v * m = ℓ v) → m ∈ R)
    (htrans : ∀ v w : Fin 3 → ZMod 2, ∃ m ∈ M, m⁻¹ * ℓ v * m = ℓ w)
    (hstab : ∀ m ∈ M, m⁻¹ * z * m = z → ∃ L : GL (Fin 3) (ZMod 2),
      ∀ v, m⁻¹ * ℓ v * m = ℓ ((L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v))
    (hstab' : ∀ L : GL (Fin 3) (ZMod 2), ∃ m ∈ M,
      ∀ v, m⁻¹ * ℓ v * m = ℓ ((L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)) :
    (IsElemAbelian 2 R ∧ Nat.card R = 128) ∧ Nat.card M = 2 ^ 13 * 21 ∧
    (∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → ¬ F ≤ R → Nat.card F ≤ 64) ∧
    (∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → Nat.card F = 128 → F = R) ∧
    (∀ S : Sylow 2 M, ∃ Q : Sylow 2 G, (Q : Subgroup G) = (S : Subgroup M).map M.subtype ∧
      Nat.card Q = 2 ^ 13 ∧ R ≤ Q ∧
      (∀ F : Subgroup G, F ≤ Q → IsElemAbelian 2 F → Nat.card F = 128 → F = R) ∧
      (R.subgroupOf Q).Characteristic) ∧
    Odd M.index ∧
    (∀ Q : Sylow 2 G, ∃! F : Subgroup G, F ≤ Q ∧ IsElemAbelian 2 F ∧ Nat.card F = 128) ∧
    (∀ F : Subgroup G, IsElemAbelian 2 F → Nat.card F = 128 →
      ∃ g : G, F = R.map (MulAut.conj g).toMonoidHom) ∧
    (∀ F : Subgroup G, IsElemAbelian 2 F → Nat.card F ≤ 128) := by
  obtain rfl : ℓ = ell θ := funext fun v => hℓ v
  subst hz
  have hRM : R ≤ M := hM ▸ Subgroup.le_normalizer
  let θ' : R.subgroupOf M ≃* Multiplicative (binarySymMatrices 3 × ZMod 2) :=
    (Subgroup.subgroupOfEquivOfLe hRM).trans θ
  have hRn : (R.subgroupOf M).Normal := hM ▸ Subgroup.normal_in_normalizer
  have H : IsAffineOrbit θ' :=
    { maps := fun m v => by
        obtain ⟨w, hw⟩ := hΩ m m.2 v
        exact ⟨w, Subtype.ext hw⟩
      faithful := fun m h => hfaith m m.2 fun v => congrArg Subtype.val (h v)
      transitive := fun v w => by
        obtain ⟨m, hm, h⟩ := htrans v w
        exact ⟨⟨m, hm⟩, Subtype.ext h⟩
      stab_linear := fun m h => by
        obtain ⟨L, hL⟩ := hstab m m.2 (congrArg Subtype.val h)
        exact ⟨L, fun v => Subtype.ext (hL v)⟩
      linear_stab := fun L => by
        obtain ⟨m, hm, h⟩ := hstab' L
        exact ⟨⟨m, hm⟩, fun v => Subtype.ext (h v)⟩ }
  have hRea := isElemAbelian_R θ
  have hR128 := card_R θ
  have hcardM : Nat.card M = 2 ^ 13 * 21 := by
    rw [H.card_eq]
    norm_num
  have h64 : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → ¬ F ≤ R → Nat.card F ≤ 64 := by
    intro F hFM hF hFR
    have hFR' : ¬ F.subgroupOf M ≤ R.subgroupOf M := fun h => hFR fun x hx =>
      h (show (⟨x, hFM hx⟩ : M) ∈ F.subgroupOf M from hx)
    have h := H.card_le_sixtyFour (isElemAbelian_subgroupOf hF M) hFR'
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv] at h
  have huniq : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → Nat.card F = 128 → F = R := by
    intro F hFM hF hF128
    by_cases hFR : F ≤ R
    · exact Subgroup.eq_of_le_of_card_ge hFR (by rw [hR128, hF128])
    · have := h64 F hFM hF hFR
      omega
  have hbound : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 2 F → Nat.card F ≤ 128 := by
    intro F hFM hF
    by_cases hFR : F ≤ R
    · rw [← hR128]
      exact Subgroup.card_le_of_le hFR
    · have := h64 F hFM hF hFR
      omega
  obtain ⟨hS, hodd, hQ, hconj, hb⟩ := sylow_control hM hRea hR128 huniq hbound hcardM
  exact ⟨⟨hRea, hR128⟩, hcardM, h64, huniq, hS, hodd, hQ, hconj, hb⟩

end CFSG.LocalAnalysis.ComponentInitial
