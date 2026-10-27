module

public import CFSG.ClassicalInvolution.Models.LinearPairs.Intrinsic
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.GH74.GLS.LU.Lift

public section

open Matrix Module CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU

variable {K : Type} [Field K]

theorem det_eq_neg_one_pow_finrank_eigSpace {n : ℕ} (h2 : (2 : K) ≠ 0)
    {I : Matrix (Fin n) (Fin n) K}
    (hI : I * I = 1) : I.det = (-1) ^ finrank K (eigSpace I (-1)) := by
  have hc := isCompl_eigSpace h2 hI
  set f := Matrix.toLin' I with hf
  let e : (eigSpace I (-1) × eigSpace I 1) ≃ₗ[K] (Fin n → K) :=
    Submodule.prodEquivOfIsCompl _ _ hc
  have key : e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap =
      (-LinearMap.id : eigSpace I (-1) →ₗ[K] eigSpace I (-1)).prodMap
        (LinearMap.id : eigSpace I 1 →ₗ[K] eigSpace I 1) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    have ha := mem_eigSpace_neg_one.mp a.2
    have hb := mem_eigSpace_one.mp b.2
    have h3 : f ((a : Fin n → K) + b) = -(a : Fin n → K) + b := by
      rw [hf, map_add, Matrix.toLin'_apply, Matrix.toLin'_apply, ha, hb]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.prodMap_apply, LinearMap.neg_apply, LinearMap.id_apply]
    rw [LinearEquiv.symm_apply_eq]
    have he : ∀ (a' : eigSpace I (-1)) (b' : eigSpace I 1), e (a', b') = (a' : Fin n → K) + b' :=
      fun a' b' => Submodule.coe_prodEquivOfIsCompl' _ _ hc (a', b')
    rw [he, he, h3]
    simp
  have h1 := LinearMap.det_conj f e.symm
  rw [LinearEquiv.symm_symm] at h1
  rw [← LinearMap.det_toLin' I, ← hf, ← h1, key, LinearMap.det_prodMap, LinearMap.det_id,
    mul_one]
  have : (-LinearMap.id : eigSpace I (-1) →ₗ[K] eigSpace I (-1)) = (-1 : K) • LinearMap.id := by
    ext x; simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]


theorem finrank_eigSpace_neg_one_eq_two_of_det (h2 : (2 : K) ≠ 0) {I : Matrix (Fin 3) (Fin 3) K}
    (hI : I * I = 1) (hdet1 : I.det = 1) (hI1 : I ≠ 1) :
    finrank K (eigSpace I (-1)) = 2 := by
  have hdet := det_eq_neg_one_pow_finrank_eigSpace h2 hI
  rw [hdet1] at hdet
  have hle : finrank K (eigSpace I (-1)) ≤ 3 := (Submodule.finrank_le _).trans (by simp)
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  generalize hd : finrank K (eigSpace I (-1)) = d at hdet hle
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [pow_one] at hdet
    exact hneg hdet.symm
  have hd3 : d ≠ 3 := by
    rintro rfl
    have : (-1 : K) ^ 3 = -1 := by ring
    rw [this] at hdet
    exact hneg hdet.symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hI1
    have hbot : eigSpace I (-1) = ⊥ := Submodule.finrank_eq_zero.mp hd
    have hsup := (isCompl_eigSpace h2 hI).sup_eq_top
    rw [hbot, bot_sup_eq] at hsup
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hv : v ∈ eigSpace I 1 := hsup ▸ Submodule.mem_top
    rw [mem_eigSpace_one] at hv
    rw [hv, Matrix.one_mulVec]
  omega

theorem finrank_eigSpace_neg_one_eq_two (h2 : (2 : K) ≠ 0) {z : SL(3, K)} (hz : z * z = 1)
    (hz1 : z ≠ 1) : finrank K (eigSpace (z : Matrix (Fin 3) (Fin 3) K) (-1)) = 2 :=
  finrank_eigSpace_neg_one_eq_two_of_det h2
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]) z.2
    (fun h => hz1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one])))

theorem mulVec_mem_eigSpace_of_commute {n : ℕ} {I g : Matrix (Fin n) (Fin n) K} (hg : g * I = I * g)
    {c : K} {v : Fin n → K} (hv : v ∈ eigSpace I c) : g *ᵥ v ∈ eigSpace I c := by
  rw [mem_eigSpace] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

theorem finrank_eigSpace_one_of_finrank_neg_one (h2 : (2 : K) ≠ 0) {I : Matrix (Fin 3) (Fin 3) K}
    (hI : I * I = 1) (hdim : finrank K (eigSpace I (-1)) = 2) : finrank K (eigSpace I 1) = 1 := by
  have h := Submodule.finrank_add_eq_of_isCompl (isCompl_eigSpace h2 hI)
  rw [Module.finrank_fin_fun] at h
  omega

theorem exists_smul_of_mem_line {n : ℕ} {W : Submodule K (Fin n → K)} (hW : finrank K W = 1) :
    ∃ w₀ ∈ W, w₀ ≠ 0 ∧ ∀ w ∈ W, ∃ c : K, w = c • w₀ := by
  obtain ⟨⟨v, hvW⟩, hv0, hgen⟩ := finrank_eq_one_iff'.mp hW
  refine ⟨v, hvW, fun h0 => hv0 (Subtype.ext h0), fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := hgen ⟨u, hu⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩


theorem commutator_mem_longRootGroup (h2 : (2 : K) ≠ 0) {z : SL(3, K)}
    (hz : (z : Matrix (Fin 3) (Fin 3) K) * z = 1)
    (hdim : finrank K (eigSpace (z : Matrix (Fin 3) (Fin 3) K) (-1)) = 2) {x y : SL(3, K)}
    (hx : x ∈ Subgroup.centralizer ({z} : Set SL(3, K)))
    (hy : y ∈ Subgroup.centralizer ({z} : Set SL(3, K))) : ⁅x, y⁆ ∈ longRootGroup (z : Matrix (Fin 3) (Fin 3) K) := by
  set I : Matrix (Fin 3) (Fin 3) K := (z : Matrix (Fin 3) (Fin 3) K) with hIdef
  have hmat : ∀ g ∈ Subgroup.centralizer ({z} : Set SL(3, K)),
      (g : Matrix (Fin 3) (Fin 3) K) * I = I * g := fun g hg => by
    have := Subgroup.mem_centralizer_iff.mp hg z rfl
    rw [hIdef, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, this]
  have hline := finrank_eigSpace_one_of_finrank_neg_one h2 hz hdim
  obtain ⟨w₀, hw₀, hw₀0, hgen⟩ := exists_smul_of_mem_line hline
  have hscal : ∀ g ∈ Subgroup.centralizer ({z} : Set SL(3, K)), ∃ c : K,
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w₀ = c • w₀ := fun g hg => by
    obtain ⟨c, hc⟩ := hgen _ (mulVec_mem_eigSpace_of_commute (hmat g hg) hw₀)
    exact ⟨c, hc⟩
  obtain ⟨c1, hc1⟩ := hscal y⁻¹ (Subgroup.inv_mem _ hy)
  obtain ⟨c2, hc2⟩ := hscal x⁻¹ (Subgroup.inv_mem _ hx)
  obtain ⟨c3, hc3⟩ := hscal y hy
  obtain ⟨c4, hc4⟩ := hscal x hx
  have hinv : ∀ (g : SL(3, K)) (a b : K), (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w₀ = a • w₀ →
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ w₀ = b • w₀ → b * a = 1 := by
    intro g a b hga hgb
    have h1 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ w₀) = w₀ := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [hgb, Matrix.mulVec_smul, hga, smul_smul] at h1
    have h2' : (b * a - 1) • w₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2').resolve_right hw₀0)
  have hyy := hinv y c3 c1 hc3 hc1
  have hxx := hinv x c4 c2 hc4 hc2
  have hcomm : (⁅x, y⁆ : SL(3, K)) ∈ Subgroup.centralizer ({z} : Set SL(3, K)) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
      (Subgroup.inv_mem _ hy)
  rw [mem_longRootGroup_iff_vec h2 hz]
  refine ⟨fun w hw => ?_, fun v hv => mulVec_mem_eigSpace_of_commute (hmat _ hcomm) hv⟩
  obtain ⟨μ, rfl⟩ := hgen w hw
  have key : ((⁅x, y⁆ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ w₀ = w₀ := by
    rw [commutatorElement_def]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    simp only [hc1, hc2, hc3, hc4, Matrix.mulVec_smul, smul_smul]
    have : c1 * c2 * c3 * c4 = 1 := by linear_combination (c2 * c4) * hyy + hxx
    rw [this, one_smul]
  rw [Matrix.mulVec_smul, key]


theorem center_pow_three (k : SL(3, K)) (hk : k ∈ Subgroup.center SL(3, K)) : k ^ 3 = 1 := by
  obtain ⟨r, hr, hrk⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  have hr3 : r ^ 3 = 1 := by simpa using hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrk, ← map_pow, hr3, map_one]
  rfl



theorem isLongRootSL2_of_involution (h2 : (2 : K) ≠ 0) {z : SL(3, K)} (hz : z * z = 1)
    (hz1 : z ≠ 1) :
    IsLongRootSL2 (by omega : 2 ≤ 3) (longRootGroup (z : Matrix (Fin 3) (Fin 3) K)) z := by
  have hI : (z : Matrix (Fin 3) (Fin 3) K) * z = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]
  have hdim := finrank_eigSpace_neg_one_eq_two h2 hz hz1
  obtain ⟨i, hi⟩ := exists_isLongRootSL2_of_isCompl h2 (by omega : 2 ≤ 3) (isCompl_eigSpace h2 hI)
    hdim (L := longRootGroup (z : Matrix (Fin 3) (Fin 3) K))
    (fun x => mem_longRootGroup_iff_vec h2 hI)
  have hzmem : z ∈ longRootGroup (z : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_longRootGroup]
    refine ⟨rfl, ?_⟩
    rw [Matrix.mul_add, Matrix.mul_one, hI, add_comm]
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz) hz1
  have := hi.eq_of_orderOf_eq_two h2 hzmem hord
  subst this
  exact hi

theorem commutator_eq_self_of_mulEquiv_perfect {H : Type*} [Group H] (U : Subgroup H)
    {G₀ : Type*} [Group G₀] (hG₀ : Group.IsPerfect G₀) (e : G₀ ≃* U) : ⁅U, U⁆ = U := by
  apply commutator_self_of_isPerfect
  refine ⟨?_⟩
  have h1 : ⁅(⊤ : Subgroup G₀), (⊤ : Subgroup G₀)⁆ = ⊤ := hG₀.commutator_eq_top
  have h2 := Subgroup.map_commutator (⊤ : Subgroup G₀) (⊤ : Subgroup G₀) e.toMonoidHom
  rw [h1] at h2
  have h3 : (⊤ : Subgroup G₀).map e.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  rw [h3] at h2
  exact h2.symm

theorem eq_map_longRootGroup [Finite K] (hK4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) {X : Type}
    [Group X] (α : SL(3, K) →* X) (hker : α.ker ≤ Subgroup.center SL(3, K)) {z : SL(3, K)}
    (hz : z * z = 1) (hz1 : z ≠ 1) {j : ℕ} (hj : j + 2 ≤ 3) (P : SL(3, K))
    (hLj : longRootGroup (z : Matrix (Fin 3) (Fin 3) K) =
      (blockSL K 3 2 j hj).range.map (MulAut.conj P).toMonoidHom)
    {U : Subgroup X} (hU : U ≤ α.range) (eU : SL(2, K) ≃* U) (haU : ∀ u ∈ U, u * α z = α z * u)
    : U = (longRootGroup (z : Matrix (Fin 3) (Fin 3) K)).map α := by
  have hdim := finrank_eigSpace_neg_one_eq_two h2 hz hz1
  have hperf : ⁅U, U⁆ = U :=
    commutator_eq_self_of_mulEquiv_perfect U
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4) eU
  have hUC : ∀ u ∈ U, ∃ g ∈ Subgroup.centralizer ({z} : Set SL(3, K)), α g = u := by
    intro u hu
    obtain ⟨g, rfl⟩ := hU hu
    refine ⟨g, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commute_of_involution_lift α hker center_pow_three hz (haU _ hu)).symm
  have hCL : ⁅Subgroup.centralizer ({z} : Set SL(3, K)), Subgroup.centralizer ({z} : Set SL(3, K))⁆ ≤
      longRootGroup (z : Matrix (Fin 3) (Fin 3) K) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_longRootGroup h2 (by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]) hdim hx hy
  have hle := le_map_of_commutator_le α hCL hperf hUC
  set α' : SL(3, K) →* X := α.comp (MulAut.conj P).toMonoidHom with hα'
  have hinj : Function.Injective (α'.comp (blockSL K 3 2 j hj)) :=
    comp_blockSL_injective (ker_comp_mulEquiv_le_center hker _) hj (by omega)
  have hrange : (α'.comp (blockSL K 3 2 j hj)).range =
      (longRootGroup (z : Matrix (Fin 3) (Fin 3) K)).map α := by
    rw [hLj, MonoidHom.range_eq_map, Subgroup.map_map, MonoidHom.range_eq_map, Subgroup.map_map]
  have hcard : Nat.card ↥((longRootGroup (z : Matrix (Fin 3) (Fin 3) K)).map α) =
      Nat.card SL(2, K) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hfin : Finite ↥((longRootGroup (z : Matrix (Fin 3) (Fin 3) K)).map α) := by
    rw [← hrange]
    exact Finite.of_surjective (MonoidHom.rangeRestrict _) (MonoidHom.rangeRestrict_surjective _)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_congr eU.toEquiv])

theorem linearBlockStandardPair_of_central_involutions [Finite K] (hK4 : 4 ≤ Nat.card K)
    (h2 : (2 : K) ≠ 0) {X : Type} [Group X] (α : SL(3, K) →* X)
    (hker : α.ker ≤ Subgroup.center SL(3, K)) {U V : Subgroup X} (hU : U ≤ α.range)
    (hV : V ≤ α.range) (eU : SL(2, K) ≃* U) (eV : SL(2, K) ≃* V) {a b : X} (ha : a ∈ U)
    (hb : b ∈ V) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (haU : ∀ u ∈ U, u * a = a * u)
    (hbV : ∀ v ∈ V, v * b = b * v) (hab : a ≠ b) (hcomm : a * b = b * a) :
    LinearBlockStandardPair K α.range U V ∧ ∃ x ∈ U, x * b ≠ b * x := by
  have ha1 : a * a = 1 := by rw [← sq, ← ha2]; exact pow_orderOf_eq_one a
  have hb1 : b * b = 1 := by rw [← sq, ← hb2]; exact pow_orderOf_eq_one b
  obtain ⟨ta, hta2, htaa⟩ := exists_involution_lift α hker center_pow_three (hU ha) ha1
  obtain ⟨tb, htb2, htbb⟩ := exists_involution_lift α hker center_pow_three (hV hb) hb1
  have hta1 : ta ≠ 1 := fun h => by
    rw [h, map_one] at htaa
    rw [← htaa] at ha2
    simp at ha2
  have htb1 : tb ≠ 1 := fun h => by
    rw [h, map_one] at htbb
    rw [← htbb] at hb2
    simp at hb2
  have hc : Commute ta tb :=
    (commute_of_involution_lift α hker center_pow_three hta2 (g := tb)
      (by rw [htaa, htbb]; exact hcomm.symm)).symm
  have hne : ta ≠ tb := fun h => hab (by rw [← htaa, ← htbb, h])
  have h₁ := isLongRootSL2_of_involution h2 hta2 hta1
  have h₂ := isLongRootSL2_of_involution h2 htb2 htb1
  rcases inf_eq_bot_or_exists_conj h2 (le_refl 3) h₁ h₂ hc hne with hV0 | ⟨P, e₁, e₂, -, hi₂⟩
  · exfalso
    have d1 := h₁.finrank_minusSpace h2
    have d2 := h₂.finrank_minusSpace h2
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (minusSpace ta) (minusSpace tb)
    rw [hV0, finrank_bot, d1, d2] at hsum
    have : finrank K ↥(minusSpace ta ⊔ minusSpace tb) ≤ 3 :=
      (Submodule.finrank_le _).trans (by simp)
    omega
  · have hU' := eq_map_longRootGroup hK4 h2 α hker hta2 hta1 (by omega : 0 + 2 ≤ 3) P e₁ hU eU
      (by rw [htaa]; exact haU)
    have hV' := eq_map_longRootGroup hK4 h2 α hker htb2 htb1 (by omega : 1 + 2 ≤ 3) P e₂ hV eV
      (by rw [htbb]; exact hbV)
    refine ⟨⟨α, P⁻¹, rfl, hker, Or.inl ⟨?_, ?_⟩⟩, ?_⟩
    · rw [inv_inv]
      show ((blockSL K 3 2 0 (by omega)).range.map (MulAut.conj P).toMonoidHom).map α = U
      rw [← e₁]
      exact hU'.symm
    · rw [inv_inv]
      show ((blockSL K 3 2 1 (by omega)).range.map (MulAut.conj P).toMonoidHom).map α = V
      rw [← e₂]
      exact hV'.symm
    · obtain ⟨A, hA⟩ := not_comm_blockSL_zero_one h2 (le_refl 3) (K := K)
      have hx0 : P * blockSL K 3 2 0 (by omega) A * P⁻¹ ∈
          longRootGroup (ta : Matrix (Fin 3) (Fin 3) K) := by
        rw [e₁]
        exact Subgroup.mem_map.mpr ⟨_, ⟨A, rfl⟩, rfl⟩
      refine ⟨α (P * blockSL K 3 2 0 (by omega) A * P⁻¹), by rw [hU']; exact ⟨_, hx0, rfl⟩,
        fun h => hA ?_⟩
      have h' := commute_of_involution_lift α hker center_pow_three htb2
        (g := P * blockSL K 3 2 0 (by omega) A * P⁻¹) (by rw [htbb]; exact h)
      rw [hi₂] at h'
      calc blockSL K 3 2 0 (by omega) A * blockSL K 3 2 1 (by omega) (-1)
          = P⁻¹ * (P * blockSL K 3 2 0 (by omega) A * P⁻¹ *
              (P * blockSL K 3 2 1 (by omega) (-1) * P⁻¹)) * P := by group
        _ = P⁻¹ * (P * blockSL K 3 2 1 (by omega) (-1) * P⁻¹ *
              (P * blockSL K 3 2 0 (by omega) A * P⁻¹)) * P := by rw [h']
        _ = blockSL K 3 2 1 (by omega) (-1) * blockSL K 3 2 0 (by omega) A := by group

end CFSG.GH74.GLS.LU
