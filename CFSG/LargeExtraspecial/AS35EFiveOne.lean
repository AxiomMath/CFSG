module

public import CFSG.LargeExtraspecial.AS35DFourFive
public import CFSG.LargeExtraspecial.AS35EDSet

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Asc77

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem isConj_of_mem_ESet {t : G} (ht : t ∈ S.ESet) : IsConj S.z t := by
  obtain ⟨h, rfl, -⟩ := ht
  exact isConj_iff.mpr ⟨h, rfl⟩

omit [Finite G] in
theorem mul_self_of_isConj {x : G} (hx : IsConj S.z x) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hx
  rw [show c * S.z * c⁻¹ * (c * S.z * c⁻¹) = c * (S.z * S.z) * c⁻¹ by group, S.z_mul_z]
  group

theorem mem_zConj_of_mem_ESet {t h : G} (ht : t ∈ S.ESet) (hh : h * S.z * h⁻¹ = t) :
    t ∈ S.zConj (S.HAt h) :=
  hh ▸ S.mem_zConj_of_ncard_eq_five (S.isHStar_of_mem_ESet ht hh).2

theorem mem_M_of_mem_ESet (hS : S.SixFourConcl) {t : G} (ht : t ∈ S.ESet) : t ∈ S.M := by
  obtain ⟨h, hh, hH, -⟩ := id ht
  obtain ⟨⟨_, _, -, hcomm, -⟩, -⟩ := (hS _ hH).1
  exact S.mem_M_iff.mpr
    (hcomm t (S.mem_zConj_of_mem_ESet ht hh) S.z (self_mem_conjIn _ _))

theorem not_mem_QG_of_mem_ESet (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {t : G} (ht : t ∈ S.ESet) : t ∉ S.QG := by
  intro htQ
  obtain ⟨h, hh, -⟩ := id ht
  exact S.ne_z_of_mem_ESet ht (hh.symm.trans (hW h (by rw [hh]; exact htQ)))

theorem not_isConj_mul_z_of_mem_DSet (hS : S.SixFourConcl) {t : G} (ht : t ∈ S.DSet) :
    ¬ IsConj t (t * S.z) ∧ ¬ IsConj t (S.z * t) := by
  have hzt := S.isConj_of_mem_ESet ht.1
  have hcomm : t * S.z = S.z * t := S.mem_M_iff.mp (S.mem_M_of_mem_ESet hS ht.1)
  refine ⟨fun h => ht.2 (hzt.trans ?_), fun h => ht.2 (hzt.trans h)⟩
  rwa [hcomm] at h

theorem card_commSpace_le {t : G} (ht : t ∈ S.ESet) (htM : t ∈ S.M) :
    Nat.card (commSpace (S.rhoL htM)) ≤ 4 := by
  obtain ⟨h, hh, -, h5⟩ := id ht
  have htH := S.mem_zConj_of_mem_ESet ht hh
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsub : (commSpace (S.rhoL htM) : Set S.Qt) ⊆
      (fun p => S.cl (t * p)) '' (S.zConj (S.HAt h) \ {S.z}) := by
    intro v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    obtain ⟨y, hy, rfl⟩ := S.exists_cl w
    have hyM := S.QG_le_M hy
    refine ⟨y * t * y⁻¹, ⟨conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa h) hy) htH, ?_⟩, ?_⟩
    · intro h1
      apply S.ne_z_of_mem_ESet ht
      have h2 : y⁻¹ * S.z * y = S.z := by
        have := S.conj_z_of_mem_M (S.M.inv_mem hyM)
        rwa [inv_inv] at this
      calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
        _ = S.z := by rw [h1, h2]
    · have hc : t * (y * t * y⁻¹) = (t * y * t⁻¹) * y⁻¹ := by rw [htinv]; group
      simp only
      rw [hc, S.cl_mul (S.conj_mem_QG htM hy) (S.QG.inv_mem hy), S.cl_inv hy,
        ← S.rhoL_cl htM hy, sub_eq_add_vec (ZMod 2)]
  have h1 : Nat.card (commSpace (S.rhoL htM)) =
      (commSpace (S.rhoL htM) : Set S.Qt).ncard := Nat.card_coe_set_eq _
  have h2 := Set.ncard_le_ncard hsub
  have h3 : ((fun p => S.cl (t * p)) '' (S.zConj (S.HAt h) \ {S.z})).ncard ≤
      (S.zConj (S.HAt h) \ {S.z}).ncard := Set.ncard_image_le
  have h4 : (S.zConj (S.HAt h) \ {S.z}).ncard = 4 := by
    rw [Set.ncard_sdiff_singleton_of_mem (self_mem_conjIn _ _), h5]
  omega

theorem fiveOne_two (hS : S.SixFourConcl)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {t : G} (ht : t ∈ S.DSet)
    (htM : t ∈ S.M) :
    IsTypeA S.q (S.rhoL htM) 2 ∧
      Nat.card S.QG = 4 * Nat.card ↥(S.QG ⊓ centralizer ({t} : Set G)) ∧
      S.cqxSub t = fixSpace (S.rhoL htM) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have htQ := S.not_mem_QG_of_mem_ESet hW ht.1
  obtain ⟨hn1, hn2⟩ := S.not_isConj_mul_z_of_mem_DSet hS ht
  rcases S.fourFive htM htt htQ with ⟨hA, hcard, -⟩ | ⟨-, -, -, hc⟩ | ⟨-, -, -, hc⟩
  rotate_left
  · exact absurd hc hn1
  · exact absurd hc hn2
  generalize hm : finrank (ZMod 2) (commSpace (S.rhoL htM)) = m at hA hcard
  have hK : S.cqxSub t = fixSpace (S.rhoL htM) := by
    have h1 := S.card_QG_eq_mul htM
    rw [hcard] at h1
    have hc0 : 0 < Nat.card ↥(S.QG ⊓ centralizer ({t} : Set G)) := Nat.card_pos
    have h2 : 2 ^ m = 2 ^ (2 * S.width - finrank (ZMod 2) (S.cqxSub t)) :=
      Nat.eq_of_mul_eq_mul_right hc0 h1
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    have h4 := finrank_commSpace_add_finrank_fixSpace (S.rhoL htM)
    rw [S.finrank_Qt_eq_two_mul_width, hm] at h4
    have hle : finrank (ZMod 2) (S.cqxSub t) ≤ finrank (ZMod 2) (fixSpace (S.rhoL htM)) :=
      Submodule.finrank_mono (S.cqxSub_le_fixSpace htM)
    exact Submodule.eq_of_le_of_finrank_eq (S.cqxSub_le_fixSpace htM) (by omega)
  have hm2 : m = 2 := by
    have hev := even_finrank_commSpace_of_forall_eq_zero S.q_nondegenerate (S.rhoL_mem htM)
      (S.rhoL_mul_self htM htt) hA.2.2.2.2
    rw [hm] at hev
    have hpos : m ≠ 0 := by
      intro h0
      apply S.rhoL_ne_one htM htQ
      have hbot := Submodule.finrank_eq_zero.mp (hm.trans h0)
      refine LinearEquiv.ext fun v => ?_
      have h1 := sub_mem_commSpace (S.rhoL htM) v
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
      exact h1
    have hle : 2 ^ m ≤ 2 ^ 2 := by
      have := S.card_commSpace_le ht.1 htM
      rw [S.card_submodule, hm] at this
      exact this
    have hle' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    obtain ⟨r, hr⟩ := hev
    omega
  refine ⟨hm2 ▸ hA, ?_, hK⟩
  rw [hcard, hm2]
  norm_num

theorem mem_closure_zConj_of_cl_mem_commSpace {t h : G} (ht : t ∈ S.ESet)
    (hh : h * S.z * h⁻¹ = t) (htM : t ∈ S.M) {x : G} (hx : x ∈ S.QG)
    (hcx : S.cl x ∈ commSpace (S.rhoL htM)) : x ∈ closure (S.zConj (S.HAt h)) := by
  have htH := S.mem_zConj_of_mem_ESet ht hh
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨w, hw⟩ := mem_commSpace.mp hcx
  obtain ⟨y, hy, rfl⟩ := S.exists_cl w
  have hyt : y * t * y⁻¹ ∈ S.zConj (S.HAt h) :=
    conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa h) hy) htH
  have hc : t * (y * t * y⁻¹) = (t * y * t⁻¹) * y⁻¹ := by rw [htinv]; group
  have hcQ : t * (y * t * y⁻¹) ∈ S.QG := by
    rw [hc]
    exact S.QG.mul_mem (S.conj_mem_QG htM hy) (S.QG.inv_mem hy)
  have hcl : S.cl (t * (y * t * y⁻¹)) = S.cl x := by
    rw [← hw, hc, S.cl_mul (S.conj_mem_QG htM hy) (S.QG.inv_mem hy), S.cl_inv hy,
      ← S.rhoL_cl htM hy, sub_eq_add_vec (ZMod 2)]
  have hcV : t * (y * t * y⁻¹) ∈ closure (S.zConj (S.HAt h)) :=
    mul_mem (subset_closure htH) (subset_closure hyt)
  rcases (S.cl_eq_cl_iff hcQ hx).mp hcl with h1 | h1
  · rw [h1]
    exact hcV
  · rw [h1]
    exact mul_mem hcV (subset_closure (self_mem_conjIn _ _))

theorem cl_mem_commSpace_of_commute (hS : S.SixFourConcl)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {t : G} (ht : t ∈ S.DSet)
    (htM : t ∈ S.M) {x : G} (hx : x ∈ S.QG)
    (hc : ∀ y ∈ S.QG ⊓ centralizer ({t} : Set G), y * x = x * y) :
    S.cl x ∈ commSpace (S.rhoL htM) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  obtain ⟨-, -, hK⟩ := S.fiveOne_two hS hW ht htM
  have h1 := S.centralizer_inf_QG_eq_clPre (X := S.QG ⊓ centralizer ({t} : Set G)) inf_le_left
  have h2 : x ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr hc⟩
  rw [h1] at h2
  have h3 := (S.mem_clPre.mp h2).2
  change S.cl x ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub t) at h3
  rwa [hK, fixSpace_eq_orthogonal_commSpace S.q_nondegenerate (S.rhoL_mem htM)
    (S.rhoL_mul_self htM htt),
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl] at h3

theorem conj_eq_of_cl_conj_eq (hS : S.SixFourConcl)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {t : G} (ht : t ∈ S.DSet)
    (htM : t ∈ S.M) {y : G} (hy : y ∈ S.QG) (h : S.cl (t * y * t⁻¹) = S.cl y) :
    t * y * t⁻¹ = y := by
  obtain ⟨-, -, hK⟩ := S.fiveOne_two hS hW ht htM
  have h1 : S.cl y ∈ fixSpace (S.rhoL htM) := by
    rw [mem_fixSpace, S.rhoL_cl htM hy, h]
  rw [← hK] at h1
  have h2 : y ∈ S.clPre (S.cqxSub t) := S.mem_clPre.mpr ⟨hy, h1⟩
  rw [S.clPre_cqxSub htM] at h2
  exact (S.mem_inf_centralizer_iff_conj.mp h2).2

theorem cl_mem_commSpace_of_mul_mem (hS : S.SixFourConcl)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {t x : G} (ht : t ∈ S.DSet)
    (htM : t ∈ S.M) (hx : x ∈ S.QG) (hxt : x * t ∈ S.DSet) :
    S.cl x ∈ commSpace (S.rhoL htM) := by
  have hxtM := S.mem_M_of_mem_ESet hS hxt.1
  have hsub : ∀ y ∈ S.QG ⊓ centralizer ({x * t} : Set G),
      y ∈ S.QG ⊓ centralizer ({t} : Set G) ∧ x * y * x⁻¹ = y := by
    intro y hy
    obtain ⟨hyQ, hyc⟩ := S.mem_inf_centralizer_iff_conj.mp hy
    have e1 : t * y * t⁻¹ = x⁻¹ * y * x := by
      calc t * y * t⁻¹ = x⁻¹ * ((x * t) * y * (x * t)⁻¹) * x := by group
        _ = x⁻¹ * y * x := by rw [hyc]
    have e2 : S.cl (t * y * t⁻¹) = S.cl y := by
      rw [e1, S.cl_mul (S.QG.mul_mem (S.QG.inv_mem hx) hyQ) hx,
        S.cl_mul (S.QG.inv_mem hx) hyQ, S.cl_inv hx, add_comm (S.cl x) (S.cl y), add_assoc,
        ZModModule.add_self, add_zero]
    have e3 := S.conj_eq_of_cl_conj_eq hS hW ht htM hyQ e2
    refine ⟨S.mem_inf_centralizer_iff_conj.mpr ⟨hyQ, e3⟩, ?_⟩
    calc x * y * x⁻¹ = x * (x⁻¹ * y * x) * x⁻¹ := by rw [← e1, e3]
      _ = y := by group
  have hle : S.QG ⊓ centralizer ({x * t} : Set G) ≤ S.QG ⊓ centralizer ({t} : Set G) :=
    fun y hy => (hsub y hy).1
  have hcard1 := (S.fiveOne_two hS hW hxt hxtM).2.1
  have hcard2 := (S.fiveOne_two hS hW ht htM).2.1
  have heq : S.QG ⊓ centralizer ({x * t} : Set G) = S.QG ⊓ centralizer ({t} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (by omega)
  refine S.cl_mem_commSpace_of_commute hS hW ht htM hx fun y hy => ?_
  rw [← heq] at hy
  have h1 := (hsub y hy).2
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

end Setting

end CFSG.LargeExtraspecial
