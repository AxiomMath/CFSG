module

public import CFSG.LargeExtraspecial.AS35DFourFiveA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

section FourFive

variable {x : G} (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) (hxx : x * x = 1)
include hxM hxx

theorem isTypeA_rhoL (hq : ∀ v ∈ commSpace (S.rhoL hxM), S.q v = 0) (hxQ : x ∉ S.QG) :
    IsTypeA S.q (S.rhoL hxM) (finrank (ZMod 2) (commSpace (S.rhoL hxM))) :=
  ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (S.rhoL_mem hxM), S.rhoL_ne_one hxM hxQ,
    S.rhoL_mul_self hxM hxx, rfl, hq⟩

theorem isTypeB_or_isTypeC_rhoL (hq : ∃ v ∈ commSpace (S.rhoL hxM), S.q v ≠ 0)
    (hxQ : x ∉ S.QG) :
    IsTypeB S.q (S.rhoL hxM) (finrank (ZMod 2) (commSpace (S.rhoL hxM))) ∨
      IsTypeC S.q (S.rhoL hxM) (finrank (ZMod 2) (commSpace (S.rhoL hxM))) := by
  rcases Nat.even_or_odd (finrank (ZMod 2) (commSpace (S.rhoL hxM))) with h | h
  · exact Or.inr ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (S.rhoL_mem hxM),
      S.rhoL_ne_one hxM hxQ, S.rhoL_mul_self hxM hxx, rfl, h, hq⟩
  · exact Or.inl ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (S.rhoL_mem hxM),
      S.rhoL_mul_self hxM hxx, rfl, h⟩

omit hxx in
theorem isConj_z_mul_of_lt
    (hlt : finrank (ZMod 2) (S.cqxSub x) < finrank (ZMod 2) (fixSpace (S.rhoL hxM))) :
    IsConj x (S.z * x) := by
  have hnle : ¬ S.clPre (fixSpace (S.rhoL hxM)) ≤ S.QG ⊓ centralizer ({x} : Set G) := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [← S.clPre_cqxSub hxM, S.card_clPre, S.card_clPre, S.card_submodule,
      S.card_submodule] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      (Nat.le_of_mul_le_mul_left h1 (by norm_num))
    omega
  obtain ⟨y, hyP, hyC⟩ := Set.not_subset.mp hnle
  have hyQ : y ∈ S.QG := (S.mem_clPre.mp hyP).1
  have hy : x * y * x⁻¹ = y * S.z := ((S.mem_clPre_fixSpace_iff hxM hyQ).mp hyP).resolve_left
    fun h => hyC (S.mem_inf_centralizer_iff_conj.mpr ⟨hyQ, h⟩)
  refine isConj_iff.mpr ⟨y⁻¹, ?_⟩
  calc y⁻¹ * x * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹) * x := by group
    _ = y⁻¹ * (y * S.z) * x := by rw [hy]
    _ = S.z * x := by group

omit hxM hxx in
theorem isotropic_inf_orthogonal (W : Submodule (ZMod 2) S.Qt) :
    ∀ a ∈ W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W,
      ∀ b ∈ W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W, polar S.q a b = 0 := by
  intro a ha b hb
  have := (LinearMap.BilinForm.mem_orthogonal_iff.mp (Submodule.mem_inf.mp ha).2) b
    (Submodule.mem_inf.mp hb).1
  rw [polarBilin_apply_apply, polar_comm] at this
  exact this

omit hxx in
theorem ncard_omegaOne_center :
    {y | y ∈ S.QG ⊓ centralizer ({x} : Set G) ⊓
        centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧ y * y = 1}.ncard
      = 2 * 2 ^ finrank (ZMod 2) (S.singSub
          (S.cqxSub x ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub x))
          (S.isotropic_inf_orthogonal (S.cqxSub x))) := by
  rw [S.center_cqx_eq hxM]
  have hset : {y | y ∈ S.clPre (S.cqxSub x ⊓
      LinearMap.BilinForm.orthogonal S.q.polarBilin (S.cqxSub x)) ∧ y * y = 1} =
      (S.clPre (S.singSub _ (S.isotropic_inf_orthogonal (S.cqxSub x))) : Set G) := by
    ext y
    exact S.mem_clPre_singSub_iff.symm
  rw [hset, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, S.card_clPre, S.card_submodule]

omit hxx in
theorem mem_cqxSub_iff_of_mem_commSpace (hxx : x * x = 1) {v : S.Qt}
    (hv : v ∈ commSpace (S.rhoL hxM)) : v ∈ S.cqxSub x ↔ S.q v = 0 := by
  obtain ⟨u, hu, rfl⟩ := S.exists_cl v
  rw [← S.commute_iff_q_eq_zero_of_cl_mem_commSpace hxM hxx hu hv]
  constructor
  · intro hK
    have h1 : u ∈ S.clPre (S.cqxSub x) := S.mem_clPre.mpr ⟨hu, hK⟩
    rw [S.clPre_cqxSub hxM] at h1
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2).symm
  · intro hc
    exact S.cl_mem_clSub (mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr hc.symm⟩) hu

theorem fourFive (hxQ : x ∉ S.QG) :
    (IsTypeA S.q (S.rhoL hxM) (finrank (ZMod 2) (commSpace (S.rhoL hxM))) ∧
        Nat.card S.QG = 2 ^ finrank (ZMod 2) (commSpace (S.rhoL hxM)) *
          Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) ∧
        {y | y ∈ S.QG ⊓ centralizer ({x} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧
          y * y = 1}.ncard = 2 ^ (finrank (ZMod 2) (commSpace (S.rhoL hxM)) + 1)) ∨
      ((IsTypeB S.q (S.rhoL hxM) (finrank (ZMod 2) (commSpace (S.rhoL hxM))) ∨
          IsTypeC S.q (S.rhoL hxM) (finrank (ZMod 2) (commSpace (S.rhoL hxM)))) ∧
        Nat.card S.QG = 2 ^ (finrank (ZMod 2) (commSpace (S.rhoL hxM)) + 1) *
          Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) ∧
        {y | y ∈ S.QG ⊓ centralizer ({x} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧
          y * y = 1}.ncard = 2 ^ finrank (ZMod 2) (commSpace (S.rhoL hxM)) ∧
        IsConj x (x * S.z)) ∨
      (IsTypeA S.q (S.rhoL hxM) (finrank (ZMod 2) (commSpace (S.rhoL hxM))) ∧
        Nat.card S.QG = 2 ^ (finrank (ZMod 2) (commSpace (S.rhoL hxM)) + 1) *
          Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) ∧
        ({y | y ∈ S.QG ⊓ centralizer ({x} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧
          y * y = 1}.ncard = 2 ^ (finrank (ZMod 2) (commSpace (S.rhoL hxM)) + 1) ∨
         {y | y ∈ S.QG ⊓ centralizer ({x} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧
          y * y = 1}.ncard = 2 ^ (finrank (ZMod 2) (commSpace (S.rhoL hxM)) + 2)) ∧
        IsConj x (S.z * x)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hσ2 := S.rhoL_mul_self hxM hxx
  have hσO := S.rhoL_mem hxM
  have hnd := S.q_nondegenerate
  have hrefl := S.polarBilin_isRefl
  set σ := S.rhoL hxM with hσ
  set U := commSpace σ with hUdef
  set C := fixSpace σ with hCdef
  set K := S.cqxSub x with hKdef
  set B := S.q.polarBilin with hB
  have hCU : C = LinearMap.BilinForm.orthogonal B U :=
    fixSpace_eq_orthogonal_commSpace hnd hσO hσ2
  have hUC : U ≤ C := commSpace_le_fixSpace hσ2
  have hCperp : LinearMap.BilinForm.orthogonal B C = U := by
    rw [hCU, LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
  have hdim : finrank (ZMod 2) U + finrank (ZMod 2) C = 2 * S.width := by
    rw [← S.finrank_Qt_eq_two_mul_width]
    exact finrank_commSpace_add_finrank_fixSpace σ
  have hKC : K ≤ C := S.cqxSub_le_fixSpace hxM
  have hdK1 : finrank (ZMod 2) K ≤ finrank (ZMod 2) C := Submodule.finrank_mono hKC
  have hdK2 : finrank (ZMod 2) C ≤ finrank (ZMod 2) K + 1 := S.finrank_fixSpace_le hxM
  have hcard := S.card_QG_eq_mul hxM
  have hΩ := S.ncard_omegaOne_center hxM
  have hUKp : U ≤ LinearMap.BilinForm.orthogonal B K := by
    rw [← hCperp]
    exact LinearMap.BilinForm.orthogonal_le hKC
  have hdKp : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal B K) =
      2 * S.width - finrank (ZMod 2) K := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, S.finrank_Qt_eq_two_mul_width]
  have hUK := fun v (hv : v ∈ U) => S.mem_cqxSub_iff_of_mem_commSpace hxM hxx hv
  set W := LinearMap.BilinForm.orthogonal B K with hWdef
  set Z := S.singSub (K ⊓ W) (S.isotropic_inf_orthogonal K) with hZdef
  have hZW : Z ≤ K ⊓ W := S.singSub_le _ _
  rcases Nat.lt_or_ge (finrank (ZMod 2) K) (finrank (ZMod 2) C) with hlt | hge
  ·
    have hconj := S.isConj_z_mul_of_lt hxM hlt
    have hk : 2 * S.width - finrank (ZMod 2) K = finrank (ZMod 2) U + 1 := by omega
    rw [hk] at hcard
    by_cases hq : ∀ v ∈ U, S.q v = 0
    ·
      right; right
      refine ⟨S.isTypeA_rhoL hxM hxx hq hxQ, hcard, ?_, hconj⟩
      have hUZ : U ≤ Z := fun v hv =>
        S.mem_singSub.mpr ⟨Submodule.mem_inf.mpr ⟨(hUK v hv).mpr (hq v hv), hUKp hv⟩, hq v hv⟩
      have h1 := Submodule.finrank_mono hUZ
      have h2 := Submodule.finrank_mono (hZW.trans inf_le_right)
      rw [hdKp, hk] at h2
      rw [hΩ]
      rcases Nat.lt_or_ge (finrank (ZMod 2) Z) (finrank (ZMod 2) U + 1) with h3 | h3
      · left
        rw [show finrank (ZMod 2) Z = finrank (ZMod 2) U by omega]
        ring
      · right
        rw [show finrank (ZMod 2) Z = finrank (ZMod 2) U + 1 by omega]
        ring
    ·
      push Not at hq
      obtain ⟨v₀, hv₀U, hv₀q⟩ := hq
      right; left
      refine ⟨S.isTypeB_or_isTypeC_rhoL hxM hxx ⟨v₀, hv₀U, hv₀q⟩ hxQ, hcard, ?_, ?_⟩
      · have hv₀K : v₀ ∉ K := fun h => hv₀q ((hUK v₀ hv₀U).mp h)
        have hv₀0 : v₀ ≠ 0 := fun h => hv₀K (h ▸ K.zero_mem)
        have hspan : finrank (ZMod 2) (ZMod 2 ∙ v₀) = 1 := finrank_span_singleton hv₀0
        have hinf : K ⊓ (ZMod 2 ∙ v₀) = ⊥ := by
          rw [eq_bot_iff]
          intro w hw
          obtain ⟨hwK, hwv⟩ := Submodule.mem_inf.mp hw
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hwv
          rcases zmod2_cases a with rfl | rfl
          · rw [zero_smul]
            exact Submodule.zero_mem _
          · rw [one_smul] at hwK
            exact absurd hwK hv₀K
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq K (ZMod 2 ∙ v₀)
        rw [hinf, finrank_bot, hspan] at hsup
        have hKv : K ⊔ (ZMod 2 ∙ v₀) = C := Submodule.eq_of_le_of_finrank_eq
          (sup_le hKC ((Submodule.span_singleton_le_iff_mem _ _).mpr (hUC hv₀U))) (by omega)
        have hKW : K ⊓ W = K ⊓ U := by
          refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
          · obtain ⟨hvK, hvW⟩ := Submodule.mem_inf.mp hv
            refine Submodule.mem_inf.mpr ⟨hvK, ?_⟩
            rw [← hCperp, LinearMap.BilinForm.mem_orthogonal_iff]
            intro c hc
            rw [← hKv] at hc
            obtain ⟨k, hk, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
            obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
            have e1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvW) k hk
            have hvC : v ∈ LinearMap.BilinForm.orthogonal B U := hCU ▸ hKC hvK
            have e2 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvC) v₀ hv₀U
            change B (k + a • v₀) v = 0
            rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
            change B k v + a • B v₀ v = 0
            rw [show B k v = 0 from e1, show B v₀ v = 0 from e2, smul_zero, add_zero]
          · obtain ⟨hvK, hvU⟩ := Submodule.mem_inf.mp hv
            exact Submodule.mem_inf.mpr ⟨hvK, hUKp hvU⟩
        have hZeq : Z = K ⊓ U := by
          refine le_antisymm (hZW.trans hKW.le) fun v hv => ?_
          obtain ⟨hvK, hvU⟩ := Submodule.mem_inf.mp hv
          exact S.mem_singSub.mpr ⟨hKW ▸ hv, (hUK v hvU).mp hvK⟩
        have hsup2 := Submodule.finrank_sup_add_finrank_inf_eq K U
        have hKU : K ⊔ U = C := by
          have h1 : K ⊔ (ZMod 2 ∙ v₀) ≤ K ⊔ U :=
            sup_le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hv₀U) K
          rw [hKv] at h1
          exact le_antisymm (sup_le hKC hUC) h1
        rw [hKU] at hsup2
        have hm1 : 1 ≤ finrank (ZMod 2) U := by
          have := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hv₀U)
          omega
        rw [hΩ, hZeq, show finrank (ZMod 2) ↥(K ⊓ U) = finrank (ZMod 2) U - 1 by omega,
          ← pow_succ', Nat.sub_add_cancel hm1]
      · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
        refine isConj_iff.mpr ⟨c, ?_⟩
        rw [hc, S.z_comm hxM]
  ·
    left
    have hKeq : K = C := Submodule.eq_of_le_of_finrank_eq hKC (le_antisymm hdK1 hge)
    have hq : ∀ v ∈ U, S.q v = 0 := fun v hv => (hUK v hv).mp (by
      have h := hUC hv
      rw [← hKeq] at h
      exact h)
    have hk : 2 * S.width - finrank (ZMod 2) K = finrank (ZMod 2) U := by
      rw [hKeq]
      omega
    rw [hk] at hcard
    refine ⟨S.isTypeA_rhoL hxM hxx hq hxQ, hcard, ?_⟩
    have hZeq : Z = U := by
      refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
      · have := (hZW hv)
        rw [hWdef, hKeq, hCperp] at this
        exact (Submodule.mem_inf.mp this).2
      · refine S.mem_singSub.mpr ⟨?_, hq v hv⟩
        rw [hWdef, hKeq, hCperp]
        exact Submodule.mem_inf.mpr ⟨hUC hv, hv⟩
    rw [hΩ, hZeq]
    ring

end FourFive

end Setting

end CFSG.LargeExtraspecial
