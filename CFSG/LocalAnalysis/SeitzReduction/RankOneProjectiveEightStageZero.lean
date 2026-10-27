module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneProjectiveEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStage
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndings
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.SeitzReduction.RankOne

open Equiv Subgroup DegreeEight CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV
  CFSG.LocalAnalysis.SteinbergBX
open scoped LinearAlgebra.Projectivization CFSG.SeitzReduction.RankOne.DegreeEight

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section StageZero

variable {D : Type} [Group D]

private theorem projEight_mem_normalizer_zpowers_of_commute {x t : D} (hxt : x * t = t * x) :
    x ∈ normalizer ((zpowers t : Subgroup D) : Set D) := by
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact (Commute.zpow_right hxt k).eq.symm

private theorem projEight_mem_of_forall_conj_eq {R U : Subgroup D}
    (hC : normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R) {x : D}
    (hx : ∀ v ∈ U ⊔ R, x * v * x⁻¹ = v) : x ∈ U ⊔ R := by
  rw [← hC]
  refine mem_inf.mpr ⟨?_, ?_⟩
  · apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro r hr
    have h1 := hx r (mem_sup_right hr)
    calc r * x = x * r * x⁻¹ * x := by rw [h1]
      _ = x * r := by group
  · rw [mem_centralizer_iff]
    intro u hu
    have h1 := hx u (mem_sup_left hu)
    calc u * x = x * u * x⁻¹ * x := by rw [h1]
      _ = x * u := by group

variable [Finite D]

theorem exists_coords_of_gms_projective_eight {J R X U P : Subgroup D} {t : D}
    (hS : GMS28.Setup J R X U P 3 t)
    (hC : normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R)
    (hβ : ∃ β : gmsRootConjugates (U ⊔ R) R ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7),
      ∀ σ : Perm (gmsRootConjugates (U ⊔ R) R),
        σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range ↔
          ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7), ∀ Q, β (σ Q) = g • β Q) :
    ∃ π : normalizer ((U ⊔ R : Subgroup D) : Set D) →* Perm (Option (ZMod 7)),
      ∃ e : gmsRootConjugates (U ⊔ R) R ≃ Option (ZMod 7),
        π.range = natPSL ∧ (∀ x, π x = 1 ↔ (x : D) ∈ U ⊔ R) ∧
          ∀ x Q, π x (e Q) = e (gmsRootConjugateAction (U ⊔ R) R x Q) := by
  obtain ⟨β, hβ⟩ := hβ
  set π₀ := gmsRootConjugateAction (U ⊔ R) R with hπ₀
  have hker₀ : ∀ x : normalizer ((U ⊔ R : Subgroup D) : Set D),
      π₀ x = 1 ↔ (x : D) ∈ U ⊔ R := by
    intro x
    constructor
    · intro hx
      exact projEight_mem_of_forall_conj_eq hC (hS.conj_eq_of_action_eq_one x hx)
    · intro hxV
      have h1 : x ∈ (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
          (normalizer ((U ⊔ R : Subgroup D) : Set D)) := by
        rw [mem_subgroupOf, mem_centralizer_iff]
        intro v hv
        exact gms_comm_V hS.data v hv x hxV
      have h2 := centralizer_le_gmsRootKernel (U ⊔ R) R h1
      rw [← ker_gmsRootConjugateAction] at h2
      exact h2
  set e : gmsRootConjugates (U ⊔ R) R ≃ Option (ZMod 7) := β.trans projEquiv.symm with he
  set κ : Perm (gmsRootConjugates (U ⊔ R) R) ≃* Perm (Option (ZMod 7)) := e.permCongrHom with hκ
  refine ⟨κ.toMonoidHom.comp π₀, e, ?_, fun x => ?_, fun x Q => ?_⟩
  · have hπapply : ∀ x z, (κ.toMonoidHom.comp π₀) x z = e (π₀ x (e.symm z)) := fun x z => rfl
    have hproj_e : ∀ Q, projEquiv (e Q) = β Q := fun Q => by simp [he]
    ext τ
    rw [mem_natPSL_iff]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨g, hg⟩ := (hβ (π₀ x)).mp ⟨x, rfl⟩
      refine ⟨g, fun z => ?_⟩
      rw [hπapply, hproj_e, hg]
      congr 1
      rw [← hproj_e, Equiv.apply_symm_apply]
    · rintro ⟨g, hg⟩
      have hmem : κ.symm τ ∈ π₀.range := by
        rw [hβ]
        refine ⟨g, fun Q => ?_⟩
        have h1 := hg (e Q)
        rw [hproj_e] at h1
        rw [← h1, ← hproj_e]
        congr 1
        change e (e.symm (τ (e Q))) = τ (e Q)
        exact Equiv.apply_symm_apply _ _
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, by change κ (π₀ x) = τ; rw [hx, MulEquiv.apply_symm_apply]⟩
  · rw [← hker₀ x]
    constructor
    · intro h1
      apply κ.injective
      rw [map_one]
      exact h1
    · intro h1
      change κ (π₀ x) = 1
      rw [h1, map_one]
  · change e (π₀ x (e.symm (e Q))) = e (π₀ x Q)
    rw [Equiv.symm_apply_apply]

theorem normalizer_inf_centralizer_eq_of_gms_projective_eight {J R X U P : Subgroup D} {t : D}
    (hS : GMS28.Setup J R X U P 3 t)
    (hC : normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R)
    (hβ : ∃ β : gmsRootConjugates (U ⊔ R) R ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7),
      ∀ σ : Perm (gmsRootConjugates (U ⊔ R) R),
        σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range ↔
          ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7), ∀ Q, β (σ Q) = g • β Q) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) = U ⊔ R := by
  obtain ⟨π, e, hrange, hker, hequiv⟩ := exists_coords_of_gms_projective_eight hS hC hβ
  have hdata := hS.data
  have htV : t ∈ U ⊔ R := hS.t_mem_V
  have htt : t * t = 1 := hS.mul_self_t
  have hcommV := gms_comm_V hdata
  have hsq := gms_sq_V hdata
  have hVN : U ⊔ R ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) := le_normalizer
  obtain ⟨-, -, hnz, -, -, -⟩ := gms_normal_root_partition_and_two_transitivity hdata hS.three_le
  refine le_antisymm (fun y0 hy0 => ?_) (le_inf hVN fun v hv => mem_centralizer_iff.mpr fun u hu =>
    hcommV u (mem_sup_left hu) v hv)
  obtain ⟨hy0N, hy0C⟩ := mem_inf.mp hy0
  set W : Subgroup (normalizer ((U ⊔ R : Subgroup D) : Set D)) :=
    (centralizer (U : Set D)).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D)) with hW
  have hEN : W.map π ≤ natPSL := by rw [← hrange]; exact map_le_range π W
  have hEn : ∀ g' ∈ natPSL, ∀ e' ∈ W.map π, g' * e' * g'⁻¹ ∈ W.map π := by
    intro g' hg' e' he'
    rw [← hrange] at hg'
    obtain ⟨y', rfl⟩ := hg'
    obtain ⟨y, hy, rfl⟩ := he'
    refine ⟨y' * y * y'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, hW, mem_subgroupOf, mem_centralizer_iff] at hy ⊢
    intro u hu
    have hu' : (y' : D)⁻¹ * u * (y' : D)⁻¹⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (hS.normalizer_V_le (inv_mem y'.2)) u).mp hu
    rw [inv_inv] at hu'
    have h1 := hy _ hu'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc u * ((y' : D) * y * (y' : D)⁻¹)
        = (y' : D) * ((y' : D)⁻¹ * u * y' * y) * (y' : D)⁻¹ := by group
      _ = (y' : D) * (y * ((y' : D)⁻¹ * u * y')) * (y' : D)⁻¹ := by rw [h1]
      _ = (y' : D) * y * (y' : D)⁻¹ * u := by group
  have hfree : ∀ e' ∈ W.map π, ∀ z, e' z = z → e' = 1 := by
    rintro _ ⟨y, hy, rfl⟩ z hz
    rw [SetLike.mem_coe, hW, mem_subgroupOf, mem_centralizer_iff] at hy
    obtain ⟨Q, rfl⟩ := e.surjective z
    have hQfix : gmsRootConjugateAction (U ⊔ R) R y Q = Q :=
      e.injective ((hequiv y Q).symm.trans hz)
    obtain ⟨k, hk, hkV⟩ := Q.2
    have hq : k⁻¹ * t * k ∈ (Q : Subgroup D) := by
      rw [hk]
      exact ⟨t, hS.mem, by simp⟩
    have hq1 : k⁻¹ * t * k ≠ 1 := fun h1 => hS.ne_one (by
      have h2 : t = k * (k⁻¹ * t * k) * k⁻¹ := by group
      rw [h2, h1]; group)
    have hqU : k⁻¹ * t * k ∉ U := hnz Q Q.2 _ hq hq1
    have hqV : k⁻¹ * t * k ∈ U ⊔ R := hkV hq
    have hyq : (y : D) * (k⁻¹ * t * k) * (y : D)⁻¹ = k⁻¹ * t * k := by
      have h1 : (Q : Subgroup D).map (MulAut.conj (y : D)).toMonoidHom = Q := by
        have h2 := congrArg Subtype.val hQfix
        rwa [gmsRootConjugateAction_apply] at h2
      have h2 : (y : D) * (k⁻¹ * t * k) * (y : D)⁻¹ ∈ (Q : Subgroup D) := by
        rw [← h1]; exact ⟨_, hq, rfl⟩
      rw [hk] at h2
      obtain ⟨r, hr, hr'⟩ := h2
      rcases hS.eq_one_or_eq_t hr with rfl | rfl
      · exfalso
        apply hq1
        have h3 : (y : D) * (k⁻¹ * t * k) * (y : D)⁻¹ = 1 := by rw [← hr']; simp
        calc k⁻¹ * t * k = (y : D)⁻¹ * ((y : D) * (k⁻¹ * t * k) * (y : D)⁻¹) * y := by group
          _ = 1 := by rw [h3]; group
      · rw [← hr']
        simp
    have hqq : (k⁻¹ * t * k) * (k⁻¹ * t * k) = 1 := by
      rw [← sq]; exact hsq _ hqV
    have hyV : (y : D) ∈ U ⊔ R := by
      apply projEight_mem_of_forall_conj_eq hC
      intro v hv
      by_cases hvU : v ∈ U
      · have h1 := hy v hvU
        calc (y : D) * v * (y : D)⁻¹ = v * y * (y : D)⁻¹ := by rw [h1]
          _ = v := by group
      · have hqv : (k⁻¹ * t * k) * v ∈ U := by
          have h1 := (hS.mem_or_mul_mem hqV).resolve_left hqU
          have h2 := (hS.mem_or_mul_mem hv).resolve_left hvU
          have h3 : (k⁻¹ * t * k) * v = ((k⁻¹ * t * k) * t) * (v * t) := by
            rw [hcommV v hv t htV]
            calc (k⁻¹ * t * k) * v = (k⁻¹ * t * k) * (t * t) * v := by rw [htt, mul_one]
              _ = ((k⁻¹ * t * k) * t) * (t * v) := by group
          rw [h3]
          exact mul_mem h1 h2
        have h4 := hy _ hqv
        have h5 : (y : D) * ((k⁻¹ * t * k) * v) * (y : D)⁻¹ = (k⁻¹ * t * k) * v := by
          calc (y : D) * ((k⁻¹ * t * k) * v) * (y : D)⁻¹
              = ((k⁻¹ * t * k) * v) * y * (y : D)⁻¹ := by rw [h4]
            _ = (k⁻¹ * t * k) * v := by group
        calc (y : D) * v * (y : D)⁻¹
            = (y : D) * (((k⁻¹ * t * k) * (k⁻¹ * t * k)) * v) * (y : D)⁻¹ := by
              rw [hqq, one_mul]
          _ = ((y : D) * (k⁻¹ * t * k) * (y : D)⁻¹) *
                ((y : D) * ((k⁻¹ * t * k) * v) * (y : D)⁻¹) := by group
          _ = (k⁻¹ * t * k) * ((k⁻¹ * t * k) * v) := by rw [hyq, h5]
          _ = v := by rw [← mul_assoc, hqq, one_mul]
    exact (hker y).mpr hyV
  have hEbot := eq_bot_of_normal_of_fixedPointFree hEN hEn hfree
  have hyE : π ⟨y0, hy0N⟩ ∈ W.map π := ⟨⟨y0, hy0N⟩, by
    rw [SetLike.mem_coe, hW, mem_subgroupOf]; exact hy0C, rfl⟩
  rw [hEbot, mem_bot] at hyE
  exact (hker _).mp hyE

theorem exists_normal_index_two_of_gms_projective_eight {J R X U P : Subgroup D} {t : D}
    (hS : GMS28.Setup J R X U P 3 t)
    (hC : normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R)
    (hβ : ∃ β : gmsRootConjugates (U ⊔ R) R ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7),
      ∀ σ : Perm (gmsRootConjugates (U ⊔ R) R),
        σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range ↔
          ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7), ∀ Q, β (σ Q) = g • β Q) :
    ∃ M : Subgroup D, M.Normal ∧ M.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, e, hrange, hker, hequiv⟩ := exists_coords_of_gms_projective_eight hS hC hβ
  have hNT := normalizer_inf_centralizer_eq_of_gms_projective_eight hS hC hβ
  have hdata := hS.data
  have htV : t ∈ U ⊔ R := hS.t_mem_V
  have htU : t ∉ U := hS.t_notMem_U
  have htt : t * t = 1 := hS.mul_self_t
  have hUV : U ≤ U ⊔ R := le_sup_left
  have hcommV := gms_comm_V hdata
  have hsq := gms_sq_V hdata
  have hUcard : Nat.card U = 2 ^ 3 := hdata.2.2.2.2.1.2.2.2
  have hVN : U ⊔ R ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) := le_normalizer
  obtain ⟨-, -, hnz, hpart, -, -⟩ :=
    gms_normal_root_partition_and_two_transitivity hdata hS.three_le
  have hmemN : ∀ x, π x ∈ natPSL := fun x => by rw [← hrange]; exact ⟨x, rfl⟩
  have hfix : ∀ x : normalizer ((U ⊔ R : Subgroup D) : Set D), ∀ v ∈ U ⊔ R, v ∉ U →
      (x : D) * v = v * x → ∃ z, π x z = z := by
    intro x v hv hvU hxv
    have hvt : v * t ∈ U := (hS.mem_or_mul_mem hv).resolve_left hvU
    have hQ := hS.zpowers_mul_t_mem hvt
    rw [mul_assoc, htt, mul_one] at hQ
    refine ⟨e ⟨zpowers v, hQ⟩, ?_⟩
    rw [hequiv]
    congr 1
    apply Subtype.ext
    rw [gmsRootConjugateAction_apply, MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxv, mul_inv_cancel_right]
  have hcl := gms_isStronglyClosedIn_of_card_eq_two hS.card hnz
    fun v hv hvU => (hpart v hv hvU).exists
  have hconjU : ∀ g : D, g⁻¹ * t * g ∉ U := by
    intro g hg
    have heq : (g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t := by group
    have h1 := hcl.2 _ hg g⁻¹ (by rw [heq]; exact htV)
    rw [heq] at h1
    exact htU h1
  have hconjtU : ∀ u ∈ U, ∃ g : D, g⁻¹ * t * g = t * u := by
    intro u hu
    obtain ⟨g, hgQ, -⟩ := hS.zpowers_mul_t_mem hu
    have h1 : u * t ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := hgQ ▸ mem_zpowers (u * t)
    obtain ⟨r, hr, hrut⟩ := h1
    rcases hS.eq_one_or_eq_t hr with rfl | rfl
    · exfalso
      apply hS.mul_t_ne_one hu
      rw [← hrut]
      simp
    · refine ⟨g, ?_⟩
      rw [← hS.commute_t hu, ← hrut]
      simp
  have hV2 : IsPGroup 2 (U ⊔ R : Subgroup D) := gms_isPGroup_V hdata
  have hVU : ∀ v ∈ U ⊔ R, v ∉ U → t * v ∈ U := by
    intro v hv hvU
    rw [hcommV t htV v hv]
    exact (hS.mem_or_mul_mem hv).resolve_left hvU
  have hsqV : ∀ v ∈ U ⊔ R, v * v ∈ U := by
    intro v hv
    rw [← sq, hsq v hv]
    exact one_mem U
  have hVcard : Nat.card (U ⊔ R : Subgroup D) = 16 := by
    rw [SteinbergBT.card_sup_of_centralizes (gms_R_le_centralizer_U hdata) hS.inf_eq_bot,
      hUcard, hS.card]
    norm_num
  have hkerV : Nat.card π.ker = Nat.card (U ⊔ R : Subgroup D) := by
    have h1 : π.ker = (U ⊔ R).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D)) := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact hker x
    rw [h1]
    exact Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv
  have hNcard : Nat.card (normalizer ((U ⊔ R : Subgroup D) : Set D)) =
      168 * Nat.card (U ⊔ R : Subgroup D) := by
    have h1 := card_eq_card_quotient_mul_card_subgroup π.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, hrange, card_natPSL,
      hkerV] at h1
    exact h1
  have hPN : P ≤ normalizer (R : Set D) := hdata.2.2.2.2.2.2.1
  have hPsyl := hdata.2.2.2.2.2.2.2.1
  have hPV : P ≤ U ⊔ R := by
    intro p hp
    have hpN : p ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := hS.P_le_normalizer_V hp
    have hpR : p ∈ normalizer (R : Set D) := hPN hp
    obtain ⟨k, hk⟩ := gms_isPGroup_P hdata ⟨p, hp⟩
    have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hfixR : π ⟨p, hpN⟩ (e ⟨R, gms_R_mem⟩) = e ⟨R, gms_R_mem⟩ := by
      rw [hequiv]
      congr 1
      apply Subtype.ext
      rw [gmsRootConjugateAction_apply]
      exact map_conj_eq_self_iff.mpr hpR
    have hpow : π ⟨p, hpN⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have h1 : (⟨p, hpN⟩ : normalizer ((U ⊔ R : Subgroup D) : Set D)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk')
      rw [h1, map_one]
    exact (hker _).mp (eq_one_of_mem_natPSL_of_fix' (hmemN _) hfixR hpow)
  have hinv : ∀ w : normalizer ((U ⊔ R : Subgroup D) : Set D), π w ∈ d8 →
      (w : D) ∉ U ⊔ R → (w : D) * w = 1 → ∀ g : D, g⁻¹ * t * g ≠ w := by
    intro w hwd hwV hww g hgw
    have hbound : ∀ K : Subgroup D, IsPGroup 2 K → K ≤ centralizer ({(w : D)} : Set D) →
        Nat.card K ≤ 16 := by
      intro K hK hKw
      have hK'R : K.map (MulAut.conj g).toMonoidHom ≤ normalizer (R : Set D) := by
        rintro _ ⟨k, hk, rfl⟩
        rw [hS.eq_zpowers]
        apply projEight_mem_normalizer_zpowers_of_commute
        have hkw : k * w = w * k := mem_centralizer_singleton_iff.mp (hKw hk)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← hgw] at hkw
        calc g * k * g⁻¹ * t = g * (k * (g⁻¹ * t * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * t * g) * k) * g⁻¹ := by rw [hkw]
          _ = t * (g * k * g⁻¹) := by group
      have h1 := Endings.card_le_of_isPGroup hPN hPsyl hK'R (hK.map _)
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1
      exact h1.trans ((Subgroup.card_le_of_le hPV).trans hVcard.le)
    have hCVw : ∀ v ∈ U ⊔ R, (w : D) * v = v * w → v ∈ U := by
      intro v hv hwv
      by_contra hvU
      obtain ⟨z, hz⟩ := hfix w v hv hvU hwv
      exact hwV ((hker w).mp (eq_one_of_mem_natPSL_of_fix (hmemN w) hz (pow_four_of_mem_d8 hwd)))
    have hnotr : ¬ ∀ u ∈ U, (w : D) * u = u * w := fun hwU =>
      hwV (hNT.le (mem_inf.mpr ⟨w.2, mem_centralizer_iff.mpr fun u hu => (hwU u hu).symm⟩))
    set CU : Subgroup D := U ⊓ centralizer ({(w : D)} : Set D) with hCU
    have hCUcard : Nat.card CU * 2 ≤ 8 := by
      have h1 := Subgroup.card_mul_index (CU.subgroupOf U)
      rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : CU ≤ U)).toEquiv, hUcard] at h1
      have h2 : (CU.subgroupOf U).index ≠ 1 := by
        rw [Ne, Subgroup.index_eq_one]
        intro h3
        apply hnotr
        intro u hu
        have h4 : (⟨u, hu⟩ : U) ∈ CU.subgroupOf U := by rw [h3]; trivial
        rw [mem_subgroupOf] at h4
        exact (mem_centralizer_singleton_iff.mp (mem_inf.mp h4).2).symm
      have h5 : (CU.subgroupOf U).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h6 : 2 ≤ (CU.subgroupOf U).index := by omega
      calc Nat.card CU * 2 ≤ Nat.card CU * (CU.subgroupOf U).index := Nat.mul_le_mul_left _ h6
        _ = 8 := by rw [h1]; rfl
    have hwwπ : π w * π w = 1 := by
      rw [← map_mul]
      have h1 : w * w = 1 := Subtype.ext hww
      rw [h1, map_one]
    obtain ⟨Pw, hPwN, hPwcard, hPwc⟩ := exists_centralizing_of_mem_d8 hwd hwwπ
    set S' := Pw.comap π with hS'
    set S : Subgroup D := S'.map (normalizer ((U ⊔ R : Subgroup D) : Set D)).subtype with hSdef
    have hS'idx : S'.index = 21 := by
      rw [hS', Subgroup.index_comap, hrange]
      have h1 := Subgroup.relIndex_mul_card (H := Pw) (K := natPSL)
      rw [inf_eq_left.mpr hPwN, hPwcard, card_natPSL] at h1
      omega
    have hScard : Nat.card S = 128 := by
      rw [hSdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      have h1 := Subgroup.card_mul_index S'
      rw [hS'idx, hNcard, hVcard] at h1
      omega
    have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [hScard]; rfl)
    have hww' : (w : D)⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hI : ∀ s ∈ S, s * w * s⁻¹ ∈ (fun u => (w : D) * u) '' (CU : Set D) := by
      intro s hs
      obtain ⟨s', hs', rfl⟩ := hs
      have hc := hPwc (π s') hs'
      set v : D := (w : D) * ((s' : D) * w * (s' : D)⁻¹) with hv
      have hvV : v ∈ U ⊔ R := by
        have h1 : π (w * (s' * w * s'⁻¹)) = 1 := by
          simp only [map_mul, map_inv]
          rw [show π s' * π w = π w * π s' from hc]
          calc π w * (π w * π s' * (π s')⁻¹) = π w * π w := by group
            _ = 1 := hwwπ
        have h2 := (hker _).mp h1
        simpa [hv] using h2
      have hvv : v * v = 1 := by rw [← sq]; exact hsq v hvV
      have hsq' : ((s' : D) * w * (s' : D)⁻¹) * ((s' : D) * w * (s' : D)⁻¹) = 1 := by
        calc ((s' : D) * w * (s' : D)⁻¹) * ((s' : D) * w * (s' : D)⁻¹)
            = (s' : D) * ((w : D) * w) * (s' : D)⁻¹ := by group
          _ = 1 := by rw [hww]; group
      have hsw : (s' : D) * w * (s' : D)⁻¹ = (w : D) * v := by
        rw [hv, ← mul_assoc, hww, one_mul]
      have hvw : (w : D) * v = v * w := by
        have h1 : ((w : D) * v) * ((w : D) * v) = 1 := by rw [← hsw]; exact hsq'
        have h2 : ((w : D) * v)⁻¹ = (w : D) * v := inv_eq_of_mul_eq_one_right h1
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hvv, hww'] at h2
        exact h2.symm
      refine ⟨v, mem_inf.mpr ⟨hCVw v hvV hvw, mem_centralizer_singleton_iff.mpr hvw.symm⟩, ?_⟩
      exact hsw.symm
    have hcount := card_le_mul_card_inf_centralizer_of_conj_mem S (w : D) _ hI
    have hIcard : Nat.card ((fun u => (w : D) * u) '' (CU : Set D)) ≤ Nat.card CU :=
      Nat.card_image_le (Set.toFinite _)
    have hCS := hbound (S ⊓ centralizer ({(w : D)} : Set D)) (hS2.to_le inf_le_left) inf_le_right
    have h1 : Nat.card S ≤
        Nat.card CU * Nat.card (S ⊓ centralizer ({(w : D)} : Set D) : Subgroup D) :=
      hcount.trans (Nat.mul_le_mul_right _ hIcard)
    rw [hScard] at h1
    have h2 : Nat.card CU * Nat.card (S ⊓ centralizer ({(w : D)} : Set D) : Subgroup D) ≤
        4 * 16 := Nat.mul_le_mul (by omega) hCS
    omega
  exact exists_normal_index_two_of_projective_eight hV2 hUV htV htU htt hVU hsqV hS.normalizer_V_le
    π hrange hker hfix hconjU hconjtU hinv

theorem le_of_odd_card_gmsPermStabilizer {J R X U P : Subgroup D} {n : ℕ} {t : D}
    (hS : GMS28.Setup J R X U P n t)
    (hC : normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R)
    (hodd : Odd (Nat.card (gmsPermStabilizer U R))) : P ≤ U ⊔ R := by
  have hdata := hS.data
  intro p hp
  have hpN : p ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := hS.P_le_normalizer_V hp
  have hpR : p ∈ normalizer (R : Set D) := hdata.2.2.2.2.2.2.1 hp
  have hstab : gmsRootConjugateAction (U ⊔ R) R ⟨p, hpN⟩ ∈ gmsPermStabilizer U R := by
    rw [GMSDichotomy.mem_gmsPermStabilizer]
    refine ⟨⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [gmsRootConjugateAction_apply]
    exact map_conj_eq_self_iff.mpr hpR
  obtain ⟨k, hk⟩ := gms_isPGroup_P hdata ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : (⟨_, hstab⟩ : gmsPermStabilizer U R) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    have h1 : (⟨p, hpN⟩ : normalizer ((U ⊔ R : Subgroup D) : Set D)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk')
    rw [h1, map_one]
  have h1 : orderOf (⟨_, hstab⟩ : gmsPermStabilizer U R) = 1 := by
    have h2 : orderOf (⟨_, hstab⟩ : gmsPermStabilizer U R) ∣ Nat.card (gmsPermStabilizer U R) :=
      orderOf_dvd_natCard _
    have h3 : orderOf (⟨_, hstab⟩ : gmsPermStabilizer U R) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    have hcop : Nat.Coprime (Nat.card (gmsPermStabilizer U R)) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    exact Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hcop ▸ Nat.dvd_gcd h2 h3)
  have h4 : gmsRootConjugateAction (U ⊔ R) R ⟨p, hpN⟩ = 1 := by
    simpa using congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  exact projEight_mem_of_forall_conj_eq hC (hS.conj_eq_of_action_eq_one ⟨p, hpN⟩ h4)

theorem sq_eq_one_of_commute_of_odd_card_gmsPermStabilizer {J R X U P : Subgroup D} {n : ℕ}
    {t : D} (hS : GMS28.Setup J R X U P n t)
    (hC : normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R)
    (hodd : Odd (Nat.card (gmsPermStabilizer U R))) {x : D} (hxt : x * t = t * x)
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x * x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPV := le_of_odd_card_gmsPermStabilizer hS hC hodd
  have hsq := gms_sq_V hS.data
  obtain ⟨-, -, -, -, -, -, ⟨-, ⟨TP, hTP⟩, -⟩⟩ := hS.data
  have hxN : x ∈ normalizer (R : Set D) := by
    rw [hS.eq_zpowers]; exact projEight_mem_normalizer_zpowers_of_commute hxt
  have hz : IsPGroup 2 ((zpowers x).subgroupOf (normalizer (R : Set D))) := by
    obtain ⟨k, hk⟩ := hx2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have h1 : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    exact h1.comap_of_injective _ (normalizer (R : Set D)).subtype_injective
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (normalizer (R : Set D)) Q TP
  have hxQ : (⟨x, hxN⟩ : normalizer (R : Set D)) ∈ (Q : Subgroup _) :=
    hQ (mem_subgroupOf.mpr (mem_zpowers x))
  have hcx : c * ⟨x, hxN⟩ * c⁻¹ ∈ (TP : Subgroup (normalizer (R : Set D))) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, hxQ, by simp [MulAut.conj_apply]⟩
  rw [hTP, mem_subgroupOf] at hcx
  have hcxV : (c : D) * x * (c : D)⁻¹ ∈ U ⊔ R := by simpa using hPV hcx
  have h1 := hsq _ hcxV
  rw [sq] at h1
  calc x * x = (c : D)⁻¹ * (((c : D) * x * (c : D)⁻¹) * ((c : D) * x * (c : D)⁻¹)) * c := by group
    _ = 1 := by rw [h1]; group

namespace SmallRootStage

variable {R X U P : Subgroup D}

theorem exists_normal_index_two_of_projectiveEight (h : SmallRootStage R X U P 3)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (hproj : GMSProjectiveEight U R) :
    ∃ M : Subgroup D, M.Normal ∧ M.index = 2 := by
  obtain ⟨t, htR, ht1⟩ := h.exists_ne_one
  exact exists_normal_index_two_of_gms_projective_eight (h.setup h3 htR ht1)
    h.normalizer_inf_centralizer hproj

end SmallRootStage

end StageZero

end CFSG.SeitzReduction.RankOne
