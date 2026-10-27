module

public import CFSG.Certificates.Kernel.QTwoD6.Glue4
public import Mathlib.Data.Fin.Tuple.Sort

public section

namespace CFSG.StandardType.QTwoD6.K

open Module CFSG.KC.QTwoD6K CFSG.StandardType.QTwoLin

@[expose] def NF (A : Subgroup (V7 ≃ₗ[ZMod 3] V7)) : Prop :=
  ∀ φ ∈ A, φ e0 ∈ Submodule.span (ZMod 3) {e0} →
    ∃ w ∈ W6, ∃ c : ZMod 3, c ≠ 0 ∧ ∃ π : Fin 6 ≃ Fin 6, (π = Equiv.refl _ ∨ π = swapD6) ∧
      ∀ i, φ (hvec i) = c • w (hvec (π i))

theorem nthL_of_mem {S : List Nat} {i : Nat} (h : i ∈ S) : ∃ m < S.length, nthL S m = i := by
  induction S with
  | nil => simp at h
  | cons x S ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨m, hm, e⟩ := ih h
      exact ⟨m + 1, by simp only [List.length_cons]; omega, e⟩

theorem cl_le {L : Set (V7 ≃ₗ[ZMod 3] V7)} {H : Subgroup (V7 ≃ₗ[ZMod 3] V7)} (hW : W6 ≤ H)
    (hL : L ⊆ H) : cl L ≤ H := by
  rw [cl, Subgroup.closure_le]
  refine Set.union_subset (fun g hg => hW ?_) hL
  rw [W6]
  exact Subgroup.subset_closure hg

theorem apply_decV (f : Dual (ZMod 3) V7) (y : Nat) : f (decV y) = ∑ j, f (ub j) * cd y j := by
  rw [decV, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem refl_fix_zero {c v : V7} {φ : Dual (ZMod 3) V7} (h2 : φ c = 2)
    (hv : reflection h2 v = v) : φ v = 0 := by
  rw [reflection_apply, sub_eq_self, smul_eq_zero] at hv
  rcases hv with hv | hv
  · exact hv
  · rw [hv, map_zero] at h2
    exact absurd h2 (by decide)

theorem refl_scale {c : V7} {φ : Dual (ZMod 3) V7} (h2 : φ c = 2) (he0 : φ e0 ≠ 0) :
    ∃ h₁ : ((φ e0)⁻¹ • φ) ((φ e0) • c) = 2, reflection h₁ = reflection h2 ∧
      ((φ e0)⁻¹ • φ) e0 = 1 := by
  have h₁ : ((φ e0)⁻¹ • φ) ((φ e0) • c) = 2 := by
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ he0, one_mul, h2]
  refine ⟨h₁, ?_, ?_⟩
  · apply LinearEquiv.ext
    intro v
    rw [reflection_apply, reflection_apply, LinearMap.smul_apply, smul_smul, smul_eq_mul,
      mul_right_comm, inv_mul_cancel₀ he0, one_mul]
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ he0]

theorem sorted_conj {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} (hJ : J6 ≤ B) {c : V7}
    {φ : Dual (ZMod 3) V7} (h2 : φ c = 2) (hr : reflection h2 ∈ B) :
    ∃ g ∈ J6, ∃ h' : (φ.comp (g : V7 →ₗ[ZMod 3] V7)) (g.symm c) = 2, reflection h' ∈ B ∧
      us 0 (g.symm c) = us 0 c ∧ (φ.comp (g : V7 →ₗ[ZMod 3] V7)) (ub 0) = φ (ub 0) ∧
      Monotone fun k : Fin 6 => 3 * (us k.succ (g.symm c)).val +
        ((φ.comp (g : V7 →ₗ[ZMod 3] V7)) (ub k.succ)).val := by
  let p : Fin 6 → ℕ := fun k => 3 * (us k.succ c).val + (φ (ub k.succ)).val
  obtain ⟨g, hgJ, hg0, hg⟩ := exists_J6_perm (Tuple.sort p)
  have hg0' : g e0 = ((1 : (ZMod 3)ˣ) : ZMod 3) • e0 := by rw [hg0, Units.val_one, one_smul]
  obtain ⟨hu0, huk⟩ := us_symm_apply hg0' hg c
  obtain ⟨hφ0, hφk⟩ := comp_ub hg0' hg φ
  obtain ⟨h', hconj⟩ := conj_reflection g h2
  refine ⟨g, hgJ, h', ?_, ?_, ?_, ?_⟩
  · rw [← hconj]
    exact B.mul_mem (B.mul_mem (B.inv_mem (hJ hgJ)) hr) (hJ hgJ)
  · rw [hu0, inv_one, Units.val_one, one_mul]
  · rw [hφ0, Units.val_one, one_mul]
  · intro a b hab
    simp only [huk, hφk]
    exact Tuple.monotone_sort p hab

theorem line_settle {A Aℓ : Subgroup (V7 ≃ₗ[ZMod 3] V7)} (hTV : TransvectionFree A)
    (hW6 : W6 ≤ A) (hNF : NF A) (hAℓA : Aℓ ≤ A) (hJ : J6 ≤ Aℓ) (hσ : sigInvK = true)
    {G : V7 ≃ₗ[ZMod 3] V7} (hGA : G ∈ A) {k : Nat} (hk : k < 4)
    (hG : (G : V7 →ₗ[ZMod 3] V7) = twL k)
    {y : Nat} {F : Nat → Nat} {N : Nat} {S : List Nat} {tauOk : Bool}
    (hcov : covK y F N = true)
    (hrow : ∀ i, 0 ≤ i → i < N → ∃ kd g₁ w₁ g₂ w₂, rowK y F S i kd g₁ w₁ g₂ w₂ = true)
    (htw : ∀ j, 0 ≤ j → j < 4 * S.length →
      ∃ kd g₁ w₁ g₂ w₂, twRowK tauOk F S j kd g₁ w₁ g₂ w₂ = true)
    (hfixy : ∀ ρ ∈ Aℓ, ρ (decV y) = decV y)
    {c : V7} {φ : Dual (ZMod 3) V7} (h2 : φ c = 2) (hr : reflection h2 ∈ Aℓ) (he0 : φ e0 ≠ 0) :
    (∃ ψ ∈ W6 ⊔ Aℓ, ∀ v ∈ Dplane, ψ (G v) ∈ Dplane) ∨
      (tauOk = true ∧ ∃ T ∈ Aℓ, (T : V7 →ₗ[ZMod 3] V7) = decL tauC) := by
  obtain ⟨h₁, hsame, hone⟩ := refl_scale h2 he0
  rw [← hsame] at hr
  obtain ⟨g, -, h', hr', hu0, hφ0, hsort⟩ := sorted_conj hJ h₁ hr
  set c' := g.symm ((φ e0) • c) with hc'
  set φ' := ((φ e0)⁻¹ • φ).comp (g : V7 →ₗ[ZMod 3] V7) with hφ'
  have ha0 : (fun j => φ' (ub j)) 0 = 1 := by
    change φ' (ub 0) = 1
    rw [hφ0, ub_zero, hone]
  have hah : ∑ j, (fun j => φ' (ub j)) j * (fun j => us j c') j = 2 := by
    rw [← apply_eq_sum_coords]
    exact h'
  have hay : ∑ j, (fun j => φ' (ub j)) j * cd y j = 0 := by
    rw [← apply_decV]
    exact refl_fix_zero h' (hfixy _ hr')
  obtain ⟨i, hi, hci, haci⟩ := covK_sound hcov _ _ ha0 hsort hah hay
  have hρ : ((reflection h' : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) = decL (F i) := by
    rw [reflection_coe, decL_eq_of_cd hci haci]
  have hρA : reflection h' ∈ A := hAℓA hr'
  have hle1 : cl {reflection h'} ≤ A := cl_le hW6 (Set.singleton_subset_iff.mpr hρA)
  have hle2 : cl {reflection h', G} ≤ A :=
    cl_le hW6 (Set.insert_subset_iff.mpr ⟨hρA, Set.singleton_subset_iff.mpr hGA⟩)
  obtain ⟨kd, g₁, w₁, g₂, w₂, hrw⟩ := hrow i (Nat.zero_le _) hi
  obtain ⟨-, -, -, hcase⟩ := rowK_sound hrw
  rcases hcase _ hρ with htv | hhl | hS
  · exact (not_tvFact hTV hle1 htv).elim
  · exact (not_hlFact hle1 hNF hhl).elim
  · obtain ⟨m, hm, hmi⟩ := nthL_of_mem hS
    have hj : 4 * m + k < 4 * S.length := by omega
    have hj4 : (4 * m + k) / 4 = m := by omega
    have hjk : (4 * m + k) % 4 = k := by omega
    obtain ⟨kd, g₁, w₁, g₂, w₂, htr⟩ := htw (4 * m + k) (Nat.zero_le _) hj
    have hρ' : ((reflection h' : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) =
        decL (F (nthL S ((4 * m + k) / 4))) := by rw [hj4, hmi]; exact hρ
    have hG' : (G : V7 →ₗ[ZMod 3] V7) = twL ((4 * m + k) % 4) := by rw [hjk]; exact hG
    have hv := rowK_prefix hrw
    rw [← hmi, ← hj4] at hv
    rcases twRowK_sound hσ htr hv _ G hρ' hG' with htv | hhl | hpl | ⟨hok, htau⟩
    · exact (not_tvFact hTV hle2 htv).elim
    · exact (not_hlFact hle2 hNF hhl).elim
    · left
      obtain ⟨ψ, hψ, hψD⟩ := absD_of_planeFact hpl hG'
      exact ⟨ψ, cl_le le_sup_left
        (Set.singleton_subset_iff.mpr ((le_sup_right : Aℓ ≤ W6 ⊔ Aℓ) hr')) hψ, hψD⟩
    · right
      exact ⟨hok, reflection h', hr', by rw [hρ', htau]⟩

theorem tauC_e0 : decL tauC e0 = (2 : ZMod 3) • e0 := by
  decide +kernel

theorem tauC_ub : ∀ k : Fin 6, decL tauC (ub k.succ) = ub k.succ := by
  decide +kernel

theorem trC_e0 : decL trC e0 = e0 := by
  decide +kernel

theorem trC_ub : ∀ k : Fin 6, decL trC (ub k.succ) = ub (Equiv.swap 4 5 k).succ := by
  decide +kernel

theorem units_neg_one : (((-1 : (ZMod 3)ˣ)) : ZMod 3) = 2 := by
  decide

theorem mem_permG_of_tauC {T : V7 ≃ₗ[ZMod 3] V7} (hT : (T : V7 →ₗ[ZMod 3] V7) = decL tauC) :
    T ∈ permG := by
  have hTv : ∀ v, T v = decL tauC v := fun v => by rw [← hT, LinearEquiv.coe_coe]
  exact ⟨1, -1, by rw [hTv, tauC_e0, units_neg_one], fun k => by rw [hTv, tauC_ub]; rfl⟩

theorem mem_permG_of_trC {T : V7 ≃ₗ[ZMod 3] V7} (hT : (T : V7 →ₗ[ZMod 3] V7) = decL trC) :
    T ∈ permG := by
  have hTv : ∀ v, T v = decL trC v := fun v => by rw [← hT, LinearEquiv.coe_coe]
  exact ⟨Equiv.swap 4 5, 1, by rw [hTv, trC_e0, Units.val_one, one_smul],
    fun k => by rw [hTv, trC_ub]⟩

theorem hK_tauC : hK tauC = 1 := by decide +kernel
theorem aK_tauC : aK tauC = 128 := by decide +kernel
theorem hK_trC : hK trC = 8224 := by decide +kernel
theorem aK_trC : aK trC = 8224 := by decide +kernel

theorem heads_cover : ∀ h a : ZMod 3,
    (h, a) ∈ [((0 : ZMod 3), (0 : ZMod 3)), (0, 1), (1, 0), (1, 1), (1, 2)] ∨
      (2 * h, 2 * a) ∈ [((0 : ZMod 3), (0 : ZMod 3)), (0, 1), (1, 0), (1, 1), (1, 2)] := by
  decide

theorem head_conj {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {T : V7 ≃ₗ[ZMod 3] V7} (hTB : T ∈ B)
    (hT : (T : V7 →ₗ[ZMod 3] V7) = decL tauC) {c : V7} {φ : Dual (ZMod 3) V7} (h2 : φ c = 2)
    (hr : reflection h2 ∈ B) (hrP : reflection h2 ∉ permG) :
    ∃ c₁ : V7, ∃ φ₁ : Dual (ZMod 3) V7, ∃ h₁ : φ₁ c₁ = 2, reflection h₁ ∈ B ∧
      reflection h₁ ∉ permG ∧
      (us 0 c₁, φ₁ (ub 0)) ∈ [((0 : ZMod 3), (0 : ZMod 3)), (0, 1), (1, 0), (1, 1), (1, 2)] := by
  rcases heads_cover (us 0 c) (φ (ub 0)) with hh | hh
  · exact ⟨c, φ, h2, hr, hrP, hh⟩
  · have hTv : ∀ v, T v = decL tauC v := fun v => by rw [← hT, LinearEquiv.coe_coe]
    have hT0 : T e0 = (((-1 : (ZMod 3)ˣ)) : ZMod 3) • e0 := by
      rw [hTv, tauC_e0, units_neg_one]
    have hTk : ∀ k, T (ub k.succ) = ub ((1 : Equiv.Perm (Fin 6)) k).succ := fun k => by
      rw [hTv, tauC_ub]
      rfl
    obtain ⟨hu0, -⟩ := us_symm_apply hT0 hTk c
    obtain ⟨hφ0, -⟩ := comp_ub hT0 hTk φ
    obtain ⟨h', hconj⟩ := conj_reflection T h2
    have hTP := mem_permG_of_tauC hT
    refine ⟨T.symm c, φ.comp (T : V7 →ₗ[ZMod 3] V7), h', ?_, ?_, ?_⟩
    · rw [← hconj]
      exact B.mul_mem (B.mul_mem (B.inv_mem hTB) hr) hTB
    · rw [← hconj]
      intro hm
      apply hrP
      have : reflection h2 = T * (T⁻¹ * reflection h2 * T) * T⁻¹ := by group
      rw [this]
      exact permG.mul_mem (permG.mul_mem hTP hm) (permG.inv_mem hTP)
    · have hinv : (((-1 : (ZMod 3)ˣ)⁻¹ : (ZMod 3)ˣ) : ZMod 3) = 2 := by decide
      rw [hu0, hφ0, hinv, units_neg_one]
      exact hh

theorem depth2_settle {A Aℓ : Subgroup (V7 ≃ₗ[ZMod 3] V7)} (hTV : TransvectionFree A)
    (hW6 : W6 ≤ A) (hNF : NF A) (hAℓA : Aℓ ≤ A) (hJ : J6 ≤ Aℓ) (hσ : sigInvK = true)
    {G : V7 ≃ₗ[ZMod 3] V7} (hGA : G ∈ A) {k : Nat} (hk : k < 4)
    (hG : (G : V7 →ₗ[ZMod 3] V7) = twL k)
    {F : Nat → Nat} {N : Nat} {S : List Nat}
    (hcov : covT F N = true)
    (hrow : ∀ i, 0 ≤ i → i < N → ∃ kd g₁ w₁ g₂ w₂, rowT F S i kd g₁ w₁ g₂ w₂ = true)
    (htw : ∀ j, 0 ≤ j → j < 4 * S.length →
      ∃ kd g₁ w₁ g₂ w₂, twRowT F S j kd g₁ w₁ g₂ w₂ = true)
    (hfixy : ∀ ρ ∈ Aℓ, ρ wb = wb)
    (hgen : Aℓ = Subgroup.closure {g | g ∈ Aℓ ∧ IsReflLin g}) (hcard : 1440 < Nat.card Aℓ)
    {T : V7 ≃ₗ[ZMod 3] V7} (hTA : T ∈ Aℓ) (hT : (T : V7 →ₗ[ZMod 3] V7) = decL tauC) :
    ∃ ψ ∈ W6 ⊔ Aℓ, ∀ v ∈ Dplane, ψ (G v) ∈ Dplane := by
  obtain ⟨r, hrA, ⟨c, φ, h2, rfl⟩, hrP⟩ := exists_refl_not_permG hgen hcard
  obtain ⟨c₁, φ₁, h₁, hr₁, hrP₁, hhead⟩ := head_conj hTA hT h2 hrA hrP
  obtain ⟨g, hgJ, h', hr', hu0, hφ0, hsort⟩ := sorted_conj hJ h₁ hr₁
  obtain ⟨hgP⟩ : J6 ≤ permG ∧ True := ⟨J6_le_permG, trivial⟩
  have hgPerm : g ∈ permG := hgP hgJ
  set c' := g.symm c₁ with hc'
  set φ' := φ₁.comp (g : V7 →ₗ[ZMod 3] V7) with hφ'
  have hrP' : reflection h' ∉ permG := by
    obtain ⟨h'', hconj⟩ := conj_reflection g h₁
    intro hm
    apply hrP₁
    have hc : reflection h₁ = g * (g⁻¹ * reflection h₁ * g) * g⁻¹ := by group
    rw [hc]
    refine permG.mul_mem (permG.mul_mem hgPerm ?_) (permG.inv_mem hgPerm)
    rw [hconj]
    exact hm
  have hhead' : ((fun j => us j c') 0, (fun j => φ' (ub j)) 0) ∈
      [((0 : ZMod 3), (0 : ZMod 3)), (0, 1), (1, 0), (1, 1), (1, 2)] := by
    change (us 0 c', φ' (ub 0)) ∈ _
    rw [hu0, hφ0]
    exact hhead
  have hah : ∑ j, (fun j => φ' (ub j)) j * (fun j => us j c') j = 2 := by
    rw [← apply_eq_sum_coords]
    exact h'
  have hay : ∑ j, (fun j => φ' (ub j)) j * cd 16128 j = 0 := by
    rw [← apply_decV, decV_16128]
    exact refl_fix_zero h' (hfixy _ hr')
  have hcode : ∀ t : Nat, (fun j => us j c') = cd (hK t) → (fun j => φ' (ub j)) = cd (aK t) →
      ((reflection h' : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) = decL t := fun t hh ha => by
    rw [reflection_coe, decL_eq_of_cd hh.symm ha.symm]
  have htau : ¬ ((fun j => us j c') = cd 1 ∧ (fun j => φ' (ub j)) = cd 128) := by
    rintro ⟨hh, ha⟩
    apply hrP'
    apply mem_permG_of_tauC
    exact hcode tauC (by rw [hK_tauC]; exact hh) (by rw [aK_tauC]; exact ha)
  have htr : ¬ ((fun j => us j c') = cd 8224 ∧ (fun j => φ' (ub j)) = cd 8224) := by
    rintro ⟨hh, ha⟩
    apply hrP'
    apply mem_permG_of_trC
    exact hcode trC (by rw [hK_trC]; exact hh) (by rw [aK_trC]; exact ha)
  obtain ⟨i, hi, hci, haci⟩ := covT_sound hcov _ _ hhead' hsort hah hay htau htr
  have hρ : ((reflection h' : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) = decL (F i) :=
    hcode (F i) hci.symm haci.symm
  have hρA : reflection h' ∈ A := hAℓA hr'
  have hTA' : T ∈ A := hAℓA hTA
  have hle1 : cl {T, reflection h'} ≤ A :=
    cl_le hW6 (Set.insert_subset_iff.mpr ⟨hTA', Set.singleton_subset_iff.mpr hρA⟩)
  have hle2 : cl {T, reflection h', G} ≤ A :=
    cl_le hW6 (Set.insert_subset_iff.mpr ⟨hTA', Set.insert_subset_iff.mpr
      ⟨hρA, Set.singleton_subset_iff.mpr hGA⟩⟩)
  obtain ⟨kd, g₁, w₁, g₂, w₂, hrw⟩ := hrow i (Nat.zero_le _) hi
  obtain ⟨-, hcase⟩ := rowT_sound hrw
  rcases hcase T _ hT hρ with htv | hhl | hS
  · exact (not_tvFact hTV hle1 htv).elim
  · exact (not_hlFact hle1 hNF hhl).elim
  · obtain ⟨m, hm, hmi⟩ := nthL_of_mem hS
    have hj : 4 * m + k < 4 * S.length := by omega
    have hj4 : (4 * m + k) / 4 = m := by omega
    have hjk : (4 * m + k) % 4 = k := by omega
    obtain ⟨kd, g₁, w₁, g₂, w₂, htr⟩ := htw (4 * m + k) (Nat.zero_le _) hj
    have hρ' : ((reflection h' : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) =
        decL (F (nthL S ((4 * m + k) / 4))) := by rw [hj4, hmi]; exact hρ
    have hG' : (G : V7 →ₗ[ZMod 3] V7) = twL ((4 * m + k) % 4) := by rw [hjk]; exact hG
    have hv := rowT_prefix hrw
    rw [← hmi, ← hj4] at hv
    rcases twRowT_sound hσ htr hv T _ G hT hρ' hG' with htv | hhl | hpl
    · exact (not_tvFact hTV hle2 htv).elim
    · exact (not_hlFact hle2 hNF hhl).elim
    · obtain ⟨ψ, hψ, hψD⟩ := absD_of_planeFact hpl hG'
      refine ⟨ψ, cl_le le_sup_left ?_ hψ, hψD⟩
      exact Set.insert_subset_iff.mpr ⟨(le_sup_right : Aℓ ≤ W6 ⊔ Aℓ) hTA,
        Set.singleton_subset_iff.mpr ((le_sup_right : Aℓ ≤ W6 ⊔ Aℓ) hr')⟩

end CFSG.StandardType.QTwoD6.K

end
