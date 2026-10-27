module

public import CFSG.GF2Type.SmithTypeE.E7.IdUA
public import CFSG.GF2Type.SmithTypeE.E7.IdPhi
public import CFSG.GF2Type.SmithTypeE.E7.IdNoA2
public import CFSG.GF2Type.SmithTypeE.E7.IdModCert
public import CFSG.GF2Type.SmithTypeE.E7.ModDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 cMbar mem_normalizer_subgroupOf_iff)
open CFSG.SmithD6 (wt wtIdx adjW tvCols applyCols)
open CFSG.GF2Type.SmithTypeE.DMod

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def rhoM (S : Setting G) : S.M →* S.Mbar :=
  S.ρ.codRestrict S.Mbar fun m => ⟨m, rfl⟩

theorem coe_rhoM (m : S.M) : (rhoM S m : S.O) = S.ρ m := rfl

theorem exists_rhoM_eq (m : S.Mbar) : ∃ x : S.M, rhoM S x = m := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp m.2
  exact ⟨x, Subtype.ext hx⟩

theorem finrank_clSub_QG_inf_Qa_le (hw : S.width = 16) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) : Module.finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa h)) ≤ 16 := by
  have hz : S.z ∈ S.QG ⊓ S.Qa h := ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩
  have h1 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa h))
  rw [S.clPre_clSub inf_le_left hz, S.card_submodule] at h1
  have h2 := S.card_QG_inf_Qa_le hne
  rw [hw, h1, show 16 + 1 = 1 + 16 from rfl, pow_add, pow_one] at h2
  have h3 := Nat.le_of_mul_le_mul_left h2 (by norm_num)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

section Equiv


variable {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {ψ : S.Mbar ≃* TD6}

theorem rhoMod_psi_apply (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) (m : S.Mbar)
    (x : S.Qt) : rhoMod (ψ m) (φ x) = φ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
  obtain ⟨y, rfl⟩ := exists_rhoM_eq m
  rw [← hΦ, Phi_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem applyCols_tvCols_lt32 (k c : ℕ) : applyCols (tvCols k) c < 2 ^ 32 :=
  applyCols_lt (size_tvCols k) (fun c hc => tvCols_lt k hc) c

theorem acts_iff {x : G} (hx : x ∈ S.M) {k : ℕ} (hk : k < 365211) :
    (∀ y ∈ S.QG, code32 (φ (S.cl (x * y * x⁻¹))) =
      applyCols (tvCols k) (code32 (φ (S.cl y)))) ↔ Phi S φ ⟨x, hx⟩ = tvEquiv k := by
  constructor
  · intro h
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨y, hy, hyv⟩ := S.exists_cl (φ.symm v)
    have hv : v = φ (S.cl y) := by rw [hyv, LinearEquiv.apply_symm_apply]
    rw [hv, Phi_cl ⟨x, hx⟩ hy, ← decode32_code32 (φ (S.cl (x * y * x⁻¹))), h y hy,
      ← tvEquiv_decode hk, decode32_code32]
  · intro h y hy
    have e := congrArg (fun f : (Fin 32 → ZMod 2) ≃ₗ[ZMod 2] (Fin 32 → ZMod 2) =>
      f (φ (S.cl y))) h
    simp only [Phi_cl ⟨x, hx⟩ hy] at e
    rw [e, ← decode32_code32 (φ (S.cl y)), tvEquiv_decode hk,
      code32_decode32 (applyCols_tvCols_lt32 _ _), decode32_code32]

theorem clause5 (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) :
    ∀ k < 365211, ∃ m ∈ S.M, ∀ y ∈ S.QG,
      code32 (φ (S.cl (m * y * m⁻¹))) = applyCols (tvCols k) (code32 (φ (S.cl y))) := by
  intro k hk
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm ⟨tvP ⟨k, hk⟩, tvP_mem ⟨k, hk⟩⟩)
  refine ⟨m, m.2, (acts_iff (S := S) (φ := φ) m.2 hk).mpr ?_⟩
  show Phi S φ m = tvEquiv k
  rw [hΦ, hm, MulEquiv.apply_symm_apply, rhoMod_tvP]

theorem wtV_ne_zero {i : ℕ} (hi : i < 75735) : wtV i ≠ 0 := by
  intro h
  have h0 : wt i = 0 := by
    refine eq_of_decode32_eq (wt_lt hi) (by norm_num) ?_
    rw [← decode32_zero] at h
    exact h
  have h1 : wt 0 = 1 := wtFacts.zero
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [h1] at h0
    exact absurd h0 (by norm_num)
  · have := wt_strictMono hpos hi
    rw [h0] at this
    exact absurd this (Nat.not_lt_zero _)

theorem exists_weight_of_conj [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ i : Fin 75735, φ (S.cl (g * S.z * g⁻¹)) = wtV i.val := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hEP⟩ := (S.isPGroup_Lbar_subgroupOf haQ).exists_le_sylow
  have hno := noA2_of_insp5 I hw hO haQ hne
  have hPN := S.le_normalizer_Lbar_of_isPGroup (by omega) haQ hne hno P.isPGroup' hEP
  have hfixP : ∀ m ∈ (P : Subgroup S.Mbar),
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    intro m hm
    have h1 : (m : S.O) ∈ S.Mbar ⊓ normalizer (S.Lbar g : Set S.O) :=
      ⟨m.2, (mem_normalizer_subgroupOf_iff (S.Lbar_le_Mbar g) m).mp (hPN hm)⟩
    rw [← cMbar_eq_normalizer I hw hO haQ hne, SMK.mem_cMbar] at h1
    exact h1.2
  have hP'2 : IsPGroup 2 ((P : Subgroup S.Mbar).map ψ.toMonoidHom) := P.isPGroup'.map _
  have hmax : ∀ Q : Subgroup S.Mbar, (P : Subgroup S.Mbar) ≤ Q → IsPGroup 2 Q → Q = P :=
    fun Q hPQ hQ => P.is_maximal' hQ hPQ
  have hP'max := isMax_map ψ hmax
  have hv : ∀ g' ∈ (P : Subgroup S.Mbar).map ψ.toMonoidHom,
      rhoMod g' (φ (S.cl (g * S.z * g⁻¹))) = φ (S.cl (g * S.z * g⁻¹)) := by
    rintro _ ⟨m, hm, rfl⟩
    show rhoMod (ψ m) (φ (S.cl (g * S.z * g⁻¹))) = _
    rw [rhoMod_psi_apply hΦ, hfixP m hm]
  rcases fixed_vec_of_maximal hP'2 hP'max hv with h | h
  · exfalso
    exact S.cl_conj_z_ne_zero haQ hne (φ.injective (by rw [h, map_zero]))
  · exact h

theorem mul_conj_mem (m : S.M) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.QG ∧
      ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ≠ S.z := by
  have e : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ = (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ := by
    group
  rw [e]
  refine ⟨S.conj_mem_QG m.2 haQ, fun h => hne ?_⟩
  have hz : (m : G)⁻¹ * S.z * (m : G) = S.z := by
    rw [mul_assoc, ← S.z_comm m.2, ← mul_assoc, inv_mul_cancel, one_mul]
  calc g * S.z * g⁻¹ = (m : G)⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * (m : G) := by group
    _ = S.z := by rw [h, hz]

theorem phi_cl_mul (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) (m : S.M) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    φ (S.cl (((m : G) * g) * S.z * ((m : G) * g)⁻¹)) =
      rhoMod (ψ (rhoM S m)) (φ (S.cl (g * S.z * g⁻¹))) := by
  have e : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ = (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ := by
    group
  rw [e, ← Phi_cl m haQ, hΦ m]

theorem exists_conj_with_weight_of [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (i : Fin 75735) :
    ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ≠ S.z ∧
      φ (S.cl (h * S.z * h⁻¹)) = wtV i.val := by
  obtain ⟨i₀, hi₀⟩ := exists_weight_of_conj I hw hO hΦ haQ hne
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq i₀ i
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm g₀)
  obtain ⟨hQ', hne'⟩ := mul_conj_mem m haQ hne
  refine ⟨(m : G) * g, hQ', hne', ?_⟩
  rw [phi_cl_mul hΦ m haQ, hm, MulEquiv.apply_symm_apply, hi₀, rhoMod_wtV, hg₀]

theorem exists_conj_with_weight [IsSimpleGroup G] (I : Inputs10) (hAS : AschbacherSmithWideInput)
    (hw : S.width = 16) (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) (i : Fin 75735) :
    ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ≠ S.z ∧
      φ (S.cl (h * S.z * h⁻¹)) = wtV i.val := by
  obtain ⟨g, haQ, hne⟩ := exists_conj_mem_QG hAS hw hO
  exact exists_conj_with_weight_of I hw hO hΦ haQ hne i

theorem isometry [IsSimpleGroup G] (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)))
    (u v : S.Qt) : fModel (φ u) (φ v) = polar S.q u v := by
  let B' : LinearMap.BilinForm (ZMod 2) (Fin 32 → ZMod 2) :=
    S.q.polarBilin.compl₁₂ (φ.symm : (Fin 32 → ZMod 2) →ₗ[ZMod 2] S.Qt)
      (φ.symm : (Fin 32 → ZMod 2) →ₗ[ZMod 2] S.Qt)
  have hB : ∀ (g : TD6) (v w : Fin 32 → ZMod 2),
      B' (rhoMod g v) (rhoMod g w) = B' v w := by
    intro g v w
    obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm g)
    have hg : rhoMod g = Phi S φ m := by rw [hΦ, hm, MulEquiv.apply_symm_apply]
    rw [hg, Phi_apply, Phi_apply]
    simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m).2 _ _
  have hBu : ∀ u v : S.Qt, B' (φ u) (φ v) = polar S.q u v := by
    intro u v
    simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      polarBilin_apply_apply]
  rcases eq_fModel_or_zero B' hB with h | h
  · have h1 : B' (φ u) (φ v) = fModel (φ u) (φ v) := by rw [h]
    rw [← hBu u v]
    exact h1.symm
  · exfalso
    have hz : ∀ x y : S.Qt, polar S.q x y = 0 := by
      intro x y
      rw [← hBu, h]
      rfl
    have hx0 : φ.symm (wtV 0) = 0 := S.q_nondegenerate.1 _ fun y => by
      rw [polarBilin_apply_apply, hz]
    exact wtV_ne_zero (by norm_num : 0 < 75735) (by simpa using congrArg φ hx0)

theorem adjW_iff {i j : ℕ} (hi : i < 75735) (hj : j < 75735) :
    adjW i j = true ↔ wtV i = wtV j ∨ ∃ k : Fin 75735, wtV i + wtV j = wtV k.val := by
  unfold adjW
  rw [Bool.or_eq_true, beq_iff_eq, decide_eq_true_iff]
  have hxor : wt i ^^^ wt j < 2 ^ 32 := Nat.xor_lt_two_pow (wt_lt hi) (wt_lt hj)
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [wtV, wtV, h])
    · refine Or.inr ⟨⟨wtIdx (wt i ^^^ wt j), h⟩, ?_⟩
      have h1 : wt (wtIdx (wt i ^^^ wt j)) = wt i ^^^ wt j := wtIdx_spec h
      show wtV i + wtV j = wtV (wtIdx (wt i ^^^ wt j))
      rw [wtV, wtV, wtV, h1, decode32_xor]
  · rintro (h | ⟨k, hk⟩)
    · exact Or.inl (eq_of_decode32_eq (wt_lt hi) (wt_lt hj) h)
    · refine Or.inr ?_
      have h1 : wt k.val = wt i ^^^ wt j := by
        refine eq_of_decode32_eq (wt_lt k.2) hxor ?_
        rw [decode32_xor]
        exact hk.symm
      rw [← h1, wtIdx_wt k.2]
      exact k.2

theorem adjW_smul_iff (g : TD6) (i j : Fin 75735) :
    adjW (g • i).val (g • j).val = true ↔ adjW i.val j.val = true := by
  rw [adjW_iff (g • i).2 (g • j).2, adjW_iff i.2 j.2]
  have e1 : ∀ x y : Fin 75735, wtV (g • x).val = wtV (g • y).val ↔ wtV x.val = wtV y.val := by
    intro x y
    rw [← rhoMod_wtV g x, ← rhoMod_wtV g y]
    exact (rhoMod g).injective.eq_iff
  have e2 : ∀ x y k : Fin 75735,
      wtV (g • x).val + wtV (g • y).val = wtV (g • k).val ↔ wtV x.val + wtV y.val = wtV k.val := by
    intro x y k
    rw [← rhoMod_wtV g x, ← rhoMod_wtV g y, ← rhoMod_wtV g k, ← map_add]
    exact (rhoMod g).injective.eq_iff
  constructor
  · rintro (h | ⟨k, hk⟩)
    · exact Or.inl ((e1 i j).mp h)
    · refine Or.inr ⟨g⁻¹ • k, (e2 i j (g⁻¹ • k)).mp ?_⟩
      rw [smul_inv_smul]
      exact hk
  · rintro (h | ⟨k, hk⟩)
    · exact Or.inl ((e1 i j).mpr h)
    · exact Or.inr ⟨g • k, (e2 i j k).mpr hk⟩

theorem psi_mem_Stab0_iff (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h : G}
    (h0 : φ (S.cl (h * S.z * h⁻¹)) = wtV 0) (m : S.Mbar) :
    ψ m ∈ Stab0 ↔
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹) := by
  rw [MulAction.mem_stabilizer_iff]
  have h1 := rhoMod_psi_apply hΦ m (S.cl (h * S.z * h⁻¹))
  rw [h0] at h1
  have h2 : rhoMod (ψ m) (wtV 0) = wtV ((ψ m • (0 : Fin 75735)).val) := rhoMod_wtV (ψ m) 0
  constructor
  · intro hs
    apply φ.injective
    rw [← h1, h2, hs, h0]
    rfl
  · intro hs
    apply Fin.ext
    refine wtV_injective (ψ m • (0 : Fin 75735)).2 (0 : Fin 75735).2 ?_
    rw [← h2, h1, hs, h0]
    rfl

theorem map_Lbar_eq_K0 [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (h0 : φ (S.cl (h * S.z * h⁻¹)) = wtV 0) :
    ((S.Lbar h).subgroupOf S.Mbar).map ψ.toMonoidHom = K0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcM := cMbar_eq_normalizer I hw hO haQ hne
  have hle : ((S.Lbar h).subgroupOf S.Mbar).map ψ.toMonoidHom ≤ Stab0 := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    refine (psi_mem_Stab0_iff hΦ h0 ℓ).mpr ?_
    have h1 : (ℓ : S.O) ∈ cMbar S h := by
      rw [hcM]
      exact ⟨ℓ.2, le_normalizer (mem_subgroupOf.mp hℓ)⟩
    exact (SMK.mem_cMbar.mp h1).2
  have hnorm : ∀ g ∈ Stab0, ∀ n ∈ ((S.Lbar h).subgroupOf S.Mbar).map ψ.toMonoidHom,
      g * n * g⁻¹ ∈ ((S.Lbar h).subgroupOf S.Mbar).map ψ.toMonoidHom := by
    rintro g hg _ ⟨ℓ, hℓ, rfl⟩
    have hm := (psi_mem_Stab0_iff hΦ h0 (ψ.symm g)).mp (by rwa [MulEquiv.apply_symm_apply])
    have hm' : ((ψ.symm g : S.Mbar) : S.O) ∈ S.Mbar ⊓ normalizer (S.Lbar h : Set S.O) := by
      rw [← hcM]
      exact ⟨(ψ.symm g).2, hm⟩
    have hmn := (mem_normalizer_subgroupOf_iff (S.Lbar_le_Mbar h) (ψ.symm g)).mpr hm'.2
    refine ⟨ψ.symm g * ℓ * (ψ.symm g)⁻¹, (mem_normalizer_iff.mp hmn ℓ).mp hℓ, ?_⟩
    simp
  have hp : IsPGroup 2 (((S.Lbar h).subgroupOf S.Mbar).map ψ.toMonoidHom) :=
    (S.isPGroup_Lbar_subgroupOf haQ).map _
  refine Subgroup.eq_of_le_of_card_ge (le_K0_of_normal hle hnorm hp) ?_
  have hc1 : Nat.card ((S.Lbar h).subgroupOf S.Mbar) = Nat.card (S.Lbar h) :=
    Nat.card_congr (subgroupOfEquivOfLe (S.Lbar_le_Mbar h)).toEquiv
  have hc2 : Nat.card (((S.Lbar h).subgroupOf S.Mbar).map ψ.toMonoidHom) =
      Nat.card ((S.Lbar h).subgroupOf S.Mbar) := Subgroup.card_map_of_injective ψ.injective
  have hc3 := S.card_Lbar_ge haQ hne
  rw [hw] at hc3
  have hc4 := card_K0_le
  omega

theorem tvDiff_mem_clSub [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (h0 : φ (S.cl (h * S.z * h⁻¹)) = wtV 0) {p : Fin 365211}
    (hp : ∀ x ∈ lineSet p.val, x ∈ planeSub 0) {k : Fin 75735} (hk : ¬ Opp 0 k.val) :
    φ.symm (tvEquiv p.val (wtV k.val) + wtV k.val) ∈ S.clSub (S.QG ⊓ S.Qa h) := by
  classical
  have hpK : (⟨tvP p, tvP_mem p⟩ : TD6) ∈ ((S.Lbar h).subgroupOf S.Mbar).map ψ.toMonoidHom := by
    rw [map_Lbar_eq_K0 I hw hO hΦ haQ hne h0]
    exact tvP_mem_K0 hp
  obtain ⟨ℓ, hℓ, hℓp⟩ := hpK
  obtain ⟨y, hyL, hyℓ⟩ := S.mem_Lbar_iff.mp (mem_subgroupOf.mp hℓ)
  have hyM : rhoM S y = ℓ := Subtype.ext hyℓ
  have hψy : ψ (rhoM S y) = ⟨tvP p, tvP_mem p⟩ := by
    rw [hyM]
    exact hℓp
  have hPhi : Phi S φ y = tvEquiv p.val := by
    rw [hΦ y, hψy, rhoMod_tvP]
  obtain ⟨c, hcQ, hcne, hck⟩ := exists_conj_with_weight_of I hw hO hΦ haQ hne k
  have hf : fModel (wtV k.val) (wtV 0) = if Opp k.val 0 then 1 else 0 :=
    fModel_wtV k.2 (0 : Fin 75735).2
  have hva : c * S.z * c⁻¹ * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * (c * S.z * c⁻¹) := by
    rw [← S.polar_cl_eq_zero_iff hcQ haQ, ← isometry hΦ, hck, h0, hf]
    have hk' : ¬ Opp k.val 0 := fun ho => hk ho.symm
    simp [hk']
  have hyLa : (y : G) ∈ S.La h := (le_sup_right : S.Qa h ⊓ S.M ≤ S.La h) hyL
  have hmem := S.commutator_mem_QG_inf_Qa haQ hne hyLa hcQ hva
  have hconj : (y : G) * (c * S.z * c⁻¹) * (y : G)⁻¹ ∈ S.QG := S.conj_mem_QG y.2 hcQ
  have hx : S.cl ((y : G) * (c * S.z * c⁻¹) * (y : G)⁻¹ * (c * S.z * c⁻¹)⁻¹) =
      φ.symm (tvEquiv p.val (wtV k.val) + wtV k.val) := by
    apply φ.injective
    rw [S.cl_mul hconj (S.QG.inv_mem hcQ), S.cl_inv hcQ, map_add, ← Phi_cl y hcQ, hck, hPhi,
      LinearEquiv.apply_symm_apply]
  rw [← hx]
  exact S.cl_mem_clSub hmem hmem.1

theorem mem_clSub_iff_adjW0 [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (h0 : φ (S.cl (h * S.z * h⁻¹)) = wtV 0) (j : Fin 75735) :
    φ.symm (wtV j.val) ∈ S.clSub (S.QG ⊓ S.Qa h) ↔ adjW 0 j.val = true := by
  obtain ⟨v, hli, hv, hadj⟩ := exists_qaBasis
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hle : Submodule.span (ZMod 2) (Set.range v) ≤
      (S.clSub (S.QG ⊓ S.Qa h)).map (φ : S.Qt →ₗ[ZMod 2] (Fin 32 → ZMod 2)) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    obtain ⟨p, hp, k, hk, hvs⟩ := hv s
    refine ⟨φ.symm (v s), ?_, by simp⟩
    rw [hvs]
    exact tvDiff_mem_clSub I hw hO hΦ haQ hne h0 hp hk
  have heq : Submodule.span (ZMod 2) (Set.range v) =
      (S.clSub (S.QG ⊓ S.Qa h)).map (φ : S.Qt →ₗ[ZMod 2] (Fin 32 → ZMod 2)) := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [LinearEquiv.finrank_map_eq, finrank_span_eq_card hli, Fintype.card_fin]
    exact finrank_clSub_QG_inf_Qa_le hw haQ hne
  rw [← hadj j, heq, Submodule.mem_map_equiv]

theorem mem_Qa_iff_adjW0 [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h c : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (h0 : φ (S.cl (h * S.z * h⁻¹)) = wtV 0)
    (hbQ : c * S.z * c⁻¹ ∈ S.QG) (j : Fin 75735) (hbj : φ (S.cl (c * S.z * c⁻¹)) = wtV j.val) :
    c * S.z * c⁻¹ ∈ S.Qa h ↔ adjW 0 j.val = true := by
  have hz : S.z ∈ S.QG ⊓ S.Qa h := ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩
  rw [← mem_clSub_iff_adjW0 I hw hO hΦ haQ hne h0 j, ← hbj, LinearEquiv.symm_apply_apply]
  constructor
  · intro hb
    exact S.cl_mem_clSub ⟨hbQ, hb⟩ hbQ
  · intro hb
    exact ((S.clPre_clSub inf_le_left hz).le ⟨hbQ, hb⟩).2

theorem mem_Qa_iff_adjW [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h c : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (hbQ : c * S.z * c⁻¹ ∈ S.QG) (hbne : c * S.z * c⁻¹ ≠ S.z)
    (i j : Fin 75735) (hai : φ (S.cl (h * S.z * h⁻¹)) = wtV i.val)
    (hbj : φ (S.cl (c * S.z * c⁻¹)) = wtV j.val) :
    c * S.z * c⁻¹ ∈ S.Qa h ↔ adjW i.val j.val = true := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq i 0
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm g₀)
  obtain ⟨haQ', hne'⟩ := mul_conj_mem m haQ hne
  obtain ⟨hbQ', -⟩ := mul_conj_mem m hbQ hbne
  have hm' : ψ (rhoM S m) = g₀ := by rw [hm, MulEquiv.apply_symm_apply]
  have h0 : φ (S.cl (((m : G) * h) * S.z * ((m : G) * h)⁻¹)) = wtV 0 := by
    rw [phi_cl_mul hΦ m haQ, hm', hai, rhoMod_wtV, hg₀]
    rfl
  have hj : φ (S.cl (((m : G) * c) * S.z * ((m : G) * c)⁻¹)) = wtV (g₀ • j).val := by
    rw [phi_cl_mul hΦ m hbQ, hm', hbj, rhoMod_wtV]
  have e1 : ((m : G) * c) * S.z * ((m : G) * c)⁻¹ ∈ S.Qa ((m : G) * h) ↔
      c * S.z * c⁻¹ ∈ S.Qa h := by
    rw [S.mem_Qa_mul_iff]
    have e : (m : G)⁻¹ * (((m : G) * c) * S.z * ((m : G) * c)⁻¹) * (m : G) = c * S.z * c⁻¹ := by
      group
    rw [e]
  rw [← e1, mem_Qa_iff_adjW0 I hw hO hΦ haQ' hne' h0 hbQ' (g₀ • j) hj, ← adjW_smul_iff g₀ i j,
    hg₀]
  rfl

theorem eq_wtV_of_code32 {v : Fin 32 → ZMod 2} {i : ℕ} (h : code32 v = wt i) : v = wtV i := by
  rw [← decode32_code32 v, h]
  rfl

theorem clauses1235_of_equiv [IsSimpleGroup G] (I : Inputs10) (hAS : AschbacherSmithWideInput)
    (hw : S.width = 16) (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) : SmithE7Clauses1235 S φ := by
  refine ⟨?_, ?_, ?_, clause5 hΦ⟩
  · intro c hc hcQ hcz
    obtain ⟨h, rfl⟩ := isConj_iff.mp hc
    obtain ⟨i, hi⟩ := exists_weight_of_conj I hw hO hΦ hcQ hcz
    refine ⟨i.val, i.2, ?_⟩
    rw [hi, wtV, code32_decode32 (wt_lt i.2)]
  · intro i hi
    obtain ⟨h, hbQ, hbne, hh⟩ := exists_conj_with_weight I hAS hw hO hΦ ⟨i, hi⟩
    refine ⟨h * S.z * h⁻¹, isConj_iff.mpr ⟨h, rfl⟩, hbQ, ?_⟩
    rw [hh, wtV, code32_decode32 (wt_lt hi)]
  · intro h b haQ hne hb hbQ hbne i j hi hj hai hbj
    obtain ⟨c, rfl⟩ := isConj_iff.mp hb
    exact mem_Qa_iff_adjW I hw hO hΦ haQ hne hbQ hbne ⟨i, hi⟩ ⟨j, hj⟩ (eq_wtV_of_code32 hai)
      (eq_wtV_of_code32 hbj)

@[expose] noncomputable def PhiO (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) :
    S.O →* ((Fin 32 → ZMod 2) ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) where
  toFun s := φ.symm.trans ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).trans φ)
  map_one' := by
    ext v
    simp
  map_mul' s t := by
    ext v
    simp only [Subgroup.coe_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

theorem PhiO_injective (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) :
    Function.Injective (PhiO S φ) := by
  intro s t h
  apply Subtype.ext
  ext u
  have := congrArg (fun f : (Fin 32 → ZMod 2) ≃ₗ[ZMod 2] (Fin 32 → ZMod 2) =>
    φ.symm (f (φ u))) h
  simpa [PhiO] using this

@[expose] noncomputable def PhiB (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) :
    S.Mbar →* ((Fin 32 → ZMod 2) ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) :=
  (PhiO S φ).comp S.Mbar.subtype

theorem PhiB_injective (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) : Function.Injective (PhiB S φ) :=
  (PhiO_injective φ).comp Subtype.val_injective

theorem PhiB_rhoM (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) (m : S.M) :
    PhiB S φ (rhoM S m) = Phi S φ m := rfl

theorem range_rhoMod_le (h5 : ∀ k : Fin 365211, ∃ m : S.M, Phi S φ m = tvEquiv k.val) :
    rhoMod.range ≤ (PhiB S φ).range := by
  have H : ∀ x ∈ Subgroup.closure (Set.range tvP), ∀ hx : x ∈ TD6,
      rhoMod ⟨x, hx⟩ ∈ (PhiB S φ).range := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx' =>
      obtain ⟨k, rfl⟩ := hx'
      intro _
      obtain ⟨m, hm⟩ := h5 k
      exact ⟨rhoM S m, by rw [PhiB_rhoM, hm, rhoMod_tvP]⟩
    | one =>
      intro h
      rw [show (⟨1, h⟩ : TD6) = 1 from rfl, map_one]
      exact (PhiB S φ).range.one_mem
    | mul x y hx hy ihx ihy =>
      intro h
      have hxT : x ∈ TD6 := hx
      have hyT : y ∈ TD6 := hy
      rw [show (⟨x * y, h⟩ : TD6) = ⟨x, hxT⟩ * ⟨y, hyT⟩ from rfl, map_mul]
      exact (PhiB S φ).range.mul_mem (ihx hxT) (ihy hyT)
    | inv x hx ihx =>
      intro h
      have hxT : x ∈ TD6 := hx
      rw [show (⟨x⁻¹, h⟩ : TD6) = (⟨x, hxT⟩ : TD6)⁻¹ from rfl, map_inv]
      exact (PhiB S φ).range.inv_mem (ihx hxT)
  rintro _ ⟨t, rfl⟩
  exact H _ t.2 t.2

theorem range_rhoMod_eq (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (h5 : ∀ k : Fin 365211, ∃ m : S.M, Phi S φ m = tvEquiv k.val) :
    rhoMod.range = (PhiB S φ).range := by
  have : Finite ((Fin 32 → ZMod 2) ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) :=
    Finite.of_injective (fun f : (Fin 32 → ZMod 2) ≃ₗ[ZMod 2] (Fin 32 → ZMod 2) =>
      (f : (Fin 32 → ZMod 2) → (Fin 32 → ZMod 2))) fun f g h => LinearEquiv.ext (congrFun h)
  refine Subgroup.eq_of_le_of_card_ge (range_rhoMod_le h5) ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective (f := PhiB S φ) (PhiB_injective φ)).toEquiv]
  obtain ⟨e⟩ := hO
  rw [Nat.card_congr (e.trans omegaTD6).toEquiv]

theorem exists_equiv_of_clause5 (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (h5 : ∀ k : Fin 365211, ∃ m : S.M, Phi S φ m = tvEquiv k.val) :
    ∃ ψ : S.Mbar ≃* TD6, ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)) := by
  have heq := range_rhoMod_eq hO h5
  refine ⟨(MonoidHom.ofInjective (f := PhiB S φ) (PhiB_injective φ)).trans
    ((MulEquiv.subgroupCongr heq.symm).trans
      (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).symm), fun m => ?_⟩
  have key : ∀ y : rhoMod.range,
      rhoMod ((MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).symm y) = y := fun y => by
    have := MonoidHom.ofInjective_apply rhoMod_injective
      (x := (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).symm y)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, key]
  rfl

theorem exists_isModelPhi_of_clauses (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} (hφ : SmithE7Clauses1235 S φ) :
    ∃ ψ : S.Mbar ≃* TD6, ∀ (c : G) (hc : c ∈ S.M) (u : G), u ∈ S.QG →
      φ (S.cl (c * u * c⁻¹)) =
        rhoMod (ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) (φ (S.cl u)) := by
  obtain ⟨-, -, -, h5⟩ := hφ
  have h5' : ∀ k : Fin 365211, ∃ m : S.M, Phi S φ m = tvEquiv k.val := fun k => by
    obtain ⟨m, hm, hA⟩ := h5 k.val k.2
    exact ⟨⟨m, hm⟩, (acts_iff hm k.2).mp hA⟩
  obtain ⟨ψ, hψ⟩ := exists_equiv_of_clause5 hO h5'
  refine ⟨ψ, fun c hc u hu => ?_⟩
  rw [← Phi_cl ⟨c, hc⟩ hu, hψ ⟨c, hc⟩]
  rfl

end Equiv

end CFSG.GF2Type.SmithTypeE.E7
