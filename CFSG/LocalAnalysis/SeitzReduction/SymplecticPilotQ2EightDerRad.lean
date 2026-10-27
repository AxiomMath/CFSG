module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightDerLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaClosRad
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaSiegPerfect

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open scoped commutatorElement

theorem sp8d_exists_of_map_eq {G H : Type} [Group G] [Group H] {M : Subgroup G}
    {Φ₁ Φ₂ : G →* H} (hC : M.map Φ₁ = M.map Φ₂) {g : G} (hg : g ∈ M) :
    ∃ g' ∈ M, Φ₂ g' = Φ₁ g := by
  have h : Φ₁ g ∈ M.map Φ₂ := hC ▸ ⟨g, hg, rfl⟩
  obtain ⟨g', hg', e⟩ := h
  exact ⟨g', hg', e⟩

variable {K : Type} [Field K]

theorem sp8d_derived_le :
    ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
      centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ ≤
      centralizer ({spARep 4 2} : Set (StatedSp 4 K)) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

@[expose, instance_reducible] noncomputable def sp8dAct (P : Subgroup (StatedSp 4 K))
    (hP : P ≤ centralizer ({spARep 4 2} : Set (StatedSp 4 K))) : MulAction P (Fin 4 → K) where
  smul p v := sp8dLam (p : StatedSp 4 K) *ᵥ v
  one_smul v := by
    show sp8dLam ((1 : P) : StatedSp 4 K) *ᵥ v = v
    rw [OneMemClass.coe_one, sp8dLam_one, Matrix.one_mulVec]
  mul_smul p q v := by
    show sp8dLam ((p * q : P) : StatedSp 4 K) *ᵥ v =
      sp8dLam (p : StatedSp 4 K) *ᵥ (sp8dLam (q : StatedSp 4 K) *ᵥ v)
    rw [Subgroup.coe_mul, sp8dLam_mul (hP q.2), Matrix.mulVec_mulVec]

variable [CharP K 2]

theorem sp8d_upperUnipotentSp_mem_derived {X : Matrix (Fin 4) (Fin 4) K} (hX : Xᵀ = X) :
    upperUnipotentSp 4 K hX ∈ ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
      centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ :=
  upperUnipotentSp_mem_commutator_two (n := 4) (j := 2) (by norm_num) le_rfl hX
    (fun a b _ => ⟨a.isLt, b.isLt⟩)

theorem sp8d_lam_eq_one [Finite K] (hK : Nat.card K = 2) {H : Type} [Group H]
    {Φ₁ Φ₂ : StatedSp 4 K →* H} (h₁ : Function.Injective Φ₁)
    (hC : (⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
        centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆).map Φ₁ =
      (⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
        centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆).map Φ₂)
    {p : StatedSp 4 K} (hp : p ∈ ((spARadical K 4 2 (by norm_num)).map Φ₂).comap Φ₁) :
    p ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K)) ∧ sp8dLam p = 1 := by
  set P := ((spARadical K 4 2 (by norm_num)).map Φ₂).comap Φ₁ with hPdef
  have hPC0 : P ≤ ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
      centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ := by
    intro q hq
    obtain ⟨r, hr, e⟩ := hq
    obtain ⟨X, hX, rfl⟩ := (mem_spARadical_iff_eq_upperUnipotentSp (show 2 * 2 = 4 from rfl)).1 hr
    obtain ⟨q', hq', e'⟩ := sp8d_exists_of_map_eq hC.symm (sp8d_upperUnipotentSp_mem_derived hX)
    rw [← h₁ (e'.trans e)]
    exact hq'
  have hPC : P ≤ centralizer ({spARep 4 2} : Set (StatedSp 4 K)) := hPC0.trans sp8d_derived_le
  refine ⟨hPC hp, ?_⟩
  have hP2 : IsPGroup 2 P :=
    ((isPGroup_spARadical (K := K) (by norm_num : 2 * 2 ≤ 4)).map Φ₂).comap_of_injective Φ₁ h₁
  let _ : MulAction P (Fin 4 → K) := sp8dAct P hPC
  have hsmul : ∀ (q : P) (v : Fin 4 → K), q • v = sp8dLam (q : StatedSp 4 K) *ᵥ v :=
    fun _ _ => rfl
  have hcard : 2 ∣ Nat.card (Fin 4 → K) := by
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have h0fix : (0 : Fin 4 → K) ∈ MulAction.fixedPoints P (Fin 4 → K) := fun q => by
    rw [hsmul, Matrix.mulVec_zero]
  obtain ⟨b, hb, hb0⟩ :=
    hP2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 4 → K) hcard h0fix
  set Fix : Set (Fin 4 → K) := {v | ∀ q ∈ P, sp8dLam q *ᵥ v = v} with hFix
  have hbFix : b ∈ Fix := fun q hq => by
    have := hb ⟨q, hq⟩
    rwa [hsmul] at this
  have hFadd : ∀ v ∈ Fix, ∀ w ∈ Fix, v + w ∈ Fix := fun v hv w hw q hq => by
    rw [Matrix.mulVec_add, hv q hq, hw q hq]
  obtain ⟨hb1, -, -⟩ := sp8d_levi_gens_mem (K := K) hK
  set g₁ := leviEmbedGL K 4 (sp8dB1GL hK) with hg₁
  have hg₁C : g₁ ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K)) := sp8d_derived_le hb1
  have hg₁iC : g₁⁻¹ ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K)) := inv_mem hg₁C
  have hlam₁ : sp8dLam g₁ = sp8dMap hK sp8dB1 := by
    rw [hg₁, sp8dLam_leviEmbedGL, coe_sp8dB1GL]
  have hlam₁i : sp8dMap hK sp8dB1 * sp8dLam g₁⁻¹ = 1 := by
    rw [← hlam₁, ← sp8dLam_mul hg₁iC, mul_inv_cancel, sp8dLam_one]
  have hconjP : ∀ q ∈ P, g₁⁻¹ * q * g₁ ∈ P := by
    intro q hq
    obtain ⟨r, hr, e⟩ := hq
    obtain ⟨X, hX, rfl⟩ := (mem_spARadical_iff_eq_upperUnipotentSp (show 2 * 2 = 4 from rfl)).1 hr
    obtain ⟨c, hc, ec⟩ := sp8d_exists_of_map_eq hC hb1
    have hciC : c⁻¹ ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K)) :=
      inv_mem (sp8d_derived_le hc)
    have hconj := sp8d_conj_upperUnipotentSp hciC hX
    rw [inv_inv] at hconj
    refine ⟨upperUnipotentSp 4 K (transpose_mul_mul_transpose (sp8dLam c⁻¹) hX),
      upperUnipotentSp_mem_spARadical (show 2 * 2 = 4 from rfl) _, ?_⟩
    rw [← hconj, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ec, e]
  have hFB : ∀ v ∈ Fix, sp8dMap hK sp8dB1 *ᵥ v ∈ Fix := by
    intro v hv q hq
    have hq' := hconjP q hq
    have hl : sp8dLam (g₁⁻¹ * q * g₁) = sp8dLam g₁⁻¹ * sp8dLam q * sp8dMap hK sp8dB1 := by
      rw [sp8dLam_mul hg₁C, sp8dLam_mul (hPC hq), hlam₁]
    have key : sp8dLam q * sp8dMap hK sp8dB1 = sp8dMap hK sp8dB1 * sp8dLam (g₁⁻¹ * q * g₁) := by
      rw [hl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hlam₁i, Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hv _ hq']
  set e := sp8dEquiv (K := K) hK with he
  set W₂ : Set (Fin 4 → ZMod 2) := {w | (fun i => e (w i)) ∈ Fix} with hW₂
  have hW₂add : ∀ x ∈ W₂, ∀ y ∈ W₂, x + y ∈ W₂ := fun x hx y hy => by
    have h : (fun i => e ((x + y) i)) = (fun i => e (x i)) + (fun i => e (y i)) := by
      funext i
      simp
    show (fun i => e ((x + y) i)) ∈ Fix
    rw [h]
    exact hFadd _ hx _ hy
  have hW₂0 : (0 : Fin 4 → ZMod 2) ∈ W₂ := by
    show (fun i => e ((0 : Fin 4 → ZMod 2) i)) ∈ Fix
    have h : (fun i => e ((0 : Fin 4 → ZMod 2) i)) = 0 := by
      funext i
      simp
    rw [h]
    exact fun q _ => Matrix.mulVec_zero _
  have hW₂B : ∀ x ∈ W₂, sp8dB1 *ᵥ x ∈ W₂ := fun x hx => by
    have h : (fun i => e ((sp8dB1 *ᵥ x) i)) = sp8dMap hK sp8dB1 *ᵥ (fun i => e (x i)) := by
      funext i
      exact RingHom.map_mulVec e.toRingHom sp8dB1 x i
    show (fun i => e ((sp8dB1 *ᵥ x) i)) ∈ Fix
    rw [h]
    exact hFB _ hx
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hW₂smul : ∀ (c : ZMod 2) {x : Fin 4 → ZMod 2}, x ∈ W₂ → c • x ∈ W₂ := by
    intro c x hx
    rcases h01 c with rfl | rfl
    · rw [zero_smul]
      exact hW₂0
    · rwa [one_smul]
  set b₂ : Fin 4 → ZMod 2 := fun i => e.symm (b i) with hb₂
  have hb₂W : b₂ ∈ W₂ := by
    show (fun i => e (b₂ i)) ∈ Fix
    have h : (fun i => e (b₂ i)) = b := by
      funext i
      simp [hb₂]
    rw [h]
    exact hbFix
  have hb₂eq : ![b₂ 0, b₂ 1, b₂ 2, b₂ 3] = b₂ := by
    funext i
    fin_cases i <;> rfl
  have hb₂0 : ![b₂ 0, b₂ 1, b₂ 2, b₂ 3] ≠ 0 := by
    rw [hb₂eq]
    intro h
    apply hb0
    funext i
    have := congrFun h i
    simp only [hb₂, Pi.zero_apply] at this
    rw [Pi.zero_apply, ← e.apply_symm_apply (b i), this, map_zero]
  have hsingle : ∀ k : Fin 4, Pi.single k 1 ∈ Fix := by
    intro k
    obtain ⟨c0, c1, c2, c3, hk⟩ := sp8dB1_irred _ _ _ _ hb₂0 k
    rw [hb₂eq] at hk
    have hk2 : (Pi.single k 1 : Fin 4 → ZMod 2) ∈ W₂ := by
      rw [hk]
      exact hW₂add _ (hW₂add _ (hW₂add _ (hW₂smul _ hb₂W) _ (hW₂smul _ (hW₂B _ hb₂W))) _
        (hW₂smul _ (hW₂B _ (hW₂B _ hb₂W)))) _ (hW₂smul _ (hW₂B _ (hW₂B _ (hW₂B _ hb₂W))))
    have h : (fun i => e ((Pi.single k 1 : Fin 4 → ZMod 2) i)) = Pi.single k 1 := by
      funext i
      by_cases hik : i = k
      · subst hik
        simp
      · simp [hik]
    have := hk2
    simp only [hW₂, Set.mem_ofPred_eq, h] at this
    exact this
  ext i k
  have h := congrFun (hsingle k p hp) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h, Matrix.one_apply, Pi.single_apply]

section F

variable {H : Type} [Group H] (Φ₁ Φ₂ : StatedSp 4 K →* H)

@[expose] def Sp8dFRel (X Y : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∃ (hX : Xᵀ = X) (hY : Yᵀ = Y), Φ₂ (upperUnipotentSp 4 K hX) = Φ₁ (upperUnipotentSp 4 K hY)

open Classical in
@[expose] noncomputable def sp8dF (X : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  if h : ∃ Y, Sp8dFRel Φ₁ Φ₂ X Y then h.choose else 0

variable {Φ₁ Φ₂} [Finite K] (hK : Nat.card K = 2) (h₁ : Function.Injective Φ₁)
  (hC : (⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
      centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆).map Φ₁ =
    (⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
      centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆).map Φ₂)
include hK h₁ hC

theorem sp8d_exists_radical {X : Matrix (Fin 4) (Fin 4) K} (hX : Xᵀ = X) :
    ∃ Y, Sp8dFRel Φ₁ Φ₂ X Y := by
  obtain ⟨p, hp, e⟩ := sp8d_exists_of_map_eq hC.symm (sp8d_upperUnipotentSp_mem_derived hX)
  have hpP : p ∈ ((spARadical K 4 2 (by norm_num)).map Φ₂).comap Φ₁ :=
    ⟨upperUnipotentSp 4 K hX, upperUnipotentSp_mem_spARadical (show 2 * 2 = 4 from rfl) hX,
      e.symm⟩
  obtain ⟨hpC, h1⟩ := sp8d_lam_eq_one hK h₁ hC hpP
  obtain ⟨Y, hY, rfl⟩ := sp8d_eq_upperUnipotentSp_of_lam hpC h1
  exact ⟨Y, hX, hY, e.symm⟩

theorem sp8dF_spec {X : Matrix (Fin 4) (Fin 4) K} (hX : Xᵀ = X) :
    Sp8dFRel Φ₁ Φ₂ X (sp8dF Φ₁ Φ₂ X) := by
  have h := sp8d_exists_radical hK h₁ hC hX
  rw [sp8dF, dite_eq_left h]
  exact h.choose_spec

theorem sp8dF_transpose {X : Matrix (Fin 4) (Fin 4) K} (hX : Xᵀ = X) :
    (sp8dF Φ₁ Φ₂ X)ᵀ = sp8dF Φ₁ Φ₂ X :=
  (sp8dF_spec hK h₁ hC hX).2.1

theorem sp8dF_eq {X : Matrix (Fin 4) (Fin 4) K} (hX : Xᵀ = X) :
    Φ₂ (upperUnipotentSp 4 K hX) =
      Φ₁ (upperUnipotentSp 4 K (sp8dF_transpose hK h₁ hC hX)) :=
  (sp8dF_spec hK h₁ hC hX).2.2

theorem sp8dF_add {X Y : Matrix (Fin 4) (Fin 4) K} (hX : Xᵀ = X) (hY : Yᵀ = Y) :
    sp8dF Φ₁ Φ₂ (X + Y) = sp8dF Φ₁ Φ₂ X + sp8dF Φ₁ Φ₂ Y := by
  have hXY : (X + Y)ᵀ = X + Y := by rw [transpose_add, hX, hY]
  have e1 := sp8dF_eq hK h₁ hC hXY
  rw [← upperUnipotentSp_mul hX hY, map_mul, sp8dF_eq hK h₁ hC hX, sp8dF_eq hK h₁ hC hY,
    ← map_mul, upperUnipotentSp_mul] at e1
  exact (upperUnipotentSp_inj_lag _ _ (h₁ e1)).symm

theorem sp8dF_injective (h₂ : Function.Injective Φ₂) {X Y : Matrix (Fin 4) (Fin 4) K}
    (hX : Xᵀ = X) (hY : Yᵀ = Y) (h : sp8dF Φ₁ Φ₂ X = sp8dF Φ₁ Φ₂ Y) : X = Y := by
  have e : Φ₂ (upperUnipotentSp 4 K hX) = Φ₂ (upperUnipotentSp 4 K hY) := by
    rw [sp8dF_eq hK h₁ hC hX, sp8dF_eq hK h₁ hC hY]
    exact congrArg Φ₁ (upperUnipotentSp_congr _ _ h)
  exact upperUnipotentSp_inj_lag _ _ (h₂ e)

theorem sp8dF_S (ha : Φ₁ (spARep 4 2) = Φ₂ (spARep 4 2)) :
    sp8dF Φ₁ Φ₂ (spARepMat 4 2) = spARepMat 4 2 := by
  have e := sp8dF_eq hK h₁ hC (spARepMat_transpose (K := K) 4 2)
  have e2 : Φ₂ (upperUnipotentSp 4 K (spARepMat_transpose (K := K) 4 2)) =
      Φ₁ (upperUnipotentSp 4 K (spARepMat_transpose (K := K) 4 2)) := ha.symm
  rw [e2] at e
  exact (upperUnipotentSp_inj_lag _ _ (h₁ e)).symm

theorem sp8dF_twisted {b c : StatedSp 4 K}
    (hb : b ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K)))
    (hc : c ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K))) (hbc : Φ₁ b = Φ₂ c)
    {Z : Matrix (Fin 4) (Fin 4) K} (hZ : Zᵀ = Z) :
    sp8dLam b * sp8dF Φ₁ Φ₂ Z * (sp8dLam b)ᵀ =
      sp8dF Φ₁ Φ₂ (sp8dLam c * Z * (sp8dLam c)ᵀ) := by
  have hZ' := transpose_mul_mul_transpose (sp8dLam c) hZ
  have e1 := sp8d_conj_upperUnipotentSp hb (sp8dF_transpose hK h₁ hC hZ)
  have e2 := sp8d_conj_upperUnipotentSp hc hZ
  have key : Φ₁ (upperUnipotentSp 4 K (transpose_mul_mul_transpose (sp8dLam b)
      (sp8dF_transpose hK h₁ hC hZ))) =
      Φ₁ (upperUnipotentSp 4 K (sp8dF_transpose hK h₁ hC hZ')) := by
    rw [← e1, ← sp8dF_eq hK h₁ hC hZ', ← e2, map_mul, map_mul, map_mul, map_mul, map_inv,
      map_inv, hbc, sp8dF_eq hK h₁ hC hZ]
  exact upperUnipotentSp_inj_lag _ _ (h₁ key)

end F

end CFSG.SeitzReduction.SymplecticPilot
