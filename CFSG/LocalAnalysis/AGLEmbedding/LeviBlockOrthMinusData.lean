module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusLeviRes
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviUnipotent
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusLevi
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped commutatorElement

variable {K : Type} [Field K] {r s : ℕ} {d : Fin (s + 1) → ℕ}

variable (K r d) in
abbrev orthLeviGroup : Fin s ⊕ Unit → Type
  | .inl l => GL (Fin (d l.succ - d l.castSucc)) K
  | .inr _ => ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K))

noncomputable instance instGroupOrthLeviGroup : ∀ j, Group (orthLeviGroup K r d j)
  | .inl l => inferInstanceAs (Group (GL (Fin (d l.succ - d l.castSucc)) K))
  | .inr _ => inferInstanceAs (Group (((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) ×
      (Fin 2 → K)) ≃ₗ[K] ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) ×
        (Fin 2 → K))))

theorem finite_orthLinearEquiv {M : Type} [AddCommGroup M] [Module K M] [Finite M] :
    Finite (M ≃ₗ[K] M) :=
  Finite.of_injective (fun g : M ≃ₗ[K] M => (g : M → M)) DFunLike.coe_injective

instance instFiniteOrthLeviGroup [Finite K] : ∀ j, Finite (orthLeviGroup K r d j)
  | .inl l => inferInstanceAs (Finite (GL (Fin (d l.succ - d l.castSucc)) K))
  | .inr _ => finite_orthLinearEquiv (M := ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) →
      K) × (Fin 2 → K)))

variable (K r d) in
@[expose] noncomputable def orthLeviBlock (b c : K) : ∀ j, Subgroup (orthLeviGroup K r d j)
  | .inl l => (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range
  | .inr _ => orthResDer K b c (r - d (Fin.last s))

variable {b c : K}

variable (b c) in
@[expose] noncomputable def orthLeviHom (hd : OrthCuts r d) :
    ↥(orthParab r (minusTailForm K b c) d) →* ∀ j, orthLeviGroup K r d j :=
  MonoidHom.pi fun j => match j with
    | .inl l => orthBlockHom (minusTailForm K b c) hd l
    | .inr _ => orthResHom (minusTailForm K b c) hd

theorem orthLeviHom_inr (hd : OrthCuts r d) (x : ↥(orthParab r (minusTailForm K b c) d))
    (u : Unit) : orthLeviHom b c hd x (.inr u) = orthResHom (minusTailForm K b c) hd x :=
  rfl

theorem isPGroup_ker_orthLeviHom [CharP K 2] (hd : OrthCuts r d) :
    IsPGroup 2 (orthLeviHom b c hd).ker := by
  rintro ⟨x, hx⟩
  set g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) :=
    ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
  have hx1 := MonoidHom.mem_ker.1 hx
  have hblk : ∀ l : Fin s, orthBlockHom (minusTailForm K b c) hd l x = 1 :=
    fun l => congrFun hx1 (.inl l)
  have hres : orthResHom (minusTailForm K b c) hd x = 1 := congrFun hx1 (.inr ())
  let F : ℕ → Submodule K ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) := fun i =>
    tailFlag K (Fin 2 → K) r (if h : i ≤ s then d ⟨i, Nat.lt_succ_of_le h⟩ else d (Fin.last s))
  have hFl : ∀ (i : ℕ) (h : i ≤ s), F i =
      tailFlag K (Fin 2 → K) r (d ⟨i, Nat.lt_succ_of_le h⟩) :=
    fun i h => by simp [F, h]
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)) :=
    mem_orthogonalGroup_of_mem_orthParab
  have hpow := CFSG.SeitzReduction.OmegaPilot.sub_one_pow_eq_zero_of_isotropic_flag
    (polarBilin (quadTail r (minusTailForm K b c))) (g := g)
    (fun v w => by simp only [polarBilin_apply_apply,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO])
    F (by rw [hFl 0 (by omega), show (⟨0, _⟩ : Fin (s + 1)) = 0 from rfl, hd.zero, tailFlag_zero])
    s (fun i hi => by
      rw [hFl i (by omega), hFl (i + 1) (by omega)]
      exact orthTailFlag_mono (hd.mono.monotone (Fin.mk_le_mk.2 (by omega))))
    (fun i hi v hv => by
      rw [hFl (i + 1) (by omega)] at hv
      rw [hFl i (by omega)]
      exact sub_mem_tailFlag_of_orthBlockHom_eq_one hd ⟨i, hi⟩ (hblk ⟨i, hi⟩) hv)
    (fun v hv => by
      rw [hFl s (by omega)] at hv ⊢
      refine sub_mem_tailFlag_of_orthResHom_eq_one hd hres
        ((polar_tailFlag_eq_zero_iff (qB := minusTailForm K b c) hd.last).1 fun w hw => ?_)
      rw [polar_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hv) w hw)
  have h2 := CFSG.SeitzReduction.OmegaPilot.pow_two_pow_eq_one_of_sub_one_pow_eq_zero hpow
  refine ⟨2 * s + 1, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
  simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2

theorem orthCommutator_mem_range_toGL {k : ℕ} (A B : GL (Fin k) K) :
    ⁅A, B⁆ ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range := by
  refine ⟨⟨(⁅A, B⁆ : GL (Fin k) K), ?_⟩, Units.ext rfl⟩
  rw [← Matrix.GeneralLinearGroup.val_det_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), Units.val_one]

theorem commutator_range_orthLeviHom_le (hd : OrthCuts r d) :
    ⁅(orthLeviHom b c hd).range, (orthLeviHom b c hd).range⁆ ≤
      Subgroup.pi Set.univ (orthLeviBlock K r d b c) := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  refine (Subgroup.mem_pi _).2 fun j _ => ?_
  rcases j with l | u
  · change ⁅orthLeviHom b c hd x (.inl l), orthLeviHom b c hd y (.inl l)⁆ ∈ _
    exact orthCommutator_mem_range_toGL _ _
  · change ⁅orthLeviHom b c hd x (.inr u), orthLeviHom b c hd y (.inr u)⁆ ∈
      orthResDer K b c (r - d (Fin.last s))
    exact Subgroup.commutator_mem_commutator (orthResHom_mem_orthogonalGroup hd x)
      (orthResHom_mem_orthogonalGroup hd y)

theorem map_tailFlag_orthLeviRes {t c : ℕ} (ht : t ≤ r) (hc : c ≤ t)
    (B : ((Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K))) :
    (tailFlag K (Fin 2 → K) r c).map ((orthLeviRes K (Fin 2 → K) ht B :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) →ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) =
      tailFlag K (Fin 2 → K) r c := by
  have hfix : ∀ v ∈ tailFlag K (Fin 2 → K) r c, orthLeviRes K (Fin 2 → K) ht B v = v :=
    fun v hv => orthLeviRes_apply_of_mem ht B (orthTailFlag_mono hc hv)
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [LinearEquiv.coe_coe, hfix w hw]
    exact hw
  · exact fun hv => ⟨v, hv, hfix v hv⟩

variable (b c) in
@[expose] noncomputable def orthLeviResElt (hd : OrthCuts r d)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c))⁆ =
        orthElementaryGroup (quadTail r (minusTailForm K b c)))
    (B : ↥(orthResDer K b c (r - d (Fin.last s)))) :
    ↥(orthParab r (minusTailForm K b c) d) :=
  ⟨⟨orthLeviRes K (Fin 2 → K) hd.last B, hE ▸ orthLeviRes_mem_commutator hd.last B.2⟩,
    mem_orthParab.2 fun i => map_tailFlag_orthLeviRes hd.last
      (hd.mono.monotone (Fin.le_last i)) _⟩

theorem coe_orthLeviResElt (hd : OrthCuts r d) (hE) (B) :
    (((orthLeviResElt b c hd hE B : ↥(orthParab r (minusTailForm K b c) d)) :
      ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) =
      orthLeviRes K (Fin 2 → K) hd.last B :=
  rfl

theorem orthBlockMat_orthLeviRes (hd : OrthCuts r d) (l : Fin s)
    (B : ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K))) :
    orthBlockMat hd l (orthLeviRes K (Fin 2 → K) hd.last B) = 1 := by
  ext i j
  have hj : (orthBlockIdx hd l j : ℕ) < d (Fin.last s) := by
    rw [orthBlockIdx_val]
    have := hd.mono.monotone (Fin.le_last l.succ)
    have := j.isLt
    omega
  refine (orthCoefMat_orthLeviRes_apply hd.last B (orthBlockIdx hd l i) hj).trans ?_
  simp only [Matrix.one_apply, (orthBlockIdx_injective hd l).eq_iff]

theorem orthBlockHom_orthLeviResElt (hd : OrthCuts r d) (hE) (B) (l : Fin s) :
    orthBlockHom (minusTailForm K b c) hd l (orthLeviResElt b c hd hE B) = 1 := by
  rw [Units.ext_iff, coe_orthBlockHom, coe_orthLeviResElt, Units.val_one]
  exact orthBlockMat_orthLeviRes (K := K) hd l B

theorem orthResHom_orthLeviResElt (hd : OrthCuts r d) (hE) (B) :
    orthResHom (minusTailForm K b c) hd (orthLeviResElt b c hd hE B) =
      (B : ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K))) :=
  LinearEquiv.ext fun v => by
    rw [orthResHom_apply, coe_orthLeviResElt, orthResMat_orthLeviRes]
    rfl

theorem orthLeviHom_orthLeviResElt (hd : OrthCuts r d) (hE) (B) :
    orthLeviHom b c hd (orthLeviResElt b c hd hE B) =
      Pi.mulSingle (M := orthLeviGroup K r d) (.inr ())
        (B : ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K)) ≃ₗ[K]
          ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K))) := by
  funext j
  rcases j with l | u
  · rw [Pi.mulSingle_eq_of_ne Sum.inl_ne_inr]
    exact orthBlockHom_orthLeviResElt hd hE B l
  · obtain rfl : u = () := rfl
    rw [Pi.mulSingle_eq_same]
    exact orthResHom_orthLeviResElt hd hE B

theorem orthLeviHom_orthLeviSL [CharP K 2] (hd : OrthCuts r d) (hr : 3 ≤ r) (l : Fin s)
    (B : Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K) :
    orthLeviHom b c hd (orthLeviSL hd (minusTailForm K b c) hr l B) =
      Pi.mulSingle (M := orthLeviGroup K r d) (.inl l)
        (Matrix.SpecialLinearGroup.toGL B : GL (Fin (d l.succ - d l.castSucc)) K) := by
  funext j
  rcases j with l' | u
  · by_cases h : l' = l
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact orthBlockHom_orthLeviSL_self hd _ hr l' B
    · rw [Pi.mulSingle_eq_of_ne (fun e => h (Sum.inl_injective e))]
      exact orthBlockHom_orthLeviSL_of_ne hd _ hr h B
  · rw [Pi.mulSingle_eq_of_ne Sum.inr_ne_inl]
    exact orthResHom_orthLeviSL hd _ hr l B

theorem pi_orthLeviBlock_le_range [CharP K 2] (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c))⁆ =
        orthElementaryGroup (quadTail r (minusTailForm K b c))) :
    Subgroup.pi Set.univ (orthLeviBlock K r d b c) ≤ (orthLeviHom b c hd).range := by
  rw [Subgroup.pi_le_iff]
  rintro (l | u)
  · rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    exact ⟨orthLeviSL hd (minusTailForm K b c) hr l B, orthLeviHom_orthLeviSL hd hr l B⟩
  · obtain rfl : u = () := rfl
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨orthLeviResElt b c hd hE ⟨B, hB⟩, orthLeviHom_orthLeviResElt hd hE ⟨B, hB⟩⟩

end CFSG.AGLEmbedding.LeviBlock
