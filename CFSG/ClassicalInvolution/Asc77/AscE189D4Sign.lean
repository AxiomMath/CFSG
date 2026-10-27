module

public import CFSG.ClassicalInvolution.Asc77.AscE189D4Frames
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthClifford
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthList
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthBig
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CliffordAlgebra QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section SpinSq

variable [FiniteDimensional K V]

theorem spin_sq_of_finrank_four (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {z : spinGroup Q} {i : V ≃ₗ[K] V} (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hii : i * i = 1) (hzi : spinAction Q z = i) (h4 : Module.finrank K (minusSp i) = 4) :
    z * z = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hW : PolarNondegOn Q (minusSp i) := polarNondegOn_minusSp h2 hQ hi hii
  have hQ' : (polarBilin (Q.restrict (minusSp i))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hW
  have hQ'' : (Q.restrict (minusSp i)).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ'
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨l, hlen, hlorth, hlne, hlspan, -⟩ := exists_orthogonal_list_restrict Q (minusSp i) hQ''
  have hl4 : l.length = 4 := hlen.trans h4
  have heven : Even l.length := by rw [hl4]; decide
  obtain ⟨_, _, hzz⟩ := spinLift_sq_and_norm hQnd hi hii hzi hlorth heven hlspan hlne
  rw [hl4] at hzz
  apply Subtype.ext
  change (z : CliffordAlgebra Q) * z = 1
  rw [hzz]
  norm_num [Nat.choose]

theorem sq_eq_of_lift (h2 : (2 : K) ≠ 0) (hQ : Q.Nondegenerate) [Nontrivial V]
    {M : Subgroup (spinGroup Q)} {z u : spinGroup Q} (hz : IsUniqueInvolution M z) (hu : u ∈ M)
    (hπ : spinAction Q z ≠ 1) (huz : spinAction Q u * spinAction Q u = spinAction Q z) :
    u * u = z := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hc : u * u * z⁻¹ ∈ (spinAction Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, huz, mul_inv_cancel]
  rcases (mem_ker_spinAction_iff Q hQ _).mp hc with h | h
  · exact mul_inv_eq_one.mp h
  · exfalso
    have hmem : spinGroup.negOne Q hQ.ne_zero ∈ M := by
      rw [← h]
      exact M.mul_mem (M.mul_mem hu hu) (M.inv_mem hz.mem)
    rcases hz.unique _ hmem (spinGroup.negOne_mul_self Q hQ.ne_zero) with h1 | h1
    · exact spinGroup.negOne_ne_one Q hQ.ne_zero h1
    · apply hπ
      have hker : spinGroup.negOne Q hQ.ne_zero ∈ (spinAction Q).ker :=
        (mem_ker_spinAction_iff Q hQ _).mpr (Or.inr rfl)
      rw [← h1]
      exact hker

end SpinSq

section DiagInv

@[expose] def cxJSL : SL(2, K) := ⟨cxJ, by simp [cxJ, Matrix.det_fin_two_of]⟩

theorem coe_cxJSL : ((cxJSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = cxJ := rfl

theorem cxJ_mul_cxJ : (cxJ * cxJ : Matrix (Fin 2) (Fin 2) K) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cxJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem cxJSL_mul_self : (cxJSL * cxJSL : SL(2, K)) = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_cxJSL, cxJ_mul_cxJ]
  simp

structure DiagData (F₀ F₁ : Frame Q) (bar : V ≃ₗ[K] V) : Prop where
  mem : bar ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  orth : ∀ X Y, polar Q (F₀.incl X) (F₁.incl Y) = 0
  bar₀ : ∀ Y, bar (F₀.incl Y) = F₀.incl (Y * cxJ)
  bar₁ : ∀ Y, bar (F₁.incl Y) = F₁.incl (Y * cxJ)

variable {F₀ F₁ : Frame Q} {bar : V ≃ₗ[K] V}

@[expose] noncomputable def diagInv (F₀ F₁ : Frame Q) (bar : V ≃ₗ[K] V) : V ≃ₗ[K] V :=
  bar * (F₀.La cxJSL * F₁.La cxJSL)

theorem DiagData.coords_incl₁ (hD : DiagData F₀ F₁ bar) (X : Matrix (Fin 2) (Fin 2) K) :
    F₀.coords (F₁.incl X) = 0 :=
  Frame.coords_incl_eq_zero_of_orth (fun X Y => by rw [polar_comm]; exact hD.orth Y X) X

theorem DiagData.coords_incl₀ (hD : DiagData F₀ F₁ bar) (X : Matrix (Fin 2) (Fin 2) K) :
    F₁.coords (F₀.incl X) = 0 :=
  Frame.coords_incl_eq_zero_of_orth hD.orth X

theorem diagInv_incl₀ (hD : DiagData F₀ F₁ bar) (X : Matrix (Fin 2) (Fin 2) K) :
    diagInv F₀ F₁ bar (F₀.incl X) = F₀.incl (cxJ * X * cxJ) := by
  rw [diagInv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Frame.La_apply_of_coords_eq_zero F₁ _ (hD.coords_incl₀ X), Frame.La_apply_incl, coe_cxJSL,
    hD.bar₀]

theorem diagInv_incl₁ (hD : DiagData F₀ F₁ bar) (Y : Matrix (Fin 2) (Fin 2) K) :
    diagInv F₀ F₁ bar (F₁.incl Y) = F₁.incl (cxJ * Y * cxJ) := by
  rw [diagInv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_apply_incl, coe_cxJSL,
    Frame.La_apply_of_coords_eq_zero F₀ _ (hD.coords_incl₁ _), hD.bar₁]

theorem diagInv_mem (hD : DiagData F₀ F₁ bar) :
    diagInv F₀ F₁ bar ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.mul_mem _ hD.mem
    (Subgroup.mul_mem _ (F₀.La_mem_orthogonalGroup _) (F₁.La_mem_orthogonalGroup _))

variable [FiniteDimensional K V]

theorem exists_incl_add (hdim : Module.finrank K V = 8) (hD : DiagData F₀ F₁ bar) (x : V) :
    ∃ X Y : Matrix (Fin 2) (Fin 2) K, x = F₀.incl X + F₁.incl Y := by
  have hdisj : F₀.span ⊓ F₁.span = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨X, rfl⟩, hx1⟩ := Submodule.mem_inf.mp hx
    have := (Frame.mem_span_iff F₁).mp hx1
    rw [hD.coords_incl₀, map_zero] at this
    simpa using this
  have hsup : F₀.span ⊔ F₁.span = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq F₀.span F₁.span
    rw [hdisj, finrank_bot, F₀.finrank_span, F₁.finrank_span] at this
    omega
  have hx : x ∈ F₀.span ⊔ F₁.span := hsup ▸ Submodule.mem_top
  obtain ⟨u, ⟨X, rfl⟩, v, ⟨Y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨X, Y, rfl⟩

theorem diagInv_mul_self (hdim : Module.finrank K V = 8) (hD : DiagData F₀ F₁ bar) :
    diagInv F₀ F₁ bar * diagInv F₀ F₁ bar = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨X, Y, rfl⟩ := exists_incl_add hdim hD x
  have h : ∀ M : Matrix (Fin 2) (Fin 2) K, cxJ * (cxJ * M * cxJ) * cxJ = M := fun M => by
    calc cxJ * (cxJ * M * cxJ) * cxJ = (cxJ * cxJ) * M * (cxJ * cxJ) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [cxJ_mul_cxJ]; simp
  rw [LinearEquiv.mul_apply, map_add, map_add, diagInv_incl₀ hD, diagInv_incl₁ hD,
    diagInv_incl₀ hD, diagInv_incl₁ hD, h, h]
  rfl

theorem four_le_finrank_of_incl_mem (hD : DiagData F₀ F₁ bar) (S : Submodule K V)
    {M₁ M₂ : Matrix (Fin 2) (Fin 2) K} (h00 : M₁ 0 0 = 1) (h01 : M₁ 0 1 = 0) (h10 : M₂ 0 0 = 0)
    (h11 : M₂ 0 1 = 1) (hS₁ : F₀.incl M₁ ∈ S) (hS₂ : F₀.incl M₂ ∈ S) (hS₃ : F₁.incl M₁ ∈ S)
    (hS₄ : F₁.incl M₂ ∈ S) : 4 ≤ Module.finrank K S := by
  set v : Fin 4 → V := ![F₀.incl M₁, F₀.incl M₂, F₁.incl M₁, F₁.incl M₂] with hv
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_four, hv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hc
    have e0 := congrArg F₀.coords hc
    have e1 := congrArg F₁.coords hc
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, Frame.coords_incl,
      Frame.coords_incl, hD.coords_incl₁, hD.coords_incl₁, map_zero, smul_zero, smul_zero,
      add_zero, add_zero] at e0
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, Frame.coords_incl,
      Frame.coords_incl, hD.coords_incl₀, hD.coords_incl₀, map_zero, smul_zero, smul_zero,
      zero_add, zero_add] at e1
    have a0 := congrFun (congrFun e0 0) 0
    have a1 := congrFun (congrFun e0 0) 1
    have b0 := congrFun (congrFun e1 0) 0
    have b1 := congrFun (congrFun e1 0) 1
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, h00, h01,
      h10, h11] at a0 a1 b0 b1
    intro i
    fin_cases i
    · simpa using a0
    · simpa using a1
    · simpa using b0
    · simpa using b1
  have hspan : Submodule.span K (Set.range v) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hS₁
    · exact hS₂
    · exact hS₃
    · exact hS₄
  calc 4 = Module.finrank K (Submodule.span K (Set.range v)) := by
        rw [finrank_span_eq_card hli]
        simp
    _ ≤ Module.finrank K S := Submodule.finrank_mono hspan

theorem finrank_minusSp_diagInv (h2 : (2 : K) ≠ 0) (hdim : Module.finrank K V = 8)
    (hD : DiagData F₀ F₁ bar) : Module.finrank K (minusSp (diagInv F₀ F₁ bar)) = 4 := by
  have hii := diagInv_mul_self hdim hD
  have hmin : ∀ (F : Frame Q) (hF : ∀ M : Matrix (Fin 2) (Fin 2) K,
      diagInv F₀ F₁ bar (F.incl M) = F.incl (cxJ * M * cxJ)) (M : Matrix (Fin 2) (Fin 2) K),
      cxJ * M * cxJ = -M → F.incl M ∈ minusSp (diagInv F₀ F₁ bar) := by
    intro F hF M hM
    rw [mem_minusSp, hF, hM, map_neg]
  have hplus : ∀ (F : Frame Q) (hF : ∀ M : Matrix (Fin 2) (Fin 2) K,
      diagInv F₀ F₁ bar (F.incl M) = F.incl (cxJ * M * cxJ)) (M : Matrix (Fin 2) (Fin 2) K),
      cxJ * M * cxJ = M → F.incl M ∈ plusSp (diagInv F₀ F₁ bar) := by
    intro F hF M hM
    rw [mem_plusSp, hF, hM]
  have m1 : cxJ * (1 : Matrix (Fin 2) (Fin 2) K) * cxJ = -1 := by
    rw [Matrix.mul_one, cxJ_mul_cxJ]
  have m2 : cxJ * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * cxJ = -!![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cxJ, Matrix.mul_apply, Fin.sum_univ_two]
  have p1 : cxJ * (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) * cxJ = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cxJ, Matrix.mul_apply, Fin.sum_univ_two]
  have p2 : cxJ * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * cxJ = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cxJ, Matrix.mul_apply, Fin.sum_univ_two]
  have h4m : 4 ≤ Module.finrank K (minusSp (diagInv F₀ F₁ bar)) :=
    four_le_finrank_of_incl_mem hD _ (M₁ := 1) (M₂ := !![0, 1; -1, 0]) (by simp) (by simp)
      (by simp) (by simp) (hmin F₀ (diagInv_incl₀ hD) _ m1) (hmin F₀ (diagInv_incl₀ hD) _ m2)
      (hmin F₁ (diagInv_incl₁ hD) _ m1) (hmin F₁ (diagInv_incl₁ hD) _ m2)
  have h4p : 4 ≤ Module.finrank K (plusSp (diagInv F₀ F₁ bar)) :=
    four_le_finrank_of_incl_mem hD _ (M₁ := !![1, 0; 0, -1]) (M₂ := !![0, 1; 1, 0]) (by simp)
      (by simp) (by simp) (by simp) (hplus F₀ (diagInv_incl₀ hD) _ p1)
      (hplus F₀ (diagInv_incl₀ hD) _ p2) (hplus F₁ (diagInv_incl₁ hD) _ p1)
      (hplus F₁ (diagInv_incl₁ hD) _ p2)
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_plusSp_minusSp h2 hii)
  omega

theorem sign_relation [Finite K] (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 8) (hD : DiagData F₀ F₁ bar)
    {M₀ M₁ : Subgroup (spinGroup Q)} (hM₀ : M₀.map (spinAction Q) = F₀.La.range)
    (hM₁ : M₁.map (spinAction Q) = F₁.La.range) {z₀ z₁ : spinGroup Q}
    (hz₀ : IsUniqueInvolution M₀ z₀) (hz₁ : IsUniqueInvolution M₁ z₁)
    (hπz₀ : spinAction Q z₀ = F₀.La (-1)) (hπz₁ : spinAction Q z₁ = F₁.La (-1))
    (hM : ∀ u ∈ M₀, ∀ v ∈ M₁, u * v = v * u) {a : spinGroup Q} (ha : spinAction Q a = bar)
    (ha₀ : ∀ w ∈ M₀, w * a = a * w) (ha₁ : ∀ w ∈ M₁, w * a = a * w) :
    a * a * (z₀ * z₁) = 1 := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨u₀, hu₀, hu₀π⟩ := Subgroup.mem_map.mp (hM₀ ▸ ⟨cxJSL, rfl⟩ :
    F₀.La cxJSL ∈ M₀.map (spinAction Q))
  obtain ⟨u₁, hu₁, hu₁π⟩ := Subgroup.mem_map.mp (hM₁ ▸ ⟨cxJSL, rfl⟩ :
    F₁.La cxJSL ∈ M₁.map (spinAction Q))
  have hsq₀ : u₀ * u₀ = z₀ :=
    sq_eq_of_lift h2 hQnd hz₀ hu₀ (by rw [hπz₀]; exact (IsFundamental.of_frame F₀).ne_one hodd)
      (by rw [hu₀π, hπz₀, ← map_mul, cxJSL_mul_self])
  have hsq₁ : u₁ * u₁ = z₁ :=
    sq_eq_of_lift h2 hQnd hz₁ hu₁ (by rw [hπz₁]; exact (IsFundamental.of_frame F₁).ne_one hodd)
      (by rw [hu₁π, hπz₁, ← map_mul, cxJSL_mul_self])
  have hw : spinAction Q (a * (u₀ * u₁)) = diagInv F₀ F₁ bar := by
    rw [map_mul, map_mul, ha, hu₀π, hu₁π]
    rfl
  have hww : (a * (u₀ * u₁)) * (a * (u₀ * u₁)) = 1 :=
    spin_sq_of_finrank_four h2 hQ (diagInv_mem hD) (diagInv_mul_self hdim hD) hw
      (finrank_minusSp_diagInv h2 hdim hD)
  have hau₀ : Commute u₀ a := ha₀ u₀ hu₀
  have hau₁ : Commute u₁ a := ha₁ u₁ hu₁
  have hu : Commute u₀ u₁ := hM u₀ hu₀ u₁ hu₁
  have hb : Commute (u₀ * u₁) a := hau₀.mul_left hau₁
  have e1 : (a * (u₀ * u₁)) * (a * (u₀ * u₁)) = (a * a) * ((u₀ * u₁) * (u₀ * u₁)) := by
    have := (Commute.mul_pow hb.symm 2)
    simpa only [pow_two] using this
  have e2 : (u₀ * u₁) * (u₀ * u₁) = (u₀ * u₀) * (u₁ * u₁) := by
    have := (Commute.mul_pow hu 2)
    simpa only [pow_two] using this
  rw [hsq₀, hsq₁] at e2
  rw [← e2, ← e1]
  exact hww

end DiagInv

end CFSG.ClassicalInvolution.Asc77
