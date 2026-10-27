module

public import CFSG.ClassicalInvolution.AschTight.S19KOutU
public import CFSG.ClassicalInvolution.AschTight.S19KUni
public import CFSG.ClassicalInvolution.AschTight.S19KUniFL

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def conjSU {M : GL (Fin 3) K} (hM : M ∈ isomU K p f) :
    Phan.Su K p f 3 →* Phan.Su K p f 3 where
  toFun x := (exists_conj_su hM x).choose
  map_one' := Subtype.ext (by rw [(exists_conj_su hM 1).choose_spec]; simp)
  map_mul' x y := Subtype.ext (by
    rw [(exists_conj_su hM (x * y)).choose_spec]
    simp only [Subgroup.coe_mul]
    rw [(exists_conj_su hM x).choose_spec, (exists_conj_su hM y).choose_spec]
    group)

theorem coe_conjSU {M : GL (Fin 3) K} (hM : M ∈ isomU K p f) (x : Phan.Su K p f 3) :
    ((conjSU hM x : Phan.Su K p f 3) : GL (Fin 3) K) = M * (x : GL (Fin 3) K) * M⁻¹ :=
  (exists_conj_su hM x).choose_spec

theorem conjSU_mul {M₁ M₂ : GL (Fin 3) K} (h₁ : M₁ ∈ isomU K p f) (h₂ : M₂ ∈ isomU K p f)
    (x : Phan.Su K p f 3) :
    conjSU ((isomU K p f).mul_mem h₁ h₂) x = conjSU h₁ (conjSU h₂ x) := by
  apply Subtype.ext
  rw [coe_conjSU, coe_conjSU, coe_conjSU]
  group

theorem exists_dpow_lift {α : Phan.Su K p f 3 →* Phan.Su K p f 3}
    {G : GL (Fin 3) K} {τ : K ≃+* K}
    (hform : ∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) *
        τ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hτ : τ = RingEquiv.refl K ∨ τ = unitaryInvolution K p f) :
    ∃ ε : Bool, ∀ x, ((α x : Phan.Su K p f 3) : GL (Fin 3) K) =
      (MulAut.conj G * dpow ε : MulAut (GL (Fin 3) K)) (x : GL (Fin 3) K) := by
  rcases hτ with rfl | rfl
  · refine ⟨false, fun x => Units.ext ?_⟩
    rw [hform, RingEquiv.mapMatrix_refl]
    rfl
  · refine ⟨true, fun x => Units.ext ?_⟩
    rw [hform]
    have h1 := conjTr_eq_inv x
    rw [conjTr] at h1
    have h2 : (unitaryInvolution K p f).mapMatrix
        (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((x⁻¹ : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).transpose := by
      rw [RingEquiv.mapMatrix_apply, ← h1, Matrix.transpose_transpose]
    rw [h2]
    rfl

theorem lift_surjectiveU {α : Phan.Su K p f 3 →* Phan.Su K p f 3} {G : GL (Fin 3) K} {ε : Bool}
    (hf : ∀ x, ((α x : Phan.Su K p f 3) : GL (Fin 3) K) =
      (MulAut.conj G * dpow ε : MulAut (GL (Fin 3) K)) (x : GL (Fin 3) K)) :
    Function.Surjective α := by
  refine Finite.injective_iff_surjective.mp fun x y hxy => ?_
  have h1 := hf x
  rw [hxy, hf y] at h1
  exact Subtype.ext ((MulAut.conj G * dpow ε).injective h1).symm

theorem hyp_of_mem_fixingSubgroupU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    {E : Type} [Group E] (θ : Phan.Su K p f 3 →* E)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) {h : MulAut E}
    (hh : h ∈ fixingSubgroup (MulAut E) (((rootU K p f).map θ : Subgroup E) : Set E)) :
    ∃ (ι : ↥((rootU K p f).map θ) ≃* SL(2, fixedSubfield K p f))
        (g : GL (Fin 2) (fixedSubfield K p f)),
      ∀ x : ↥((rootU K p f).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((rootU K p f).map θ)) : E) = h x := by
  have hR : ∀ r ∈ rootU K p f, r ∈ Subgroup.center (Phan.Su K p f 3) → r = 1 :=
    fun r hr hc => eq_one_of_mem_center_rootSU2 hK hp hf hr hc
  obtain ⟨ι₀, -⟩ := exists_stdEquivU hK
  refine ⟨(restrictEquiv θ hker hR).symm.trans ι₀, 1, fun x => ?_⟩
  have h1 : ∀ A : SL(2, fixedSubfield K p f),
      Asc77.AscL62.semilinHom 1 (RingEquiv.refl _) A = A := fun A =>
    Subtype.ext (by rw [Asc77.AscL62.coe_semilinHom]; simp)
  rw [h1, MulEquiv.symm_apply_apply]
  exact ((mem_fixingSubgroup_iff (MulAut E)).mp hh x x.2).symm

theorem fg2Uni (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {E : Type}
    [Group E] (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) :
    ⁅⁅fixingSubgroup (MulAut E) (((rootU K p f).map θ : Subgroup E) : Set E),
      fixingSubgroup (MulAut E) (((rootU K p f).map θ : Subgroup E) : Set E)⁆,
      ⁅fixingSubgroup (MulAut E) (((rootU K p f).map θ : Subgroup E) : Set E),
      fixingSubgroup (MulAut E) (((rootU K p f).map θ : Subgroup E) : Set E)⁆⁆ = ⊥ := by
  set H := fixingSubgroup (MulAut E) (((rootU K p f).map θ : Subgroup E) : Set E)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hcard := card_fixedSubfield (F := K) (p := p) (f := f) hK
  have hcl2 := Models.isClassicalSL2_rootSU2 (K := K) (p := p) (f := f) hK hp (n := 3)
    (by norm_num)
  have : Group.IsPerfect (rootU K p f) := hcl2.isPerfect (by omega)
  set N := innerDiag θ (SUid (unitaryInvolution K p f) 3).subtype Subtype.val_injective
    (isomU K p f) (fun M hM x => exists_conj_su hM x)
  refine derived_derived_eq_bot (A := H ⊓ N) ?_ ?_
  · rw [Subgroup.commutator_le]
    intro h₁ hh₁ h₂ hh₂
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
    obtain ⟨α₁, G₁, τ₁, hα₁, hf₁, hiso₁, -, hτ₁⟩ := uni_lift_data hK hp hq hcard θ hθ hker h₁
      (hyp_of_mem_fixingSubgroupU hK hp hf θ hker hh₁)
    obtain ⟨α₂, G₂, τ₂, hα₂, hf₂, hiso₂, -, hτ₂⟩ := uni_lift_data hK hp hq hcard θ hθ hker h₂
      (hyp_of_mem_fixingSubgroupU hK hp hf θ hker hh₂)
    obtain ⟨ε₁, hd₁⟩ := exists_dpow_lift hf₁ hτ₁
    obtain ⟨ε₂, hd₂⟩ := exists_dpow_lift hf₂ hτ₂
    have hsurj : Function.Surjective (α₂.comp α₁) := by
      rw [MonoidHom.coe_comp]
      exact (lift_surjectiveU hd₂).comp (lift_surjectiveU hd₁)
    exact commutator_mem_innerDiag θ _ _ (isomU K p f) _ (fun M hM => invTr_mem_isomU hK hM)
      hiso₁ hiso₂ hα₁ hα₂ hd₁ hd₂ hsurj
  · have key : ∀ a ∈ H ⊓ N, ∃ (M : GL (Fin 3) K) (hM : M ∈ isomU K p f),
        IsBlockScalar (M : Matrix (Fin 3) (Fin 3) K) ∧ ∀ x, a (θ x) = θ (conjSU hM x) := by
      rintro a ⟨haH, M, hMU, hM⟩
      have hconj : ∀ x, a (θ x) = θ (conjSU hMU x) := fun x => hM x _ (coe_conjSU hMU x)
      have hab := ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hker
        ((conjSU hMU).comp (rootU K p f).subtype) (rootU K p f).subtype fun r => by
          rw [MonoidHom.comp_apply, ← hconj]
          exact (mem_fixingSubgroup_iff (MulAut E)).mp haH _ ⟨r, r.2, rfl⟩
      refine ⟨M, hMU, isBlockScalar_of_commute_rootSU2 hK hp (by omega) fun x hx => ?_, hconj⟩
      have h1 := congrArg (fun y : Phan.Su K p f 3 =>
        (((y : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (DFunLike.congr_fun hab ⟨x, hx⟩)
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_conjSU, Units.val_mul] at h1
      calc (M : Matrix (Fin 3) (Fin 3) K) * (((x : Phan.Su K p f 3) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) =
          (M : Matrix (Fin 3) (Fin 3) K) * (((x : Phan.Su K p f 3) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) * (((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              (M : Matrix (Fin 3) (Fin 3) K)) := by rw [Units.inv_mul, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h1]
    intro a ha b hb
    obtain ⟨M₁, hU₁, hM₁, ha'⟩ := key a ha
    obtain ⟨M₂, hU₂, hM₂, hb'⟩ := key b hb
    have hMM : M₁ * M₂ = M₂ * M₁ :=
      Units.ext (commute_of_isBlockDiag ⟨hM₁.2.1, hM₁.2.2.2.1, hM₁.2.2.2.2.1,
        hM₁.2.2.2.2.2.1⟩ hM₂)
    ext e
    obtain ⟨x, rfl⟩ := hθ e
    rw [MulAut.mul_apply, MulAut.mul_apply, hb', ha', ha', hb', ← conjSU_mul, ← conjSU_mul]
    congr 1
    apply Subtype.ext
    rw [coe_conjSU, coe_conjSU, hMM]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
