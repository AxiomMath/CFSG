module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlusPart
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlusWeir

public section

namespace CFSG.AGLEmbeddingD2.HeisSpinPlus

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.AGLEmbeddingD2.SquareSpinPlus CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow

theorem isLeft_swap_of_not {n : ℕ} (x : Fin n ⊕ Fin n) (h : ¬ x.isLeft = true) :
    x.swap.isLeft = true := by
  cases x <;> simp_all

theorem not_isLeft_swap_of_isLeft {n : ℕ} (x : Fin n ⊕ Fin n) (h : x.isLeft = true) :
    ¬ x.swap.isLeft = true := by
  cases x <;> simp_all

section Form

variable {n : ℕ} {F : Type} [Field F] {κ : Type} [DecidableEq κ]
  {s : Fin n ⊕ Fin n → κ} {κ₀ : κ}

theorem blockExt_single (a : {z // s z = κ₀}) :
    blockExt (F := F) s κ₀ (Pi.single a 1) = Pi.single (a : Fin n ⊕ Fin n) 1 := by
  funext z
  by_cases hz : s z = κ₀
  · rw [blockExt_of_eq _ hz]
    by_cases h : z = a
    · subst h
      simp
    · have : (⟨z, hz⟩ : {z // s z = κ₀}) ≠ a := fun e => h (congrArg Subtype.val e)
      simp [this, h]
  · rw [blockExt_of_ne _ hz]
    have : z ≠ (a : Fin n ⊕ Fin n) := fun e => hz (e ▸ a.2)
    simp [this]

theorem polar_blockForm (hsw : ∀ z, s z = κ₀ → s z.swap = κ₀) (v : {z // s z = κ₀} → F)
    (a : {z // s z = κ₀}) :
    polar (blockForm (F := F) s κ₀) v (Pi.single a 1) = v ⟨a.1.swap, hsw a.1 a.2⟩ := by
  have h : polar (blockForm (F := F) s κ₀) v (Pi.single a 1) =
      polar (quadPlus n F) (blockExt s κ₀ v) (blockExt s κ₀ (Pi.single a 1)) := by
    simp only [polar, blockForm, QuadraticMap.comp_apply, map_add]
  rw [h, blockExt_single, polar_quadPlus_single_swap]
  exact blockExt_of_eq v (hsw a.1 a.2)

theorem nondegenerate_polarBilin_blockForm (hsw : ∀ z, s z = κ₀ → s z.swap = κ₀) :
    (polarBilin (blockForm (F := F) s κ₀)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  funext a
  have h := hv (Pi.single ⟨a.1.swap, hsw a.1 a.2⟩ 1)
  rw [polar_blockForm hsw] at h
  simpa using h

theorem isPlusType_blockForm (hsw : ∀ z, s z = κ₀ → s z.swap = κ₀) :
    IsPlusType (blockForm (F := F) s κ₀) := by
  classical
  let b : {z : {z // s z = κ₀} // z.1.isLeft = true} → ({z // s z = κ₀} → F) :=
    fun z => Pi.single z.1 1
  have hli : LinearIndependent F b := by
    have := (Pi.basisFun F {z // s z = κ₀}).linearIndependent.comp
      (fun z : {z : {z // s z = κ₀} // z.1.isLeft = true} => z.1) Subtype.val_injective
    simpa [b, Function.comp_def] using this
  have key : ∀ x ∈ Submodule.span F (Set.range b), ∀ z : {z // s z = κ₀},
      z.1.isLeft = false → x z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      intro z hz
      have : z ≠ y.1 := fun e => by
        have := y.2
        rw [← e, hz] at this
        exact Bool.false_ne_true this
      simp [b, this.symm]
    | zero => intro z _; simp
    | add x y _ _ hx hy => intro z hz; simp [hx z hz, hy z hz]
    | smul a x _ hx => intro z hz; simp [hx z hz]
  refine ⟨Submodule.span F (Set.range b), ?_, ?_⟩
  · rw [finrank_span_eq_card hli, Module.finrank_fintype_fun_eq_card]
    have h1 : Fintype.card {z : {z // s z = κ₀} // ¬ z.1.isLeft = true} =
        Fintype.card {z : {z // s z = κ₀} // z.1.isLeft = true} :=
      Fintype.card_congr
        { toFun := fun z => ⟨⟨z.1.1.swap, hsw _ z.1.2⟩, isLeft_swap_of_not _ z.2⟩
          invFun := fun z => ⟨⟨z.1.1.swap, hsw _ z.1.2⟩, not_isLeft_swap_of_isLeft _ z.2⟩
          left_inv := fun z => by ext; simp
          right_inv := fun z => by ext; simp }
    have h2 := Fintype.card_subtype_compl (fun z : {z // s z = κ₀} => z.1.isLeft = true)
    have h3 := Fintype.card_subtype_le (fun z : {z // s z = κ₀} => z.1.isLeft = true)
    omega
  · intro x hx
    rw [blockForm_apply, quadPlus_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : blockExt s κ₀ x (Sum.inr i) = 0 := by
      by_cases hz : s (Sum.inr i) = κ₀
      · rw [blockExt_of_eq _ hz]
        exact key x hx ⟨_, hz⟩ rfl
      · exact blockExt_of_ne _ hz
    rw [h0, mul_zero]

end Form

section Group

variable {n : ℕ} {F : Type} [Field F] [Finite F] {κ : Type} [DecidableEq κ]
  {s : Fin n ⊕ Fin n → κ} {κ₀ : κ}

theorem isMulCommutative_of_isoBlock_card_twenty {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f)
    (hcard : Fintype.card {z // s z = κ₀} = 20) (hsw : ∀ z, s z = κ₀ → s z.swap = κ₀)
    (P : Subgroup (GL {z // s z = κ₀} F)) (hPi : P ≤ isoBlock F s κ₀) (h5 : IsPGroup 5 P) :
    IsMulCommutative P := by
  classical
  let Φ := toLinEquiv {z // s z = κ₀} F
  let Q := blockForm (F := F) s κ₀
  have hΦO : ∀ A ∈ isoBlock F s κ₀, Φ A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun A hA =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [toLinEquiv_apply]
      exact hA v
  let Pamb : Subgroup (({z // s z = κ₀} → F) ≃ₗ[F] ({z // s z = κ₀} → F)) :=
    P.map Φ.toMonoidHom
  have hle : Pamb ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨A, hA, rfl⟩
    exact hΦO A (hPi hA)
  have hPamb5 : IsPGroup 5 Pamb := h5.map Φ.toMonoidHom
  let PO : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) := Pamb.subgroupOf _
  have hPO : IsPGroup 5 PO := hPamb5.comap_of_injective _ (Subgroup.subtype_injective _)
  have hcomm := isMulCommutative_of_isPGroup_five_orthogonal hf hF
    (V := {z // s z = κ₀} → F) (by rw [Module.finrank_fintype_fun_eq_card, hcard]) Q
    (nondegenerate_polarBilin_blockForm hsw) (isPlusType_blockForm hsw) PO hPO
  refine ⟨⟨fun a b => ?_⟩⟩
  have hab := hcomm.is_comm.comm
    (⟨⟨Φ a, hle ⟨a.1, a.2, rfl⟩⟩, ⟨a.1, a.2, rfl⟩⟩ : PO)
    (⟨⟨Φ b, hle ⟨b.1, b.2, rfl⟩⟩, ⟨b.1, b.2, rfl⟩⟩ : PO)
  have hab' : Φ a.1 * Φ b.1 = Φ b.1 * Φ a.1 :=
    congrArg (fun z : PO => ((z : TauCeti.QuadraticMap.orthogonalGroup Q) :
      ({z // s z = κ₀} → F) ≃ₗ[F] ({z // s z = κ₀} → F))) hab
  exact Subtype.ext (Φ.injective (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hab'))

theorem isMulCommutative_of_part_odd [CharP F 2] {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f)
    {Q : Subgroup (spinGroup (quadPlus n F))} (hQs : Q ≤ partSub (F := F) s)
    (hQ5 : IsPGroup 5 Q)
    (hs : ∀ κ₀ : κ, Fintype.card {z // s z = κ₀} < 20 ∨
      (Fintype.card {z // s z = κ₀} = 20 ∧ ∀ z, s z = κ₀ → s z.swap = κ₀)) :
    IsMulCommutative Q :=
  isMulCommutative_of_blocks hQs hQ5 fun κ₀ P hP hP5 => by
    rcases hs κ₀ with h | ⟨h, hsw⟩
    · exact PartStab.isMulCommutative_of_isPGroup_five_GL_fintype hF (Or.inl ⟨hf, h⟩) P hP5
    · exact isMulCommutative_of_isoBlock_card_twenty hf hF h hsw P hP hP5

theorem isMulCommutative_of_part_two [CharP F 2] {f : ℕ} (hf : f % 4 = 2) (hF : Nat.card F = 2 ^ f)
    {Q : Subgroup (spinGroup (quadPlus n F))} (hQs : Q ≤ partSub (F := F) s)
    (hQ5 : IsPGroup 5 Q) (hs : ∀ κ₀ : κ, Fintype.card {z // s z = κ₀} < 10) :
    IsMulCommutative Q :=
  isMulCommutative_of_blocks hQs hQ5 fun κ₀ P _ hP5 =>
    PartStab.isMulCommutative_of_isPGroup_five_GL_fintype hF (Or.inr (Or.inl ⟨hf, hs κ₀⟩)) P hP5

end Group

end CFSG.AGLEmbeddingD2.HeisSpinPlus
