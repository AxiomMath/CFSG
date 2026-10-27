module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Matrix MatrixGroups Matrix.SpecialLinearGroup

section SL2

variable {F : Type*} [Field F]

theorem apply_one_zero_of_mem_normalizer_slUni {A : SL(2, F)}
    (hA : A ∈ Subgroup.normalizer (slUni F : Set SL(2, F))) :
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have h1 : A * slUpper (1 : F) * A⁻¹ ∈ slUni F :=
    (Subgroup.mem_normalizer_iff.1 hA (slUpper 1)).1 ((mem_slUni).2 ⟨1, rfl⟩)
  obtain ⟨c, hc⟩ := mem_slUni.1 h1
  have h2 := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 1 0) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, slUpper_val, Matrix.mul_apply, Fin.sum_univ_two] at h2
  simp at h2
  have h3 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    linear_combination -h2
  exact mul_self_eq_zero.1 h3

theorem mem_normalizer_slUni_iff {A : SL(2, F)} :
    A ∈ Subgroup.normalizer (slUni F : Set SL(2, F)) ↔ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  ⟨apply_one_zero_of_mem_normalizer_slUni, mem_normalizer_slUni_of_apply_one_zero A⟩

theorem slUni_normalizer_ne_top : Subgroup.normalizer (slUni F : Set SL(2, F)) ≠ ⊤ := by
  intro h
  let w : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  have hw : w ∈ Subgroup.normalizer (slUni F : Set SL(2, F)) := by
    rw [h]; exact Subgroup.mem_top w
  have h2 := apply_one_zero_of_mem_normalizer_slUni hw
  have h3 : (-1 : F) = 0 := h2
  exact one_ne_zero (neg_eq_zero.1 h3)

theorem apply_zero_zero_mul_apply_one_one {A : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have h := A.property
  rw [Matrix.det_fin_two, hA, mul_zero, sub_zero] at h
  exact h

theorem apply_zero_zero_mul (A B : SL(2, F)) :
    ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mulVec_of_apply_one_zero {A : SL(2, F)} (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (v : Fin 2 → F) :
    (A : Matrix (Fin 2) (Fin 2) F).mulVec v 0 =
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 * v 0 + (A : Matrix (Fin 2) (Fin 2) F) 0 1 * v 1 ∧
      (A : Matrix (Fin 2) (Fin 2) F).mulVec v 1 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hA]

end SL2

section Adapted

variable {G : Type*} [Group G]

structure Adapted (L P : Subgroup G) (n : ℕ) (F : Type) [Field F] [Fintype F] where
  P_le : P ≤ L
  card_eq : Fintype.card F = 2 ^ n
  α : L →* SL(2, F)
  α_surj : Function.Surjective α
  α_ker : α.ker = CFSG.pCore 2 L
  β : blockU L →* Multiplicative (Fin 2 → F)
  β_surj : Function.Surjective β
  β_ker : β.ker = (blockZ L).subgroupOf (blockU L)
  β_equiv : ∀ ℓ : L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))
  mem_P : ∀ ℓ : L, (ℓ : G) ∈ P ↔ α ℓ ∈ slUni F

theorem exists_adapted [Finite G] {L P : Subgroup G} {n : ℕ} (hn : 0 < n) (h : IsLin2Type L n)
    (hP : IsSylowTwoOf P L) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Nonempty (Adapted L P n F) := by
  classical
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαker, β, hβs, hβker, hβeq⟩ := h
  have hP2 : IsPGroup 2 (P.subgroupOf L) :=
    hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.le).symm
  have hker : α.ker ≤ P.subgroupOf L := by
    rw [hαker]
    intro z hz
    have hz' : (z : G) ∈ pCoreOf 2 L := ⟨z, by assumption, rfl⟩
    exact hP.pCoreOf_le hz'
  have hmem : ∀ y : L, y ∈ P.subgroupOf L ↔ α y ∈ (P.subgroupOf L).map α := by
    intro y
    constructor
    · exact fun hy => Subgroup.mem_map_of_mem α hy
    · rintro ⟨z, hz, hzy⟩
      have h1 : z⁻¹ * y ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzy, inv_mul_cancel]
      have h2 : z⁻¹ * y ∈ P.subgroupOf L := hker h1
      have := (P.subgroupOf L).mul_mem hz h2
      simpa using this
  have hPsyl : IsSylowTwoOf ((P.subgroupOf L).map α) ⊤ := by
    refine ⟨le_top, hP2.map α, ?_⟩
    show ¬ 2 ∣ ((P.subgroupOf L).map α).relIndex ⊤
    rw [Subgroup.relIndex_top_right, Subgroup.index_map_eq (P.subgroupOf L) hαs hker]
    exact hP.2.2
  have hU : IsSylowTwoOf (slUni F) ⊤ := isSylowTwoOf_slUni hcard hn
  have : Finite F := Finite.of_fintype F
  obtain ⟨g, -, hg⟩ := hU.exists_conj hPsyl
  have hgg : ∀ w : Fin 2 → F, (g : Matrix (Fin 2) (Fin 2) F).mulVec
      (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hgg' : ∀ w : Fin 2 → F, ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
      ((g : Matrix (Fin 2) (Fin 2) F).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  let gl : (Fin 2 → F) →+ (Fin 2 → F) :=
    (Matrix.mulVecLin ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)).toAddMonoidHom
  have hgl : ∀ w, gl w = ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w := fun _ => rfl
  have hglinj : Function.Injective (AddMonoidHom.toMultiplicative gl) := by
    intro a b hab
    have h1 : gl (Multiplicative.toAdd a) = gl (Multiplicative.toAdd b) :=
      congrArg Multiplicative.toAdd hab
    rw [hgl, hgl] at h1
    have h2 := congrArg (fun w => (g : Matrix (Fin 2) (Fin 2) F).mulVec w) h1
    simp only [hgg] at h2
    exact Multiplicative.toAdd.injective h2
  have hβ' : ∀ u, Multiplicative.toAdd (((AddMonoidHom.toMultiplicative gl).comp β) u) =
      ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) :=
    fun _ => rfl
  refine ⟨F, hFfield, hFfin, ⟨⟨hP.le, hcard, (MulAut.conj g⁻¹).toMonoidHom.comp α, ?_, ?_,
    (AddMonoidHom.toMultiplicative gl).comp β, ?_, ?_, ?_, ?_⟩⟩⟩
  · rw [MonoidHom.coe_comp]
    exact (MulAut.conj g⁻¹).surjective.comp hαs
  · rw [MonoidHom.ker_comp_of_injective α (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective, hαker]
  · rw [MonoidHom.coe_comp]
    refine Function.Surjective.comp ?_ hβs
    intro y
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd y)), ?_⟩
    apply Multiplicative.toAdd.injective
    change gl (Multiplicative.toAdd (Multiplicative.ofAdd _)) = _
    rw [toAdd_ofAdd, hgl]
    exact hgg' _
  · rw [MonoidHom.ker_comp_of_injective β (AddMonoidHom.toMultiplicative gl) hglinj, hβker]
  · intro ℓ u v hv
    rw [hβ', hβ', hβeq ℓ u v hv]
    have hSL : (g⁻¹ * α ℓ * g⁻¹⁻¹) * g⁻¹ = g⁻¹ * α ℓ := by simp
    have e : (((g⁻¹ * α ℓ * g⁻¹⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (α ℓ : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hSL]
    change _ = ((g⁻¹ * α ℓ * g⁻¹⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  · intro ℓ
    rw [show ((ℓ : G) ∈ P) ↔ ℓ ∈ P.subgroupOf L from Iff.rfl, hmem ℓ, hg]
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.comp_apply]
    constructor
    · rintro ⟨s, hs, hsℓ⟩
      have : g⁻¹ * α ℓ * g⁻¹⁻¹ = s := by rw [← hsℓ]; group
      rw [this]
      exact hs
    · intro h
      exact ⟨g⁻¹ * α ℓ * g⁻¹⁻¹, h, by group⟩

namespace Adapted

variable {L P : Subgroup G} {n : ℕ} {F : Type} [Field F] [Fintype F]

theorem mem_pCoreOf_iff (A : Adapted L P n F) (ℓ : L) :
    (ℓ : G) ∈ pCoreOf 2 L ↔ A.α ℓ = 1 := by
  constructor
  · rintro ⟨y, hy, hyℓ⟩
    have hy' : y = ℓ := Subtype.ext hyℓ
    subst hy'
    have : y ∈ A.α.ker := by rw [A.α_ker]; assumption
    exact this
  · intro h
    have : ℓ ∈ A.α.ker := h
    rw [A.α_ker] at this
    exact ⟨ℓ, by assumption, rfl⟩

theorem normalizer_iff (A : Adapted L P n F) (ℓ : L) :
    (ℓ : G) ∈ Subgroup.normalizer (P : Set G) ↔
      (A.α ℓ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have e : ∀ q : L, A.α ℓ * A.α q * (A.α ℓ)⁻¹ = A.α (ℓ * q * ℓ⁻¹) := by
    intro q; simp [map_mul, map_inv]
  constructor
  · intro h
    rw [← mem_normalizer_slUni_iff, Subgroup.mem_normalizer_iff]
    intro z
    obtain ⟨q, rfl⟩ := A.α_surj z
    rw [e, ← A.mem_P, ← A.mem_P]
    exact Subgroup.mem_normalizer_iff.1 h (q : G)
  · intro h
    have h1 := Subgroup.mem_normalizer_iff.1 (mem_normalizer_slUni_of_apply_one_zero (A.α ℓ) h)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ L
    · have := h1 (A.α ⟨y, hy⟩)
      rw [e, ← A.mem_P, ← A.mem_P] at this
      exact this
    · have hy' : (ℓ : G) * y * (ℓ : G)⁻¹ ∉ L := by
        intro hh
        apply hy
        have := L.mul_mem (L.mul_mem (L.inv_mem ℓ.2) hh) ℓ.2
        simpa [mul_assoc] using this
      exact ⟨fun hP => absurd (A.P_le hP) hy, fun hP => absurd (A.P_le hP) hy'⟩

theorem not_le_normalizer (A : Adapted L P n F) :
    ¬ L ≤ Subgroup.normalizer (P : Set G) := by
  intro h
  apply slUni_normalizer_ne_top (F := F)
  rw [eq_top_iff]
  intro a _
  obtain ⟨ℓ, rfl⟩ := A.α_surj a
  exact mem_normalizer_slUni_iff.2 ((A.normalizer_iff ℓ).1 (h ℓ.2))

end Adapted

end Adapted

end CFSG.QuasithinUnique.Lin2
