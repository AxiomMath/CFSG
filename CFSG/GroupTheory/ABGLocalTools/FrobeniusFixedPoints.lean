module

public import CFSG.GroupTheory.ABGLocalTools.FixedPointCount
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Pi

public section

open Module TensorProduct

namespace CFSG.ABGLocalTools

section BaseChange

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
variable (E : Type*) [Field E] [Algebra F E]

@[expose] noncomputable def baseChangeRep (ρ : Representation F G V) :
    Representation E G (E ⊗[F] V) where
  toFun g := (ρ g).baseChange E
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one F V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

@[simp]
theorem baseChangeRep_apply_tmul (ρ : Representation F G V) (g : G) (e : E) (v : V) :
    baseChangeRep E ρ g (e ⊗ₜ v) = e ⊗ₜ ρ g v :=
  LinearMap.baseChange_tmul _ _ _

noncomputable def invariantsDefect (ρ : Representation F G V) : V →ₗ[F] (G → V) :=
  LinearMap.pi fun g => ρ g - LinearMap.id

theorem ker_invariantsDefect (ρ : Representation F G V) :
    LinearMap.ker (invariantsDefect ρ) = Representation.invariants ρ := by
  ext v
  simp only [LinearMap.mem_ker, invariantsDefect, Representation.mem_invariants]
  constructor
  · intro h g
    have := congrFun h g
    simpa [sub_eq_zero] using this
  · intro h
    funext g
    simp [h g]

variable {E}

theorem finrank_invariants_baseChange [Finite G] [FiniteDimensional F V]
    (ρ : Representation F G V) :
    finrank E (Representation.invariants (baseChangeRep E ρ)) =
      finrank F (Representation.invariants ρ) := by
  classical
  let _ := Fintype.ofFinite G
  set Φ := invariantsDefect ρ with hΦ
  have hfac : invariantsDefect (baseChangeRep E ρ) =
      (piRight F E E (fun _ : G => V)).toLinearMap ∘ₗ Φ.baseChange E := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro e v
    funext g
    simp [invariantsDefect, hΦ, tmul_sub]
  have hker : LinearMap.ker (invariantsDefect (baseChangeRep E ρ)) =
      LinearMap.ker (Φ.baseChange E) := by
    rw [hfac, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  have hflat := Module.Flat.ker_lTensor_eq (R := F) E E Φ
  have hbc : Φ.baseChange E = AlgebraTensorModule.lTensor E E Φ := rfl
  have hinj :
      Function.Injective (AlgebraTensorModule.lTensor E E (LinearMap.ker Φ).subtype) := by
    rw [AlgebraTensorModule.coe_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker Φ).injective_subtype
  rw [← ker_invariantsDefect, hker, hbc, hflat, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_baseChange, ← ker_invariantsDefect]

end BaseChange

section Group

variable {H : Type*} [Group H]

theorem exists_eq_conj_mul_inv_of_fixedPointFree [Finite H] {K : Subgroup H}
    {b : H} (hbK : b ∈ Subgroup.normalizer (K : Set H))
    (hfpf : ∀ k ∈ K, b * k = k * b → k = 1) {k : H} (hk : k ∈ K) :
    ∃ l ∈ K, k = b⁻¹ * l * b * l⁻¹ := by
  have hconj : ∀ l ∈ K, b⁻¹ * l * b ∈ K := fun l hl => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbK) l).mp hl
    simpa using this
  let φ : K → K := fun l => ⟨b⁻¹ * l * b * (l : H)⁻¹,
    K.mul_mem (hconj l l.2) (K.inv_mem l.2)⟩
  have hinj : Function.Injective φ := by
    intro l l' h
    have h' : b⁻¹ * (l : H) * b * (l : H)⁻¹ = b⁻¹ * l' * b * (l' : H)⁻¹ := congrArg Subtype.val h
    set u : K := ⟨b⁻¹ * l * b, hconj l l.2⟩
    set u' : K := ⟨b⁻¹ * l' * b, hconj l' l'.2⟩
    have hK' : u * l⁻¹ = u' * l'⁻¹ := Subtype.ext h'
    have hx : u'⁻¹ * u = l'⁻¹ * l := by
      calc u'⁻¹ * u = u'⁻¹ * (u * l⁻¹) * l := by group
        _ = u'⁻¹ * (u' * l'⁻¹) * l := by rw [hK']
        _ = l'⁻¹ * l := by group
    have hxb : b * ((l' : H)⁻¹ * l) = ((l' : H)⁻¹ * l) * b := by
      have h2 : ((u'⁻¹ * u : K) : H) = b⁻¹ * ((l' : H)⁻¹ * l) * b := by
        simp only [u, u', Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have h3 : ((u'⁻¹ * u : K) : H) = (l' : H)⁻¹ * l := by
        rw [hx]
        simp
      rw [h2] at h3
      calc b * ((l' : H)⁻¹ * l) = b * (b⁻¹ * ((l' : H)⁻¹ * l) * b) := by rw [h3]
        _ = ((l' : H)⁻¹ * l) * b := by group
    have h1 := hfpf _ (K.mul_mem (K.inv_mem l'.2) l.2) hxb
    rw [inv_mul_eq_one] at h1
    exact (Subtype.ext h1).symm
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  obtain ⟨l, hl⟩ := hsurj ⟨k, hk⟩
  exact ⟨l, l.2, (congrArg Subtype.val hl).symm⟩

end Group

section Semisimple

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W]

theorem isFinitelySemisimple_of_pow_eq_one {T : Module.End E W} {m : ℕ}
    (hT : T ^ m = 1) (hchar : (m : E) ≠ 0) : Module.End.IsFinitelySemisimple T := by
  have hsep : (Polynomial.X ^ m - Polynomial.C (1 : E)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 hchar one_ne_zero
  apply Module.End.IsSemisimple.isFinitelySemisimple
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
  simp [hT]

end Semisimple

section Eigen

theorem iSupIndep_iInf_eigenspace_and_iSup_eq_top {E : Type*} [Field E] [IsAlgClosed E]
    {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W] {ι : Type*}
    (f : ι → Module.End E W) (hcomm : ∀ i j, Commute (f i) (f j))
    (hss : ∀ i, Module.End.IsFinitelySemisimple (f i)) :
    iSupIndep (fun χ : ι → E => ⨅ i, Module.End.eigenspace (f i) (χ i)) ∧
      ⨆ χ : ι → E, ⨅ i, Module.End.eigenspace (f i) (χ i) = ⊤ := by
  have heq : ∀ χ : ι → E, ⨅ i, Module.End.eigenspace (f i) (χ i) =
      ⨅ i, Module.End.maxGenEigenspace (f i) (χ i) := by
    intro χ
    congr 1
    funext i
    exact ((hss i).maxGenEigenspace_eq_eigenspace (χ i)).symm
  simp_rw [heq]
  constructor
  · apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    intro i j φ
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  · apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun i j _ => hcomm i j)
    intro i
    exact Module.End.iSup_maxGenEigenspace_eq_top (f i)

end Eigen

section Main

open Subgroup

theorem finrank_invariants_mul_card_of_fixedPointFree {F : Type*} [Field F] {H : Type*}
    [Group H] [Finite H] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F H V) {K B : Subgroup H} (hK : IsMulCommutative K)
    (hBK : B ≤ normalizer (K : Set H))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1)
    (hchar : ¬ ringChar F ∣ Nat.card K)
    (hfix : Representation.invariants (ρ.comp K.subtype) = ⊥) :
    Module.finrank F (Representation.invariants (ρ.comp B.subtype)) * Nat.card B =
      Module.finrank F V := by
  classical
  let E := AlgebraicClosure F
  let W := E ⊗[F] V
  let ρE := baseChangeRep E ρ
  have hdB : finrank E (Representation.invariants (ρE.comp B.subtype)) =
      finrank F (Representation.invariants (ρ.comp B.subtype)) :=
    finrank_invariants_baseChange (E := E) (ρ.comp B.subtype)
  have hdK : Representation.invariants (ρE.comp K.subtype) = ⊥ := by
    have h := finrank_invariants_baseChange (E := E) (ρ.comp K.subtype)
    rw [hfix, finrank_bot] at h
    exact Submodule.finrank_eq_zero.mp h
  have hW : finrank E W = finrank F V := Module.finrank_baseChange
  let f : K → Module.End E W := fun k => ρE k
  have hcomm : ∀ k l : K, Commute (f k) (f l) := by
    intro k l
    show ρE k * ρE l = ρE l * ρE k
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hK.is_comm.comm k l)
  have hss : ∀ k : K, Module.End.IsFinitelySemisimple (f k) := by
    intro k
    apply isFinitelySemisimple_of_pow_eq_one (m := Nat.card K)
    · show ρE k ^ Nat.card K = 1
      rw [← map_pow, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one, map_one]
    · intro h0
      apply hchar
      have : ((Nat.card K : ℕ) : F) = 0 := by
        apply (algebraMap F E).injective
        rw [map_natCast, map_zero]
        exact h0
      exact (ringChar.spec F _).mp this
  obtain ⟨hind, htop⟩ := iSupIndep_iInf_eigenspace_and_iSup_eq_top f hcomm hss
  set Vχ : (K → E) → Submodule E W := fun χ => ⨅ k, Module.End.eigenspace (f k) (χ k)
    with hVχ
  have hmemVχ : ∀ (χ : K → E) (v : W), v ∈ Vχ χ ↔ ∀ k : K, ρE k v = χ k • v := by
    intro χ v
    simp only [hVχ, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, f]
  have hconj : ∀ b ∈ B, ∀ k ∈ K, b⁻¹ * k * b ∈ K := fun b hb k hk => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBK hb)) k).mp hk
    simpa using this
  let act : B → (K → E) → (K → E) := fun b χ k =>
    χ ⟨(b : H)⁻¹ * k * b, hconj b b.2 k k.2⟩
  have hmaps : ∀ (b : B) (χ : K → E), ∀ v ∈ Vχ χ, ρE b v ∈ Vχ (act b χ) := by
    intro b χ v hv
    rw [hmemVχ] at hv ⊢
    intro k
    have h1 : ρE k (ρE b v) = ρE b (ρE ((b : H)⁻¹ * k * b) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    have h2 : ρE ((b : H)⁻¹ * k * b) v = χ ⟨(b : H)⁻¹ * k * b, hconj b b.2 k k.2⟩ • v :=
      hv ⟨(b : H)⁻¹ * k * b, hconj b b.2 k k.2⟩
    rw [h1, h2, map_smul]
  have hne : ∀ (b : B) (χ : K → E), Vχ χ ≠ ⊥ → Vχ (act b χ) ≠ ⊥ := by
    intro b χ hχ hbot
    apply hχ
    rw [eq_bot_iff]
    intro v hv
    have h1 := hmaps b χ v hv
    rw [hbot, Submodule.mem_bot] at h1
    have h2 := congrArg (ρE (b : H)⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h2
    exact (Submodule.mem_bot E).mpr h2
  let I := {χ : K → E // Vχ χ ≠ ⊥}
  have hIfin : Finite I := by
    have := hind.fintypeNeBotOfFiniteDimensional
    infer_instance
  let mulAct : MulAction B I :=
    { smul := fun b χ => ⟨act b χ.1, hne b χ.1 χ.2⟩
      one_smul := fun χ => Subtype.ext (funext fun k => by
        change χ.1 ⟨((1 : B) : H)⁻¹ * k * ((1 : B) : H), _⟩ = χ.1 k
        exact congrArg χ.1 (Subtype.ext (by simp)))
      mul_smul := fun b c χ => Subtype.ext (funext fun k => by
        change χ.1 ⟨((b * c : B) : H)⁻¹ * k * ((b * c : B) : H), _⟩ =
          χ.1 ⟨(c : H)⁻¹ * ((b : H)⁻¹ * k * b) * c, _⟩
        exact congrArg χ.1 (Subtype.ext (by simp only [Subgroup.coe_mul, mul_inv_rev]; group))) }
  have hfree : ∀ (b : B) (χ : I), b • χ = χ → b = 1 := by
    intro b χ hbχ
    by_contra hb1
    have hb1' : (b : H) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.2
    have hv' := (hmemVχ χ.1 v).mp hv
    have hfix' : ∀ k : K, χ.1 ⟨(b : H)⁻¹ * k * b, hconj b b.2 k k.2⟩ = χ.1 k := fun k =>
      congrFun (congrArg Subtype.val hbχ) k
    have hmul : ∀ k l : K, χ.1 (k * l) = χ.1 k * χ.1 l := by
      intro k l
      have h1 : ρE (k * l : K) v = (χ.1 k * χ.1 l) • v := by
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hv' l, map_smul, hv' k, smul_smul,
          mul_comm]
      rw [hv' (k * l)] at h1
      exact smul_left_injective E hv0 h1
    have hone : χ.1 1 = 1 := by
      have h1 : ρE ((1 : K) : H) v = (1 : E) • v := by
        rw [Subgroup.coe_one, map_one, Module.End.one_apply, one_smul]
      rw [hv' 1] at h1
      exact smul_left_injective E hv0 h1
    have htriv : ∀ k : K, χ.1 k = 1 := by
      intro k
      obtain ⟨l, hl, hkl⟩ := exists_eq_conj_mul_inv_of_fixedPointFree (hBK b.2)
        (hfpf b b.2 hb1') k.2
      have hk : k = ⟨(b : H)⁻¹ * l * b, hconj b b.2 l hl⟩ * (⟨l, hl⟩ : K)⁻¹ :=
        Subtype.ext (by rw [hkl]; simp)
      rw [hk, hmul, hfix' ⟨l, hl⟩]
      rw [← hmul, mul_inv_cancel, hone]
    have hvK : v ∈ Representation.invariants (ρE.comp K.subtype) := by
      intro k
      change ρE k v = v
      rw [hv' k, htriv k, one_smul]
    rw [hdK, Submodule.mem_bot] at hvK
    exact hv0 hvK
  have htopI : ⨆ χ : I, Vχ χ.1 = ⊤ := by
    rw [eq_top_iff, ← htop]
    apply iSup_le
    intro χ
    by_cases hχ : Vχ χ = ⊥
    · rw [hχ]
      exact bot_le
    · exact le_iSup_of_le (⟨χ, hχ⟩ : I) le_rfl
  have hcount := finrank_invariants_mul_card_of_free (ρE.comp B.subtype) hfree
    (fun χ : I => Vχ χ.1) (hind.comp Subtype.val_injective) htopI
    (fun b χ v hv => hmaps b χ.1 v hv)
  rw [hdB, hW] at hcount
  exact hcount

end Main

section Frobenius

open Subgroup

variable {H : Type*} [Group H]

theorem frobenius_fixedPointFree {K A : Subgroup H}
    (hfrob : IsFrobeniusGroupWithKernelComplement K A) :
    ∀ b ∈ A, b ≠ 1 → ∀ k ∈ K, b * k = k * b → k = 1 := by
  intro b hb hb1 k hk hbk
  by_contra hk1
  have hkA : k ∉ A := fun hkA =>
    hk1 (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint hk hkA)
  have hbconj : b ∈ A.conjBy k := by
    refine ⟨b, hb, ?_⟩
    change k * b * k⁻¹ = b
    rw [← hbk, mul_assoc, mul_inv_cancel, mul_one]
  exact hb1 (Subgroup.disjoint_def.mp (hfrob.disjoint_conjBy k hkA) hb hbconj)

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem invariants_kernel_eq_bot_of_frobenius (ρ : Representation F H V)
    (hfaith : Function.Injective ρ) [ρ.IsIrreducible] {K A : Subgroup H}
    (hfrob : IsFrobeniusGroupWithKernelComplement K A) :
    Representation.invariants (ρ.comp K.subtype) = ⊥ := by
  have hKn : K.Normal := hfrob.normal
  let S : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp K.subtype)
      apply_mem_toSubmodule := by
        intro h v hv k
        change ρ k (ρ h v) = ρ h v
        have hk' : h⁻¹ * k * h ∈ K := by
          have := hKn.conj_mem k k.2 h⁻¹
          simpa using this
        have hv' : ρ (h⁻¹ * k * h) v = v := hv ⟨h⁻¹ * k * h, hk'⟩
        calc ρ k (ρ h v) = ρ h (ρ (h⁻¹ * k * h) v) := by
              rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
              congr 2
              group
          _ = ρ h v := by rw [hv'] }
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · exact congrArg Subrepresentation.toSubmodule h
  · exfalso
    apply hfrob.kernel_ne_bot
    rw [eq_bot_iff]
    intro k hk
    have hk1 : ρ k = 1 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ S.toSubmodule := by
        rw [h]
        exact Submodule.mem_top
      exact hv ⟨k, hk⟩
    exact (Subgroup.mem_bot).mpr (hfaith (hk1.trans (map_one ρ).symm))

theorem frobenius_finrank_invariants_mul_card [Finite H] [FiniteDimensional F V]
    (ρ : Representation F H V) (hfaith : Function.Injective ρ) [ρ.IsIrreducible]
    {K A : Subgroup H} (hfrob : IsFrobeniusGroupWithKernelComplement K A)
    (hK : IsMulCommutative K) (hchar : ¬ ringChar F ∣ Nat.card K) {B : Subgroup H}
    (hBA : B ≤ A) :
    Module.finrank F (Representation.invariants (ρ.comp B.subtype)) * Nat.card B =
      Module.finrank F V := by
  have hKn : K.Normal := hfrob.normal
  apply finrank_invariants_mul_card_of_fixedPointFree ρ hK
  · rw [Subgroup.normalizer_eq_top]
    exact le_top
  · intro b hb hb1 k hk hbk
    exact frobenius_fixedPointFree hfrob b (hBA hb) hb1 k hk hbk
  · exact hchar
  · exact invariants_kernel_eq_bot_of_frobenius ρ hfaith hfrob

theorem frobenius_complement_fixed_points_not_centralized [Finite H] [FiniteDimensional F V]
    (ρ : Representation F H V) (hfaith : Function.Injective ρ) [ρ.IsIrreducible]
    {K A : Subgroup H} (hfrob : IsFrobeniusGroupWithKernelComplement K A)
    (hK : IsMulCommutative K) (hchar : ¬ ringChar F ∣ Nat.card K) {t u : H} (ht : t ∈ A)
    (hu : u ∈ A) (hut : u ∉ zpowers t) :
    ∃ v : V, ρ t v = v ∧ ρ u v ≠ v := by
  set B₁ : Subgroup H := zpowers t with hB₁
  set B₂ : Subgroup H := closure {t, u} with hB₂
  have htB₂ : t ∈ B₂ := subset_closure (by simp)
  have huB₂ : u ∈ B₂ := subset_closure (by simp)
  have hB₁A : B₁ ≤ A := zpowers_le.mpr ht
  have hB₂A : B₂ ≤ A := by
    rw [hB₂, closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ht
    · exact hu
  have hB₁B₂ : B₁ ≤ B₂ := zpowers_le.mpr htB₂
  have h₁ := frobenius_finrank_invariants_mul_card ρ hfaith hfrob hK hchar hB₁A
  have h₂ := frobenius_finrank_invariants_mul_card ρ hfaith hfrob hK hchar hB₂A
  have hcard : Nat.card B₁ < Nat.card B₂ :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hB₁B₂ (fun h => hut (h ▸ huB₂)))
  have hV : 0 < Module.finrank F V := by
    apply Nat.pos_of_ne_zero
    intro h0
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp h0
    apply (IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ))
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  set f₁ := Module.finrank F (Representation.invariants (ρ.comp B₁.subtype))
  set f₂ := Module.finrank F (Representation.invariants (ρ.comp B₂.subtype))
  have hc₁ : 0 < Nat.card B₁ := Nat.card_pos
  have hlt : f₂ < f₁ := by
    have hf₂ : 0 < f₂ := by
      apply Nat.pos_of_ne_zero
      intro h
      rw [h, zero_mul] at h₂
      omega
    have : f₂ * Nat.card B₁ < f₁ * Nat.card B₁ := by
      calc f₂ * Nat.card B₁ < f₂ * Nat.card B₂ := Nat.mul_lt_mul_of_pos_left hcard hf₂
        _ = f₁ * Nat.card B₁ := by rw [h₂, h₁]
    exact Nat.lt_of_mul_lt_mul_right this
  have hnle : ¬ Representation.invariants (ρ.comp B₁.subtype) ≤
      Representation.invariants (ρ.comp B₂.subtype) := fun hle =>
    (Submodule.finrank_mono hle).not_gt hlt
  obtain ⟨v, hv₁, hv₂⟩ := Set.not_subset.mp hnle
  refine ⟨v, hv₁ ⟨t, mem_zpowers t⟩, fun hu' => hv₂ ?_⟩
  let stab : Subgroup H :=
    { carrier := {g | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        change ρ 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha => by
        change ρ a⁻¹ v = v
        have ha' : ρ a v = v := ha
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] }
  have hstab : B₂ ≤ stab := by
    rw [hB₂, closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hv₁ ⟨x, mem_zpowers x⟩
    · exact hu'
  intro b
  exact hstab b.2

end Frobenius

end CFSG.ABGLocalTools
