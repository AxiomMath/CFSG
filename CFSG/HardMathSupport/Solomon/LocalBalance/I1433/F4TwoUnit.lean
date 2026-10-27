module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quasi
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open scoped commutatorElement MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false


section Pinning

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem exists_unitary_pinning {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → S.ρ (σ a b) = σ (π b) (π a)) (σQ : L ≃+* L)
    (hσc : ∀ c, σQ c = c ^ S.D.q) :
    ∃ B : SL(ν, L), ∀ X : SL(ν, L),
      ψ B * S.D.step (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
  classical
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      S.D.step (pinnedX τ L (σ a b) c) =
        pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hμ, hπ a b hab, hσc]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ S.D.q * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      S.D.step (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => S.D.step (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  refine ⟨B, ?_⟩
  have h : (MulAut.conj (ψ B)).toMonoidHom.comp (S.D.step.comp ψ) =
      ψ.comp (stdUnitary σQ.toRingHom) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
    rintro _ ⟨a, b, hab, t, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
      stdUnitary_transvection]
    congr 2
    rw [hd a b hab]
    simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have h0 : (d a : L) ≠ 0 := Units.ne_zero _
    have h0' : (d b : L) ≠ 0 := Units.ne_zero _
    field_simp
  intro X
  have := DFunLike.congr_fun h X
  simpa [MulAut.conj_apply] using this

end Pinning

section CommonLang

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
  {a : Fin Tag.F4.rank → Lˣ}

include S in
theorem commute_of_mem_torus_sup_kernel {z : ModGL Tag.F4 L}
    (hz : z ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (kernelRoots (rootCharHom a))) :
    rootDiagUnit Tag.F4 a * z = z * rootDiagUnit Tag.F4 a := by
  have hT : torusGroup Tag.F4 L ≤ Subgroup.centralizer {rootDiagUnit Tag.F4 a} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hR : rootSpan Tag.F4 L (kernelRoots (rootCharHom a)) ≤
      Subgroup.centralizer {rootDiagUnit Tag.F4 a} :=
    rootSpan_le_centralizer a (fun γ hγ => hγ)
  exact (Subgroup.mem_centralizer_singleton_iff.1 ((sup_le hT hR) hz)).symm

theorem exists_common_lang (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    {ψ₁ ψ₂ : SL(3, L) →* ModGL Tag.F4 L} (B₁ B₂ : SL(3, L)) (σQ : L ≃+* L)
    (h₁ : ∀ X, ψ₁ B₁ * S.D.step (ψ₁ X) * (ψ₁ B₁)⁻¹ = ψ₁ (stdUnitary σQ.toRingHom X))
    (h₂ : ∀ X, ψ₂ B₂ * S.D.step (ψ₂ X) * (ψ₂ B₂)⁻¹ = ψ₂ (stdUnitary σQ.toRingHom X))
    (hcomm : ∀ X Y, ψ₁ X * ψ₂ Y = ψ₂ Y * ψ₁ X)
    (hy₁ : ψ₁ B₁ * ψ₂ B₂ ∈ rootSpan Tag.F4 L (kernelRoots (rootCharHom a))) :
    ∃ z : ModGL Tag.F4 L,
      z ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (kernelRoots (rootCharHom a)) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL Tag.F4 L,
        g ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) j)) ∧
      (∀ X, S.D.step (z * ψ₁ X * z⁻¹) = z * ψ₁ (stdUnitary σQ.toRingHom X) * z⁻¹) ∧
      (∀ X, S.D.step (z * ψ₂ X * z⁻¹) = z * ψ₂ (stdUnitary σQ.toRingHom X) * z⁻¹) := by
  classical
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S (χ := rootCharHom a) (s := 1)
    one_pos (fun γ hγ => by simpa using outer_rho_mem_kernelRoots S hT hγ)
    (Subgroup.mem_sup_right hy₁)
  have hz' : S.D.step z = z * (ψ₁ B₁ * ψ₂ B₂) := by
    have := hz
    rwa [iterHom_eq_iterate, Function.iterate_one] at this
  have hcom1 : ∀ Y, ψ₁ B₁ * ψ₂ Y * (ψ₁ B₁)⁻¹ = ψ₂ Y := fun Y => by
    rw [hcomm B₁ Y, mul_inv_cancel_right]
  have hcom2 : ∀ Y, ψ₂ B₂ * ψ₁ Y * (ψ₂ B₂)⁻¹ = ψ₁ Y := fun Y => by
    rw [← hcomm Y B₂, mul_inv_cancel_right]
  refine ⟨z, hzZ, mem_componentRootSpan_iff_conj_of_mem hzZ, fun X => ?_, fun X => ?_⟩
  · have e1 : S.D.step (ψ₁ X) = (ψ₁ B₁)⁻¹ * ψ₁ (stdUnitary σQ.toRingHom X) * ψ₁ B₁ := by
      rw [← h₁ X]
      group
    obtain ⟨Y, hY⟩ : ∃ Y, S.D.step (ψ₁ X) = ψ₁ Y :=
      ⟨B₁⁻¹ * stdUnitary σQ.toRingHom X * B₁, by rw [e1, map_mul, map_mul, map_inv]⟩
    rw [map_mul, map_mul, map_inv, hz', hY]
    calc z * (ψ₁ B₁ * ψ₂ B₂) * ψ₁ Y * (z * (ψ₁ B₁ * ψ₂ B₂))⁻¹
        = z * (ψ₁ B₁ * (ψ₂ B₂ * ψ₁ Y * (ψ₂ B₂)⁻¹) * (ψ₁ B₁)⁻¹) * z⁻¹ := by group
      _ = z * (ψ₁ B₁ * ψ₁ Y * (ψ₁ B₁)⁻¹) * z⁻¹ := by rw [hcom2]
      _ = z * ψ₁ (stdUnitary σQ.toRingHom X) * z⁻¹ := by rw [← hY, h₁]
  · rw [map_mul, map_mul, map_inv, hz']
    calc z * (ψ₁ B₁ * ψ₂ B₂) * S.D.step (ψ₂ X) * (z * (ψ₁ B₁ * ψ₂ B₂))⁻¹
        = z * (ψ₁ B₁ * (ψ₂ B₂ * S.D.step (ψ₂ X) * (ψ₂ B₂)⁻¹) * (ψ₁ B₁)⁻¹) * z⁻¹ := by group
      _ = z * (ψ₁ B₁ * ψ₂ (stdUnitary σQ.toRingHom X) * (ψ₁ B₁)⁻¹) * z⁻¹ := by rw [h₂]
      _ = z * ψ₂ (stdUnitary σQ.toRingHom X) * z⁻¹ := by rw [hcom1]

end CommonLang

section Member

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
  {a : Fin Tag.F4.rank → Lˣ}

theorem conj_mem_rationalComponent (i : KernelComponent (rootCharHom a))
    {ψ : SL(3, L) →* ModGL Tag.F4 L} {σ : Fin 3 → Fin 3 → V4} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) {z : ModGL Tag.F4 L}
    (hz : ∀ g : ModGL Tag.F4 L, g ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) →
      z * g * z⁻¹ ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i))
    {σQ : L ≃+* L}
    (hconj : ∀ X, S.D.step (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹)
    (hperf : Group.IsPerfect (fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)))
    {X : SL(3, L)} (hX : stdUnitary σQ.toRingHom X = X) :
    z * ψ X * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  set C := fixSubgroup (stdUnitaryEquiv (ν := 3) σQ) with hC
  have hCmem : ∀ Y : SL(3, L), Y ∈ C ↔ stdUnitary σQ.toRingHom Y = Y := fun Y => by
    rw [hC, mem_fixSubgroup, stdUnitaryEquiv_apply]
  let θ : C →* ModGL Tag.F4 L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ c * z⁻¹ := fun c => rfl
  have hψS : ∀ Y : SL(3, L), ψ Y ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) :=
    fun Y => by
      rw [hΨ, ← hψ.range]
      exact ⟨Y, rfl⟩
  have hθS : ∀ c : C, θ c ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) := fun c => by
    rw [hθ]
    exact hz _ (hψS c)
  have hθfix : ∀ c : C, S.D.step (θ c) = θ c := fun c => by
    rw [hθ, hconj, (hCmem c).1 c.2]
  have hθM : ∀ c : C, θ c ∈ S.D.model := fun c =>
    ⟨rootSpan_le_adjointGroup L _ (hθS c), hθfix c⟩
  have hθΓ : ∀ c : C, θ c ∈ S.Γ := map_mem_commutator_of_perfect hperf θ S.D.model hθM
  have hsub : componentRoots (rootCharHom a) i ⊆ rationalRoots S.ρ (rootCharHom a) i :=
    fun γ hγ => ⟨0, γ, hγ, rfl⟩
  have hθR : ∀ c : C, θ c ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := fun c =>
    Subgroup.mem_inf.2 ⟨rootSpan_mono hsub (hθS c), hθΓ c⟩
  exact map_mem_commutator_of_perfect hperf θ (rationalSpan S.ρ S.Γ (rootCharHom a) i) hθR
    (⟨X, (hCmem X).2 hX⟩ : C)

end Member

section Comp

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} {a : Fin Tag.F4.rank → Lˣ}

theorem glaPComponent_of_rational {C : Type} [Group C] [Finite C] (S : LangSetup Tag.F4 L p₀)
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (ι : C →* ModGL Tag.F4 L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) {x : C}
    (hx : ι x = rootDiagUnit Tag.F4 a) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (h3 : 3 ∣ Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set C))
      ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) := by
  classical
  set d := rootDiagUnit Tag.F4 a with hd
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
  have hcompR : IsComponentOf R (S.Γ ⊓ Subgroup.centralizer {d}) :=
    ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hq⟩
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun y hy => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hy).1
  have hRrange : R ≤ ι.range := hle.trans hCdrange
  have hcomapC : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = Subgroup.centralizer {x} := by
    ext c
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply hι
      rw [map_mul, map_mul, hx]
      exact h
    · intro h
      refine ⟨?_, ?_⟩
      · have : ι c ∈ ι.range := ⟨c, rfl⟩
        rwa [hrange] at this
      · rw [← hx, ← map_mul, ← map_mul, h]
  have hcomp := isComponentOf_comap_of_injective ι hι hRrange hCdrange hcompR
  rw [hcomapC] at hcomp
  obtain ⟨hle', hsn', hq'⟩ := hcomp
  have hmap : (R.comap ι).map ι = R := Subgroup.map_comap_eq_self hRrange
  have e : ↥(R.comap ι) ≃* ↥R :=
    (Subgroup.equivMapOfInjective (R.comap ι) ι hι).trans (MulEquiv.subgroupCongr hmap)
  have h3' : 3 ∣ Nat.card ↥(R.comap ι) := by
    rw [Nat.card_congr e.toEquiv]
    exact h3
  exact i253_glaPComponent_of_subnormal hle' hsn' hq' h3'

end Comp

section Diag

variable {L : Type} [Field L]

theorem stdUnitary_diagSL3_eq_self (σ : L →+* L) (l : Fin 3 → Lˣ) (hl : l 0 * l 1 * l 2 = 1)
    (hσ : ∀ i, σ (l i : L) * (l i : L) = 1) :
    stdUnitary σ (diagSL3 l hl) = diagSL3 l hl := by
  apply Subtype.ext
  rw [coe_stdUnitary, coe_diagSL3, Matrix.diagonal_map (map_zero σ)]
  have hinv : (Matrix.diagonal fun i => σ (l i : L))⁻¹ = Matrix.diagonal fun i => (l i : L) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => σ (l i : L) * (l i : L)) = fun _ => 1 := funext hσ
    rw [this, Matrix.diagonal_one]
  rw [hinv, Matrix.diagonal_transpose]

end Diag

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
