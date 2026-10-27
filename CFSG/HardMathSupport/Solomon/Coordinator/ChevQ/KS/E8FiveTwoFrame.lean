module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoUni
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxBridge
public import CFSG.HardMathSupport.Malle.SeitzCube.Landing
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Acts

variable {τ : Tag} {L : Type} [Field L]

@[expose] def ActsBy (ρ : SL(5, L) →* ModGL τ L) (ε : ModGL τ L) (M : GL (Fin 5) L) : Prop :=
  ∀ A, ε * ρ A * ε⁻¹ = ρ (conjSLn M A)

theorem conjSLn_mul' (M N : GL (Fin 5) L) (A : SL(5, L)) :
    conjSLn (M * N) A = conjSLn M (conjSLn N A) := by
  refine Subtype.ext ?_
  simp only [coe_conjSLn, Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

theorem conjSLn_one' (A : SL(5, L)) : conjSLn (1 : GL (Fin 5) L) A = A := by
  refine Subtype.ext ?_
  simp [coe_conjSLn]

variable {ρ : SL(5, L) →* ModGL τ L} {ε ε₁ ε₂ : ModGL τ L} {M M₁ M₂ : GL (Fin 5) L}

theorem ActsBy.mul (h₁ : ActsBy ρ ε₁ M₁) (h₂ : ActsBy ρ ε₂ M₂) :
    ActsBy ρ (ε₁ * ε₂) (M₁ * M₂) := fun A => by
  calc ε₁ * ε₂ * ρ A * (ε₁ * ε₂)⁻¹ = ε₁ * (ε₂ * ρ A * ε₂⁻¹) * ε₁⁻¹ := by group
    _ = ρ (conjSLn (M₁ * M₂) A) := by rw [h₂, h₁, conjSLn_mul']

theorem actsBy_one : ActsBy ρ 1 (1 : GL (Fin 5) L) := fun A => by
  rw [conjSLn_one']
  group

theorem ActsBy.pow (h : ActsBy ρ ε M) (n : ℕ) : ActsBy ρ (ε ^ n) (M ^ n) := by
  induction n with
  | zero => simpa using actsBy_one
  | succ n ih => simpa [pow_succ] using ih.mul h

theorem ActsBy.comm (h : ActsBy ρ ε M) {A : SL(5, L)}
    (hA : (A : Matrix (Fin 5) (Fin 5) L) * (M : Matrix (Fin 5) (Fin 5) L) =
      (M : Matrix (Fin 5) (Fin 5) L) * A) : ε * ρ A = ρ A * ε := by
  have h1 : conjSLn M A = A := by
    refine Subtype.ext ?_
    rw [coe_conjSLn, ← hA, Matrix.mul_assoc,
      show (M : Matrix (Fin 5) (Fin 5) L) * (↑M⁻¹ : Matrix (Fin 5) (Fin 5) L) = 1 from M.mul_inv,
      Matrix.mul_one]
  have := h A
  rw [h1] at this
  calc ε * ρ A = ε * ρ A * ε⁻¹ * ε := by group
    _ = ρ A * ε := by rw [this]

end Acts

section Frame


theorem frame_le_hyperClosure {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hq5 : 5 ∣ ℓ ^ f + 1)
    {w : WeylGroup Tag.E8} (D : LangLevi Tag.E8 K w) {S : Set (Fin Tag.E8.rank → ℤ)}
    (ρ : SL(5, D.L) →* ModGL Tag.E8 D.L) (hρinj : Function.Injective ρ)
    (hρS : ρ.range = rootSpan Tag.E8 D.L S)
    (Φ : SL(5, D.L) ≃* SL(5, D.L)) (π : Equiv.Perm (Fin 5)) (b : Fin 5 → Fin 5 → D.Lˣ)
    (hΦ : ∀ (i j : Fin 5) (hij : i ≠ j) (t : D.L),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(5, D.L)) :
        Matrix (Fin 5) (Fin 5) D.L) = 1 + Matrix.single (π j) (π i) ((b i j : D.L) * t ^ ℓ ^ f))
    (hΦρ : ∀ X, D.nW * D.frobGL (ρ X) * D.nW⁻¹ = ρ (Φ X))
    (E : Subgroup (adjointGroup Tag.E8 K)) (hEc : Nat.card E = 5 ^ 3)
    (z e₀ e₁ : adjointGroup Tag.E8 K) (εz ε₀ ε₁ : ModGL Tag.E8 D.L)
    (hz : z ∈ E) (he₀ : e₀ ∈ E) (he₁ : e₁ ∈ E)
    (hιz : baseChangeGL (algebraMap K D.L) (z : ModGL Tag.E8 K) = D.g * εz * D.g⁻¹)
    (hι₀ : baseChangeGL (algebraMap K D.L) (e₀ : ModGL Tag.E8 K) = D.g * ε₀ * D.g⁻¹)
    (hι₁ : baseChangeGL (algebraMap K D.L) (e₁ : ModGL Tag.E8 K) = D.g * ε₁ * D.g⁻¹)
    (hεz : ∀ A, εz * ρ A = ρ A * εz)
    (M₀ M₁ : GL (Fin 5) D.L) (hε₀ : ActsBy ρ ε₀ M₀) (hε₁ : ActsBy ρ ε₁ M₁)
    {ζ : D.L} (hζ : IsPrimitiveRoot ζ 5)
    (hcomm : (M₀ : Matrix (Fin 5) (Fin 5) D.L) * M₁ = ζ • ((M₁ : Matrix (Fin 5) (Fin 5) D.L) * M₀))
    {c₀ c₁ : D.L} (h₀ : ((M₀ ^ 5 : GL (Fin 5) D.L) : Matrix (Fin 5) (Fin 5) D.L) = c₀ • 1)
    (h₁ : ((M₁ ^ 5 : GL (Fin 5) D.L) : Matrix (Fin 5) (Fin 5) D.L) = c₁ • 1)
    (hidx : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) →
      Subgroup.closure ({z, e₀ ^ a * e₁ ^ b} : Set (adjointGroup Tag.E8 K)) ≤ E ∧
      (Subgroup.closure ({z, e₀ ^ a * e₁ ^ b} : Set (adjointGroup Tag.E8 K))).relIndex E = 5) :
    D.frame S ≤ (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E).map
      (adjointGroup Tag.E8 K).subtype := by
  classical
  set ι := baseChangeGL (algebraMap K D.L) with hι
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hfixε : ∀ (e : adjointGroup Tag.E8 K) (ε : ModGL Tag.E8 D.L),
      ι (e : ModGL Tag.E8 K) = D.g * ε * D.g⁻¹ → D.nW * D.frobGL ε * D.nW⁻¹ = ε := by
    intro e ε he
    have h1 := D.frobGL_baseChangeGL (e : ModGL Tag.E8 K)
    rw [← hι, he, map_mul, map_mul, map_inv, D.frobGL_g] at h1
    have h2 : D.g * (D.nW * D.frobGL ε * D.nW⁻¹) * D.g⁻¹ = D.g * ε * D.g⁻¹ := by
      calc D.g * (D.nW * D.frobGL ε * D.nW⁻¹) * D.g⁻¹
          = D.g * D.nW * D.frobGL ε * (D.g * D.nW)⁻¹ := by group
        _ = D.g * ε * D.g⁻¹ := h1
    exact mul_left_cancel (mul_right_cancel h2)
  have hcΦ : ∀ (ε : ModGL Tag.E8 D.L) (M : GL (Fin 5) D.L),
      D.nW * D.frobGL ε * D.nW⁻¹ = ε → ActsBy ρ ε M →
      ∀ X : SL(5, D.L), Φ (conjSLn M X) = conjSLn M (Φ X) := by
    intro ε M hεF hε X
    apply hρinj
    calc ρ (Φ (conjSLn M X)) = D.nW * D.frobGL (ρ (conjSLn M X)) * D.nW⁻¹ := (hΦρ _).symm
      _ = D.nW * D.frobGL (ε * ρ X * ε⁻¹) * D.nW⁻¹ := by rw [← hε X]
      _ = (D.nW * D.frobGL ε * D.nW⁻¹) * (D.nW * D.frobGL (ρ X) * D.nW⁻¹) *
          (D.nW * D.frobGL ε * D.nW⁻¹)⁻¹ := by simp only [map_mul, map_inv]; group
      _ = ε * ρ (Φ X) * ε⁻¹ := by rw [hεF, hΦρ]
      _ = ρ (conjSLn M (Φ X)) := hε _
  have hc₀ := hcΦ ε₀ M₀ (hfixε e₀ ε₀ hι₀) hε₀
  have hc₁ := hcΦ ε₁ M₁ (hfixε e₁ ε₁ hι₁) hε₁
  set Hm : Subgroup (ModGL Tag.E8 K) :=
    (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E).map
      (adjointGroup Tag.E8 K).subtype with hHm
  set J : Subgroup (ModGL Tag.E8 D.L) :=
    ((Hm ⊓ D.frame S).map ι).map (MulAut.conj D.g⁻¹).toMonoidHom with hJ
  set H₀ : Subgroup SL(5, D.L) := J.comap ρ with hH₀
  have hmemH₀ : ∀ A, A ∈ H₀ ↔
      ∃ x, x ∈ Hm ∧ x ∈ D.frame S ∧ D.g⁻¹ * ι x * D.g = ρ A := by
    intro A
    simp only [hH₀, Subgroup.mem_comap, hJ, Subgroup.mem_map, Subgroup.mem_inf,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨y, ⟨x, ⟨hxH, hxF⟩, rfl⟩, hy⟩
      exact ⟨x, hxH, hxF, hy⟩
    · rintro ⟨x, hxH, hxF, hx⟩
      exact ⟨ι x, ⟨x, ⟨hxH, hxF⟩, rfl⟩, hx⟩
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  have hH : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) → ∀ X ∈ fixSubgroup Φ,
      (X : Matrix (Fin 5) (Fin 5) D.L) * ((M₀ ^ a * M₁ ^ b : GL (Fin 5) D.L) :
        Matrix (Fin 5) (Fin 5) D.L) = ((M₀ ^ a * M₁ ^ b : GL (Fin 5) D.L) :
        Matrix (Fin 5) (Fin 5) D.L) * X → X ∈ H₀ := by
    intro a b hab X hX hXM
    have hρX : ρ X ∈ D.fixedRoot S := by
      refine ⟨hρS ▸ ⟨X, rfl⟩, ?_⟩
      show D.nW * D.frobGL (ρ X) * D.nW⁻¹ = ρ X
      rw [hΦρ, (mem_fixSubgroup Φ).1 hX]
    have hadj := D.conj_mem_adjointGroup hρX
    have hF := D.frobGL_conj_fixedRoot hρX
    obtain ⟨x', hx'G, hx'⟩ := Subgroup.mem_map.1
      (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E8
        (K := K) (L := D.L) D.Fr D.hFr hadj hF)
    have hx'conj : D.g⁻¹ * ι x' * D.g = ρ X := by
      rw [hx']
      group
    have hx'frame : x' ∈ D.frame S :=
      (D.frame_mem_iff S x').2 ⟨hx'G, by rw [hx'conj]; exact hρS ▸ ⟨X, rfl⟩⟩
    set k : adjointGroup Tag.E8 K := ⟨x', hx'G⟩ with hk
    have hcommε : ∀ (ε : ModGL Tag.E8 D.L), (∀ A, ε * ρ A = ρ A * ε) →
        ε * (D.g⁻¹ * ι x' * D.g) = (D.g⁻¹ * ι x' * D.g) * ε := fun ε hε => by
      rw [hx'conj]
      exact hε X
    have hzk : z * k = k * z := by
      refine Subtype.ext (hιinj ?_)
      show ι (z * x') = ι (x' * z)
      rw [map_mul, map_mul, hιz, hx']
      calc D.g * εz * D.g⁻¹ * (D.g * ρ X * D.g⁻¹) = D.g * (εz * ρ X) * D.g⁻¹ := by group
        _ = D.g * (ρ X * εz) * D.g⁻¹ := by rw [hεz X]
        _ = D.g * ρ X * D.g⁻¹ * (D.g * εz * D.g⁻¹) := by group
    have hek : (e₀ ^ a * e₁ ^ b) * k = k * (e₀ ^ a * e₁ ^ b) := by
      refine Subtype.ext (hιinj ?_)
      show ι (((e₀ ^ a * e₁ ^ b : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) * x') =
        ι (x' * ((e₀ ^ a * e₁ ^ b : adjointGroup Tag.E8 K) : ModGL Tag.E8 K))
      have hι' : ι ((e₀ ^ a * e₁ ^ b : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
          D.g * (ε₀ ^ a * ε₁ ^ b) * D.g⁻¹ := by
        simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, map_mul, map_pow, hι₀, hι₁, conj_pow]
        group
      rw [map_mul, map_mul, hι', hx']
      have hact : ActsBy ρ (ε₀ ^ a * ε₁ ^ b) (M₀ ^ a * M₁ ^ b) := (hε₀.pow a).mul (hε₁.pow b)
      have hcm := hact.comm hXM
      calc D.g * (ε₀ ^ a * ε₁ ^ b) * D.g⁻¹ * (D.g * ρ X * D.g⁻¹)
          = D.g * ((ε₀ ^ a * ε₁ ^ b) * ρ X) * D.g⁻¹ := by group
        _ = D.g * (ρ X * (ε₀ ^ a * ε₁ ^ b)) * D.g⁻¹ := by rw [hcm]
        _ = D.g * ρ X * D.g⁻¹ * (D.g * (ε₀ ^ a * ε₁ ^ b) * D.g⁻¹) := by group
    have hHk : x' ∈ Hm := by
      refine Subgroup.mem_map.2 ⟨k, ?_, rfl⟩
      obtain ⟨hle, hid⟩ := hidx a b hab
      exact mem_hyperClosure_pair hle hid hzk hek
    exact (hmemH₀ X).2 ⟨x', hHk, hx'frame, hx'conj⟩
  have hmain := fixSubgroup_le_of_heis_lines hℓ hf hK hq5 π Φ b hΦ M₀ M₁ hc₀ hc₁ hζ hcomm h₀ h₁
    H₀ hH
  intro x hx
  obtain ⟨hxG, hxS⟩ := (D.frame_mem_iff S x).1 hx
  obtain ⟨A, hA⟩ : ∃ A, ρ A = D.g⁻¹ * ι x * D.g := by
    have : D.g⁻¹ * ι x * D.g ∈ ρ.range := hρS ▸ hxS
    obtain ⟨A, hA⟩ := this
    exact ⟨A, hA⟩
  have hAfix : A ∈ fixSubgroup Φ := by
    have h1 := (D.conj_mem_fixedRoot hx).2
    show Φ A = A
    apply hρinj
    rw [← hΦρ, hA]
    exact h1
  obtain ⟨x'', hx''H, -, hx''⟩ := (hmemH₀ A).1 (hmain hAfix)
  have : x'' = x := by
    apply hιinj
    have h2 := hx''.trans hA
    have h3 := congrArg (fun y => D.g * y * D.g⁻¹) h2
    simpa [mul_assoc] using h3
  rw [this] at hx''H
  exact hx''H

end Frame

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
