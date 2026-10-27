module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open scoped Matrix

namespace P614K292

section Frames

variable {K : Type} [Field K]

@[expose] def yFrame (y : GL (Fin 3) K) (v : Fin 3 → K) (i : Fin 3) : Fin 3 → K :=
  ((y : Matrix (Fin 3) (Fin 3) K) ^ (i : ℕ)) *ᵥ v

@[expose] def frameGroupOf (n : ℕ) (b : Fin 3 → Fin 3 → K) : Subgroup (GL (Fin 3) K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
    ∀ i, ∃ c : K, c ^ n = 1 ∧ (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i}
  mul_mem' := by
    rintro g h ⟨hg1, hg⟩ ⟨hh1, hh⟩
    refine ⟨by rw [Units.val_mul, Matrix.det_mul, hg1, hh1, mul_one], fun i => ?_⟩
    obtain ⟨c, hc, hgc⟩ := hg i
    obtain ⟨d, hd, hhd⟩ := hh i
    refine ⟨c * d, by rw [mul_pow, hc, hd, mul_one], ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hhd, Matrix.mulVec_smul, hgc, smul_smul,
      mul_comm d c]
  one_mem' := ⟨by simp, fun i => ⟨1, one_pow n, by simp⟩⟩
  inv_mem' := by
    rintro g ⟨hg1, hg⟩
    refine ⟨?_, fun i => ?_⟩
    · have h := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K).det)
        (inv_mul_cancel g)
      simp only [Units.val_mul, Matrix.det_mul, hg1, mul_one, Units.val_one,
        Matrix.det_one] at h
      exact h
    · obtain ⟨c, hc, hgc⟩ := hg i
      refine ⟨c⁻¹, by rw [inv_pow, hc, inv_one], ?_⟩
      have hb : b i = c • (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) := by
        rw [← Matrix.mulVec_smul, ← hgc, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
      by_cases hc0 : c = 0
      · rw [hc0, zero_smul] at hb
        rw [hb, Matrix.mulVec_zero, smul_zero]
      · conv_rhs => rw [hb]
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

@[expose] def twoFrame (y : GL (Fin 3) K) (v : Fin 3 → K) : Subgroup (GL (Fin 3) K) :=
  frameGroupOf 2 (yFrame y v)

@[expose] def threeFrame (y : GL (Fin 3) K) (v : Fin 3 → K) : Subgroup (GL (Fin 3) K) :=
  frameGroupOf 3 (yFrame y v)

@[expose] def YFrameOrth (q : ℕ) (y : GL (Fin 3) K) (v : Fin 3 → K) : Prop :=
  ∀ i j : Fin 3, i ≠ j → ∑ k, yFrame y v i k ^ q * yFrame y v j k = 0

@[expose] def frameCands (π : Bool) (q : ℕ) (y : GL (Fin 3) K) :
    Set (Subgroup (GL (Fin 3) K)) :=
  {E | E ≤ slPi π 3 q K ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
    StatedScalars (Fin 3) K ⊓ slPi π 3 q K ≤ E ∧ ∀ e ∈ E, y * e * y⁻¹ ∈ E}

theorem yFrame_eq (y : GL (Fin 3) K) (v : Fin 3 → K) :
    yFrame y v = ![v, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v,
      ((y : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v] := by
  funext i
  fin_cases i <;> simp [yFrame]

theorem mem_frameGroupOf {n : ℕ} {b : Fin 3 → Fin 3 → K} {g : GL (Fin 3) K} :
    g ∈ frameGroupOf n b ↔ (g : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      ∀ i, ∃ c : K, c ^ n = 1 ∧ (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i :=
  Iff.rfl

end Frames

@[expose] def threeFrameIn {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type}
    [Field K] (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (y : GL (Fin 3) K) (v : Fin 3 → K) :
    Subgroup X :=
  ((threeFrame y v).subgroupOf (slPi π 3 (p ^ f) K)).map (L.subtype.comp ν)

theorem mem_threeFrameIn {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type}
    [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {y : GL (Fin 3) K} {v : Fin 3 → K} {g : X} :
    g ∈ threeFrameIn ν y v ↔ ∃ s : ↥(slPi π 3 (p ^ f) K),
      (s : GL (Fin 3) K) ∈ threeFrame y v ∧ ((ν s : ↥L) : X) = g :=
  Iff.rfl

structure LinUniCfgThree {X : Type} [Group X] [Finite X] (L : Subgroup X) (x : X)
    (Px B : Subgroup X) : Prop where
  setup : KFactProofs.T29.T29Setup X L x
  perf : ∀ (N : Subgroup X) [N.Normal], IsPGroup 3 (X ⧸ N) → N = ⊤
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 Px (centralizer ({x} : Set X))
  le : B ≤ Px
  elem : IsElemAbelian 3 B
  omega : ∀ q ∈ Px, q ^ 3 = 1 → q ∈ B

structure ShapeThree {X : Type} [Group X] [Finite X] (L : Subgroup X) (x : X) (B : Subgroup X)
    (π : Bool) (p f : ℕ) (K : Type) [Field K] (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L)
    (y : GL (Fin 3) K) : Prop where
  model : LModel L π p f K ν
  inj : Function.Injective ν
  lift : IsLiftAt ν x y
  typeThree : IsTypeThree π (p ^ f) K y
  cent : centralizer (L : Set X) = CFSG.pCore 3 X
  plane : B = zpowers x ⊔ (center ↥L).map L.subtype
  sc : CFSG.LocalAnalysis.GLTheoremB.IsSCp 3 ⊤ B
  two_mem : ∀ t : X, IsPGroup 2 (zpowers t) → ∀ c : GL (Fin 3) K, IsLiftAt ν t c → t ∈ L
  comm : ∀ g h : X, ∃ c : GL (Fin 3) K, IsLiftAt ν (g * h * g⁻¹ * h⁻¹) c

end P614K292

open P614K292

@[expose] def KD292Shape3 : Prop :=
  KFactProofs.T29.GL83I291Three →
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X) (Px B : Subgroup X),
    LinUniCfgThree L x Px B →
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L)
      (y : GL (Fin 3) K), ShapeThree L x B π p f K ν y

@[expose] def KD292TwoFrame3 : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K),
    PiField π p f K → ModThree π (p ^ f) → 2 < p ^ f → IsTypeThree π (p ^ f) K y →
    ∀ R : Subgroup (GL (Fin 3) K), R ≤ slPi π 3 (p ^ f) K → IsPGroup 2 R → R ≠ ⊥ →
      R = Subgroup.closure {r | r ∈ R ∧ r ^ 2 = 1} → (∀ r ∈ R, y * r * y⁻¹ ∈ R) →
      (2 : K) ≠ 0 ∧ ∃ v : Fin 3 → K, v ≠ 0 ∧ R = twoFrame y v ∧
        (π = false → YFrameOrth (p ^ f) y v)

@[expose] def KD292ThreeFrameLin3 : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K),
    PiField true p f K → ModThree true (p ^ f) → 2 < p ^ f → IsTypeThree true (p ^ f) K y →
    (∀ E ∈ frameCands true (p ^ f) y, ∃ v : Fin 3 → K, v ≠ 0 ∧ E = threeFrame y v) ∧
      Odd (Nat.card ↥(frameCands true (p ^ f) y))

@[expose] def KD292UniOuter3 : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K),
    PiField false p f K → ModThree false (p ^ f) → 2 < p ^ f → IsTypeThree false (p ^ f) K y →
    ∀ α : MulAut ↥(slPi false 3 (p ^ f) K), (∃ n : ℕ, α ^ (2 ^ n) = 1) →
      (∀ s t : ↥(slPi false 3 (p ^ f) K), (t : GL (Fin 3) K) = y * s * y⁻¹ →
        ((α t : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) = y * α s * y⁻¹) →
      ∃ g ∈ glPi false 3 (p ^ f) K, ∀ s : ↥(slPi false 3 (p ^ f) K),
        ((α s : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) = g * s * g⁻¹

@[expose] def KD292ThreeFrameNorm3 : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K),
    PiField π p f K → ModThree π (p ^ f) → 2 < p ^ f → IsTypeThree π (p ^ f) K y →
    ∀ v : Fin 3 → K, v ≠ 0 → (π = false → YFrameOrth (p ^ f) y v) →
      threeFrame y v ∈ frameCands π (p ^ f) y ∧
      (∀ E : Subgroup (GL (Fin 3) K), E ≤ slPi π 3 (p ^ f) K → IsElemAbelian 3 E →
        Nat.card E = 9 → StatedScalars (Fin 3) K ⊓ slPi π 3 (p ^ f) K ≤ E →
        ∃ a ∈ slPi π 3 (p ^ f) K, E.map (MulAut.conj a).toMonoidHom = threeFrame y v) ∧
      ¬ 3 ∣ (normalizer (threeFrame y v : Set (GL (Fin 3) K))).relIndex
        (slPi π 3 (p ^ f) K) ∧
      Group.IsSolvable
        ↥(slPi π 3 (p ^ f) K ⊓ normalizer (threeFrame y v : Set (GL (Fin 3) K))) ∧
      ((2 : K) ≠ 0 → ∀ g : GL (Fin 3) K, g ∈ threeFrame y v ↔
        g ∈ slPi π 3 (p ^ f) K ∧ (∀ r ∈ twoFrame y v, g * r = r * g) ∧ g ^ 3 = 1)

@[expose] def KD292FrameNormX3 : Prop :=
  KD292ThreeFrameNorm3 →
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X) (Px B : Subgroup X) (π : Bool)
    (p f : ℕ) (K : Type) [Field K] (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (y : GL (Fin 3) K),
    LinUniCfgThree L x Px B → ShapeThree L x B π p f K ν y →
    ∀ v : Fin 3 → K, v ≠ 0 → (π = false → YFrameOrth (p ^ f) y v) →
      B ≤ normalizer (threeFrameIn ν y v : Set X) ∧
      Group.IsSolvable ↥(normalizer (threeFrameIn ν y v : Set X)) ∧
      ∃ Q : Sylow 3 X, (Q : Subgroup X) ≤ normalizer (threeFrameIn ν y v : Set X)

@[expose] def KD292CaseA3 : Prop :=
  KD292ThreeFrameLin3 → KD292UniOuter3 →
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X) (Px B : Subgroup X) (π : Bool)
    (p f : ℕ) (K : Type) [Field K] (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (y : GL (Fin 3) K),
    LinUniCfgThree L x Px B → ShapeThree L x B π p f K ν y →
    ∀ T : Subgroup X, IsPGroup 2 T → x ∈ normalizer (T : Set X) → T ⊓ L = ⊥ →
      (π = true → ∃ v : Fin 3 → K, v ≠ 0 ∧ T ≤ normalizer (threeFrameIn ν y v : Set X)) ∧
      (π = false → T = ⊥)

@[expose] def KD292CaseB3 : Prop :=
  KD292TwoFrame3 → KD292ThreeFrameNorm3 →
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X) (Px B : Subgroup X) (π : Bool)
    (p f : ℕ) (K : Type) [Field K] (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (y : GL (Fin 3) K),
    LinUniCfgThree L x Px B → ShapeThree L x B π p f K ν y →
    ∀ T : Subgroup X, IsPGroup 2 T → x ∈ normalizer (T : Set X) → T ⊓ L ≠ ⊥ →
      ∃ v : Fin 3 → K, v ≠ 0 ∧ (π = false → YFrameOrth (p ^ f) y v) ∧
        T ≤ normalizer (threeFrameIn ν y v : Set X)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
