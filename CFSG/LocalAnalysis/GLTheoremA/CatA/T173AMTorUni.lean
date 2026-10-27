module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMTorRank
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel
open scoped commutatorElement MatrixGroups Matrix

private theorem unitaryFieldData_two_of_card {n : ℕ} {F : Type} [Field F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) : UnitaryFieldData 2 n F where
  prime := Nat.prime_two
  one_le := hn
  card := by rw [hF, pow_two, ← pow_add, two_mul]

private theorem gu_bar_transpose_mul {n d : ℕ} {F : Type} [Field F]
    (hUF : UnitaryFieldData 2 n F) {A : GL (Fin d) F}
    (hA : A ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) :
    ∃ μ : F, μ ≠ 0 ∧ Matrix.transpose
      ((A : Matrix (Fin d) (Fin d) F).map hUF.bar) * (A : Matrix (Fin d) (Fin d) F) =
      μ • (1 : Matrix (Fin d) (Fin d) F) := by
  obtain ⟨μ, hμ0, _hμq, hμ⟩ := hA
  refine ⟨μ, hμ0, ?_⟩
  rw [← CFSG.StandardType.TableBUD.map_pow_eq_map_bar hUF]
  exact hμ

private theorem gramForm_one_gu_zero_iff {n d : ℕ} {F : Type} [Field F]
    (hUF : UnitaryFieldData 2 n F) {A : GL (Fin d) F}
    (hA : A ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) (u v : Fin d → F) :
    gramForm hUF 1 ((A : Matrix (Fin d) (Fin d) F) *ᵥ u)
      ((A : Matrix (Fin d) (Fin d) F) *ᵥ v) = 0 ↔ gramForm hUF 1 u v = 0 := by
  obtain ⟨μ, hμ0, hμ⟩ := gu_bar_transpose_mul hUF hA
  rw [gramForm_mulVec, Matrix.mul_one, hμ, gramForm_apply, gramForm_apply,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero]
  simp [hμ0]

private theorem gu_bar_transpose_mul_pow {n d : ℕ} {F : Type} [Field F]
    (hUF : UnitaryFieldData 2 n F) {A : GL (Fin d) F}
    (hA : A ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) :
    ∃ μ : F, μ ≠ 0 ∧ μ ^ (2 ^ n) = μ ∧ Matrix.transpose
      ((A : Matrix (Fin d) (Fin d) F).map hUF.bar) * (A : Matrix (Fin d) (Fin d) F) =
      μ • (1 : Matrix (Fin d) (Fin d) F) := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hA
  refine ⟨μ, hμ0, hμq, ?_⟩
  rw [← CFSG.StandardType.TableBUD.map_pow_eq_map_bar hUF]
  exact hμ

private theorem gramForm_gu_mul {n d : ℕ} {F : Type} [Field F]
    (hUF : UnitaryFieldData 2 n F) {A : GL (Fin d) F}
    (hA : A ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) :
    ∃ μ : F, μ ≠ 0 ∧ μ ^ (2 ^ n) = μ ∧
      ∀ x y : Fin d → F,
        gramForm hUF 1 ((A : Matrix (Fin d) (Fin d) F) *ᵥ x)
          ((A : Matrix (Fin d) (Fin d) F) *ᵥ y) = μ * gramForm hUF 1 x y := by
  obtain ⟨μ, hμ0, hμq, hμ⟩ := gu_bar_transpose_mul_pow hUF hA
  refine ⟨μ, hμ0, hμq, fun x y => ?_⟩
  rw [gramForm_mulVec, Matrix.mul_one, hμ, gramForm_apply, gramForm_apply,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

private lemma gl_mulVec_mulVec {d : ℕ} {F : Type} [Field F] (U V : GL (Fin d) F)
    (v : Fin d → F) :
    (U : Matrix (Fin d) (Fin d) F) *ᵥ ((V : Matrix (Fin d) (Fin d) F) *ᵥ v) =
      ((U * V : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, Units.val_mul]


private theorem exists_ne_fixed_of_isPGroup_two {T V : Type*} [Group T] [MulAction T V]
    [Finite V] (hT : IsPGroup 2 T) (h2 : 2 ∣ Nat.card V) {a : V}
    (ha : a ∈ MulAction.fixedPoints T V) :
    ∃ v : V, v ≠ a ∧ ∀ t : T, t • v = v := by
  obtain ⟨b, hb, hb0⟩ :=
    hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2 ha
  exact ⟨b, hb0.symm, hb⟩



theorem tor_uni_frame {p n d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1)
    {G : Subgroup (GL (Fin d) F)} (hZG : LargeEvenScalars (Fin d) F ≤ G) (htor : MToral p d F G)
    (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) :
    ∃ P : GL (Fin d) F, P ∈ LargeEvenGUSet (Fin d) F (2 ^ n) ∧ MDiagAt d F P G := by
  classical
  have hUF : UnitaryFieldData 2 n F := unitaryFieldData_two_of_card hF hn
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, ?_, ?_⟩
    · refine ⟨1, one_ne_zero, one_pow _, ?_⟩
      simp
    · intro g hg
      exact ⟨Matrix.diag _, (Matrix.IsDiag.diagonal_diag
        (Matrix.isDiag_of_subsingleton _)).symm⟩
  · let H : Subgroup (primeFormUnitary hUF (idGram F d)) :=
      { carrier := {u | (u : GL (Fin d) F) ∈ G ∧ u ^ p = 1}
        mul_mem' := by
          rintro u v ⟨hu, hup⟩ ⟨hv, hvp⟩
          refine ⟨G.mul_mem hu hv, ?_⟩
          have huv : Commute u v := Subtype.ext (htor.1 _ hu _ hv)
          rw [huv.mul_pow, hup, hvp, one_mul]
        one_mem' := ⟨G.one_mem, one_pow p⟩
        inv_mem' := by
          rintro u ⟨hu, hup⟩
          exact ⟨G.inv_mem hu, by rw [inv_pow, hup, inv_one]⟩ }
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag hUF hp hpq H
      (fun x hx y hy => Subtype.ext (htor.1 _ hx.1 _ hy.1)) (fun x hx => hx.2)
    have hPmem : ((P⁻¹ : primeFormUnitary hUF (idGram F d)) : GL (Fin d) F) ∈
        LargeEvenGUSet (Fin d) F (2 ^ n) := by
      refine ⟨1, one_ne_zero, one_pow _, ?_⟩
      rw [CFSG.StandardType.TableBUD.map_pow_eq_map_bar hUF, one_smul]
      have h3 := (P⁻¹ : primeFormUnitary hUF (idGram F d)).2
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at h3
      simpa only [idGram, Units.val_one, Matrix.mul_one] using h3
    refine ⟨(P : GL (Fin d) F)⁻¹, hPmem, ?_⟩
    intro A hA
    obtain ⟨a, ha⟩ := htor.2 A hA
    let B : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) a * A
    have hgM : (B : Matrix (Fin d) (Fin d) F) =
        (a : F) • (A : Matrix (Fin d) (Fin d) F) := by
      dsimp only [B]
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      exact CFSG.StandardType.TableBUD.scalar_mul_eq_smul (a : F)
        (A : Matrix (Fin d) (Fin d) F)
    have hB : B ∈ primeFormUnitary hUF (idGram F d) :=
      CFSG.StandardType.TableBUD.mem_primeFormUnitary_of_pow_eq_one hUF hpq hd
        (hGU A hA) hgM ha
    have hBmem : B ∈ G := G.mul_mem (hZG ⟨a, rfl⟩) hA
    have hBp' : (⟨B, hB⟩ : primeFormUnitary hUF (idGram F d)) ^ p = 1 := by
      apply Subtype.ext
      change B ^ p = 1
      exact ha
    have hBH : (⟨B, hB⟩ : primeFormUnitary hUF (idGram F d)) ∈ H := ⟨hBmem, hBp'⟩
    have hdiag := hP ⟨B, hB⟩ hBH
    have hdiagB : ((P : GL (Fin d) F)⁻¹ * (B : Matrix (Fin d) (Fin d) F) *
        (P : GL (Fin d) F)).IsDiag := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, Units.val_mul,
        Units.val_inv_eq_inv_val] using hdiag
    have hAeq : (P : GL (Fin d) F)⁻¹ * (A : Matrix (Fin d) (Fin d) F) *
        (P : GL (Fin d) F) = ((a : F)⁻¹) •
        ((P : GL (Fin d) F)⁻¹ * (B : Matrix (Fin d) (Fin d) F) *
          (P : GL (Fin d) F)) := by
      rw [hgM]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero a), one_smul]
    have hdiagA : ((P : GL (Fin d) F)⁻¹ * (A : Matrix (Fin d) (Fin d) F) *
        (P : GL (Fin d) F)).IsDiag := by
      rw [hAeq]
      exact hdiagB.smul _
    refine ⟨Matrix.diag ((P : GL (Fin d) F)⁻¹ * (A : Matrix (Fin d) (Fin d) F) *
      (P : GL (Fin d) F)), ?_⟩
    rw [Matrix.IsDiag.diagonal_diag hdiagA]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]

theorem uni_isotropic_inv {n d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) {T : Subgroup (GL (Fin d) F)}
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hTU : ∀ t ∈ T, t ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    {G : Subgroup (GL (Fin d) F)} (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hGT : ∀ A ∈ G, A ∈ Subgroup.normalizer (T : Set (GL (Fin d) F))) :
    ∃ R : Submodule F (Fin d → F), R ≠ ⊥ ∧
      (∀ u ∈ R, ∀ v ∈ R, ∑ i, (u i) ^ (2 ^ n) * v i = 0) ∧
      ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin d) (Fin d) F).mulVec v ∈ R := by
  classical
  have hUF : UnitaryFieldData 2 n F := unitaryFieldData_two_of_card hF hn
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    exfalso
    apply hT1
    refine (Subgroup.eq_bot_iff_forall T).mpr fun x _ => ?_
    exact Units.ext (Subsingleton.elim _ _)
  · letI : MulAction T (Fin d → F) :=
      { smul := fun t v => ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v
        one_smul := fun v => by
          show (((1 : T) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v = v
          rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
        mul_smul := fun s t v => by
          show (((s * t : T) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v =
            ((s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
              (((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v)
          rw [Subgroup.coe_mul, Units.val_mul]
          exact (Matrix.mulVec_mulVec v ((s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
            ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)).symm }
    let W : Submodule F (Fin d → F) :=
      { carrier := {v | ∀ t ∈ T, ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v = v}
        zero_mem' := by intro t _; rw [Matrix.mulVec_zero]
        add_mem' := by
          intro u v hu hv t ht
          rw [Matrix.mulVec_add, hu t ht, hv t ht]
        smul_mem' := by
          intro c v hv t ht
          rw [Matrix.mulVec_smul, hv t ht] }
    let Wp : Submodule F (Fin d → F) :=
      { carrier := {v | ∀ w ∈ W, gramForm hUF 1 w v = 0}
        zero_mem' := by intro w _; exact map_zero (gramForm hUF 1 w)
        add_mem' := by
          intro u v hu hv w hw
          rw [map_add, hu w hw, hv w hw, add_zero]
        smul_mem' := by
          intro c v hv w hw
          rw [map_smul, hv w hw, smul_zero] }
    have hWT : ∀ t ∈ T, ∀ v ∈ W,
        ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ W := by
      intro t ht v hv s hs
      calc ((s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
              (((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v)
          = ((s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v := by rw [hv t ht]
        _ = v := hv s hs
        _ = ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v := (hv t ht).symm
    have hWG : ∀ A ∈ G, ∀ v ∈ W, (A : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ W := by
      intro A hA v hv t ht
      have hAt : A⁻¹ * t * A ∈ T :=
        ((Subgroup.mem_normalizer_iff''.mp (show A ∈ Subgroup.normalizer T from hGT A hA)) t).mp ht
      have hga : (t : GL (Fin d) F) * A = A * (A⁻¹ * t * A) := by group
      calc (t : Matrix (Fin d) (Fin d) F) *ᵥ ((A : Matrix (Fin d) (Fin d) F) *ᵥ v)
          = (((t : GL (Fin d) F) * A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v :=
            gl_mulVec_mulVec t A v
        _ = ((A * (A⁻¹ * t * A) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v := by rw [hga]
        _ = (A : Matrix (Fin d) (Fin d) F) *ᵥ
              (((A⁻¹ * t * A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v) :=
            (gl_mulVec_mulVec A (A⁻¹ * t * A) v).symm
        _ = (A : Matrix (Fin d) (Fin d) F) *ᵥ v :=
            congrArg (fun w => (A : Matrix (Fin d) (Fin d) F) *ᵥ w) (hv _ hAt)
    have hWp_invT : ∀ t ∈ T, ∀ v ∈ Wp,
        ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ Wp := by
      intro t ht v hv w hw
      let X : Fin d → F := (((t⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ w
      have hX : X ∈ W := hWT t⁻¹ (T.inv_mem ht) w hw
      have hweq : ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ X = w := by
        calc ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ X
            = (((t : GL (Fin d) F) * t⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w :=
              gl_mulVec_mulVec t t⁻¹ w
          _ = w := by rw [mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← hweq, gramForm_one_gu_zero_iff hUF (hTU t ht) X v]
      exact hv X hX
    have hWpG : ∀ A ∈ G, ∀ v ∈ Wp, (A : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ Wp := by
      intro A hA v hv w hw
      let X : Fin d → F := (((A⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ w
      have hX : X ∈ W := hWG A⁻¹ (G.inv_mem hA) w hw
      have hweq : (A : Matrix (Fin d) (Fin d) F) *ᵥ X = w := by
        calc (A : Matrix (Fin d) (Fin d) F) *ᵥ X
            = (((A : GL (Fin d) F) * A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w :=
              gl_mulVec_mulVec A A⁻¹ w
          _ = w := by rw [mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← hweq, gramForm_one_gu_zero_iff hUF (hGU A hA) X v]
      exact hv X hX
    let R : Submodule F (Fin d → F) := W ⊓ Wp
    have hRne : R ≠ ⊥ := by
      intro hRbot
      have hbot : W ⊓ Wp = ⊥ := by simpa [R] using hRbot
      have hWpbot : Wp = ⊥ := by
        by_contra hWpne
        letI : MulAction T Wp :=
          { smul := fun t v => ⟨((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v.1,
              hWp_invT t t.2 v.1 v.2⟩
            one_smul := fun v => by
              apply Subtype.ext
              show (((1 : T) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v.1 = v.1
              rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
            mul_smul := fun s t v => by
              apply Subtype.ext
              show (((s * t : T) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v.1 =
                ((s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
                  (((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v.1)
              rw [Subgroup.coe_mul, Units.val_mul]
              exact (Matrix.mulVec_mulVec v.1 ((s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
                ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)).symm }
        have h2Wp : 2 ∣ Nat.card Wp := by
          obtain ⟨v, hvWp, hv0⟩ := (Submodule.ne_bot_iff Wp).mp hWpne
          have h2v : (2 : ℕ) • (⟨v, hvWp⟩ : Wp) = 0 := by
            apply Subtype.ext
            change (2 : ℕ) • v = 0
            rw [two_nsmul, ← one_smul F v, ← add_smul, one_add_one_eq_two,
              CharTwo.two_eq_zero, zero_smul]
          have hord : addOrderOf (⟨v, hvWp⟩ : Wp) = 2 :=
            addOrderOf_eq_prime (by simpa using h2v)
              (fun h => hv0 (congrArg Subtype.val h))
          simpa [hord] using addOrderOf_dvd_natCard (⟨v, hvWp⟩ : Wp)
        have h0Wp : (0 : Wp) ∈ MulAction.fixedPoints T Wp := fun t => by
          apply Subtype.ext
          change ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ (0 : Fin d → F) = 0
          rw [Matrix.mulVec_zero]
        obtain ⟨z, hz0, hzfix⟩ :=
          exists_ne_fixed_of_isPGroup_two hT h2Wp (a := (0 : Wp)) h0Wp
        have hzW : z.1 ∈ W := fun t ht => by
          exact congrArg (fun w : Wp => (w : Fin d → F)) (hzfix ⟨t, ht⟩)
        have hzbot : z.1 ∈ (⊥ : Submodule F (Fin d → F)) := by
          rw [← hbot]
          exact ⟨hzW, z.2⟩
        have hz1 : z.1 = 0 := by
          have := hzbot
          rwa [Submodule.mem_bot] at this
        exact hz0 (Subtype.ext hz1)
      have hWtop : W = ⊤ := by
        let Wb : Submodule F (Fin d → F) :=
          { carrier := {u | ∃ w ∈ W, u = fun i => hUF.bar (w i)}
            zero_mem' := ⟨0, W.zero_mem, by funext i; simp⟩
            add_mem' := by
              rintro u v ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
              exact ⟨a + b, W.add_mem ha hb, by funext i; simp [map_add]⟩
            smul_mem' := by
              rintro c u ⟨a, ha, rfl⟩
              exact ⟨hUF.bar c • a, W.smul_mem _ ha,
                by funext i; simp [map_mul, hUF.bar_bar]⟩ }
        have hWp_eq : Wp = (Matrix.toBilin' (1 : Matrix (Fin d) (Fin d) F)).orthogonal Wb := by
          ext v
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          constructor
          · intro hv u hu
            obtain ⟨w, hw, rfl⟩ := hu
            have h := hv w hw
            rw [gramForm_apply, Matrix.one_mulVec] at h
            rwa [Matrix.toBilin'_apply', Matrix.one_mulVec]
          · intro hv w hw
            have h := hv (fun i => hUF.bar (w i)) ⟨w, hw, rfl⟩
            rw [Matrix.toBilin'_apply', Matrix.one_mulVec] at h
            rwa [gramForm_apply, Matrix.one_mulVec]
        have horth : (Matrix.toBilin' (1 : Matrix (Fin d) (Fin d) F)).orthogonal Wb = ⊥ := by
          rw [← hWp_eq]; exact hWpbot
        have hB_nd : (Matrix.toBilin' (1 : Matrix (Fin d) (Fin d) F)).Nondegenerate :=
          Matrix.Nondegenerate.toBilin'
            (Matrix.Nondegenerate.of_det_ne_zero (by simp))
        have hB_refl : (Matrix.toBilin' (1 : Matrix (Fin d) (Fin d) F)).IsRefl :=
          fun _ _ => by simp [Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct_comm]
        have hWb_top : Wb = ⊤ := by
          calc Wb = (Matrix.toBilin' (1 : Matrix (Fin d) (Fin d) F)).orthogonal
                ((Matrix.toBilin' (1 : Matrix (Fin d) (Fin d) F)).orthogonal Wb) :=
                (LinearMap.BilinForm.orthogonal_orthogonal hB_nd hB_refl Wb).symm
            _ = (Matrix.toBilin' (1 : Matrix (Fin d) (Fin d) F)).orthogonal ⊥ := by rw [horth]
            _ = ⊤ := LinearMap.BilinForm.orthogonal_bot
        ext v
        simp only [Submodule.mem_top, iff_true]
        have hbar : (fun i => hUF.bar (v i)) ∈ Wb := by rw [hWb_top]; exact Submodule.mem_top
        obtain ⟨w, hw, hwv⟩ := hbar
        have hvw : v = w := by
          funext i
          have hi := congrFun hwv i
          calc v i = hUF.bar (hUF.bar (v i)) := (hUF.bar_bar (v i)).symm
            _ = hUF.bar (hUF.bar (w i)) := by rw [hi]
            _ = w i := hUF.bar_bar (w i)
        rw [hvw]
        exact hw
      have hTbot : T = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall T).mpr fun x hx => ?_
        apply Units.ext
        apply Matrix.ext
        intro i j
        have hv : Pi.single j (1 : F) ∈ W := by rw [hWtop]; exact Submodule.mem_top
        have hxfix : (x : Matrix (Fin d) (Fin d) F) *ᵥ (Pi.single j (1 : F)) =
            Pi.single j 1 := hv x hx
        have h := congrFun hxfix i
        rw [Matrix.mulVec_single_one] at h
        simpa [Matrix.col_apply, Matrix.one_apply, Pi.single_apply] using h
      exact hT1 hTbot
    refine ⟨R, hRne, ?_, ?_⟩
    · intro u hu v hv
      have h := hv.2 u hu.1
      simpa [gramForm_apply, Matrix.one_mulVec, dotProduct,
        UnitaryFieldData.bar_apply] using h
    · intro A hA v hv
      exact ⟨hWG A hA v hv.1, hWpG A hA v hv.2⟩

private noncomputable abbrev hfOrth {n d : ℕ} {F : Type} [Field F] (hUF : UnitaryFieldData 2 n F)
    (R : Submodule F (Fin d → F)) : Submodule F (Fin d → F) :=
  R.orthogonalBilin (gramForm hUF 1)

private theorem finrank_hfOrth_add {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) (R : Submodule F (Fin d → F)) :
    Module.finrank F R + Module.finrank F (hfOrth hUF R) = d := by
  haveI : FiniteDimensional F (Fin d → F) := inferInstance
  have hσ : Function.Surjective hUF.bar := fun x => ⟨hUF.bar x, hUF.bar_bar x⟩
  have hB : (gramForm hUF 1).SeparatingLeft :=
    CFSG.ClassicalGroups.UnitaryFlag.gramForm_separatingLeft hUF
      (by simp : (1 : Matrix (Fin d) (Fin d) F).det ≠ 0)
  have h := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq
    (σ := hUF.bar) (B := gramForm hUF 1) hσ hB R
  rw [Module.finrank_fin_fun] at h
  have h' : Module.finrank F (hfOrth hUF R) = d - Module.finrank F R := h
  have hle : Module.finrank F R ≤ d := by
    have h2 := Submodule.finrank_le R
    rwa [Module.finrank_fin_fun] at h2
  omega

private theorem le_hfOrth_of_isotropic {n d : ℕ} {F : Type} [Field F]
    (hUF : UnitaryFieldData 2 n F) {R : Submodule F (Fin d → F)}
    (hRiso : ∀ u ∈ R, ∀ v ∈ R, ∑ i, (u i) ^ (2 ^ n) * v i = 0) :
    R ≤ hfOrth hUF R := by
  intro r hr
  rw [Submodule.mem_orthogonalBilin]
  intro r' hr'
  rw [gramForm_apply, Matrix.one_mulVec]
  simpa [dotProduct, UnitaryFieldData.bar_apply] using hRiso r' hr' r hr

private theorem finrank_le_three_of_isotropic {n : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) {R : Submodule F (Fin 6 → F)}
    (hRiso : ∀ u ∈ R, ∀ v ∈ R, ∑ i, (u i) ^ (2 ^ n) * v i = 0) :
    Module.finrank F R ≤ 3 := by
  have h1 := finrank_hfOrth_add (d := 6) hUF R
  have h2 : R ≤ hfOrth hUF R := le_hfOrth_of_isotropic hUF hRiso
  haveI : FiniteDimensional F (hfOrth hUF R) :=
    FiniteDimensional.of_injective (Submodule.subtype _) Subtype.coe_injective
  have h3 : Module.finrank F R ≤ Module.finrank F (hfOrth hUF R) :=
    Submodule.finrank_mono h2
  omega

private theorem eq_hfOrth_of_isotropic_finrank_eq {n : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) {R : Submodule F (Fin 6 → F)}
    (hRiso : ∀ u ∈ R, ∀ v ∈ R, ∑ i, (u i) ^ (2 ^ n) * v i = 0)
    (hr : Module.finrank F R = 3) : hfOrth hUF R = R := by
  haveI : FiniteDimensional F (hfOrth hUF R) :=
    FiniteDimensional.of_injective (Submodule.subtype _) Subtype.coe_injective
  have h2 : R ≤ hfOrth hUF R := le_hfOrth_of_isotropic hUF hRiso
  have h1 := finrank_hfOrth_add (d := 6) hUF R
  have h3 : Module.finrank F R = Module.finrank F (hfOrth hUF R) := by omega
  exact (Submodule.eq_of_le_of_finrank_eq h2 h3).symm

private theorem sub_smul_mem_of_isScalarOn {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hUF : UnitaryFieldData 2 n F) {R : Submodule F (Fin 6 → F)}
    (hRperp : hfOrth hUF R = R)
    {A : GL (Fin 6) F} {lam : F} (hlam0 : lam ≠ 0)
    (hlam : ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v = lam • v)
    {μ : F} (hμ : ∀ x y : Fin 6 → F,
      gramForm hUF 1 ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ x)
        ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ y) = μ * gramForm hUF 1 x y) :
    ∀ x : Fin 6 → F,
      (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x - (μ / lam ^ (2 ^ n)) • x ∈ R := by
  intro x
  rw [← hRperp, Submodule.mem_orthogonalBilin]
  intro r hr
  have hAinv : ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r = lam⁻¹ • r := by
    have h1 : r = lam • (((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r) := by
      have h := congrArg (fun z => ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ z)
        (hlam r hr)
      simpa [gl_mulVec_mulVec, Matrix.mulVec_smul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] using h
    calc ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r
        = lam⁻¹ • (lam • (((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r)) := by
          rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      _ = lam⁻¹ • r := by rw [← h1]
  have hkey : gramForm hUF 1 r ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ x) =
      (μ / lam ^ (2 ^ n)) * gramForm hUF 1 r x := by
    have hr' : (A : Matrix (Fin 6) (Fin 6) F) *ᵥ
        (((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r) = r := by
      rw [gl_mulVec_mulVec, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    calc gramForm hUF 1 r ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ x)
        = gramForm hUF 1 ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ
            (((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r))
            ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ x) := by rw [hr']
      _ = μ * gramForm hUF 1 (((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r) x :=
            hμ _ _
      _ = μ * gramForm hUF 1 (lam⁻¹ • r) x := by rw [hAinv]
      _ = μ * ((lam⁻¹) ^ (2 ^ n) * gramForm hUF 1 r x) := by
            rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, UnitaryFieldData.bar_apply]
      _ = (μ / lam ^ (2 ^ n)) * gramForm hUF 1 r x := by
            rw [inv_pow, div_eq_mul_inv, mul_assoc]
  rw [map_sub, map_smul, smul_eq_mul, hkey, sub_self]

private lemma matrix_pow_mulVec {d : ℕ} {F : Type} [Field F]
    (M : Matrix (Fin d) (Fin d) F) {v : Fin d → F} {lam : F}
    (h : M *ᵥ v = lam • v) (k : ℕ) : (M ^ k) *ᵥ v = lam ^ k • v := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

private lemma scalar_mulVec {d : ℕ} {F : Type} [Field F] (c : F) (v : Fin d → F) :
    (Matrix.scalar (Fin d) c) *ᵥ v = c • v := by
  rw [Matrix.scalar_apply]
  ext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

private theorem lam_cube_eq {F : Type} [Field F]
    {A : GL (Fin 6) F} {lam : F} {κ : Fˣ} {r : Fin 6 → F}
    (hlamr : (A : Matrix (Fin 6) (Fin 6) F) *ᵥ r = lam • r)
    (hA3 : (A : GL (Fin 6) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (hr0 : r ≠ 0) : lam ^ 3 = (κ : F) := by
  have hpow2 : (((A : GL (Fin 6) F) ^ 3 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r =
      lam ^ 3 • r := by
    rw [Units.val_pow_eq_pow_val, matrix_pow_mulVec (A : Matrix (Fin 6) (Fin 6) F) hlamr 3]
  have hκ2 : (((A : GL (Fin 6) F) ^ 3 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ r =
      (κ : F) • r := by
    rw [hA3, Matrix.GeneralLinearGroup.coe_scalar, scalar_mulVec]
  have h2 : ((κ : F) - lam ^ 3) • r = 0 := by
    rw [sub_smul, ← hκ2, hpow2, sub_self]
  have h3 : (κ : F) - lam ^ 3 = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hr0
  exact (sub_eq_zero.mp h3).symm

private lemma pow_sub_smul_mem {F : Type} [Field F] {R : Submodule F (Fin 6 → F)}
    {A : GL (Fin 6) F} {ν : F}
    (hAR : ∀ x, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x - ν • x ∈ R)
    (hR : ∀ x ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x ∈ R) (k : ℕ) (x : Fin 6 → F) :
    ((A : Matrix (Fin 6) (Fin 6) F) ^ k) *ᵥ x - ν ^ k • x ∈ R := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul, sub_self]; exact R.zero_mem
  | succ k ih =>
    have hAy : (A : Matrix (Fin 6) (Fin 6) F) *ᵥ
        (((A : Matrix (Fin 6) (Fin 6) F) ^ k) *ᵥ x) -
        ν • (((A : Matrix (Fin 6) (Fin 6) F) ^ k) *ᵥ x) ∈ R := hAR _
    have hz : ν • ((((A : Matrix (Fin 6) (Fin 6) F) ^ k) *ᵥ x) - ν ^ k • x) ∈ R :=
      R.smul_mem ν ih
    convert R.add_mem hAy hz using 1
    rw [pow_succ', ← Matrix.mulVec_mulVec, smul_sub, pow_succ', smul_smul]
    abel

private theorem nu_cube_eq {F : Type} [Field F] {R : Submodule F (Fin 6 → F)}
    {A : GL (Fin 6) F} {ν : F} {κ : Fˣ}
    (hAR : ∀ x, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x - ν • x ∈ R)
    (hR : ∀ x ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x ∈ R)
    (hA3 : (A : GL (Fin 6) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (hRtop : R ≠ ⊤) : ν ^ 3 = (κ : F) := by
  have hnot : ¬ (∀ x, x ∈ R) := fun h => hRtop ((Submodule.eq_top_iff').mpr h)
  obtain ⟨x, hxR⟩ := not_forall.mp hnot
  have hmem : ((A : Matrix (Fin 6) (Fin 6) F) ^ 3) *ᵥ x - ν ^ 3 • x ∈ R :=
    pow_sub_smul_mem hAR hR 3 x
  have hκx : ((A : Matrix (Fin 6) (Fin 6) F) ^ 3) *ᵥ x = (κ : F) • x := by
    rw [← Units.val_pow_eq_pow_val, hA3, Matrix.GeneralLinearGroup.coe_scalar, scalar_mulVec]
  have hmem2 : ((κ : F) - ν ^ 3) • x ∈ R := by
    convert hmem using 1
    rw [hκx, sub_smul]
  have hzero : (κ : F) - ν ^ 3 = 0 := by
    by_contra hne
    apply hxR
    have h1 : ((κ : F) - ν ^ 3)⁻¹ • (((κ : F) - ν ^ 3) • x) ∈ R := R.smul_mem _ hmem2
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h1
  exact (sub_eq_zero.mp hzero).symm

private theorem nu_eq_lam {n : ℕ} {F : Type} [Field F] [Finite F]
    (hUF : UnitaryFieldData 2 n F) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {μ lam ν : F} (hμ0 : μ ≠ 0) (hμq : μ ^ (2 ^ n) = μ) (hlam0 : lam ≠ 0)
    (hν : ν = μ / lam ^ (2 ^ n)) (hcube : ν ^ 3 = lam ^ 3) : ν = lam := by
  have hν0 : ν ≠ 0 := by rw [hν]; exact div_ne_zero hμ0 (pow_ne_zero _ hlam0)
  have hlam_sq : lam ^ ((2 ^ n) * (2 ^ n)) = lam := by
    rw [pow_mul, ← UnitaryFieldData.bar_apply, ← UnitaryFieldData.bar_apply]
    exact hUF.bar_bar lam
  have hxq : (ν / lam) ^ (2 ^ n) = ν / lam := by
    have hx : ν / lam = μ / lam ^ (2 ^ n + 1) := by
      rw [hν, div_div, pow_succ]
    rw [hx, div_pow, hμq]
    congr 1
    rw [← pow_mul, show (2 ^ n + 1) * 2 ^ n = 2 ^ n * 2 ^ n + 2 ^ n from by ring, pow_add,
      hlam_sq, ← pow_succ']
  have hx3 : (ν / lam) ^ 3 = 1 := by
    rw [div_pow, hcube, div_self (pow_ne_zero 3 hlam0)]
  have hxne : ν / lam ≠ 0 := div_ne_zero hν0 hlam0
  have hxqm1 : (ν / lam) ^ (2 ^ n - 1) = 1 := by
    have h1 : (ν / lam) ^ (2 ^ n - 1) * (ν / lam) = ν / lam := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hxq]
    exact mul_right_cancel₀ hxne (by rw [h1, one_mul])
  have hg : Nat.gcd 3 (2 ^ n - 1) = 1 := by
    have hcop : Nat.Coprime 3 (2 ^ n - 1) := by
      rw [Nat.prime_three.coprime_iff_not_dvd]
      intro hd
      obtain ⟨j, hj⟩ := hd
      obtain ⟨k, hk⟩ := hpq
      have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    exact hcop
  have hx1 : ν / lam = 1 := by
    have hord3 : orderOf (ν / lam) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
    have hordq : orderOf (ν / lam) ∣ 2 ^ n - 1 := orderOf_dvd_iff_pow_eq_one.mpr hxqm1
    have hdvd : orderOf (ν / lam) ∣ 1 := by
      rw [← hg]
      exact Nat.dvd_gcd hord3 hordq
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  exact (div_eq_one_iff_eq hlam0).mp hx1

private theorem eq_scalar_of_sub_smul_mem {F : Type} [Field F] [CharP F 2]
    {R : Submodule F (Fin 6 → F)} {A : GL (Fin 6) F} {lam : F} (hlam0 : lam ≠ 0) {κ : Fˣ}
    (hAR : ∀ x, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x - lam • x ∈ R)
    (hRkill : ∀ x ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x = lam • x)
    (hA3 : (A : GL (Fin 6) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) κ)
    (hκ : lam ^ 3 = (κ : F)) :
    (A : Matrix (Fin 6) (Fin 6) F) = lam • 1 := by
  let B : GL (Fin 6) F :=
    (Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 lam hlam0))⁻¹ * A
  let N : Matrix (Fin 6) (Fin 6) F := (B : Matrix (Fin 6) (Fin 6) F) - 1
  have hBs : (B : Matrix (Fin 6) (Fin 6) F) = lam⁻¹ • (A : Matrix (Fin 6) (Fin 6) F) := by
    dsimp only [B]
    rw [Units.val_mul, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_inv_eq_inv_val, Units.val_mk0, CFSG.StandardType.TableBUD.scalar_mul_eq_smul]
  have hN : ∀ x, N *ᵥ x ∈ R := by
    intro x
    have h1 : N *ᵥ x = lam⁻¹ • ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ x - lam • x) := by
      dsimp only [N]
      rw [hBs, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_sub, smul_smul,
        inv_mul_cancel₀ hlam0, one_smul]
    rw [h1]
    exact R.smul_mem _ (hAR x)
  have hNkill : ∀ x ∈ R, N *ᵥ x = 0 := by
    intro x hx
    have h1 : N *ᵥ x = lam⁻¹ • ((A : Matrix (Fin 6) (Fin 6) F) *ᵥ x - lam • x) := by
      dsimp only [N]
      rw [hBs, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_sub, smul_smul,
        inv_mul_cancel₀ hlam0, one_smul]
    rw [h1, hRkill x hx, sub_self, smul_zero]
  have hNN : N * N = 0 := by
    ext i j
    have h1 : (N * N) *ᵥ (Pi.single j (1 : F)) = 0 := by
      rw [← Matrix.mulVec_mulVec, hNkill _ (hN (Pi.single j (1 : F)))]
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one, Pi.zero_apply] at h2
    exact h2
  have hB' : (B : Matrix (Fin 6) (Fin 6) F) = 1 + N := by
    dsimp only [N]; abel
  have hB2 : (B : Matrix (Fin 6) (Fin 6) F) ^ 2 = 1 := by
    rw [hB', pow_two, mul_add, mul_one, add_mul, one_mul, hNN, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have hB3 : B ^ 3 = 1 := by
    have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 lam hlam0))⁻¹ A :=
      Commute.inv_left (show Commute
        (Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 lam hlam0)) A
        from Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 lam hlam0) A)
    have hu3 : (Units.mk0 lam hlam0) ^ 3 = κ :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hκ])
    have hBexp : B ^ 3 =
        ((Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 lam hlam0))⁻¹ ^ 3) * A ^ 3 := by
      dsimp only [B]
      rw [hcomm.mul_pow]
    rw [hBexp, inv_pow, ← map_pow, ← map_inv, hA3, ← map_mul, hu3, inv_mul_cancel, map_one]
  have hBm3 : (B : Matrix (Fin 6) (Fin 6) F) ^ 3 = 1 := by
    rw [show (B : Matrix (Fin 6) (Fin 6) F) ^ 3 =
      ((B ^ 3 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) from
      by rw [Units.val_pow_eq_pow_val], hB3, Units.val_one]
  have hBeq : (B : Matrix (Fin 6) (Fin 6) F) = 1 := by
    calc (B : Matrix (Fin 6) (Fin 6) F)
        = (B : Matrix (Fin 6) (Fin 6) F) * 1 := (mul_one _).symm
      _ = (B : Matrix (Fin 6) (Fin 6) F) * (B : Matrix (Fin 6) (Fin 6) F) ^ 2 := by rw [hB2]
      _ = (B : Matrix (Fin 6) (Fin 6) F) ^ 3 := by rw [← pow_succ']
      _ = 1 := hBm3
  have h1 : lam⁻¹ • (A : Matrix (Fin 6) (Fin 6) F) = 1 := by rw [← hBs, hBeq]
  calc (A : Matrix (Fin 6) (Fin 6) F)
      = lam • (lam⁻¹ • (A : Matrix (Fin 6) (Fin 6) F)) := by
        rw [smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    _ = lam • 1 := by rw [h1]

private theorem eq_scalar_of_isScalarOn {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hUF : UnitaryFieldData 2 n F) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {G : Subgroup (GL (Fin 6) F)} (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin 6) F (2 ^ n))
    (hel : MElemMod 3 6 F G) {R : Submodule F (Fin 6 → F)} (hR0 : R ≠ ⊥)
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v ∈ R)
    (hr3 : Module.finrank F R = 3) (hRperp : hfOrth hUF R = R)
    {A : GL (Fin 6) F} (hA : A ∈ G) {lam : F} (hlam0 : lam ≠ 0)
    (hlam : ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v = lam • v) :
    (A : Matrix (Fin 6) (Fin 6) F) = lam • 1 := by
  obtain ⟨μ, hμ0, hμq, hμform⟩ := gramForm_gu_mul hUF (hGU A hA)
  obtain ⟨κ, hκ⟩ := hel.1 A hA
  have hA3 : (A : GL (Fin 6) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) κ := hκ.symm
  have hνmem : ∀ x, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ x - (μ / lam ^ (2 ^ n)) • x ∈ R :=
    sub_smul_mem_of_isScalarOn hUF hRperp hlam0 hlam hμform
  have hRtop : R ≠ ⊤ := by
    intro h
    have h6 : Module.finrank F R = 6 := by
      rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨r, hrR, hr0⟩ := (Submodule.ne_bot_iff R).mp hR0
  have hlam3 : lam ^ 3 = (κ : F) := lam_cube_eq (hlam r hrR) hA3 hr0
  have hν3 : (μ / lam ^ (2 ^ n)) ^ 3 = (κ : F) :=
    nu_cube_eq hνmem (hRG A hA) hA3 hRtop
  have hcube : (μ / lam ^ (2 ^ n)) ^ 3 = lam ^ 3 := by rw [hν3, hlam3]
  have hνeq : μ / lam ^ (2 ^ n) = lam :=
    nu_eq_lam hUF hn hpq hμ0 hμq hlam0 rfl hcube
  exact eq_scalar_of_sub_smul_mem hlam0 (fun x => by simpa [hνeq] using hνmem x)
    (fun x hx => hlam x hx) hA3 hlam3

private noncomputable def restrictEquiv {d : ℕ} {F : Type} [Field F]
    (R : Submodule F (Fin d → F)) (A : GL (Fin d) F)
    (hA : ∀ v ∈ R, (A : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R)
    (hiA : ∀ v ∈ R, ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R) :
    R ≃ₗ[F] R where
  toFun v := ⟨(A : Matrix (Fin d) (Fin d) F) *ᵥ (v : Fin d → F), hA v.1 v.2⟩
  invFun v := ⟨((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ (v : Fin d → F),
    hiA v.1 v.2⟩
  left_inv v := by
    apply Subtype.ext
    calc ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
          ((A : Matrix (Fin d) (Fin d) F) *ᵥ (v : Fin d → F))
        = (((A⁻¹ : GL (Fin d) F) * A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
            (v : Fin d → F) := gl_mulVec_mulVec A⁻¹ A (v : Fin d → F)
      _ = (v : Fin d → F) := by rw [inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    apply Subtype.ext
    calc ((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
          (((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ (v : Fin d → F))
        = (((A : GL (Fin d) F) * A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
            (v : Fin d → F) := gl_mulVec_mulVec A A⁻¹ (v : Fin d → F)
      _ = (v : Fin d → F) := by rw [mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Matrix.mulVec_add]
  map_smul' c x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Matrix.mulVec_smul, RingHom.id_apply]

private lemma restrictEquiv_apply {d : ℕ} {F : Type} [Field F]
    (R : Submodule F (Fin d → F)) (A : GL (Fin d) F) (hA hiA) (v : R) :
    ((restrictEquiv R A hA hiA) v : Fin d → F) =
      (A : Matrix (Fin d) (Fin d) F) *ᵥ (v : Fin d → F) :=
  rfl

private noncomputable def restrictHom {d : ℕ} {F : Type} [Field F]
    (R : Submodule F (Fin d → F)) (G : Subgroup (GL (Fin d) F))
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R) :
    ↥G →* (R ≃ₗ[F] R) where
  toFun A := restrictEquiv R (A : GL (Fin d) F) (hRG A A.2) (hRG A⁻¹ (G.inv_mem A.2))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [restrictEquiv_apply]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec, LinearEquiv.coe_one,
      LinearMap.id_apply]
    rfl
  map_mul' A B := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [LinearEquiv.mul_apply, restrictEquiv_apply, restrictEquiv_apply, restrictEquiv_apply]
    rw [Subgroup.coe_mul, Units.val_mul]
    exact (Matrix.mulVec_mulVec (v : Fin d → F)
      (((A : ↥G) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
      (((B : ↥G) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)).symm

private noncomputable def restrictDet {d : ℕ} {F : Type} [Field F]
    (R : Submodule F (Fin d → F)) (G : Subgroup (GL (Fin d) F))
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R) :
    ↥G →* Fˣ :=
  (LinearEquiv.det).comp (restrictHom R G hRG)

private lemma restrictEquiv_scalar {d : ℕ} {F : Type} [Field F]
    (R : Submodule F (Fin d → F)) (c : Fˣ)
    (hA : ∀ v ∈ R,
      (Matrix.GeneralLinearGroup.scalar (Fin d) c : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R)
    (hiA : ∀ v ∈ R,
      (((Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R) :
    restrictEquiv R (Matrix.GeneralLinearGroup.scalar (Fin d) c) hA hiA =
      c • (1 : R ≃ₗ[F] R) := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rw [restrictEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  change (Matrix.diagonal (fun _ => (c : F)) *ᵥ (v : Fin d → F)) = (c : F) • (v : Fin d → F)
  ext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

private theorem restrictDet_commutator {d : ℕ} {F : Type} [Field F]
    (R : Submodule F (Fin d → F)) (G : Subgroup (GL (Fin d) F))
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R)
    (g h : ↥G) : restrictDet R G hRG ⁅g, h⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]

private lemma scalar_mem_LES {d : ℕ} {F : Type} [Field F] (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ LargeEvenScalars (Fin d) F :=
  Set.mem_range_self c

private theorem restrictDet_scalar {d : ℕ} {F : Type} [Field F]
    (R : Submodule F (Fin d → F)) (G : Subgroup (GL (Fin d) F))
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin d) (Fin d) F) *ᵥ v ∈ R)
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (c : Fˣ) :
    restrictDet R G hRG ⟨Matrix.GeneralLinearGroup.scalar (Fin d) c, hZG (scalar_mem_LES c)⟩ =
      c ^ Module.finrank F R := by
  show LinearEquiv.det
    (restrictHom R G hRG
      ⟨Matrix.GeneralLinearGroup.scalar (Fin d) c, hZG (scalar_mem_LES c)⟩) =
      c ^ Module.finrank F R
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ G := hZG (scalar_mem_LES c)
  haveI : Module.Finite F R :=
    FiniteDimensional.of_injective (Submodule.subtype R) Subtype.coe_injective
  haveI : Module.Free F R := Module.Free.of_basis (Module.finBasis F R)
  change LinearEquiv.det
    (restrictEquiv R (Matrix.GeneralLinearGroup.scalar (Fin d) c)
      (hRG (Matrix.GeneralLinearGroup.scalar (Fin d) c) hmem)
      (hRG ((Matrix.GeneralLinearGroup.scalar (Fin d) c))⁻¹ (G.inv_mem hmem))) =
      c ^ Module.finrank F R
  rw [restrictEquiv_scalar]
  apply Units.ext
  rw [LinearEquiv.coe_det]
  rw [show ((c • (1 : R ≃ₗ[F] R) : R ≃ₗ[F] R) : R →ₗ[F] R) =
    (c : F) • (1 : R →ₗ[F] R) from rfl]
  rw [LinearMap.det_smul, LinearMap.det.map_one, mul_one, Units.val_pow_eq_pow_val]

private lemma toMatrixAlgEquiv_smul_one {F : Type} [Field F] {R : Submodule F (Fin 6 → F)}
    (e : Module.Basis (Fin 3) F R) (c : F) :
    LinearMap.toMatrixAlgEquiv e (c • (1 : Module.End F R)) = Matrix.scalar (Fin 3) (c : F) := by
  rw [← Algebra.algebraMap_eq_smul_one, AlgEquiv.commutes, Matrix.algebraMap_eq_diagonal,
    Matrix.scalar_apply, Pi.algebraMap_def]
  simp

private lemma toMatrixAlgEquiv_symm_scalar {F : Type} [Field F] {R : Submodule F (Fin 6 → F)}
    (e : Module.Basis (Fin 3) F R) (c : F) :
    (LinearMap.toMatrixAlgEquiv e).symm (Matrix.scalar (Fin 3) (c : F)) =
      c • (1 : Module.End F R) := by
  rw [← toMatrixAlgEquiv_smul_one e c, AlgEquiv.symm_apply_apply]

private noncomputable def rankThreeHom {F : Type} [Field F] [Finite F] [CharP F 2]
    (R : Submodule F (Fin 6 → F)) (G : Subgroup (GL (Fin 6) F))
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v ∈ R)
    (e : Module.Basis (Fin 3) F R) : ↥G →* GL (Fin 3) F :=
  (Units.map (LinearMap.toMatrixAlgEquiv e).toRingEquiv.toMonoidHom).comp
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv F R).symm).toMonoidHom.comp
      (restrictHom R G hRG))

private lemma rankThreeHom_scalar {F : Type} [Field F] [Finite F] [CharP F 2]
    (R : Submodule F (Fin 6 → F)) (G : Subgroup (GL (Fin 6) F))
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v ∈ R)
    (e : Module.Basis (Fin 3) F R) (c : Fˣ)
    (hmem : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ G) :
    rankThreeHom R G hRG e ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hmem⟩ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  apply Units.ext
  dsimp only [rankThreeHom, MonoidHom.comp_apply, Units.coe_map]
  change (LinearMap.toMatrixAlgEquiv e)
      (↑((LinearMap.GeneralLinearGroup.generalLinearEquiv F R).symm
        (restrictEquiv R (Matrix.GeneralLinearGroup.scalar (Fin 6) c)
          (hRG (Matrix.GeneralLinearGroup.scalar (Fin 6) c) hmem)
          (hRG ((Matrix.GeneralLinearGroup.scalar (Fin 6) c))⁻¹ (G.inv_mem hmem))))) =
    Matrix.scalar (Fin 3) (c : F)
  rw [restrictEquiv_scalar]
  change (LinearMap.toMatrixAlgEquiv e)
    (↑((LinearMap.GeneralLinearGroup.generalLinearEquiv F R).symm
      (c • (1 : R ≃ₗ[F] R)))) = Matrix.scalar (Fin 3) (c : F)
  rw [show (LinearMap.GeneralLinearGroup.generalLinearEquiv F R).symm (c • (1 : R ≃ₗ[F] R)) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (c • (1 : R ≃ₗ[F] R)) from rfl]
  change (LinearMap.toMatrixAlgEquiv e) ((c : F) • (1 : Module.End F R)) =
    Matrix.scalar (Fin 3) (c : F)
  rw [toMatrixAlgEquiv_smul_one]

private lemma coe_scalar_eq_smul_one {d : ℕ} {F : Type} [Field F] (c : Fˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin d) c : Matrix (Fin d) (Fin d) F) = (c : F) • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

private lemma rankThreeHom_apply {F : Type} [Field F] [Finite F] [CharP F 2]
    (R : Submodule F (Fin 6 → F)) (G : Subgroup (GL (Fin 6) F))
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v ∈ R)
    (e : Module.Basis (Fin 3) F R) (A : ↥G) :
    ((rankThreeHom R G hRG e A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      LinearMap.toMatrixAlgEquiv e
        (((restrictHom R G hRG A : R ≃ₗ[F] R)) : R →ₗ[F] R) := by
  dsimp only [rankThreeHom, MonoidHom.comp_apply, Units.coe_map]
  change (LinearMap.toMatrixAlgEquiv e)
      (↑((LinearMap.GeneralLinearGroup.generalLinearEquiv F R).symm
        ((restrictHom R G hRG) A))) = LinearMap.toMatrixAlgEquiv e
      (((restrictHom R G hRG) A : R ≃ₗ[F] R) : R →ₗ[F] R)
  rw [show (LinearMap.GeneralLinearGroup.generalLinearEquiv F R).symm
      ((restrictHom R G hRG) A) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv ((restrictHom R G hRG) A) from rfl]
  rfl

private theorem rankThreeHom_mem_scalars_iff {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hUF : UnitaryFieldData 2 n F) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {G : Subgroup (GL (Fin 6) F)} (hZG : LargeEvenScalars (Fin 6) F ≤ G)
    (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin 6) F (2 ^ n)) (hel : MElemMod 3 6 F G)
    {R : Submodule F (Fin 6 → F)} (hR0 : R ≠ ⊥)
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v ∈ R)
    (hr3 : Module.finrank F R = 3) (hRperp : hfOrth hUF R = R)
    (e : Module.Basis (Fin 3) F R) (A : ↥G) :
    rankThreeHom R G hRG e A ∈ LargeEvenScalars (Fin 3) F ↔
      (A : GL (Fin 6) F) ∈ LargeEvenScalars (Fin 6) F := by
  constructor
  · intro hA
    obtain ⟨c, hc⟩ := hA
    have hmat : LinearMap.toMatrixAlgEquiv e
        (((restrictHom R G hRG A : R ≃ₗ[F] R)) : R →ₗ[F] R) = Matrix.scalar (Fin 3) (c : F) := by
      rw [← rankThreeHom_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
    have hlin : (((restrictHom R G hRG A : R ≃ₗ[F] R)) : R →ₗ[F] R) =
        (c : F) • (1 : Module.End F R) := by
      rw [← toMatrixAlgEquiv_symm_scalar e (c : F)]
      simpa using congrArg (LinearMap.toMatrixAlgEquiv e).symm hmat
    have hAv : ∀ v ∈ R, ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ v = (c : F) • v := by
      intro v hv
      have h1 := congrArg (fun f : R →ₗ[F] R => f ⟨v, hv⟩) hlin
      have h2 := congrArg (fun w : R => (w : Fin 6 → F)) h1
      simpa [restrictHom, restrictEquiv_apply, LinearMap.smul_apply] using h2
    have hA6 : ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = (c : F) • 1 :=
      eq_scalar_of_isScalarOn hUF hn hpq hGU hel hR0 hRG hr3 hRperp A.2 (Units.ne_zero c) hAv
    have : (A : GL (Fin 6) F) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      apply Units.ext
      rw [hA6, coe_scalar_eq_smul_one]
    rw [this]
    exact scalar_mem_LES c
  · intro hA
    obtain ⟨c, hc⟩ := hA
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ G := hZG (scalar_mem_LES c)
    have hAeq : (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hmem⟩ : ↥G) = A := Subtype.ext hc
    rw [← hAeq, rankThreeHom_scalar]
    exact scalar_mem_LES c


private theorem rankThreeHom_injective {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hUF : UnitaryFieldData 2 n F) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {G : Subgroup (GL (Fin 6) F)} (hZG : LargeEvenScalars (Fin 6) F ≤ G)
    (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin 6) F (2 ^ n)) (hel : MElemMod 3 6 F G)
    {R : Submodule F (Fin 6 → F)} (hR0 : R ≠ ⊥)
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v ∈ R)
    (hr3 : Module.finrank F R = 3) (hRperp : hfOrth hUF R = R)
    (e : Module.Basis (Fin 3) F R) : Function.Injective (rankThreeHom R G hRG e) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hmat : LinearMap.toMatrixAlgEquiv e
      (((restrictHom R G hRG A : R ≃ₗ[F] R)) : R →ₗ[F] R) = 1 := by
    rw [← rankThreeHom_apply, hA, Units.val_one]
  have hlin : (((restrictHom R G hRG A : R ≃ₗ[F] R)) : R →ₗ[F] R) = 1 := by
    have := congrArg (LinearMap.toMatrixAlgEquiv e).symm hmat
    simpa using this
  have hAv : ∀ v ∈ R, ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ v = (1 : F) • v := by
    intro v hv
    have h1 := congrArg (fun g : R →ₗ[F] R => g ⟨v, hv⟩) hlin
    have h2 := congrArg (fun w : R => (w : Fin 6 → F)) h1
    simpa [restrictHom, restrictEquiv_apply] using h2
  have hA1 : ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = (1 : F) • 1 :=
    eq_scalar_of_isScalarOn hUF hn hpq hGU hel hR0 hRG hr3 hRperp A.2 one_ne_zero hAv
  apply Subtype.ext
  apply Units.ext
  rw [hA1, Subgroup.coe_one, Units.val_one, one_smul]

private theorem uni_survivor_false_of_rank_three {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {G : Subgroup (GL (Fin 6) F)} (hZG : LargeEvenScalars (Fin 6) F ≤ G)
    (hel : MElemMod 3 6 F G) (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin 6) F (2 ^ n))
    (hrank : 3 ^ 3 ≤ (LargeEvenScalars (Fin 6) F).relIndex G)
    (R : Submodule F (Fin 6 → F)) (hR0 : R ≠ ⊥)
    (hRiso : ∀ u ∈ R, ∀ v ∈ R, ∑ i, (u i) ^ (2 ^ n) * v i = 0)
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F).mulVec v ∈ R)
    (hUF : UnitaryFieldData 2 n F) (hr3 : Module.finrank F R = 3) : False := by
  classical
  have hRperp : hfOrth hUF R = R := eq_hfOrth_of_isotropic_finrank_eq hUF hRiso hr3
  haveI : Module.Finite F R :=
    FiniteDimensional.of_injective (Submodule.subtype R) Subtype.coe_injective
  let e : Module.Basis (Fin 3) F R := Module.finBasisOfFinrankEq F R hr3
  let f := rankThreeHom R G hRG e
  let H : Subgroup (GL (Fin 3) F) := f.range
  have hfinj : Function.Injective f :=
    rankThreeHom_injective hUF hn hpq hZG hGU hel hR0 hRG hr3 hRperp e
  have hsc3 : LargeEvenScalars (Fin 3) F ≤ H := by
    intro s hs
    obtain ⟨c, hc⟩ := hs
    exact ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hZG (scalar_mem_LES c)⟩,
      (rankThreeHom_scalar R G hRG e c (hZG (scalar_mem_LES c))).trans hc⟩
  have hMElem : MElemMod 3 3 F H := by
    refine ⟨?_, ?_⟩
    · rintro h ⟨A, rfl⟩
      obtain ⟨κ, hκ⟩ := hel.1 A A.2
      refine ⟨κ, ?_⟩
      rw [← map_pow, ← show (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) κ,
        hZG (scalar_mem_LES κ)⟩ : ↥G) = A ^ 3 from Subtype.ext hκ, rankThreeHom_scalar]
    · rintro h ⟨A, rfl⟩ k ⟨B, rfl⟩
      obtain ⟨ζ, hζ⟩ := hel.2 A A.2 B B.2
      refine ⟨ζ, ?_⟩
      rw [← map_commutatorElement, ← show (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) ζ,
        hZG (scalar_mem_LES ζ)⟩ : ↥G) = ⁅A, B⁆ from Subtype.ext hζ, rankThreeHom_scalar]
  have hmapsc : ((LargeEvenScalars (Fin 6) F).subgroupOf G).map f =
      LargeEvenScalars (Fin 3) F := by
    apply le_antisymm
    · rintro s ⟨A, hA, rfl⟩
      exact (rankThreeHom_mem_scalars_iff hUF hn hpq hZG hGU hel hR0 hRG hr3 hRperp e A).mpr hA
    · intro s hs
      obtain ⟨c, hc⟩ := hs
      refine Subgroup.mem_map.mpr ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c,
        hZG (scalar_mem_LES c)⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact scalar_mem_LES c
      · rw [rankThreeHom_scalar, hc]
  have hrel : (LargeEvenScalars (Fin 6) F).relIndex G ≤
      (LargeEvenScalars (Fin 3) F).relIndex H := by
    have h := Subgroup.relIndex_map_map_of_injective (f := f)
      ((LargeEvenScalars (Fin 6) F).subgroupOf G) (⊤ : Subgroup ↥G) hfinj
    rw [Subgroup.map_top, hmapsc, Subgroup.relIndex_top_right] at h
    exact h.symm.le
  have hpF : 3 ∣ Nat.card F - 1 := by
    have h2 : Nat.card F - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [hF]
      have hsq := sq_tsub_sq (2 ^ n) 1
      rw [one_pow] at hsq
      rw [← hsq, sq]
    rw [h2]
    exact Dvd.dvd.mul_right hpq _
  have hle := tor_rank_le (p := 3) (d := 3) Nat.prime_three (by norm_num) hpF hsc3 hMElem
  have hbound : (LargeEvenScalars (Fin 3) F).relIndex H ≤ 9 := by simpa using hle
  have h27 : 3 ^ 3 ≤ (LargeEvenScalars (Fin 3) F).relIndex H := le_trans hrank hrel
  omega

theorem uni_survivor {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {G : Subgroup (GL (Fin 6) F)} (hZG : LargeEvenScalars (Fin 6) F ≤ G)
    (hel : MElemMod 3 6 F G) (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin 6) F (2 ^ n))
    (hrank : 3 ^ 3 ≤ (LargeEvenScalars (Fin 6) F).relIndex G)
    (R : Submodule F (Fin 6 → F)) (hR0 : R ≠ ⊥)
    (hRiso : ∀ u ∈ R, ∀ v ∈ R, ∑ i, (u i) ^ (2 ^ n) * v i = 0)
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin 6) (Fin 6) F).mulVec v ∈ R) :
    MToral 3 6 F G := by
  classical
  have hUF : UnitaryFieldData 2 n F := unitaryFieldData_two_of_card hF hn
  haveI : Module.Finite F R :=
    FiniteDimensional.of_injective (Submodule.subtype R) Subtype.coe_injective
  have hle3 : Module.finrank F R ≤ 3 := finrank_le_three_of_isotropic hUF hRiso
  have hrpos : 0 < Module.finrank F R := by
    by_contra h
    have h0 : Module.finrank F R = 0 := by omega
    exact hR0 (Submodule.finrank_eq_zero.mp h0)
  by_cases hr3 : Module.finrank F R = 3
  · exfalso
    exact uni_survivor_false_of_rank_three hF hn hpq hZG hel hGU hrank R hR0 hRiso hRG hUF hr3
  · have hr12 : Module.finrank F R = 1 ∨ Module.finrank F R = 2 := by omega
    refine ⟨?_, ?_⟩
    · intro g hg h hh
      obtain ⟨c, hc⟩ := hel.2 g hg h hh
      have hmem : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ G := hZG (scalar_mem_LES c)
      have hcomm : (⁅(⟨g, hg⟩ : ↥G), (⟨h, hh⟩ : ↥G)⁆ : ↥G) =
          ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hmem⟩ := by
        apply Subtype.ext
        simpa [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hc.symm
      have hdet : c ^ Module.finrank F R = 1 := by
        have h1 := restrictDet_commutator R G hRG (⟨g, hg⟩ : ↥G) (⟨h, hh⟩ : ↥G)
        rw [hcomm, restrictDet_scalar R G hRG hZG c] at h1
        exact h1
      have hc1 : c = 1 := by
        rcases hr12 with hr1 | hr2
        · rw [hr1, pow_one] at hdet; exact hdet
        · rw [hr2] at hdet
          have h2 : (c : F) ^ 2 = 1 := by
            have := congrArg Units.val hdet
            simpa [Units.val_pow_eq_pow_val] using this
          rcases sq_eq_one_iff.mp h2 with h | h
          · exact Units.ext h
          · exact Units.ext (by rw [h, CharTwo.neg_eq (1 : F), Units.val_one])
      have hone : ⁅g, h⁆ = 1 := by
        have hsub : (⟨⁅g, h⁆, hZG (hel.2 g hg h hh)⟩ : ↥G) = 1 := by
          rw [show (⟨⁅g, h⁆, hZG (hel.2 g hg h hh)⟩ : ↥G) =
              ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hmem⟩ from Subtype.ext hc.symm]
          subst hc1
          apply Subtype.ext
          simp
        exact congrArg Subtype.val hsub
      exact commutatorElement_eq_one_iff_mul_comm.mp hone
    · intro g hg
      obtain ⟨κ, hκ⟩ := hel.1 g hg
      let d : Fˣ := restrictDet R G hRG ⟨g, hg⟩
      have hdet3 : κ ^ Module.finrank F R = d ^ 3 := by
        have h1 : restrictDet R G hRG ⟨g ^ 3, G.pow_mem hg 3⟩ = d ^ 3 := by
          rw [show (⟨g ^ 3, G.pow_mem hg 3⟩ : ↥G) = (⟨g, hg⟩ : ↥G) ^ 3 from
            Subtype.ext (by simp), map_pow]
        have h2 : (⟨g ^ 3, G.pow_mem hg 3⟩ : ↥G) =
            ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) κ, hZG (scalar_mem_LES κ)⟩ :=
          Subtype.ext hκ.symm
        rw [h2, restrictDet_scalar R G hRG hZG κ] at h1
        exact h1
      obtain ⟨e, he⟩ : ∃ e : Fˣ, e ^ 3 = κ := by
        rcases hr12 with hr1 | hr2
        · rw [hr1, pow_one] at hdet3
          exact ⟨d, hdet3.symm⟩
        · rw [hr2] at hdet3
          refine ⟨κ * d⁻¹, ?_⟩
          have hd : d ^ 3 = κ ^ 2 := hdet3.symm
          calc (κ * d⁻¹) ^ 3 = κ ^ 3 * (d⁻¹) ^ 3 := by rw [mul_pow]
            _ = κ ^ 3 * (d ^ 3)⁻¹ := by rw [inv_pow]
            _ = κ ^ 3 * (κ ^ 2)⁻¹ := by rw [hd]
            _ = κ := by group
      refine ⟨e⁻¹, ?_⟩
      have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 6) e⁻¹) g :=
        Matrix.GeneralLinearGroup.scalar_commute e⁻¹ g
      rw [hcomm.mul_pow, ← map_pow, ← hκ, ← map_mul, inv_pow, he, inv_mul_cancel, map_one]


theorem uni_toral_of_rank {p n d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1)
    (hpd : p ∣ d) {G : Subgroup (GL (Fin d) F)} (hZG : LargeEvenScalars (Fin d) F ≤ G)
    (hel : MElemMod p d F G) (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    {T : Subgroup (GL (Fin d) F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTU : ∀ t ∈ T, t ∈ LargeEvenGUSet (Fin d) F (2 ^ n))
    (hGT : ∀ A ∈ G, A ∈ Subgroup.normalizer (T : Set (GL (Fin d) F)))
    (hrank : p ^ max 3 (d - 3) ≤ (LargeEvenScalars (Fin d) F).relIndex G) :
    MToral p d F G := by
  have hpF : p ∣ Nat.card F - 1 := by
    have h2 : Nat.card F - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [hF]
      have hsq := sq_tsub_sq (2 ^ n) 1
      rw [one_pow] at hsq
      rw [← hsq, sq]
    rw [h2]
    exact Dvd.dvd.mul_right hpq _
  rcases tor_dichotomy hp hp2 hpF hZG hel with h | ⟨-, hle⟩
  · exact h
  · have h1 : p ^ max 3 (d - 3) ≤ p ^ (d / p + 1) := hrank.trans hle
    have h2 : max 3 (d - 3) ≤ d / p + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    obtain ⟨k, hk⟩ := hpd
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hdk : d / p = k := by
      rw [hk]
      exact Nat.mul_div_cancel_left k hp.pos
    rw [hdk] at h2
    have h3 : 3 ≤ k + 1 := le_trans (le_max_left _ _) h2
    have h4 : d - 3 ≤ k + 1 := le_trans (le_max_right _ _) h2
    have hk2 : 2 ≤ k := by omega
    have hp3' : p = 3 := by
      by_contra hne
      have h4p : 4 ≤ p := by omega
      have h5 : 4 * k ≤ p * k := Nat.mul_le_mul_right k h4p
      omega
    have hk2' : k = 2 := by
      subst hp3'
      omega
    have hd6 : d = 6 := by
      rw [hk, hp3', hk2']
    subst hp3'
    subst hd6
    obtain ⟨R, hR0, hRiso, hRG⟩ := uni_isotropic_inv hF hn hT hT1 hTU hGU hGT
    have hrank' : 3 ^ 3 ≤ (LargeEvenScalars (Fin 6) F).relIndex G := by
      refine le_trans ?_ hrank
      norm_num
    exact uni_survivor hF hn hpq hZG hel hGU hrank' R hR0 hRiso hRG

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
