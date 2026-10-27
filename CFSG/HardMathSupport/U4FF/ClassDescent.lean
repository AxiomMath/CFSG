module

public import CFSG.HardMathSupport.U4FF.ClassFrob
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFields

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso fixedSub)
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing matRepE matRepE_apply matRepE_isIrreducible
  repD finite_endRing)


@[expose] def Classif (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Prop :=
  ∀ (E : Type) [Field E] [CharP E 2] [Algebra K E] {V : Type} [AddCommGroup V] [Module E V]
    (σ : Representation E (SU4 K n) V), σ.IsIrreducible →
      ∃ l : Lbl n, Nonempty ((matRep (Tmod K l E)).Equiv σ)

section Label

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem ambRepF_eq_one_of_nil (k : Type) [Field k] (fs : List FK) (hfs : fs = [])
    (g : Matrix.SpecialLinearGroup (Fin 4) k) : ambRepF k fs g = 1 := by
  subst hfs
  have h1 : ambDim ([] : List FK) = 1 := Finset.prod_eq_one fun i _ => Fin.elim0 i
  ext x y
  have hxy : x = y := Fin.ext (by have := x.isLt; have := y.isLt; omega)
  subst hxy
  rw [Matrix.one_apply_eq, ambRepF_apply, Matrix.submatrix_apply, ambRep_apply, kronDep_apply]
  exact Finset.prod_eq_one fun i _ => Fin.elim0 i

private theorem locR_zero_weight (k : Type) [Field k] [CharP k 2] (a b c : Bool)
    (ha : a = false) (hb : b = false) (hc : c = false)
    (g : Matrix.SpecialLinearGroup (Fin 4) k) : locR a b c k g = 1 := by
  subst ha hb hc
  rw [locR_apply]
  unfold LocSpec.locMat
  rw [ambRepF_eq_one_of_nil k (fsOf false false false) rfl g, Matrix.one_mul]
  exact (locSpec false false false (locValid false false false).1).Pmk_Bk k

private theorem repEquiv_apply_u4 {k G V W : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] {ρ₁ : Representation k G V}
    {σ : Representation k G W} (φ : ρ₁.Equiv σ) (g : G) (v : V) : φ (ρ₁ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ₁ σ φ.toIntertwiningMap g v

theorem card_TIdx (l : Lbl n) : Fintype.card (TIdx l) = l.dim := by
  simp only [TIdx, Lbl.dim, Fintype.card_pi, Fintype.card_fin]

theorem Tmod_isZero (l : Lbl n) (hl : l.IsZero) (k : Type) [Field k] [CharP k 2] [Algebra K k]
    (g : SU4 K n) : Tmod K l k g = 1 := by
  have hz : ∀ i : Fin n, locR (l.a i) (l.b i) (l.c i) k (twistHom n (frobTw K k i) g) =
      (1 : Matrix (Fin (locM (l.a i) (l.b i) (l.c i))) (Fin (locM (l.a i) (l.b i) (l.c i))) k) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hl i
    exact locR_zero_weight k (l.a i) (l.b i) (l.c i) h1 h2 h3 _
  rw [Tmod_eq, TmodΦ_apply]
  simp only [hz]
  exact kronDep_one

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) (SU4 K n) W} [Fact ρ.IsIrreducible]

@[expose] noncomputable def u4MatHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type} [Field E] (ι : EndRing ρ →+* E) : SU4 K n →* Matrix (Fin m) (Fin m) E :=
  matMap ι (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b)

theorem u4MatHomE_apply {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) (g : SU4 K n) :
    u4MatHomE b ι g = (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ι := rfl

theorem matRep_u4MatHomE {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E]
    (ι : EndRing ρ →+* E) : matRep (u4MatHomE b ι) = matRepE b ι := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [matRep_apply, matRepE_apply, u4MatHomE_apply]

theorem u4_exists_label (hC : Classif K n) (hnt : ∃ g, ρ g ≠ 1) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [CharP E 2] (ιK : K →+* E)
    (ιD : EndRing ρ →+* E) :
    ∃ l : Lbl n, ¬ l.IsZero ∧
      (letI := ιK.toAlgebra
       Nonempty ((matRep (Tmod K l E)).Equiv (matRepE b ιD))) ∧ m = l.dim := by
  classical
  let _ : Algebra K E := ιK.toAlgebra
  have hirr := matRepE_isIrreducible b ιD
  obtain ⟨l, ⟨Φ⟩⟩ := hC E (matRepE b ιD) hirr
  have hdimE : m = l.dim := by
    have h1 := Φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, card_TIdx] at h1
    exact h1.symm
  refine ⟨l, fun h0 => ?_, ⟨Φ⟩, hdimE⟩
  obtain ⟨g, hg⟩ := hnt
  apply hg
  have hid : ∀ x, matRepE b ιD g x = x := by
    intro x
    have h1 := repEquiv_apply_u4 Φ g (Φ.symm x)
    rw [Representation.Equiv.apply_symm_apply] at h1
    rw [← h1, matRep_apply, Tmod_isZero l h0 E g, Matrix.one_mulVec,
      Representation.Equiv.apply_symm_apply]
  have hmat : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    have := hid x
    rw [matRepE_apply] at this
    simpa [Matrix.toLin'_apply] using this
  have hmat' : CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g = 1 := by
    have : (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD =
        (1 : Matrix (Fin _) (Fin _) (EndRing ρ)).map ιD := by
      rw [hmat, Matrix.map_one ιD (map_zero ιD) (map_one ιD)]
    exact Matrix.map_injective ιD.injective this
  have hrep : repD ρ g = 1 := by
    apply (LinearMap.toMatrix b b).injective
    rw [show LinearMap.toMatrix b b (repD ρ g) =
      CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g from rfl, hmat', LinearMap.toMatrix_one]
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun φ : Module.End (EndRing ρ) W => φ w) hrep
  have h2 : repD ρ g w = w := by simpa using h1
  exact h2

theorem u4_descent (hC : Classif K n) (hK : Nat.card K = (2 ^ n) ^ 2) (hnt : ∃ g, ρ g ≠ 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card (EndRing ρ) = 2 ^ d ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W,
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (ιK : K →+* E)
        (ιD : EndRing ρ →+* E) (l : Lbl n), ¬ l.IsZero ∧
        (letI := ιK.toAlgebra
         Nonempty ((matRep (Tmod K l E)).Equiv (matRepE b ιD))) ∧
        2 ^ d * l.e1 ≡ l.e1 [MOD (2 ^ n) ^ 2 - 1] ∧ 2 ^ d * l.e2 ≡ l.e2 [MOD 2 ^ n - 1] ∧
        Module.finrank (EndRing ρ) W = l.dim := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (ZMod 2) (EndRing ρ) := Module.Finite.of_finite
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank (ZMod 2) (EndRing ρ) = d := ⟨_, rfl⟩
  have hDcard : Nat.card (EndRing ρ) = 2 ^ d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ)
    rw [hd, Nat.card_zmod] at this
    exact this
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      have h1 : Nat.card (EndRing ρ) = 1 := by rw [hDcard]; rfl
      have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
      omega
    · exact h
  refine ⟨d, hd1, hDcard, fun b => ?_⟩
  have : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hn : 1 ≤ n := by
    by_contra h0
    have h00 : n = 0 := by omega
    have h1 : Nat.card K = 1 := by simp [hK, h00]
    have h2 := Finite.one_lt_card (α := K)
    omega
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, E, hEF, hEfin, hEchar, ιK, ιD, -, -, -, -, -, -, -, hfrobD, -⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.finite_fields_common_extension 2
      (by omega : 1 ≤ 2 * n) hd1 hK' hDcard
  let _ : Algebra K E := ιK.toAlgebra
  obtain ⟨l, hl0, ⟨Φ⟩, hdimW⟩ := u4_exists_label hC hnt b ιK ιD
  have hmod : 2 ^ d * l.e1 ≡ l.e1 [MOD (2 ^ n) ^ 2 - 1] ∧
      2 ^ d * l.e2 ≡ l.e2 [MOD 2 ^ n - 1] := by
    refine e_modEq_of_frob E hK (u4MatHomE b ιD) d (fun g => ?_)
      (Φ.trans (Representation.Equiv.mk (LinearEquiv.refl E _) (fun g => ?_)))
    · ext i j
      rw [Matrix.map_apply, u4MatHomE_apply, Matrix.map_apply, iterateFrobenius_def]
      exact hfrobD _
    · rw [matRep_u4MatHomE]
      rfl
  exact ⟨E, hEF, hEfin, hEchar, ιK, ιD, l, hl0, ⟨Φ⟩, hmod.1, hmod.2, hdimW⟩

end Label

end CFSG.HardMathSupport.U4FF
