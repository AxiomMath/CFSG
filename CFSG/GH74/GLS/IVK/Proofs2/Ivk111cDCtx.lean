module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDSemi
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDFrob
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section XTdef

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra (ZMod p) F] (W : Type) [AddCommGroup W]
  [Module (ZMod p) W]

@[expose] def XT : Type := F ⊗[ZMod p] W

instance : AddCommGroup (XT p F W) := inferInstanceAs (AddCommGroup (F ⊗[ZMod p] W))
instance : Module F (XT p F W) := inferInstanceAs (Module F (F ⊗[ZMod p] W))

variable {p F W}

@[expose] def xtEquiv : (F ⊗[ZMod p] W) ≃ₗ[F] XT p F W := LinearEquiv.refl F _

@[expose] noncomputable def repXT (σ : Representation (ZMod p) (SLm F) W) :
    Representation F (SLm F) (XT p F W) :=
  CFSG.Theory.Representation.extendScalars F σ

@[expose] noncomputable def xEquiv (σ : Representation (ZMod p) (SLm F) W) :
    (CFSG.Theory.Representation.extendScalars F σ).asModule ≃ₗ[MonoidAlgebra F (SLm F)]
      (repXT σ).asModule :=
  LinearEquiv.refl _ _

end XTdef

section StM

variable (F : Type) [Field F] [Finite F]

@[expose] def StM (A : ℕ) : Type := ↥(steinbergSub F F A)

noncomputable instance (A : ℕ) : AddCommGroup (StM F A) := inferInstanceAs (AddCommGroup ↥(steinbergSub F F A))
noncomputable instance (A : ℕ) : Module F (StM F A) := inferInstanceAs (Module F ↥(steinbergSub F F A))

instance (A : ℕ) : Finite (StM F A) := inferInstanceAs (Finite ↥(steinbergSub F F A))

instance (A : ℕ) : Module.Finite F (StM F A) := Module.Finite.of_finite

@[expose] noncomputable def stRep (A : ℕ) : Representation F (SLm F) (StM F A) :=
  steinbergRep F F A

@[expose] noncomputable def stEquiv (A : ℕ) :
    (steinbergRep F F A).asModule ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule :=
  LinearEquiv.refl _ _

end StM

section Ctx

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]

@[expose] noncomputable def frobF (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F] [CharP F p] :
    F ≃+* F :=
  RingEquiv.ofBijective (frobenius F p)
    ⟨frobenius_inj F p, Finite.surjective_of_injective (frobenius_inj F p)⟩

omit [Algebra (ZMod p) F] in
theorem frobF_apply (c : F) : frobF p F c = c ^ p := rfl

variable {W : Type} [AddCommGroup W] [Module (ZMod p) W]

@[expose] noncomputable def phiAdd : XT p F W ≃+ XT p F W :=
  AddEquiv.ofBijective (frobTensor (p := p) (F := F) W).toAddMonoidHom frobTensor_bijective

variable (σ : Representation (ZMod p) (SLm F) W)

@[expose] noncomputable def phiMod :
    (repXT σ).asModule ≃ₛₗ[
      ((gaTwist (G := SLm F) (frobF p F) : MonoidAlgebra F (SLm F) ≃+* MonoidAlgebra F (SLm F)) :
        MonoidAlgebra F (SLm F) →+* MonoidAlgebra F (SLm F))] (repXT σ).asModule :=
  semilinOfFrob (repXT σ) (repXT σ) (frobF p F) phiAdd
    (fun c x => frobTensor_smul c x)
    (fun g x => frobTensor_baseChange (σ g) x)

theorem phiMod_apply (x : (repXT σ).asModule) :
    xtEquiv.symm ((repXT σ).asModuleEquiv (phiMod σ x)) =
      frobTensor W (xtEquiv.symm ((repXT σ).asModuleEquiv x)) := rfl

omit [Algebra (ZMod p) F] in
theorem steinbergTheta {n : ℕ} (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) {A : ℕ} (hA : A < p ^ n) :
    Nonempty ((steinbergRep F F A).asModule ≃ₛₗ[
      ((gaTwist (G := SLm F) (frobF p F) : MonoidAlgebra F (SLm F) ≃+* MonoidAlgebra F (SLm F)) :
        MonoidAlgebra F (SLm F) →+* MonoidAlgebra F (SLm F))]
      (steinbergRep F F (rot p n A)).asModule) := by
  obtain ⟨Θ, hbij, hs, hg⟩ := ((hS p n (Fact.out) hp2 hn F hF).1 A hA).2.2.2.2
  exact ⟨semilinOfFrob (steinbergRep F F A) (steinbergRep F F (rot p n A)) (frobF p F)
    (AddEquiv.ofBijective Θ hbij) (fun c x => by simpa [frobF_apply] using hs c x)
    (fun g x => hg g x)⟩

theorem mix11cD_rot_lt {p : ℕ} (hp : 1 < p) {n : ℕ} (hn : 0 < n) {A : ℕ} (hA : A < p ^ n) :
    rot p n A < p ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h1 : A % p ^ m < p ^ m := Nat.mod_lt _ (by positivity)
  have h2 : A / p ^ m < p := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    simpa [pow_succ, mul_comm] using hA
  simp only [rot, Nat.succ_sub_one]
  calc (A % p ^ m) * p + A / p ^ m < (A % p ^ m) * p + p := by omega
    _ = (A % p ^ m + 1) * p := by ring
    _ ≤ p ^ m * p := Nat.mul_le_mul_right _ h1
    _ = p ^ (m + 1) := by ring

theorem map_phi_label {n : ℕ} (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule)
    {B : ℕ} (hB : B < p ^ n)
    (ι : N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F B).asModule) :
    Nonempty (N.map (phiMod σ).toLinearMap ≃ₗ[MonoidAlgebra F (SLm F)]
      (stRep F (rot p n B)).asModule) := by
  obtain ⟨Θ⟩ := steinbergTheta (p := p) (F := F) hS hp2 hn hF hB
  exact ⟨(twistTransport (R := MonoidAlgebra F (SLm F)) (gaTwist (G := SLm F) (frobF p F))
    (M := (repXT σ).asModule)
    (P := (steinbergRep F F B).asModule) (Q := (steinbergRep F F (rot p n B)).asModule)
    (phiMod σ) Θ N (ι.trans (stEquiv F B).symm)).trans (stEquiv F (rot p n B))⟩

omit [Algebra (ZMod p) F] [CharP F p] in
theorem stRep_simple {n : ℕ} (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) {A : ℕ} (hA : A < p ^ n) :
    IsSimpleModule (MonoidAlgebra F (SLm F)) (stRep F A).asModule := by
  have h := ((hS p n Fact.out hp2 hn F hF).1 A hA).1
  exact IsSimpleModule.congr (N := (steinbergRep F F A).asModule) (stEquiv F A).symm

end Ctx

end CFSG.GH74.GLS.Stage4.Rest
