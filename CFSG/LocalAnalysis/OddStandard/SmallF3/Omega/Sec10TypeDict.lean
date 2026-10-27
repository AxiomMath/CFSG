module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  CFSG.ComponentClassification.CatFactsSmall.PSp43 QuadraticMap

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def centCount (a : P45) : ℕ :=
  ((elemsT QA45).filter fun g => decide (g * a = a * g)).length

@[expose] def InvCent (n : ℕ) (a : P45) : Prop :=
  a ∈ QA45.originalSubgroup ∧ a * a = 1 ∧ a ≠ 1 ∧ centCount a = n

namespace TyDict

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def indAut (hQ : Q.Nondegenerate) (ε : ↥L ≃* omegaProj hQ) :
    ProjOrth Q →* MulAut ↥L :=
  (MulAut.congr ε.symm).toMonoidHom.comp MulAut.conjNormal

theorem coe_eps_indAut (hQ : Q.Nondegenerate) (ε : ↥L ≃* omegaProj hQ) (y : ProjOrth Q)
    (l : ↥L) : ((ε (indAut hQ ε y l) : omegaProj hQ) : ProjOrth Q) =
      y * (ε l : ProjOrth Q) * y⁻¹ := by
  simp [indAut, MulAut.congr_apply, MulAut.conjNormal_apply]

theorem indAut_injective (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    (hσ : quadSign Q = 1) (ε : ↥L ≃* omegaProj hQ) : Function.Injective (indAut hQ ε) := by
  intro y y' h
  apply conjNormal_injective_five hQ hdim hσ
  ext w
  obtain ⟨l, rfl⟩ := ε.surjective w
  have h1 := congrArg (fun f : MulAut ↥L => ((ε (f l) : omegaProj hQ) : ProjOrth Q)) h
  simp only [coe_eps_indAut] at h1
  simp only [MulAut.conjNormal_apply]
  exact h1

variable (hL : IsPSp43 L) (F : PspFrame L)
  (hQ : Q.Nondegenerate) (ε : ↥L ≃* omegaProj hQ)

include hL in
theorem exists_conjOf (y : ProjOrth Q) :
    ∃ a ∈ QA45.originalSubgroup, ∀ l : ↥L, F.ψ (indAut hQ ε y l) = a * F.ψ l * a⁻¹ :=
  F.exists_conjA hL (indAut hQ ε y)

@[expose] noncomputable def conjOf (y : ProjOrth Q) : P45 :=
  Classical.choose (exists_conjOf hL F hQ ε y)

theorem conjOf_mem (y : ProjOrth Q) : conjOf hL F hQ ε y ∈ QA45.originalSubgroup :=
  (Classical.choose_spec (exists_conjOf hL F hQ ε y)).1

theorem psi_indAut (y : ProjOrth Q) (l : ↥L) :
    F.ψ (indAut hQ ε y l) = conjOf hL F hQ ε y * F.ψ l * (conjOf hL F hQ ε y)⁻¹ :=
  (Classical.choose_spec (exists_conjOf hL F hQ ε y)).2 l

theorem eq_conjOf {y : ProjOrth Q} {a : P45} (ha : a ∈ QA45.originalSubgroup)
    (h : ∀ l : ↥L, F.ψ (indAut hQ ε y l) = a * F.ψ l * a⁻¹) : a = conjOf hL F hQ ε y :=
  F.conjA_unique ha (conjOf_mem hL F hQ ε y) fun l => by rw [← h l, psi_indAut hL F hQ ε]

theorem conjOf_mul (y y' : ProjOrth Q) :
    conjOf hL F hQ ε (y * y') = conjOf hL F hQ ε y * conjOf hL F hQ ε y' := by
  symm
  apply eq_conjOf
  · exact QA45.originalSubgroup.mul_mem (conjOf_mem hL F hQ ε y) (conjOf_mem hL F hQ ε y')
  · intro l
    rw [map_mul, MulAut.mul_apply, psi_indAut hL F hQ ε y, psi_indAut hL F hQ ε y']
    group

theorem conjOf_one : conjOf hL F hQ ε (1 : ProjOrth Q) = 1 := by
  symm
  apply eq_conjOf
  · exact QA45.originalSubgroup.one_mem
  · intro l
    simp

@[expose] noncomputable def conjHom : ProjOrth Q →* P45 where
  toFun := conjOf hL F hQ ε
  map_one' := conjOf_one hL F hQ ε
  map_mul' := conjOf_mul hL F hQ ε

theorem conjHom_injective (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) :
    Function.Injective (conjHom hL F hQ ε) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : conjOf hL F hQ ε y = 1 := hy
  apply indAut_injective hQ hdim hσ ε
  rw [map_one]
  refine MulEquiv.ext fun l => F.ψ_injective ?_
  rw [psi_indAut hL F hQ ε y, h1]
  simp

theorem conjHom_range (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) :
    (conjHom hL F hQ ε).range = QA45.originalSubgroup := by
  have hinj := conjHom_injective hL F hQ ε hdim hσ
  have hle : (conjHom hL F hQ ε).range ≤ QA45.originalSubgroup := by
    rintro _ ⟨y, rfl⟩
    exact conjOf_mem hL F hQ ε y
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, natCard_projOrth_five hQ hdim,
    card_QA45]

theorem exists_conjOf_eq (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {a : P45}
    (ha : a ∈ QA45.originalSubgroup) : ∃ y : ProjOrth Q, conjOf hL F hQ ε y = a := by
  have h : a ∈ (conjHom hL F hQ ε).range := by
    rw [conjHom_range hL F hQ ε hdim hσ]
    exact ha
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

theorem natCard_centralizer_eq (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1)
    (y : ProjOrth Q) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set (ProjOrth Q))) =
      centCount (conjOf hL F hQ ε y) := by
  rw [centCount, ← card_inf_centralizer QA45 QA45_ok]
  have hinj := conjHom_injective hL F hQ ε hdim hσ
  have hrange := conjHom_range hL F hQ ε hdim hσ
  let f : ↥(Subgroup.centralizer ({y} : Set (ProjOrth Q))) →
      ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({conjOf hL F hQ ε y} : Set P45)) :=
    fun g => ⟨conjOf hL F hQ ε g, Subgroup.mem_inf.2 ⟨conjOf_mem hL F hQ ε g, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
      have h2 : conjHom hL F hQ ε (g * y) = conjHom hL F hQ ε (y * g) := congrArg _ h
      simp only [map_mul] at h2
      exact h2⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      apply Subtype.ext
      exact hinj (congrArg Subtype.val h)
    · rintro ⟨a, ha⟩
      obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.1 ha
      obtain ⟨g, hg⟩ := exists_conjOf_eq hL F hQ ε hdim hσ ha1
      refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.1 ha2
      rw [← hg] at h
      apply hinj
      show conjOf hL F hQ ε (g * y) = conjOf hL F hQ ε (y * g)
      rw [conjOf_mul, conjOf_mul]
      exact h
  exact Nat.card_congr (Equiv.ofBijective f hf)

end TyDict

end CFSG.OddStandard.SmallF3.Omega
