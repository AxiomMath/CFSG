module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal

structure TwinDatumOn (t : StatedLieTag) (M : LieUniversal) (R R' : Subgroup M.K)
    (x x' : M.K) : Prop where
  mem : R ∈ fundamentalSubgroups t M.D
  mem' : R' ∈ fundamentalSubgroups t M.D
  ne : R ≠ R'
  comm : Commutes R R'
  hx : x ∈ R
  hx' : x' ∈ R'
  cx : ∀ r ∈ R, x * r = r * x
  cx' : ∀ r ∈ R', x' * r = r * x'
  nx : x ≠ 1
  nx' : x' ≠ 1
  same : x * x'⁻¹ ∈ Subgroup.center M.K

@[expose] def TwinMFCommutantOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ (R R' : Subgroup M.K) (x x' : M.K), TwinDatumOn t M R R' x x' →
    ∀ R'' ∈ fundamentalSubgroups t M.D,
      (∀ S ∈ fundamentalSubgroups t M.D, Commutes S R → Commutes S R' → Commutes R'' S) →
        R'' = R ∨ R'' = R'

@[expose] def TwinMFCentralizingOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ (R R' : Subgroup M.K) (x x' : M.K), TwinDatumOn t M R R' x x' →
    ∀ a ∈ R, ∀ a' ∈ R', a * a * x⁻¹ ∈ Subgroup.center M.K →
      a' * a' * x'⁻¹ ∈ Subgroup.center M.K → ∀ S ∈ fundamentalSubgroups t M.D,
        (∀ s ∈ S, (a * a') * s = s * (a * a')) →
        ∃ g : M.K, g * (a * a') = (a * a') * g ∧
          Commutes (conjSub g S) R ∧ Commutes (conjSub g S) R'

@[expose] def TwinMFGenerationOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ (R R' : Subgroup M.K) (x x' : M.K), TwinDatumOn t M R R' x x' →
    ∀ a ∈ R, ∀ a' ∈ R', a * a * x⁻¹ ∈ Subgroup.center M.K →
      a' * a' * x'⁻¹ ∈ Subgroup.center M.K → ∀ S ∈ fundamentalSubgroups t M.D,
        S ≤ Subgroup.centralizer ({x} : Set M.K) ⊔ Subgroup.centralizer ({a * a'} : Set M.K) ⊔
          Subgroup.centralizer ({x * (a * a')} : Set M.K)

section Model

variable {p f : ℕ} [Fact p.Prime] {tY : StatedLieTag} {nY : ℕ}

theorem TwinDatum.toOn {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    {x x' : (modelUniv tY nY p f Fact.out).K} (h : TwinDatum p f tY nY R R' x x') :
    TwinDatumOn tY (modelUniv tY nY p f Fact.out) R R' x x' :=
  ⟨h.mem, h.mem', h.ne, h.comm, h.hx, h.hx', h.cx, h.cx', h.nx, h.nx', h.same⟩

theorem twinMFCommutant_of_on (h : TwinMFCommutantOn tY (modelUniv tY nY p f Fact.out)) :
    TwinMFCommutant p f tY nY :=
  fun R R' x x' hd R'' hR'' hc => h R R' x x' hd.toOn R'' hR'' hc

theorem twinMFCentralizing_of_on (h : TwinMFCentralizingOn tY (modelUniv tY nY p f Fact.out)) :
    TwinMFCentralizing p f tY nY :=
  fun R R' x x' hd a ha a' ha' hsq hsq' S hS hc => h R R' x x' hd.toOn a ha a' ha' hsq hsq' S hS hc

theorem twinMFGeneration_of_on (h : TwinMFGenerationOn tY (modelUniv tY nY p f Fact.out)) :
    TwinMFGeneration p f tY nY :=
  fun R R' x x' hd a ha a' ha' hsq hsq' S hS => h R R' x x' hd.toOn a ha a' ha' hsq hsq' S hS

end Model

end CFSG.ClassicalInvolution.RouteD.TwinY
