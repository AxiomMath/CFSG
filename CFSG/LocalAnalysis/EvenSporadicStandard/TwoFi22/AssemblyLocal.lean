module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fusion
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerPoints

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.Fischer

variable {G : Type} [Group G] {t : G}

theorem psi_mem_starSet (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε) {x : G}
    (hx : x ∈ LocalClass {g : G | IsConj t g} t) :
    M.ψ ⟨x, mem_centralizer_singleton_iff.2 hx.2.2⟩ ∈ starSet ε :=
  (hε _).1 ⟨hx.1, hx.2.1⟩

theorem orderOf_mul_mem (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε) :
    ∀ x ∈ LocalClass {g : G | IsConj t g} t, ∀ y ∈ LocalClass {g : G | IsConj t g} t,
      orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
  intro x hx y hy
  obtain ⟨z₁, hz₁, z₂, hz₂, hzz⟩ := starSet_mul_two (psi_mem_starSet M hε hx)
    (psi_mem_starSet M hε hy)
  have h1 : orderOf (x * y) = orderOf (z₁ * z₂) := by
    rw [← hzz, ← map_mul, orderOf_injective M.ψ M.inj]
    exact Subgroup.orderOf_coe (⟨x, mem_centralizer_singleton_iff.2 hx.2.2⟩ *
      ⟨y, mem_centralizer_singleton_iff.2 hy.2.2⟩ : centralizer ({t} : Set G))
  rw [h1]
  exact pair_J.2.2.2.1 z₁ hz₁.1 z₂ hz₂.1

@[expose] noncomputable def psiStar (M : Model G t)
    (x : LocalClass {g : G | IsConj t g} t) : J :=
  M.ψ ⟨x.1, mem_centralizer_singleton_iff.2 x.2.2.2⟩

theorem psiStar_comm_d (M : Model G t) (x : LocalClass {g : G | IsConj t g} t) :
    psiStar M x * d = d * psiStar M x :=
  psi_comm_d M _

@[expose] noncomputable def starMap (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε)
    (x : LocalClass {g : G | IsConj t g} t) : LocalClass D23 d :=
  ⟨twist ε (psiStar M x), by
    obtain ⟨z, hz, hzx⟩ := psi_mem_starSet M hε x.2
    change twist ε (M.ψ ⟨x.1, _⟩) ∈ _
    rw [← hzx, twist_twist]
    exact hz⟩

theorem starMap_val (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε)
    (x : LocalClass {g : G | IsConj t g} t) :
    (starMap M hε x : J) = twist ε (psiStar M x) := rfl

theorem starMap_injective (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε) :
    Function.Injective (starMap M hε) := by
  intro x x' h
  have h1 := twist_injective ε (congrArg Subtype.val h)
  have h2 := M.inj h1
  exact Subtype.ext (congrArg (fun z : centralizer ({t} : Set G) => (z : G)) h2)

theorem starMap_surjective (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε) :
    Function.Surjective (starMap M hε) := by
  intro y
  have hy : twist ε y.1 ∈ starSet ε := ⟨y.1, y.2, rfl⟩
  obtain ⟨v, hv⟩ := (M.range _).1 (starSet_comm_d hy)
  have hvD : v ∈ Dt t := (hε v).2 (by rw [hv]; exact hy)
  refine ⟨⟨(v : G), hvD.1, hvD.2, mem_centralizer_singleton_iff.1 v.2⟩, ?_⟩
  apply Subtype.ext
  rw [starMap_val]
  change twist ε (M.ψ v) = y.1
  rw [hv, twist_twist]

@[expose] noncomputable def starEquiv (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε) :
    LocalClass {g : G | IsConj t g} t ≃ LocalClass D23 d :=
  Equiv.ofBijective (starMap M hε) ⟨starMap_injective M hε, starMap_surjective M hε⟩

set_option maxRecDepth 100000 in
theorem psiStar_mul_comm (M : Model G t) (x y : LocalClass {g : G | IsConj t g} t) :
    x.1 * y.1 = y.1 * x.1 ↔ psiStar M x * psiStar M y = psiStar M y * psiStar M x := by
  have e : ∀ a b : LocalClass {g : G | IsConj t g} t,
      psiStar M a * psiStar M b =
        M.ψ (⟨a.1, mem_centralizer_singleton_iff.2 a.2.2.2⟩ *
          ⟨b.1, mem_centralizer_singleton_iff.2 b.2.2.2⟩) := fun a b => by
    rw [map_mul]
    rfl
  constructor
  · intro h
    rw [e x y, e y x]
    exact congrArg M.ψ (Subtype.ext h)
  · intro h
    rw [e x y, e y x] at h
    exact congrArg (fun z : centralizer ({t} : Set G) => (z : G)) (M.inj h)

theorem starMap_mul_comm (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε)
    (x y : LocalClass {g : G | IsConj t g} t) :
    x.1 * y.1 = y.1 * x.1 ↔
      (starMap M hε x : J) * starMap M hε y = starMap M hε y * starMap M hε x := by
  rw [psiStar_mul_comm M, starMap_val, starMap_val, twist_mul_twist ε (psiStar_comm_d M x),
    twist_mul_twist ε (psiStar_comm_d M y)]

set_option maxRecDepth 100000 in
theorem psiStar_tau (M : Model G t) (x y : LocalClass {g : G | IsConj t g} t)
    (h : x.1 * y.1 * x.1 ∈ LocalClass {g : G | IsConj t g} t) :
    psiStar M ⟨x.1 * y.1 * x.1, h⟩ = psiStar M x * psiStar M y * psiStar M x := by
  unfold psiStar
  rw [← map_mul, ← map_mul]
  rfl

set_option maxRecDepth 100000 in
theorem starMap_tau (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε)
    (x y : LocalClass {g : G | IsConj t g} t)
    (h : x.1 * y.1 * x.1 ∈ LocalClass {g : G | IsConj t g} t) :
    (starMap M hε ⟨x.1 * y.1 * x.1, h⟩ : J) =
      (starMap M hε x : J) * starMap M hε y * starMap M hε x := by
  show twist ε (psiStar M ⟨x.1 * y.1 * x.1, h⟩) =
    twist ε (psiStar M x) * twist ε (psiStar M y) * twist ε (psiStar M x)
  rw [psiStar_tau]
  exact (twist_mul_three ε (psiStar_comm_d M x) (psiStar_comm_d M y)).symm

theorem nonempty_localPoints_J :
    Nonempty (LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) D23 d) :=
  CFSG.Sporadic.Fi22.F23.nonempty_localPoints_fi22 polarFacts f23_J (IsConj.refl d)

set_option maxRecDepth 100000 in
@[expose] noncomputable def localPointsT (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε)
    (Lj : LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) D23 d) :
    LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) {g : G | IsConj t g} t where
  χ := (starEquiv M hε).trans Lj.χ
  comm f g := by
    rw [starMap_mul_comm M hε f g]
    exact Lj.comm (starEquiv M hε f) (starEquiv M hε g)
  tau f g h := by
    have e := starMap_tau M hε f g h
    have h' : (starEquiv M hε f : J) * starEquiv M hε g * starEquiv M hε f ∈
        LocalClass D23 d := by
      change (starMap M hε f : J) * starMap M hε g * starMap M hε f ∈ _
      rw [← e]
      exact (starMap M hε ⟨_, h⟩).2
    have key := Lj.tau (starEquiv M hε f) (starEquiv M hε g) h'
    have hsub : starEquiv M hε ⟨f.1 * g.1 * f.1, h⟩ =
        ⟨(starEquiv M hε f : J) * starEquiv M hε g * starEquiv M hε f, h'⟩ := Subtype.ext e
    show Lj.χ (starEquiv M hε ⟨f.1 * g.1 * f.1, h⟩) =
      (pairModel CFSG.Sporadic.Fi22.pair_D).tv (Lj.χ (starEquiv M hε f))
        (Lj.χ (starEquiv M hε g))
    rw [hsub]
    exact key

theorem nonempty_localPoints (M : Model G t) {ε : Bool}
    (hε : ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε)
    (Lj : LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) D23 d) :
    ∀ f ∈ {g : G | IsConj t g},
      Nonempty (LocalPoints (pairModel CFSG.Sporadic.Fi22.pair_D) {g : G | IsConj t g} f) := by
  intro f hf
  obtain ⟨g, rfl⟩ := isConj_iff.1 hf
  exact ⟨CFSG.EvenSmallLie.UnitarySix.Fischer.localPointsConj
    (fun g' x hx => IsConj.trans hx (isConj_iff.2 ⟨g', rfl⟩)) (localPointsT M hε Lj) g⟩

end CFSG.EvenSporadicStandard.TwoFi22
