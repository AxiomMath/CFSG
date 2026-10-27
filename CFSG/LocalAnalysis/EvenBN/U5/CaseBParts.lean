module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBDiagonal

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

@[expose] def Nc (c : d.CaseBData) : Subgroup G :=
  c.Kc ⊔ c.Kc.map (MulAut.conj d.s).toMonoidHom

@[expose] def Nt (c : d.CaseBData) : Subgroup G := c.Nc.map (MulAut.conj d.t).toMonoidHom

@[expose] def Hc (c : d.CaseBData) : Subgroup G := c.Nc ⊔ c.Nt

@[expose] def Qt (c : d.CaseBData) : Subgroup G := c.Qc.map (MulAut.conj d.t).toMonoidHom

@[expose] def W₂t (c : d.CaseBData) : Subgroup G := c.W₂.map (MulAut.conj d.t).toMonoidHom

variable (hB : d.CaseBHyp) (c : d.CaseBData)

structure Sec52Sylow : Prop where
  S_eq : c.S = c.Qc ⊔ c.Qt
  map_δ : (c.Qc.subgroupOf c.Kc).map (c.δ hB) = d.P
  V_eq : d.V = CFSG.centerIn c.Qc ⊔ CFSG.centerIn c.Qt

structure Sec52Factors : Prop where
  E_eq : d.E = c.W₂ ⊔ c.W₂t
  inf_eq_bot : c.W₂ ⊓ c.W₂t = ⊥
  map_δ : (c.W₂.subgroupOf c.Kc).map (c.δ hB) = d.A₂

@[expose] def Sec52Comm : Prop :=
  c.Kc.map (MulAut.conj (d.s * d.t)).toMonoidHom ≤ centralizer (c.Kc : Set G)

structure Sec52 : Prop where
  quasisimple : CFSG.Open.IsQuasisimple c.Nc
  odd_center : Odd (Nat.card (center c.Nc))
  commute : c.Nc.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (c.Nc : Set G)
  diag_mem : ∀ x ∈ c.Nc, x * (d.t * x * d.t⁻¹) ∈ d.L
  diag_surj : ∀ y ∈ d.L, ∃ x ∈ c.Nc, x * (d.t * x * d.t⁻¹) = y
  iso : Nonempty (c.Nc ⧸ center c.Nc ≃* hypPSU h 2 1)

end CaseBData

end Data

namespace CaseBParts

open Data

@[expose] def Sec52SylowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52Sylow hB c

@[expose] def Sec52FactorsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52Sylow hB c → CaseBData.Sec52Factors hB c

@[expose] def Sec52SInvStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52Sylow hB c → CaseBData.Sec52Factors hB c →
    c.W₂.map (MulAut.conj d.s).toMonoidHom = c.W₂

@[expose] def Sec52GenStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52Sylow hB c → CaseBData.Sec52Factors hB c →
    c.W₂.map (MulAut.conj d.s).toMonoidHom = c.W₂ →
    c.Kc = c.W₂ ⊔ (c.W₂ ⊓ c.W₂.map (MulAut.conj d.r).toMonoidHom).map
      (MulAut.conj (d.r * d.s)).toMonoidHom

@[expose] def Sec52CommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52Sylow hB c → CaseBData.Sec52Factors hB c →
    c.W₂.map (MulAut.conj d.s).toMonoidHom = c.W₂ →
    c.Kc = c.W₂ ⊔ (c.W₂ ⊓ c.W₂.map (MulAut.conj d.r).toMonoidHom).map
      (MulAut.conj (d.r * d.s)).toMonoidHom →
    CaseBData.Sec52Comm c

@[expose] def Sec52Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52Comm c → CaseBData.Sec52 c

@[expose] def HGenStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52Sylow hB c → CaseBData.Sec52 c → c.Hc = d.L ⊔ d.V

@[expose] def NormalizerTPStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.CaseBHyp →
    normalizer (d.tP : Set G) ≤ normalizer ((d.L ⊔ d.V : Subgroup G) : Set G)

@[expose] def PerfectNormalizerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52 c → ∀ H : Subgroup G, H ≤ normalizer (c.Hc : Set G) → ⁅H, H⁆ = H → H ≤ c.Hc

@[expose] def InvolutoryFixedElemAbStatement : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 2 ≤ f →
    ∀ θ : MulAut (hypPSU h 2 1), θ * θ = 1 →
      ∃ E : Subgroup (hypPSU h 2 1), CFSG.IsElementaryAbelian 2 E ∧ (∀ x ∈ E, θ x = x) ∧
        (2 ^ f) ^ 3 ≤ Nat.card E

@[expose] def NonSwapStatement : Prop :=
  InvolutoryFixedElemAbStatement →
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h) (hB : d.CaseBHyp) (c : d.CaseBData),
    CaseBData.Sec52 c → ∀ g : G, d.t ∈ normalizer ((c.Nc.map (MulAut.conj g).toMonoidHom : Subgroup G) :
        Set G) →
      d.t ∈ normalizer (((c.Nt).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
