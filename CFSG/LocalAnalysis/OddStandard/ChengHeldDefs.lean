module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def cj {G : Type*} [Group G] (a b : G) : G := b⁻¹ * a * b

@[expose] def cm {G : Type*} [Group G] (a b : G) : G := a⁻¹ * b⁻¹ * a * b

structure Hyp (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop where
  setting : StandardSetting G A
  model : LieModel (A ⧸ center A) .PSL 3 2 2
  even : Even (Nat.card (center A))
  cyclic : ∀ R : Sylow 2 (centralizer (A : Set G)),
    IsCyclic (R : Subgroup (centralizer (A : Set G)))

structure HypBal (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop extends Hyp G A where
  balanced : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥

structure Datum {G : Type} [Group G] [Finite G] (A : Subgroup G) where
  q : G
  q_mem : q ∈ A
  q_cent : q ∈ centralizer (A : Set G)
  q_ord : orderOf q = 2
  X : Subgroup G
  X_sylow : IsSylowOf 2 X (normalizer (A : Set G))

namespace Datum

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)

@[expose] def S : Subgroup G := d.X ⊓ A

@[expose] def Q : Subgroup G := d.X ⊓ centralizer (A : Set G)

@[expose] def QS : Subgroup G := d.Q ⊔ d.S

end Datum

structure Frame4 {G : Type*} [Group G] (α : ℕ) (t pi tau mu lam ze xi : G) : Prop where
  t4 : t ^ 4 = 1
  pi2 : pi ^ 2 = 1
  tau4 : tau ^ 4 = 1
  mu2 : mu ^ 2 = 1
  lam2 : lam ^ 2 = 1
  ze2 : ze ^ 2 = 1
  xi2 : xi ^ 2 = 1
  tau_sq : tau ^ 2 = t ^ 2
  pi_tau : cm pi tau = 1
  pi_mu : cj pi mu = t ^ 2 * pi
  pi_lam : cj pi lam = t ^ 2 * pi
  pi_ze : cj pi ze = t ^ 2 * pi
  pi_mulam : cj pi (mu * lam) = pi
  pi_xi : cj pi xi = pi
  tau_xi : cj tau xi = t ^ 2 * tau
  tau_lam : cj tau lam = t ^ 2 * tau
  tau_ze : cj tau ze = t ^ 2 * tau
  tau_mu : cm tau mu = 1
  mu_lam : cm mu lam = 1
  ze_xi : cm ze xi = 1
  mu_xi : cm mu xi = pi * tau
  mu_ze : cm mu ze = t * pi
  lam_xi : cm lam xi = tau
  lam_ze : cm lam ze = t * t ^ (2 * α) * pi * tau

structure Frame2 {G : Type*} [Group G] (q pi tau mu lam ze xi : G) : Prop where
  ord : q ^ 2 = 1 ∧ pi ^ 2 = 1 ∧ tau ^ 2 = 1 ∧ mu ^ 2 = 1 ∧ lam ^ 2 = 1 ∧ ze ^ 2 = 1 ∧ xi ^ 2 = 1
  q_cent : ∀ x ∈ ({pi, tau, mu, lam, ze, xi} : Set G), q * x = x * q
  R1 : ∀ x ∈ ({pi, tau, mu, lam} : Set G), ∀ y ∈ ({pi, tau, mu, lam} : Set G), x * y = y * x
  R2 : ∀ x ∈ ({pi, tau, ze, xi} : Set G), ∀ y ∈ ({pi, tau, ze, xi} : Set G), x * y = y * x
  mu_xi : cm mu xi = pi * tau
  lam_xi : cm lam xi = tau
  mu_ze : cm mu ze = q * pi
  lam_ze : cm lam ze = q * pi * tau

inductive Kind | field | graph | unitary

@[expose] def Kind.Act {G : Type*} [Group G] (α : ℕ) :
    Kind → (t pi tau mu lam ze xi y : G) → Prop
  | .field, t, pi, tau, mu, lam, ze, xi, y =>
      if α = 0 then
        cj t y = t ∧ cj pi y = pi ∧ cj tau y = pi * tau ∧ cj mu y = t ^ 2 * lam ∧
        cj lam y = t ^ 2 * mu ∧ cj ze y = ze * xi ∧ cj xi y = xi
      else
        cj t y = t⁻¹ ∧ cj pi y = pi ∧ cj tau y = pi * tau ∧ cj mu y = t ^ 2 * lam ∧
        cj lam y = t ^ 2 * mu ∧ cj ze y = t ^ 2 * ze * xi ∧ cj xi y = xi
  | .graph, t, pi, tau, mu, lam, ze, xi, y =>
      if α = 0 then
        cj t y = t⁻¹ ∧ cj pi y = pi ∧ cj tau y = tau⁻¹ ∧ cj mu y = t ^ 2 * ze * xi ∧
        cj lam y = ze ∧ cj ze y = lam ∧ cj xi y = t ^ 2 * mu * lam
      else
        cj t y = t ∧ cj pi y = pi ∧ cj tau y = tau ∧ cj mu y = ze * xi ∧
        cj lam y = ze ∧ cj ze y = lam ∧ cj xi y = mu * lam
  | .unitary, t, pi, tau, mu, lam, ze, xi, y =>
      if α = 0 then
        cj t y = t⁻¹ ∧ cj pi y = pi ∧ cj tau y = pi * tau⁻¹ ∧ cj mu y = t ^ 2 * ze ∧
        cj lam y = ze * xi ∧ cj ze y = t ^ 2 * mu ∧ cj xi y = t ^ 2 * mu * lam
      else
        cj t y = t⁻¹ ∧ cj pi y = pi ∧ cj tau y = pi * tau ∧ cj mu y = t ^ 2 * ze ∧
        cj lam y = t ^ 2 * ze * xi ∧ cj ze y = t ^ 2 * mu ∧ cj xi y = mu * lam

@[expose] def Kind.Act2 {G : Type*} [Group G] :
    Kind → (q pi tau mu lam ze xi y : G) → Prop
  | .field, q, pi, tau, mu, lam, ze, xi, y =>
      cj q y = q ∧ cj pi y = pi ∧ cj tau y = pi * tau ∧ cj mu y = lam ∧ cj lam y = mu ∧
      cj ze y = ze * xi ∧ cj xi y = xi
  | .graph, q, pi, tau, mu, lam, ze, xi, y =>
      cj q y = q ∧ cj pi y = pi ∧ cj tau y = tau ∧ cj mu y = ze * xi ∧ cj lam y = ze ∧
      cj ze y = lam ∧ cj xi y = mu * lam
  | .unitary, q, pi, tau, mu, lam, ze, xi, y =>
      cj q y = q ∧ cj pi y = pi ∧ cj tau y = pi * tau ∧ cj mu y = ze ∧ cj lam y = ze * xi ∧
      cj ze y = mu ∧ cj xi y = mu * lam

structure Chart4 {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A) (α : ℕ) where
  t : G
  pi : G
  tau : G
  mu : G
  lam : G
  ze : G
  xi : G
  frame : Frame4 α t pi tau mu lam ze xi
  q_eq : d.q = t ^ 2
  t_mem : t ∈ d.Q ∧ t ∈ d.S
  mem : pi ∈ d.S ∧ tau ∈ d.S ∧ mu ∈ d.S ∧ lam ∈ d.S ∧ ze ∈ d.S ∧ xi ∈ d.S
  gen : Subgroup.closure ({t, pi, tau, mu, lam, ze, xi} : Set G) = d.S
  rep : Kind → Option G
  rep_mem : ∀ k y, rep k = some y → y ∈ d.X ∧ y ∉ d.QS ∧ k.Act α t pi tau mu lam ze xi y
  cover : ∀ y ∈ d.X, y ∉ d.QS → ∃ k y0, rep k = some y0 ∧ ∃ u ∈ d.QS, y = u * y0

structure Chart2 {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A) where
  pi : G
  tau : G
  mu : G
  lam : G
  ze : G
  xi : G
  frame : Frame2 d.q pi tau mu lam ze xi
  mem : pi ∈ d.S ∧ tau ∈ d.S ∧ mu ∈ d.S ∧ lam ∈ d.S ∧ ze ∈ d.S ∧ xi ∈ d.S ∧ d.q ∈ d.S
  gen : Subgroup.closure ({d.q, pi, tau, mu, lam, ze, xi} : Set G) = d.S
  rep : Kind → Option G
  rep_mem : ∀ k y, rep k = some y → y ∈ d.X ∧ y ∉ d.QS ∧ k.Act2 d.q pi tau mu lam ze xi y
  cover : ∀ y ∈ d.X, y ∉ d.QS → ∃ k y0, rep k = some y0 ∧ ∃ u ∈ d.QS, y = u * y0

namespace Chart4

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

@[expose] def kinds (c : Chart4 d α) : Set Kind := {k | (c.rep k).isSome}

@[expose] def V (c : Chart4 d α) : Subgroup G := Subgroup.closure ({d.q, c.pi, c.t * c.tau} : Set G)

@[expose] def W (c : Chart4 d α) : Subgroup G := d.S ⊓ centralizer (c.V : Set G)

end Chart4

end CFSG.OddStandard.ChengHeld
