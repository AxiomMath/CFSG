module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V1
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section GenericOdd

variable {Γ : Type*} [Group Γ]

@[expose] def oddCoreSub (K : Subgroup Γ) : Subgroup Γ :=
  (standardComponentOddCore ↥K).map K.subtype

end GenericOdd

section Vocab

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Xg (d : Data G) : Subgroup G := zpowers d.x₅

@[expose] noncomputable def CQ2X (d : Data G) : Subgroup G :=
  d.s56Q2 ⊓ centralizer ((Xg d : Subgroup G) : Set G)

@[expose] noncomputable def sylT (d : Data G) : Subgroup G :=
  (((Model.parrottU 1).subgroupOf titsA).comap d.ρ).map (centralizer ({d.t} : Set G)).subtype

@[expose] def IsV5 (d : Data G) (y : G) : Prop :=
  ∃ hy : y ∈ centralizer ({d.t} : Set G),
    (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 5

@[expose] def IsV1 (d : Data G) (z₀ y₁ : G) : Prop :=
  y₁ ∈ sylT d ∧ y₁ * z₀ = z₀ * y₁ ∧
    ∃ hy : y₁ ∈ centralizer ({d.t} : Set G),
      (d.ρ ⟨y₁, hy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 1 ∨
        (d.ρ ⟨y₁, hy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 1 * Model.parrottV 5

@[expose] def IsY (d : Data G) (y : G) : Prop :=
  y ∈ d.N ⊓ d.L ∧ orderOf y = 3 ∧ y * d.pv 10 = d.pv 10 * y

@[expose] noncomputable def P11 (d : Data G) : Subgroup G := centralizerMod d.s56P d.s56U11 d.B

@[expose] noncomputable def Pe11 (d : Data G) : Subgroup G := ⁅P11 d, d.N⁆

@[expose] noncomputable def P1 (d : Data G) : Subgroup G :=
  d.s56P ⊓ centralizer ((Pe11 d : Subgroup G) : Set G)

@[expose] noncomputable def Pe10 (d : Data G) : Subgroup G :=
  centralizerMod (P1 d) d.s56U10 (zpowers d.t)

@[expose] noncomputable def Hg (d : Data G) : Subgroup G := normalizer (d.s56V : Set G)

@[expose] noncomputable def Cv (d : Data G) : Subgroup G := centralizer (d.s56V : Set G)

@[expose] noncomputable def star (d : Data G) (g : G) : MulAut ↥d.s56V := actFun d.s56V g

@[expose] noncomputable def img (d : Data G) (K : Subgroup G) : Subgroup (MulAut ↥d.s56V) :=
  imgIn d.s56V K

@[expose] noncomputable def pre (d : Data G) (K : Subgroup (MulAut ↥d.s56V)) : Subgroup G :=
  preIn d.s56V K

@[expose] noncomputable def Hs (d : Data G) : Subgroup (MulAut ↥d.s56V) := img d (Hg d)

@[expose] noncomputable def CMt (d : Data G) : Subgroup G := d.M ⊓ centralizer ({d.t} : Set G)

@[expose] noncomputable def Us (d : Data G) : Subgroup (MulAut ↥d.s56V) :=
  ⁅img d (pCoreOf 2 (CMt d)), img d (Xg d)⁆

@[expose] noncomputable def U0s (d : Data G) : Subgroup (MulAut ↥d.s56V) :=
  Us d ⊔ zpowers (star d d.t)

@[expose] noncomputable def Ks (d : Data G) : Subgroup (MulAut ↥d.s56V) :=
  normalizer ((U0s d : Subgroup _) : Set (MulAut ↥d.s56V)) ⊓ Hs d

@[expose] noncomputable def W0s (d : Data G) : Subgroup (MulAut ↥d.s56V) := pCoreOf 2 (Ks d)

@[expose] noncomputable def Ws (d : Data G) : Subgroup (MulAut ↥d.s56V) :=
  ⁅W0s d, img d (Xg d)⁆

@[expose] noncomputable def Is (d : Data G) : Subgroup (MulAut ↥d.s56V) :=
  normalizer ((Ws d : Subgroup _) : Set (MulAut ↥d.s56V)) ⊓ Hs d

@[expose] noncomputable def Kg (d : Data G) : Subgroup G := pre d (Ks d)

@[expose] noncomputable def Ig (d : Data G) : Subgroup G := pre d (Is d)

@[expose] noncomputable def Ialpha (d : Data G) : Subgroup (MulAut ↥(Ws d)) := imgIn (Ws d) (Is d)

@[expose] noncomputable def Zz (d : Data G) (z₀ : G) : Subgroup G := zpowers d.z ⊔ zpowers z₀

@[expose] noncomputable def H0 (d : Data G) (z₀ : G) : Subgroup G :=
  Hg d ⊓ centralizer ((Zz d z₀ : Subgroup G) : Set G)

@[expose] noncomputable def Wg (d : Data G) (z₀ : G) : Subgroup G :=
  pre d (W0s d) ⊓ centralizer ({z₀} : Set G)

@[expose] noncomputable def Jg (d : Data G) : Subgroup G :=
  (normalClosure (((Xg d).subgroupOf (Hg d) : Subgroup ↥(Hg d)) : Set ↥(Hg d))).map
    (Hg d).subtype

@[expose] noncomputable def Jp (d : Data G) : Subgroup G := pre d (img d (Jg d))

@[expose] def IsS (d : Data G) (S : Subgroup G) : Prop :=
  fusionIsSylowIn 2 S (Ig d) ∧ sylT d ≤ S

@[expose] noncomputable def Ug (d : Data G) : Subgroup G := pre d (Us d)

@[expose] noncomputable def U0g (d : Data G) : Subgroup G := pre d (U0s d)

@[expose] def DeltaS (d : Data G) : Set (MulAut ↥d.s56V) :=
  {x | x ∈ U0s d ∧ ∃ h ∈ Hg d, star d (h * d.t * h⁻¹) = x}

@[expose] def InAH (d : Data G) (s : G) : Prop :=
  ∃ h ∈ Hg d, zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) =
    d.A.map (MulAut.conj h).toMonoidHom

@[expose] def StarConj (d : Data G) (s : G) : Prop :=
  ∃ h ∈ Hg d, star d (h * d.t * h⁻¹) = star d s

@[expose] noncomputable def alpha (d : Data G) (g : G) : MulAut ↥(Ws d) :=
  actFun (Ws d) (star d g)

@[expose] noncomputable def Alpha (d : Data G) (K : Subgroup G) : Subgroup (MulAut ↥(Ws d)) :=
  imgIn (Ws d) (img d K)

@[expose] noncomputable def Ja (d : Data G) : Subgroup (MulAut ↥(Ws d)) :=
  (normalClosure (((Alpha d (Xg d)).subgroupOf (Ialpha d) : Subgroup ↥(Ialpha d)) :
    Set ↥(Ialpha d))).map (Ialpha d).subtype

end Vocab

section Props

variable {G : Type} [Group G] [Finite G]

@[expose] def Node05 (d : Data G) (z₀ : G) : Prop :=
  (d.ρ.range = titsD.subgroupOf titsA → d.s56Q0 = d.s56Q ⊔ zpowers d.t) ∧
  (∀ y, IsV5 d y → d.s56Q0 = d.s56Q ⊔ zpowers d.t ⊔ zpowers y) ∧
  d.N.relIndex d.s56Q0 = 2 ∧
  fusionIsSylowIn 2 (d.s56Q0 ⊔ sylT d) d.M ∧ d.N.relIndex (d.s56Q0 ⊔ sylT d) = 2 ∧
  ⁅d.s56Q, CQ2X d⁆ ≤ d.E ∧
  d.s56Q0 = d.s56Q ⊔ CQ2X d ∧
  d.s56Q ⊓ (CQ2X d ⊔ d.E) = d.E ⊔ zpowers z₀ ∧
  (d.ρ.range = titsD.subgroupOf titsA → IsElemAbQuot (CQ2X d ⊔ d.E) d.E 2) ∧
  (d.ρ.range = ⊤ → IsElemAbQuot (CQ2X d ⊔ d.E) d.E 3) ∧
  Nat.card d.s56Q = 2 ^ 14 ∧
  centralizerMod d.s56Q d.E d.s56Q = d.E ⊔ zpowers z₀ ∧
  ⁅d.s56Q, d.s56Q⁆ ⊔ d.E = d.E ⊔ zpowers z₀

@[expose] def Node06 (d : Data G) (z₀ : G) : Prop :=
  Nat.card d.s56V = 2 ^ 10 ∧ d.M ≤ normalizer (d.s56V : Set G) ∧ d.E ≤ d.s56V ∧
    z₀ ∈ d.s56V ∧ (∀ s ∈ d.E ⊔ zpowers z₀, ∀ v ∈ d.s56V, s * v = v * s) ∧
    (∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b * a⁻¹ * b⁻¹ ∈ zpowers d.z) ∧
    (z₀ * z₀ = 1 → ∀ v ∈ d.s56V, v * v ∈ zpowers d.z) ∧
    (z₀ * z₀ = d.z → ∀ v ∈ d.s56V, v * v * d.s56Eps v ∈ zpowers d.z) ∧
    ((∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) ∨
      ∀ v ∈ d.s56V, ((∀ w ∈ d.s56V, v * w = w * v) ↔ v ∈ d.E ⊔ zpowers z₀)) ∧
    ((∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a) → z₀ * z₀ = 1 → ∀ v ∈ d.s56V, v * v = 1)

@[expose] def Node07 (d : Data G) : Prop :=
  (∃ y, IsY d y) ∧
  (∀ y, IsY d y → zpowers d.z ⊔ zpowers (y * d.z * y⁻¹) = d.s56U11) ∧
  d.s56U11 = d.F ⊓ centralizer (d.s56P0 : Set G) ∧
  d.s56P0 = d.N ⊓ centralizer (d.s56U11 : Set G) ∧
  (∀ n ∈ d.N, ∀ u ∈ d.s56U10, n * u * n⁻¹ ∈ d.s56U10) ∧
  ((d.s56P10 : Set G) * ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) =
    (d.N : Set G)) ∧
  (∃ _ : (d.s56P10.subgroupOf d.N).Normal,
    Nonempty (↥d.N ⧸ d.s56P10.subgroupOf d.N ≃* Equiv.Perm (Fin 4))) ∧
  ⁅d.s56P0, d.F⁆ ≤ d.s56U10 ∧
  ⁅d.s56P10 ⊓ centralizer ({d.t} : Set G), d.B⁆ ≤ d.s56U11 ∧
  (∃ e ∈ d.E, IsTransv e d.B d.z (d.A ⊓ d.B) ∧
    ∀ e' ∈ d.E, e' ∈ centralizer (d.B : Set G) ∨ ∀ b ∈ d.B, e' * b * e'⁻¹ = e * b * e⁻¹) ∧
  (∀ p : G, p ∈ d.s56P0 ⊓ d.M ↔ p ∈ d.s56P0 ∧ ∃ e ∈ d.E, p * d.t * p⁻¹ = d.t * e) ∧
  (d.s56P0 ⊓ d.M).relIndex d.s56P0 = 2

@[expose] def Node08 (d : Data G) (z₀ : G) : Prop :=
  d.B ≤ P11 d ∧ d.F ≤ Pe11 d ∧ P11 d = Pe11 d ⊔ zpowers d.t ∧
  (∀ y, IsY d y → Pe11 d = d.F ⊔ Subgroup.closure {z₀, y * z₀ * y⁻¹}) ∧
  IsElemAbelian 2 (Pe11 d) ∧ Nat.card (Pe11 d) = 2 ^ 7 ∧ d.t ∉ Pe11 d ∧
  (Pe11 d : Set G) = (d.F : Set G) * ((Pe11 d ⊓ d.s56V : Subgroup G) : Set G)

@[expose] def Node09 (d : Data G) (z₀ : G) : Prop :=
  centralizerMod d.s56P10 d.s56U10 d.B ≤ centralizerMod d.s56P10 d.s56U11 d.F ∧
  ⁅d.s56P10, d.F⁆ ≤ d.s56U11 ∧
  ((d.s56P : Set G) * ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) =
    (d.N : Set G)) ∧
  d.B ≤ d.s56P ∧ IsElemAbQuot d.s56P d.B 5 ∧ d.s56P ⊓ centralizer ({d.t} : Set G) = d.B ∧
  (∀ s ∈ (fun f => d.t * f) '' (d.F : Set G), ∃ p ∈ d.s56P, p * d.t * p⁻¹ = s) ∧
  fusionIsSylowIn 2 (sylT d) (centralizer ({d.t} : Set G)) ∧ d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G) ∧
  sylT d = zpowers d.t ⊔ (sylT d ⊓ centralizer ({z₀} : Set G)) ∧
  d.pv 2 ∈ centralizer ({z₀} : Set G) ∧
  (d.ρ.range = ⊤ → ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y) ∧
  ∃ y₁, IsV1 d z₀ y₁

@[expose] def Node10 (d : Data G) (z₀ : G) : Prop :=
  (∀ y, IsV5 d y → y ∈ sylT d → y * z₀ = z₀ * y →
    (∀ q ∈ d.s56Q2, y * q = q * y) ∧
      (Subgroup.center ↥d.s56Q2).map d.s56Q2.subtype = d.E ⊔ zpowers y) ∧
  IsElemAbelian 2 d.s56V ∧ Nat.card d.s56V = 2 ^ 10 ∧
  fusionIsSylowIn 2 (sylT d ⊔ d.s56P) d.N ∧
  (d.ρ.range = titsD.subgroupOf titsA → d.s56Q2 = d.s56V ⊔ zpowers d.t) ∧
  (∀ y, IsV5 d y → d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y) ∧
  Nat.card (d.s56Q2 ⊓ d.s56P : Subgroup G) = 2 ^ 9 ∧ Nat.card (d.s56V ⊓ d.N : Subgroup G) = 2 ^ 9 ∧
  d.s56Q2.relIndex d.s56P = 4

@[expose] def Node11 (d : Data G) (z₀ : G) : Prop :=
  (IsMulCommutative ((d.s56Q2 ⊓ d.s56P ⊓ centralizer ({z₀} : Set G)) ⊔ d.F : Subgroup G) ∧
    ((d.s56Q2 ⊓ d.s56P ⊓ centralizer ({z₀} : Set G)) ⊔ d.F) ≤ P1 d ∧
    ((d.s56Q2 ⊓ d.s56P ⊓ centralizer ({z₀} : Set G)) ⊔ d.F).relIndex d.s56P = 4) ∧
  (d.s56P : Set G) = (zpowers d.t : Set G) * (P1 d : Set G) ∧
  ((∃ u ∈ d.s56Q2 ⊓ d.s56P ⊓ centralizer ({z₀} : Set G),
      u * d.t * u⁻¹ * d.t⁻¹ = d.pv 10 ∧ Pe10 d = Pe11 d ⊔ zpowers u) ∧
    (∀ n ∈ d.N, ∀ x ∈ Pe10 d, n * x * n⁻¹ ∈ Pe10 d) ∧
    ∀ x ∈ Pe10 d, ∀ p ∈ P1 d, x * p = p * x) ∧
  (IsMulCommutative (P1 d) ∧ ∀ y, IsY d y → ∃ v ∈ d.s56Q2 ⊓ d.s56P ⊓ centralizer ({z₀} : Set G),
      v * d.t * v⁻¹ * d.t⁻¹ = d.pv 9 ∧ P1 d = Pe10 d ⊔ Subgroup.closure {v, y * v * y⁻¹}) ∧
  (∀ n ∈ d.N, ∀ x ∈ P1 d, n * x * n⁻¹ ∈ P1 d) ∧
  P1 d ⊓ centralizer ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) = ⊥ ∧
  ((IsElemAbelian 2 (P1 d) ∧ Nat.card (P1 d) = 2 ^ 10) ∨
    (d.ρ.range = ⊤ ∧
      Nonempty (↥(P1 d) ≃* (Multiplicative (Fin 6 → ZMod 2)) ×
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
      (frattini ↥(P1 d)).map (P1 d).subtype = d.s56U11))

@[expose] def Node12 (d : Data G) (z₀ : G) : Prop :=
  ({x | ∃ q ∈ d.s56Q2, q * d.t * q⁻¹ = x} = (fun e => d.t * e) '' (d.E : Set G) ∧
    {x | ∃ v ∈ d.s56V, v * d.t * v⁻¹ = x} = (fun e => d.t * e) '' (d.E : Set G)) ∧
  (∀ y, IsV5 d y → y ∈ sylT d → y * z₀ = z₀ * y →
    {x | ∃ q ∈ d.s56Q2, q * (d.t * y * z₀) * q⁻¹ = x} =
        (fun e => d.t * y * z₀ * e) '' (d.E : Set G) ∧
      {x | ∃ v ∈ d.s56V, v * (d.t * y * z₀) * v⁻¹ = x} =
        (fun e => d.t * y * z₀ * e) '' (d.E : Set G)) ∧
  {s | s ∈ d.s56Q2 ∧ s ∉ d.s56V ∧ s * s = 1} =
    (fun e => d.t * e) '' (d.E : Set G) ∪
      {s | ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y ∧ ∃ e ∈ d.E, s = d.t * y * z₀ * e} ∧
  maxElemAbelian2 d.s56Q2 = {d.s56V} ∧
  (∀ x ∈ d.s56Q2, x ∉ d.s56V → x * x = 1 →
    CFSG.Open.pRank 2 (d.s56Q2 ⊓ centralizer ({x} : Set G)) = 6) ∧
  maxElemAbelian2 d.M = {d.s56V}

@[expose] def Node13 (d : Data G) : Prop :=
  ((∀ s ∈ d.s56P, s ∉ P1 d → s * s = 1 → s ∈ (fun f => d.t * f) '' (d.F : Set G)) ∧
    {x | ∃ p ∈ P1 d, p * d.t * p⁻¹ = x} = (fun f => d.t * f) '' (d.F : Set G)) ∧
  (CFSG.Open.pRank 2 d.N < 10 ∨
    (IsElemAbelian 2 (P1 d) ∧ Nat.card (P1 d) = 2 ^ 10 ∧
      maxElemAbelian2 d.N = {P1 d}))

@[expose] def Node14 (d : Data G) : Prop :=
  (∀ s ∈ d.tG, s ∈ Hg d →
    (InAH d s ∧ StarConj d s) ∨
    (IsElemAbelian 2 (P1 d) ∧ Nat.card (P1 d) = 2 ^ 10 ∧ ∃ k : G, k * d.t * k⁻¹ = s ∧
      zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) = d.B.map (MulAut.conj k).toMonoidHom ∧
      d.s56V = (P1 d).map (MulAut.conj k).toMonoidHom)) ∧
  (InAH d (d.t * d.pv 7) ∧ StarConj d (d.t * d.pv 7)) ∧
  (InAH d (d.t * d.pv 2) ∧ StarConj d (d.t * d.pv 2))

@[expose] def Node15 (d : Data G) (z₀ : G) : Prop :=
  ∀ y₁, IsV1 d z₀ y₁ → ∀ S' : Subgroup (MulAut ↥d.s56V),
    fusionIsSylowIn 2 S' (centralizer ((img d (Xg d) ⊔ zpowers (star d y₁) :
      Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) ⊓ Hs d) →
    star d d.t ∈ S' →
    S' = zpowers (star d d.t) ∨
      ∃ β ∈ Hg d, S' = Subgroup.closure {star d d.t, star d β} ∧
        IsTransv β d.s56V d.z (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z) ∧
        d.s56V ⊓ centralizer ({d.t * β} : Set G) = d.E ⊔ zpowers z₀

@[expose] def OrbSet (d : Data G) (S : Subgroup G) : Set G :=
  {x | (∃ h ∈ Hg d, h * d.t * h⁻¹ = x) ∧ ∃ s ∈ S, x = s * d.t}

@[expose] def Trans (S : Subgroup G) (O : Set G) : Prop :=
  ∀ a ∈ O, ∀ b ∈ O, ∃ s ∈ S, s * a * s⁻¹ = b

@[expose] def Node16 (d : Data G) (z₀ : G) : Prop :=
  (∀ S : Subgroup G, fusionIsSylowIn 2 S (Cv d) → (∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S) →
    (Cv d = oddCoreSub (Cv d) ⊔ d.s56V ∨
      (d.ρ.range = ⊤ ∧
        ∃ _ : (d.s56V.subgroupOf (S ⊔ zpowers d.t)).Normal,
          ((∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(S ⊔ zpowers d.t) ⧸ d.s56V.subgroupOf (S ⊔ zpowers d.t) ≃*
              DihedralGroup (2 ^ m))) ∨
            ∃ k : ℕ, 4 ≤ k ∧ Nonempty (↥(S ⊔ zpowers d.t) ⧸ d.s56V.subgroupOf (S ⊔ zpowers d.t) ≃*
              SemidihedralGroup k)) ∧
          {x | ∃ c ∈ Cv d, c * d.t * c⁻¹ = x} ∩ (S ⊔ zpowers d.t : Subgroup G) =
            {x | ∃ s ∈ S, s * d.t * s⁻¹ = x}))) ∧
  (∀ S : Subgroup G, fusionIsSylowIn 2 S (Cv d) → (∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S) →
    ((Trans S (OrbSet d S) ∧
        img d (Hg d ⊓ centralizer ({d.t} : Set G)) = centralizer ({star d d.t} : Set _) ⊓ Hs d) ∨
      ((∃ a ∈ OrbSet d S, ∃ b ∈ OrbSet d S, (∀ x ∈ OrbSet d S, (∃ s ∈ S, s * a * s⁻¹ = x) ∨
          (∃ s ∈ S, s * b * s⁻¹ = x)) ∧ ¬ ∃ s ∈ S, s * a * s⁻¹ = b) ∧
        ∃ β ∈ Hg d, centralizer ({star d d.t} : Set _) ⊓ Hs d = img d (CMt d) ⊔ zpowers (star d β) ∧
          img d (CMt d) ⊓ zpowers (star d β) = ⊥ ∧
          (∀ c ∈ img d (CMt d), c * star d β = star d β * c) ∧
          IsTransv β d.s56V d.z (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z) ∧
          d.s56V ⊓ centralizer ({d.t * β} : Set G) = d.E ⊔ zpowers z₀)))

@[expose] def Node17s (d : Data G) (z₀ : G) : Prop :=
  IsElemAbelian 2 (Us d) ∧ Nat.card (Us d) = 16 ∧
  (∀ y₁, IsV1 d z₀ y₁ →
    img d (CMt d) = zpowers (star d d.t) ⊔ (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁)) ∧
    zpowers (star d d.t) ⊓ (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁)) = ⊥ ∧
    ∀ a ∈ (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)),
      star d d.t * a = a * star d d.t)

@[expose] def Node17 (d : Data G) (z₀ : G) : Prop :=
  d.s56V ⊓ centralizer ((Ug d : Subgroup G) : Set G) = Zz d z₀ ∧
  d.s56V ⊓ centralizer ((U0g d : Subgroup G) : Set G) = zpowers d.z ∧
  centralizerMod d.s56V (zpowers d.z) (U0g d) = d.E ⊔ zpowers z₀ ∧
  img d (CMt d) = centralizer ({star d d.t} : Set _) ⊓ Hs d ∧
  (∀ S : Subgroup G, fusionIsSylowIn 2 S (Cv d) → (∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S) →
    Trans S (OrbSet d S)) ∧
  (∀ h ∈ Hg d, star d (h * d.t * h⁻¹) ∉ Us d)

@[expose] def Node18 (d : Data G) : Prop :=
  (∀ T' : Subgroup (MulAut ↥d.s56V), fusionIsSylowIn 2 T' (img d (CMt d)) →
      maxElemAbelian2 T' = {U0s d}) ∧
  (DeltaS d ⊆ (fun u => star d d.t * u) '' (Us d : Set (MulAut ↥d.s56V))) ∧
  (∀ a ∈ DeltaS d, ∀ b ∈ DeltaS d, ∃ k ∈ Ks d, k * a * k⁻¹ = b) ∧
  DeltaS d = (fun u => star d d.t * u) '' (Us d : Set (MulAut ↥d.s56V))

@[expose] def Node19 (d : Data G) (z₀ : G) : Prop :=
  (∀ T' : Subgroup (MulAut ↥d.s56V), fusionIsSylowIn 2 T' (img d (CMt d)) →
      Nat.card (Ks d) = Nat.card T' * 5 * 16) ∧
  (U0s d ≤ W0s d ∧ IsElemAbQuot (W0s d) (U0s d) 4 ∧
    centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ W0s d = U0s d ∧
    (∀ x ∈ DeltaS d, ∃ w ∈ W0s d, w * star d d.t * w⁻¹ = x) ∧
    (W0s d : Set (MulAut ↥d.s56V)) *
      (img d (Kg d ⊓ centralizer ({d.t} : Set G)) : Set (MulAut ↥d.s56V)) =
        (Ks d : Set (MulAut ↥d.s56V))) ∧
  ((∀ k ∈ Kg d, ∀ x ∈ Zz d z₀, k * x * k⁻¹ ∈ Zz d z₀) ∧ ∀ k ∈ Kg d, k * d.z = d.z * k) ∧
  (((Kg d ⊓ centralizer ({z₀} : Set G)).subgroupOf (Kg d)).Normal ∧
    Kg d = (Kg d ⊓ centralizer ({z₀} : Set G)) ⊔ zpowers d.t) ∧
  img d (Wg d z₀) = Ws d ∧ IsElemAbQuot (Ws d) (Us d) 4 ∧
  IsElemAbelian 2 (Ws d) ∧ Nat.card (Ws d) = 2 ^ 8

@[expose] def Node19b (d : Data G) (_z₀ : G) : Prop :=
  img d (Xg d) ≤ Ks d

@[expose] def Node20 (d : Data G) (z₀ : G) : Prop :=
  maxElemAbelian2 (Ks d) = {Ws d} ∧
  (∀ T' : Subgroup (MulAut ↥d.s56V), fusionIsSylowIn 2 T' (img d (CMt d)) →
      maxElemAbelian2 (Ws d ⊔ T') = {Ws d}) ∧
  sylT d ≤ Ig d ∧ Ws d ⊓ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) = Us d ∧
  fusionIsSylowIn 2 (Ws d) (centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) :
    Set (MulAut ↥d.s56V)) ⊓ Hs d) ∧
  (∀ y₁, IsV1 d z₀ y₁ →
    Alpha d (Ig d ⊓ centralizer ({d.t} : Set G)) =
        centralizer ({alpha d d.t} : Set (MulAut ↥(Ws d))) ⊓ Ialpha d ∧
      centralizer ({alpha d d.t} : Set (MulAut ↥(Ws d))) ⊓ Ialpha d =
        zpowers (alpha d d.t) ⊔ (Alpha d (Xg d) ⊔ zpowers (alpha d y₁)) ∧
      zpowers (alpha d d.t) ⊓ (Alpha d (Xg d) ⊔ zpowers (alpha d y₁)) = ⊥ ∧
      ∀ a ∈ (Alpha d (Xg d) ⊔ zpowers (alpha d y₁) : Subgroup (MulAut ↥(Ws d))),
        alpha d d.t * a = a * alpha d d.t) ∧
  (∀ h ∈ Hg d, h * d.t * h⁻¹ ∈ Ig d →
    (zpowers (star d (h * d.t * h⁻¹)) ⊔
        (Ws d ⊓ centralizer ({star d (h * d.t * h⁻¹)} : Set (MulAut ↥d.s56V))) =
      (U0s d).map (MulAut.conj (star d h)).toMonoidHom) ∧ h ∈ Ig d) ∧
  ∃ i ∈ Ig d, alpha d (d.t * d.pv 2) = alpha d i * alpha d d.t * (alpha d i)⁻¹

@[expose] def Node21 (d : Data G) (_z₀ : G) : Prop :=
  ((Nonempty (↥(Ja d) ≃* alternatingGroup (Fin 6)) ∧
      PGLTwoSquareOuter ((Ja d).subgroupOf (Ialpha d)) (elemOf (Ialpha d) (alpha d d.t))) ∨
    Nonempty (↥(Ja d) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
  (∀ S : Subgroup G, IsS d S →
    (∀ j ∈ Alpha d S, j * j = 1 → j ≠ 1 → 4 ≤ Nat.card (commImg (S := ↥(Ws d)) j)) ∧
    (∀ F : Subgroup (MulAut ↥(Ws d)), F ≤ Alpha d S → IsElemAbelian 2 F → Nat.card F = 4 →
      ∃ j ∈ F, 16 ≤ Nat.card (commImg (S := ↥(Ws d)) j)) ∧
    {x | x ∈ Alpha d S ∧ ∃ i ∈ Ialpha d, x = i * alpha d d.t * i⁻¹} =
      {x | ∃ s ∈ Alpha d S, x = s * alpha d d.t * s⁻¹}) ∧
  Nat.card (Ialpha d) ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2 ∧
  ∀ S : Subgroup G, IsS d S → ∀ F : Subgroup (MulAut ↥(Ws d)), F ≤ Alpha d S → IsElemAbelian 2 F →
    Nat.card F ≤ 8

@[expose] def Node22 (d : Data G) (_z₀ : G) : Prop :=
  ∀ S : Subgroup G, IsS d S →
    ((maxElemAbelian2 (img d S) = {Ws d} ∧
        (∀ h ∈ Hs d, (Ws d).map (MulAut.conj h).toMonoidHom ≤ img d S →
          (Ws d).map (MulAut.conj h).toMonoidHom = Ws d) ∧
        (∀ j ∈ img d S, j ∉ Ws d → j * j = 1 → 4 ≤ Nat.card (⁅Ws d, zpowers j⁆ : Subgroup (MulAut ↥d.s56V))) ∧
        (∀ F : Subgroup (MulAut ↥d.s56V), F ≤ img d S → Ws d ≤ F → (Ws d).relIndex F = 4 →
          (∀ p ∈ F, p * p ∈ Ws d) → ∃ j ∈ F, j ∉ Ws d ∧ 16 ≤ Nat.card (⁅Ws d, zpowers j⁆ : Subgroup (MulAut ↥d.s56V)))) ∧
      fusionIsSylowIn 2 S (Hg d) ∧
      ∀ h ∈ Hs d, ∀ x ∈ Ws d ⊔ oddCoreSub (Hs d), h * x * h⁻¹ ∈ Ws d ⊔ oddCoreSub (Hs d))

@[expose] def Node23a (d : Data G) (z₀ : G) : Prop :=
  (∀ o ∈ oddCoreSub (Hs d), star d d.t * o * (star d d.t)⁻¹ = o⁻¹) ∧
  ((∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) ∧
    img d (Xg d) ≤ centralizer ((oddCoreSub (Hs d) : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V))) ∧
  (Zz d z₀ = d.s56V ⊓ centralizer ((Wg d z₀ : Subgroup G) : Set G) ∧
    ∀ h ∈ Hg d, ∀ x ∈ Zz d z₀, h * x * h⁻¹ ∈ Zz d z₀) ∧
  d.t ∉ H0 d z₀ ∧
  (∃ _ : ((H0 d z₀).subgroupOf (Hg d)).Normal,
    Nonempty (↥(Hg d) ⧸ (H0 d z₀).subgroupOf (Hg d) ≃* Equiv.Perm (Fin 2)) ∨
      Nonempty (↥(Hg d) ⧸ (H0 d z₀).subgroupOf (Hg d) ≃* Equiv.Perm (Fin 3))) ∧
  Ws d ≤ img d (Jg d) ∧
  (∃ _ : ((Ws d).subgroupOf (img d (Jg d))).Normal,
    Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(img d (Jg d)) ⧸ (Ws d).subgroupOf (img d (Jg d)) ≃*
        Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))

@[expose] def Node23b (d : Data G) (z₀ : G) : Prop :=
  ⁅d.s56V, Wg d z₀⁆ = Zz d z₀ ∧
  (((∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6))) ∧
    ∃ V₁ V₂ : Subgroup G, Zz d z₀ ≤ V₁ ∧ V₁ ≤ d.s56V ∧ Zz d z₀ ≤ V₂ ∧ V₂ ≤ d.s56V ∧
      V₁ ⊔ V₂ = d.s56V ∧ V₁ ⊓ V₂ = Zz d z₀ ∧
      (∀ j ∈ Jp d, ∀ v ∈ V₁, j * v * j⁻¹ ∈ V₁) ∧ (∀ j ∈ Jp d, ∀ v ∈ V₂, j * v * j⁻¹ ∈ V₂) ∧
      V₂ = V₁.map (MulAut.conj d.t).toMonoidHom ∧
      IsElemAbQuot V₁ (Zz d z₀) 4 ∧ IsElemAbQuot V₂ (Zz d z₀) 4 ∧
      (∀ U : Subgroup G, Zz d z₀ ≤ U → U ≤ V₁ → (∀ j ∈ Jp d, ∀ u ∈ U, j * u * j⁻¹ ∈ U) →
        U = Zz d z₀ ∨ U = V₁) ∧
      (∀ U : Subgroup G, Zz d z₀ ≤ U → U ≤ V₂ → (∀ j ∈ Jp d, ∀ u ∈ U, j * u * j⁻¹ ∈ U) →
        U = Zz d z₀ ∨ U = V₂) ∧
      centralizerMod (Jp d) (Zz d z₀) V₁ = Wg d z₀ ∧ centralizerMod (Jp d) (Zz d z₀) V₂ = Wg d z₀) ∨
  ((∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃*
        Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
    ∃ J₁ J₂ V₁ V₂ : Subgroup G, Wg d z₀ ≤ J₁ ∧ J₁ ≤ Jp d ∧ Wg d z₀ ≤ J₂ ∧ J₂ ≤ Jp d ∧
      J₁ ⊔ J₂ = Jp d ∧ J₁ ⊓ J₂ = Wg d z₀ ∧
      (Wg d z₀).relIndex J₁ = 5 ∧ (Wg d z₀).relIndex J₂ = 5 ∧
      V₁ = centralizerMod d.s56V (Zz d z₀) J₁ ∧ V₂ = centralizerMod d.s56V (Zz d z₀) J₂ ∧
      V₁ ⊔ V₂ = d.s56V ∧ V₁ ⊓ V₂ = Zz d z₀ ∧
      IsElemAbQuot V₁ (Zz d z₀) 4 ∧ IsElemAbQuot V₂ (Zz d z₀) 4 ∧
      V₂ = V₁.map (MulAut.conj d.t).toMonoidHom))

@[expose] noncomputable def Kz (d : Data G) (z₀ : G) : Subgroup G :=
  centralizerMod (Hg d) (Zz d z₀) d.s56V

@[expose] def Node23c (d : Data G) (z₀ : G) : Prop :=
  ((∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6))) →
    ∀ o ∈ Hg d, (∀ j ∈ Jp d, o * j * o⁻¹ * j⁻¹ ∈ Kz d z₀) → o ∈ Kz d z₀) ∧
  ∀ s ∈ Hg d, s * s = 1 → (Zz d z₀).relIndex (⁅d.s56V, zpowers s⁆ ⊔ Zz d z₀) = 8 →
    (∃ _ : ((Wg d z₀).subgroupOf (Jp d)).Normal,
      Nonempty (↥(Jp d) ⧸ (Wg d z₀).subgroupOf (Jp d) ≃* alternatingGroup (Fin 6))) ∧
    s ∉ Jp d ⊔ Kz d z₀ ∧
    ∃ V₁ : Subgroup G, Zz d z₀ ≤ V₁ ∧ V₁ ≤ d.s56V ∧ IsElemAbQuot V₁ (Zz d z₀) 4 ∧
      (∀ j ∈ Jp d, ∀ v ∈ V₁, j * v * j⁻¹ ∈ V₁) ∧
      V₁ ⊔ V₁.map (MulAut.conj d.t).toMonoidHom = d.s56V ∧
      V₁ ⊓ V₁.map (MulAut.conj d.t).toMonoidHom = Zz d z₀ ∧ ∀ v ∈ V₁, s * v * s⁻¹ ∈ V₁

@[expose] def Node24 (d : Data G) : Prop :=
  d.tG ∩ (Hg d : Set G) = {x | ∃ h ∈ Hg d, h * d.t * h⁻¹ = x}

@[expose] def Node25 (d : Data G) (_z₀ : G) : Prop :=
  ∀ S : Subgroup G, IsS d S →
    d.tG ∩ (S : Set G) = {x | ∃ s ∈ S, s * d.t * s⁻¹ = x} ∧
    ∃ P : Sylow 2 G, (P : Subgroup G) = S

@[expose] def Node26 (d : Data G) (z₀ : G) : Prop :=
  ∀ S : Subgroup G, IsS d S → CFSG.LocalAnalysis.FirstTransferData S (S ⊓ H0 d z₀) d.t

end Props

end CFSG.LocalAnalysis.EvenBN.Tits.N
