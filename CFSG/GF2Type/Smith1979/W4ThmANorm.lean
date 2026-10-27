module

public import CFSG.GF2Type.Smith1979.W4ThmAEnd
public import CFSG.GF2Type.Smith1979.W4ThmALin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4ThmA

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.GF2Type.Smith1980Orth.W4Sigma

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

structure Swap (S : Setting G) (g u : G) : Prop where
  mem : u ∈ S.QG ⊔ S.Qa g
  conj_z : u * S.z * u⁻¹ = g * S.z * g⁻¹
  conj_a : u * (g * S.z * g⁻¹) * u⁻¹ = S.z

namespace Swap

variable {u : G} (hu : Swap S g u)
include hu

omit [Finite G] in
theorem conj_z' : u⁻¹ * S.z * u = g * S.z * g⁻¹ := by
  calc u⁻¹ * S.z * u = u⁻¹ * (u * (g * S.z * g⁻¹) * u⁻¹) * u := by rw [hu.conj_a]
    _ = g * S.z * g⁻¹ := by group

omit [Finite G] in
theorem conj_a' : u⁻¹ * (g * S.z * g⁻¹) * u = S.z := by
  calc u⁻¹ * (g * S.z * g⁻¹) * u = u⁻¹ * (u * S.z * u⁻¹) * u := by rw [hu.conj_z]
    _ = S.z := by group

theorem mem_Qa_iff (y : G) : y ∈ S.Qa g ↔ u⁻¹ * y * u ∈ S.QG := by
  rw [Setting.Qa_eq_of_conj_eq S hu.conj_z.symm, mem_Qa_iff']

theorem mem_QG_iff (y : G) : y ∈ S.QG ↔ u⁻¹ * y * u ∈ S.Qa g := by
  rw [Setting.Qa_eq_of_conj_eq S
    (show g * S.z * g⁻¹ = u⁻¹ * S.z * u⁻¹⁻¹ by rw [inv_inv, hu.conj_z']), mem_Qa_iff', inv_inv,
    show u * (u⁻¹ * y * u) * u⁻¹ = y by group]

end Swap

@[expose] def Ysub (u : G) (V : Subgroup G) : Subgroup G := V.map (MulAut.conj u).toMonoidHom

omit [Finite G] in
theorem mem_Ysub {u : G} {V : Subgroup G} {y : G} : y ∈ Ysub u V ↔ u⁻¹ * y * u ∈ V := by
  rw [Ysub, Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hv
  · intro hy
    exact ⟨u⁻¹ * y * u, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

namespace Swap

variable {u : G} (hu : Swap S g u)
include hu

theorem Y_le_Qa {t : S.O} {y : G} (hy : y ∈ Ysub u (V S g t)) : y ∈ S.Qa g :=
  (hu.mem_Qa_iff y).mpr (mem_Ysub.mp hy).1

theorem a_mem_Y {t : S.O} : g * S.z * g⁻¹ ∈ Ysub u (V S g t) :=
  mem_Ysub.mpr (by rw [hu.conj_a']; exact z_mem_V)

end Swap

omit [Finite G] in
theorem comm_of_mul_mem {V : Subgroup G} {x : G} (hx : ∀ v ∈ V, x * v = v * x) (hxx : x * x = 1)
    {a : G} (ha : x * a ∈ V) : a * x = x * a := by
  have h := hx _ ha
  have e : x * (x * a) = a := by rw [← mul_assoc, hxx, one_mul]
  rw [e] at h
  calc a * x = ((x * a) * x) * x := by rw [← h]
    _ = x * a * (x * x) := by group
    _ = x * a := by rw [hxx, mul_one]

@[expose] def Wsub (V : Subgroup G) (x : G) (hx : ∀ v ∈ V, x * v = v * x) (hxx : x * x = 1) :
    Subgroup G where
  carrier := {b | b ∈ V ∨ x * b ∈ V}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (V.mul_mem ha hb)
    · refine Or.inr ?_
      rw [← mul_assoc, hx a ha, mul_assoc]
      exact V.mul_mem ha hb
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact V.mul_mem ha hb
    · refine Or.inl ?_
      have hax : a * x = x * a := comm_of_mul_mem hx hxx ha
      have e : a * b = (x * a) * (x * b) := by
        calc a * b = (x * x) * a * b := by rw [hxx, one_mul]
          _ = x * (x * a) * b := by group
          _ = x * (a * x) * b := by rw [hax]
          _ = (x * a) * (x * b) := by group
      rw [e]
      exact V.mul_mem ha hb
  one_mem' := Or.inl V.one_mem
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (V.inv_mem ha)
    · refine Or.inr ?_
      have hax : a * x = x * a := comm_of_mul_mem hx hxx ha
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      have e : x * a⁻¹ = (x * a)⁻¹ := by
        calc x * a⁻¹ = (a * x⁻¹)⁻¹ := by group
          _ = (a * x)⁻¹ := by rw [hxi]
          _ = (x * a)⁻¹ := by rw [hax]
      rw [e]
      exact V.inv_mem ha

section Wsub

variable {V : Subgroup G} {x : G} {hx : ∀ v ∈ V, x * v = v * x} {hxx : x * x = 1}

omit [Finite G] in
theorem mem_Wsub {b : G} : b ∈ Wsub V x hx hxx ↔ b ∈ V ∨ x * b ∈ V := Iff.rfl

omit [Finite G] in
theorem V_le_Wsub {b : G} (hb : b ∈ V) : b ∈ Wsub V x hx hxx := Or.inl hb

omit [Finite G] in
theorem x_mem_Wsub : x ∈ Wsub V x hx hxx := Or.inr (by rw [hxx]; exact V.one_mem)

omit [Finite G] in
theorem Wsub_cases {b : G} (hb : b ∈ Wsub V x hx hxx) : b ∈ V ∨ ∃ v ∈ V, b = x * v := by
  rcases hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr ⟨x * b, hb, by rw [← mul_assoc, hxx, one_mul]⟩

omit [Finite G] in
theorem Wsub_comm (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {a b : G} (ha : a ∈ Wsub V x hx hxx)
    (hb : b ∈ Wsub V x hx hxx) : a * b = b * a := by
  have cx : ∀ v ∈ V, Commute x v := fun v hv => hx v hv
  have cv : ∀ v ∈ V, ∀ w ∈ V, Commute v w := fun v hv w hw => hVc v hv w hw
  rcases Wsub_cases ha with ha | ⟨v₁, hv₁, rfl⟩ <;> rcases Wsub_cases hb with hb | ⟨v₂, hv₂, rfl⟩
  · exact cv a ha b hb
  · exact ((cx a ha).symm.mul_right (cv a ha v₂ hv₂)).eq
  · exact ((cx b hb).mul_left (cv v₁ hv₁ b hb)).eq
  · exact (((Commute.refl x).mul_right (cx v₂ hv₂)).mul_left
      ((cx v₁ hv₁).symm.mul_right (cv v₁ hv₁ v₂ hv₂))).eq

omit [Finite G] in
theorem Wsub_mul_self (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1) {a : G}
    (ha : a ∈ Wsub V x hx hxx) : a * a = 1 := by
  rcases Wsub_cases ha with ha | ⟨v, hv, rfl⟩
  · exact hV2 a ha
  · have h : v * x = x * v := (hx v hv).symm
    have e : x * v * (x * v) = (x * x) * (v * v) := by
      calc x * v * (x * v) = x * (v * x) * v := by group
        _ = x * (x * v) * v := by rw [h]
        _ = (x * x) * (v * v) := by group
    rw [e, hxx, hV2 v hv, one_mul]

theorem card_Wsub (hxV : x ∉ V) : Nat.card (Wsub V x hx hxx) = 2 * Nat.card V := by
  have hset : ((Wsub V x hx hxx : Subgroup G) : Set G) =
      (V : Set G) ∪ (fun v => x * v) '' (V : Set G) := by
    ext b
    simp only [SetLike.mem_coe, Set.mem_union, Set.mem_image, mem_Wsub]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨x * b, h, by rw [← mul_assoc, hxx, one_mul]⟩
    · rintro (h | ⟨v, hv, rfl⟩)
      · exact Or.inl h
      · right
        rw [← mul_assoc, hxx, one_mul]
        exact hv
  have hdisj : Disjoint (V : Set G) ((fun v => x * v) '' (V : Set G)) := by
    rw [Set.disjoint_left]
    rintro b hb ⟨v, hv, rfl⟩
    apply hxV
    have e : x = (x * v) * v⁻¹ := by group
    rw [e]
    exact mul_mem hb (inv_mem hv)
  have hV : (V : Set G).ncard = Nat.card V := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ (mul_right_injective x), hV]
  ring

end Wsub

namespace ThmAData

variable {t : S.O} (D : ThmAData S g t) {u : G} (hu : Swap S g u)
include D hu

omit hu in
theorem z_mem_V0 : S.z ∈ V S g t ⊓ S.Qa g :=
  ⟨z_mem_V, S.z_mem_Qa_of_mem_QG rfl D.haQ D.hne⟩

omit hu in
theorem a_mem_V0 : g * S.z * g⁻¹ ∈ V S g t ⊓ S.Qa g :=
  ⟨D.a_mem_V, (S.conjBy g).z_mem_QG⟩

omit hu in
theorem QG_le_normalizer_V0 :
    S.QG ≤ normalizer ((V S g t ⊓ S.Qa g : Subgroup G) : Set G) := by
  rw [le_normalizer_iff]
  intro q hq e he
  rcases S.mul_comm_or hq he.1.1 with h | h
  · rw [h, mul_inv_cancel_right]
    exact he
  · have e1 : q * e * q⁻¹ = S.z * e := by rw [h]; group
    rw [e1]
    exact mul_mem (D.z_mem_V0) he

omit hu in
theorem Qa_le_normalizer_V0 :
    S.Qa g ≤ normalizer ((V S g t ⊓ S.Qa g : Subgroup G) : Set G) := by
  rw [le_normalizer_iff]
  intro q hq e he
  rcases (S.conjBy g).mul_comm_or hq he.2 with h | h
  · rw [h, mul_inv_cancel_right]
    exact he
  · have e1 : q * e * q⁻¹ = (g * S.z * g⁻¹) * e := by
      rw [h]
      change (S.conjBy g).z * (e * q) * q⁻¹ = (S.conjBy g).z * e
      group
    rw [e1]
    exact mul_mem (D.a_mem_V0) he

theorem u_mem_normalizer_V0 :
    u ∈ normalizer ((V S g t ⊓ S.Qa g : Subgroup G) : Set G) :=
  sup_le (D.QG_le_normalizer_V0) (D.Qa_le_normalizer_V0) hu.mem

omit hu in
theorem Y_comm {y y' : G} (hy : y ∈ Ysub u (V S g t)) (hy' : y' ∈ Ysub u (V S g t)) :
    y * y' = y' * y := by
  have h := D.V_comm (mem_Ysub.mp hy) (mem_Ysub.mp hy')
  have e : y * y' = u * ((u⁻¹ * y * u) * (u⁻¹ * y' * u)) * u⁻¹ := by group
  rw [e, h]
  group

omit hu in
theorem Y_mul_self {y : G} (hy : y ∈ Ysub u (V S g t)) : y * y = 1 := by
  have h := D.V_mul_self (mem_Ysub.mp hy)
  calc y * y = u * ((u⁻¹ * y * u) * (u⁻¹ * y * u)) * u⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem z_mem_Y : S.z ∈ Ysub u (V S g t) :=
  mem_Ysub.mpr (by rw [hu.conj_z']; exact D.a_mem_V)

theorem Y_le_M {y : G} (hy : y ∈ Ysub u (V S g t)) : y ∈ S.M :=
  S.mem_M_iff.mpr (D.Y_comm hy (D.z_mem_Y hu))

omit hu in
theorem card_Y : Nat.card (Ysub u (V S g t)) = 32 := by
  rw [Ysub, Subgroup.card_map_of_injective (MulAut.conj u).injective, D.card_V]

theorem mem_V0_of_mem_Y_QG {y : G} (hy : y ∈ Ysub u (V S g t)) (hyQ : y ∈ S.QG) :
    y ∈ V S g t ⊓ S.Qa g := by
  have h1 : u⁻¹ * y * u ∈ V S g t ⊓ S.Qa g := ⟨mem_Ysub.mp hy, (hu.mem_QG_iff y).mp hyQ⟩
  have h2 := (mem_normalizer_iff.mp (D.u_mem_normalizer_V0 hu) _).mp h1
  rwa [show u * (u⁻¹ * y * u) * u⁻¹ = y by group] at h2

theorem V0_le_Y {e : G} (he : e ∈ V S g t ⊓ S.Qa g) : e ∈ Ysub u (V S g t) :=
  mem_Ysub.mpr ((mem_normalizer_iff''.mp (D.u_mem_normalizer_V0 hu) e).mp he).1

theorem not_Y_le_V : ¬ ∀ y ∈ Ysub u (V S g t), y ∈ V S g t := by
  intro h
  have hle : Ysub u (V S g t) ≤ V S g t := h
  have hEq : Ysub u (V S g t) = V S g t :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [D.card_Y, D.card_V])
  apply D.hVQ
  intro v hv
  refine hu.Y_le_Qa (t := t) ?_
  rw [hEq]
  exact hv

theorem Y_rho {y : G} (hy : y ∈ Ysub u (V S g t)) :
    S.ρ ⟨y, D.Y_le_M hu hy⟩ = 1 ∨ S.ρ ⟨y, D.Y_le_M hu hy⟩ = t := by
  have hL : S.ρ ⟨y, D.Y_le_M hu hy⟩ ∈ S.Lbar g :=
    S.ρ_mem_Lbar ⟨hu.Y_le_Qa hy, D.Y_le_M hu hy⟩
  refine D.axis hL fun e he => ?_
  rw [S.ρ_cl ⟨y, D.Y_le_M hu hy⟩ he.1.1, D.Y_comm hy (D.V0_le_Y hu he), mul_inv_cancel_right]

end ThmAData

structure XData (S : Setting G) (g : G) (t : S.O) (u x : G) : Prop where
  memY : x ∈ Ysub u (V S g t)
  notQ : x ∉ S.QG
  hM : x ∈ S.M
  rho : S.ρ ⟨x, hM⟩ = t
  sq : x * x = 1
  comm : ∀ v ∈ V S g t, x * v = v * x

namespace ThmAData

variable {t : S.O} (D : ThmAData S g t) {u : G} (hu : Swap S g u)
include D hu

theorem mem_Y_of_comm {c : G} (hc : c ∈ S.Qa g)
    (hcomm : ∀ y ∈ Ysub u (V S g t), c * y = y * c) : c ∈ Ysub u (V S g t) := by
  have hcQ : u⁻¹ * c * u ∈ S.QG := (hu.mem_Qa_iff c).mp hc
  refine mem_Ysub.mpr (D.mem_V_of_comm hcQ fun v hv => ?_)
  have hvY : u * v * u⁻¹ ∈ Ysub u (V S g t) :=
    mem_Ysub.mpr (by rw [show u⁻¹ * (u * v * u⁻¹) * u = v by group]; exact hv)
  have h := hcomm _ hvY
  calc u⁻¹ * c * u * v = u⁻¹ * (c * (u * v * u⁻¹)) * u := by group
    _ = u⁻¹ * ((u * v * u⁻¹) * c) * u := by rw [h]
    _ = v * (u⁻¹ * c * u) := by group

theorem exists_XData : ∃ x, XData S g t u x := by
  obtain ⟨x, hxY, hxQ⟩ : ∃ x ∈ Ysub u (V S g t), x ∉ S.QG := by
    by_contra hcon
    push Not at hcon
    exact D.not_Y_le_V hu fun y hy => (D.mem_V0_of_mem_Y_QG hu hy (hcon y hy)).1
  have hxM := D.Y_le_M hu hxY
  have hxt : S.ρ ⟨x, hxM⟩ = t :=
    (D.Y_rho hu hxY).resolve_left fun h => hxQ ((S.ρ_eq_one_iff ⟨x, hxM⟩).mp h)
  have hxx := D.Y_mul_self hxY
  exact ⟨x, hxY, hxQ, hxM, hxt, hxx, fun v hv => D.comm_of_ρ_eq_t hxM hxt hxx hv⟩

variable {x : G} (X : XData S g t u x)
include X

theorem Y_le_Wsub {y : G} (hy : y ∈ Ysub u (V S g t)) :
    y ∈ Wsub (V S g t) x X.comm X.sq := by
  rcases D.Y_rho hu hy with h | h
  · exact Or.inl (D.mem_V0_of_mem_Y_QG hu hy ((S.ρ_eq_one_iff _).mp h)).1
  · right
    have hxyY : x * y ∈ Ysub u (V S g t) := mul_mem X.memY hy
    have hxyM := D.Y_le_M hu hxyY
    have hxyQ : x * y ∈ S.QG := by
      rw [← S.ρ_eq_one_iff ⟨x * y, hxyM⟩]
      have e : (⟨x * y, hxyM⟩ : S.M) = ⟨x, X.hM⟩ * ⟨y, D.Y_le_M hu hy⟩ := rfl
      rw [e, map_mul, X.rho, h, D.t_mul_t]
    exact (D.mem_V0_of_mem_Y_QG hu hxyY hxyQ).1

omit hu in
theorem conj_mem_Wsub {m : G} (hmR : m ∈ R S g t) {b : G}
    (hb : b ∈ Wsub (V S g t) x X.comm X.sq) : m * b * m⁻¹ ∈ Wsub (V S g t) x X.comm X.sq := by
  obtain ⟨hmM, hρ⟩ := (mem_R_iff D.ht).mp hmR
  have hconjV : ∀ v ∈ V S g t, m * v * m⁻¹ ∈ V S g t := fun v hv =>
    D.conj_mem_V_of_mem_Rbar hmM hρ hv
  have hx' : m * x * m⁻¹ ∈ Wsub (V S g t) x X.comm X.sq := by
    have hx'M : m * x * m⁻¹ ∈ S.M := mul_mem (mul_mem hmM X.hM) (inv_mem hmM)
    have hx't : S.ρ ⟨m * x * m⁻¹, hx'M⟩ = t := by
      have e : (⟨m * x * m⁻¹, hx'M⟩ : S.M) = ⟨m, hmM⟩ * ⟨x, X.hM⟩ * ⟨m, hmM⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, X.rho, commute_of_mem_Rbar D.H.conj_mem hρ,
        mul_inv_cancel_right]
    have hx'x' : m * x * m⁻¹ * (m * x * m⁻¹) = 1 := by
      calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
        _ = 1 := by rw [X.sq]; group
    have hx'V : ∀ v ∈ V S g t, m * x * m⁻¹ * v = v * (m * x * m⁻¹) := fun v hv =>
      D.comm_of_ρ_eq_t hx'M hx't hx'x' hv
    have hxx'Q : x * (m * x * m⁻¹) ∈ S.QG := by
      rw [← S.ρ_eq_one_iff ⟨x * (m * x * m⁻¹), mul_mem X.hM hx'M⟩]
      have e : (⟨x * (m * x * m⁻¹), mul_mem X.hM hx'M⟩ : S.M) =
          ⟨x, X.hM⟩ * ⟨m * x * m⁻¹, hx'M⟩ := rfl
      rw [e, map_mul, X.rho, hx't, D.t_mul_t]
    have hxx'V : x * (m * x * m⁻¹) ∈ V S g t := by
      refine D.mem_V_of_comm hxx'Q fun v hv => ?_
      exact (Commute.mul_left (X.comm v hv : Commute x v) (hx'V v hv : Commute _ v)).eq
    exact Or.inr hxx'V
  rcases hb with hb | hb
  · exact Or.inl (hconjV b hb)
  · have e : m * b * m⁻¹ = (m * x * m⁻¹) * (m * (x * b) * m⁻¹) := by
      calc m * b * m⁻¹ = m * (x * (x * b)) * m⁻¹ := by rw [← mul_assoc x x b, X.sq, one_mul]
        _ = (m * x * m⁻¹) * (m * (x * b) * m⁻¹) := by group
    rw [e]
    exact mul_mem hx' (Or.inl (hconjV _ hb))

omit hu in
theorem R_le_normalizer_Wsub :
    R S g t ≤ normalizer ((Wsub (V S g t) x X.comm X.sq : Subgroup G) : Set G) := by
  rw [le_normalizer_iff]
  intro m hm b hb
  exact D.conj_mem_Wsub X hm hb

omit hu in
theorem QG_le_normalizer_Wsub :
    S.QG ≤ normalizer ((Wsub (V S g t) x X.comm X.sq : Subgroup G) : Set G) :=
  (QG_le_R D.ht).trans (D.R_le_normalizer_Wsub X)

theorem comm_mem_Y {q b : G} (hq : q ∈ S.Qa g) (hb : b ∈ V S g t) :
    q * b * q⁻¹ * b⁻¹ ∈ Ysub u (V S g t) := by
  have hbM : b ∈ (S.conjBy g).M := (S.conjBy g).mem_M_iff.mpr (D.V_comm hb D.a_mem_V)
  have hc : q * b * q⁻¹ * b⁻¹ ∈ S.Qa g := by
    have e : q * b * q⁻¹ * b⁻¹ = q * (b * q⁻¹ * b⁻¹) := by group
    rw [e]
    exact (S.conjBy g).QG.mul_mem hq ((S.conjBy g).conj_mem_QG hbM ((S.conjBy g).QG.inv_mem hq))
  refine D.mem_Y_of_comm hu hc fun y hy => ?_
  have hVc : ∀ a ∈ V S g t, ∀ b ∈ V S g t, a * b = b * a := fun a ha b hb => D.V_comm ha hb
  have hby : Commute y b := (Wsub_comm hVc (D.Y_le_Wsub hu X hy) (V_le_Wsub hb))
  have key : y * (q * b * q⁻¹ * b⁻¹) * y⁻¹ = q * b * q⁻¹ * b⁻¹ := by
    rcases (S.conjBy g).mul_comm_or (hu.Y_le_Qa hy) hq with h | h
    · have hyq : Commute y q := h
      have hcm : Commute y (q * b * q⁻¹ * b⁻¹) :=
        (((hyq.mul_right hby).mul_right hyq.inv_right).mul_right hby.inv_right)
      rw [hcm.eq, mul_inv_cancel_right]
    · have e1 : y * q * y⁻¹ = (g * S.z * g⁻¹) * q := by
        rw [h]
        change (S.conjBy g).z * (q * y) * y⁻¹ = (S.conjBy g).z * q
        group
      have haq : Commute (g * S.z * g⁻¹) q := ((S.conjBy g).z_comm_QG hq).symm
      have hab : Commute (g * S.z * g⁻¹) b := D.V_comm D.a_mem_V hb
      have hcm : Commute (g * S.z * g⁻¹) (q * b * q⁻¹) :=
        ((haq.mul_right hab).mul_right haq.inv_right)
      calc y * (q * b * q⁻¹ * b⁻¹) * y⁻¹
          = (y * q * y⁻¹) * (y * b * y⁻¹) * (y * q * y⁻¹)⁻¹ * (y * b * y⁻¹)⁻¹ := by group
        _ = (g * S.z * g⁻¹) * q * b * ((g * S.z * g⁻¹) * q)⁻¹ * b⁻¹ := by
            rw [e1, hby.eq, mul_inv_cancel_right]
        _ = ((g * S.z * g⁻¹) * (q * b * q⁻¹) * (g * S.z * g⁻¹)⁻¹) * b⁻¹ := by group
        _ = q * b * q⁻¹ * b⁻¹ := by rw [hcm.eq, mul_inv_cancel_right]
  calc (q * b * q⁻¹ * b⁻¹) * y = y * (q * b * q⁻¹ * b⁻¹) * y⁻¹ * y := by rw [key]
    _ = y * (q * b * q⁻¹ * b⁻¹) := by group

theorem Qa_le_normalizer_Wsub :
    S.Qa g ≤ normalizer ((Wsub (V S g t) x X.comm X.sq : Subgroup G) : Set G) := by
  rw [le_normalizer_iff]
  intro q hq b hb
  have hV : ∀ v ∈ V S g t, q * v * q⁻¹ ∈ Wsub (V S g t) x X.comm X.sq := by
    intro v hv
    have e : q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact mul_mem (D.Y_le_Wsub hu X (D.comm_mem_Y hu X hq hv)) (Or.inl hv)
  rcases hb with hb | hb
  · exact hV b hb
  · have e : q * b * q⁻¹ = (q * x * q⁻¹) * (q * (x * b) * q⁻¹) := by
      calc q * b * q⁻¹ = q * (x * (x * b)) * q⁻¹ := by rw [← mul_assoc x x b, X.sq, one_mul]
        _ = (q * x * q⁻¹) * (q * (x * b) * q⁻¹) := by group
    rw [e]
    refine mul_mem ?_ (hV _ hb)
    have hqx : q * x * q⁻¹ ∈ Ysub u (V S g t) := by
      rcases (S.conjBy g).mul_comm_or hq (hu.Y_le_Qa X.memY) with h | h
      · rw [h, mul_inv_cancel_right]
        exact X.memY
      · have e2 : q * x * q⁻¹ = (g * S.z * g⁻¹) * x := by
          rw [h]
          change (S.conjBy g).z * (x * q) * q⁻¹ = (S.conjBy g).z * x
          group
        rw [e2]
        exact mul_mem (hu.a_mem_Y) X.memY
    exact D.Y_le_Wsub hu X hqx

theorem u_mem_normalizer_Wsub :
    u ∈ normalizer ((Wsub (V S g t) x X.comm X.sq : Subgroup G) : Set G) :=
  sup_le (D.QG_le_normalizer_Wsub X) (D.Qa_le_normalizer_Wsub hu X) hu.mem

omit hu in
theorem exists_conj_x {v : G} (hv : v ∈ V S g t) :
    ∃ q ∈ S.QG, q * x * q⁻¹ = x * v ∨ q * x * q⁻¹ = x * v * S.z := by
  obtain ⟨q, hq, hcl⟩ := D.exists_cl_comm_eq X.hM X.rho hv
  have hcQ : q * x * q⁻¹ * x⁻¹ ∈ S.QG := by
    rw [show q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) by group]
    exact mul_mem hq (S.conj_mem_QG X.hM (inv_mem hq))
  have hxz : x * S.z = S.z * x := S.z_comm X.hM
  refine ⟨q, hq, ?_⟩
  have e : q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
  rcases (S.cl_eq_cl_iff hv.1 hcQ).mp hcl.symm with h | h
  · left
    rw [e, h, X.comm v hv]
  · right
    rw [e, h, mul_assoc, ← hxz, ← mul_assoc, X.comm v hv]

end ThmAData

namespace ThmAData

variable {t : S.O} (D : ThmAData S g t)

@[expose] noncomputable def eV : ElemAb G :=
  ⟨V S g t, fun _ ha _ hb => D.V_comm ha hb, fun _ ha => D.V_mul_self ha⟩

include D in
theorem transv_V (f : Module.Dual (ZMod 2) (Additive D.eV.E)) (hz : S.z ∈ D.eV.E)
    (hf : f (ElemAb.vec (⟨S.z, hz⟩ : D.eV.E)) = 0) :
    ∃ q ∈ S.QG, ∀ v : D.eV.E, q * (v : G) = v * q ↔ f (ElemAb.vec v) = 0 := by
  have hmem : ∀ v : D.eV.E, (v : G) ∈ V S g t := fun v => v.2
  let π₀ : Additive D.eV.E →+ Vt S g t :=
    { toFun := fun a => ⟨S.cl ((Additive.toMul a : D.eV.E) : G), (hmem (Additive.toMul a)).2⟩
      map_zero' := Subtype.ext S.cl_one
      map_add' := fun a b => Subtype.ext
        (S.cl_mul (hmem (Additive.toMul a)).1 (hmem (Additive.toMul b)).1) }
  let π : Additive D.eV.E →ₗ[ZMod 2] Vt S g t := π₀.toZModLinearMap 2
  have hπ : ∀ v : D.eV.E, π (ElemAb.vec v) = ⟨S.cl v, (hmem v).2⟩ := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro s
    obtain ⟨v, hvQ, hv⟩ := S.exists_cl (s : S.Qt)
    exact ⟨ElemAb.vec (⟨v, ⟨hvQ, by rw [hv]; exact s.2⟩⟩ : D.eV.E), Subtype.ext hv⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker f := by
    intro a ha
    obtain ⟨v, rfl⟩ := ElemAb.exists_vec a
    have h0 : S.cl (v : G) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    rw [LinearMap.mem_ker]
    rcases (S.cl_eq_zero_iff (hmem v).1).mp h0 with h | h
    · rw [ElemAb.vec_eq_zero_iff.mpr h, map_zero]
    · rw [show ElemAb.vec v = ElemAb.vec (⟨S.z, hz⟩ : D.eV.E) from ElemAb.vec_eq_vec_iff.mpr h]
      exact hf
  let φ : Vt S g t →ₗ[ZMod 2] ZMod 2 :=
    ((LinearMap.ker π).liftQ f hker).comp (π.quotKerEquivOfSurjective hπs).symm.toLinearMap
  have hφ : ∀ a, φ (π a) = f a := by
    intro a
    show (LinearMap.ker π).liftQ f hker ((π.quotKerEquivOfSurjective hπs).symm (π a)) = f a
    rw [show (π.quotKerEquivOfSurjective hπs).symm (π a) = Submodule.Quotient.mk a by
      rw [LinearEquiv.symm_apply_eq]; rfl]
    rfl
  obtain ⟨q, hq, hqφ⟩ := exists_comm_iff φ
  refine ⟨q, hq, fun v => ?_⟩
  rw [hqφ v (hmem v), ← hφ (ElemAb.vec v), hπ v]

variable {u : G} {x : G}

@[expose] noncomputable def eW (X : XData S g t u x) : ElemAb G :=
  ⟨Wsub (V S g t) x X.comm X.sq,
    fun _ ha _ hb => Wsub_comm (fun a ha b hb => D.V_comm ha hb) ha hb,
    fun _ ha => Wsub_mul_self (fun a ha b hb => D.V_comm ha hb) (fun a ha => D.V_mul_self ha) ha⟩

theorem sigmaEnd4 (hu : Swap S g u) (X : XData S g t u x) : SigmaEnd4 S (D.eW X) D.eV x u where
  V_le := fun b hb => Or.inl hb
  card_A := by
    have hxV : x ∉ V S g t := fun hxV => X.notQ hxV.1
    change Nat.card (Wsub (V S g t) x X.comm X.sq) = 64
    rw [card_Wsub hxV, D.card_V]
  card_V := D.card_V
  z_mem := z_mem_V
  mem_QG_iff := by
    intro b hb
    refine ⟨fun hbQ => ?_, fun hbV => hbV.1⟩
    rcases hb with hb | hb
    · exact hb
    · exfalso
      apply X.notQ
      have e : x = (x * b) * b⁻¹ := by group
      rw [e]
      exact mul_mem hb.1 (inv_mem hbQ)
  x_mem := x_mem_Wsub (hx := X.comm) (hxx := X.sq)
  x_not_mem := fun hxV => X.notQ hxV.1
  u_mem := D.u_mem_normalizer_Wsub hu X
  u_conj_mem := by
    change u * S.z * u⁻¹ ∈ V S g t
    rw [hu.conj_z]
    exact D.a_mem_V
  u_conj_ne := by
    rw [hu.conj_z]
    exact D.hne
  u_not_norm := by
    by_contra hcon
    push Not at hcon
    exact D.not_Y_le_V hu fun y hy => by
      have := hcon (u⁻¹ * y * u) (mem_Ysub.mp hy)
      rwa [show u * (u⁻¹ * y * u) * u⁻¹ = y by group] at this
  QG_le := D.QG_le_normalizer_Wsub X
  trans := by
    intro v hv w hw hv1 hvz hw1 hwz
    obtain ⟨m, hmM, hρ, hm⟩ := D.exists_conj_eq_of_mem_V hv hw hv1 hvz hw1 hwz
    exact ⟨m, D.R_le_normalizer_Wsub X ((mem_R_iff D.ht).mpr ⟨hmM, hρ⟩), hmM, hm⟩
  surj := fun v hv => D.exists_conj_x X hv
  cent_le := fun q hq hc => D.mem_V_of_comm hq hc
  transv := fun f hf => D.transv_V f _ hf

end ThmAData

end CFSG.GF2Type.Smith1979.W4ThmA
