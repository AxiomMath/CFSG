module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CA2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ) {π : MulAut ↥E →* Equiv.Perm (Fin 5)}

@[expose] noncomputable def lamHom (π : MulAut ↥E →* Equiv.Perm (Fin 5)) : ↥c.N1 →* ℤˣ :=
  Perm.sign.comp (π.comp ((MonoidHom.fst (MulAut ↥E) (MulAut ↥E)).comp c.rho))

theorem lamHom_apply (n : ↥c.N1) :
    c.lamHom π n = Perm.sign (π (c.rho n).1) := rfl

theorem lamHom_zconj
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    (n : ↥c.N1) : c.lamHom π (c.zconjN1 n) = c.lamHom π n := by
  rw [lamHom_apply, lamHom_apply, c.rho_zconj]
  exact (hsig _ _ ⟨n, rfl⟩).symm

@[expose] noncomputable def parFun (π : MulAut ↥E →* Equiv.Perm (Fin 5)) (x : G) : ℤˣ := by
  classical
  exact if h : x ∈ c.N1 then c.lamHom π ⟨x, h⟩
    else if h' : x * z ∈ c.N1 then -(c.lamHom π ⟨x * z, h'⟩) else 1

theorem parFun_of_mem {x : G} (hx : x ∈ c.N1) : c.parFun π x = c.lamHom π ⟨x, hx⟩ := by
  classical
  unfold parFun
  rw [dif_pos hx]

theorem parFun_of_not_mem {x : G} (hx : x ∉ c.N1) (hxz : x * z ∈ c.N1) :
    c.parFun π x = -(c.lamHom π ⟨x * z, hxz⟩) := by
  classical
  unfold parFun
  rw [dif_neg hx, dif_pos hxz]

variable {c}

namespace IsRs

variable {Rs : Subgroup G} (hR : c.IsRs Rs)

include hR in
theorem not_mem_N1_mul_z {x : G} (hx : x ∈ Rs) (hxN : x ∉ c.N1) : x * z ∈ c.N1 :=
  (hR.mul_z_mem hx (fun h => hxN h.2)).2

end IsRs

variable (c)

include c in
theorem z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq

theorem zconj_eq_mul (n : ↥c.N1) : ((c.zconjN1 n : ↥c.N1) : G) = z * (n : G) * z := by
  rw [zconjN1_coe, c.z_inv]

theorem parFun_mul_case2 {Rs : Subgroup G} (hR : c.IsRs Rs) {x y : G} (hx : x ∈ Rs)
    (hy : y ∈ Rs) (hxN : x ∈ c.N1) (hyN : y ∉ c.N1) :
    c.parFun π (x * y) = c.parFun π x * c.parFun π y := by
  have hyz : y * z ∈ c.N1 := hR.not_mem_N1_mul_z hy hyN
  have hxyN : x * y ∉ c.N1 := fun h => hyN (by
    have h2 : x⁻¹ * (x * y) ∈ c.N1 := c.N1.mul_mem (c.N1.inv_mem hxN) h
    rwa [inv_mul_cancel_left] at h2)
  have hxyz : x * y * z ∈ c.N1 := by
    have e : x * y * z = x * (y * z) := mul_assoc x y z
    rw [e]; exact c.N1.mul_mem hxN hyz
  rw [c.parFun_of_mem hxN, c.parFun_of_not_mem hyN hyz, c.parFun_of_not_mem hxyN hxyz]
  have e : (⟨x * y * z, hxyz⟩ : ↥c.N1) = ⟨x, hxN⟩ * ⟨y * z, hyz⟩ :=
    Subtype.ext (mul_assoc x y z)
  rw [e, map_mul]
  generalize c.lamHom π ⟨x, hxN⟩ = a
  generalize c.lamHom π ⟨y * z, hyz⟩ = b
  exact (mul_neg a b).symm

theorem parFun_mul_case3
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) {x y : G} (hx : x ∈ Rs)
    (hxN : x ∉ c.N1) (hyN : y ∈ c.N1) :
    c.parFun π (x * y) = c.parFun π x * c.parFun π y := by
  have hxz : x * z ∈ c.N1 := hR.not_mem_N1_mul_z hx hxN
  have hxyN : x * y ∉ c.N1 := fun h => hxN (by
    have h2 : x * y * y⁻¹ ∈ c.N1 := c.N1.mul_mem h (c.N1.inv_mem hyN)
    rwa [mul_inv_cancel_right] at h2)
  have hzyz : z * y * z ∈ c.N1 := by
    have h2 := c.z_conj_N1 hyN
    rwa [c.z_inv] at h2
  have e0 : x * y * z = (x * z) * (z * y * z) := by
    calc x * y * z = x * (z * z) * y * z := by rw [c.h.z_sq]; group
      _ = (x * z) * (z * y * z) := by group
  have hxyz : x * y * z ∈ c.N1 := by rw [e0]; exact c.N1.mul_mem hxz hzyz
  rw [c.parFun_of_mem hyN, c.parFun_of_not_mem hxN hxz, c.parFun_of_not_mem hxyN hxyz]
  have e : (⟨x * y * z, hxyz⟩ : ↥c.N1) = ⟨x * z, hxz⟩ * c.zconjN1 ⟨y, hyN⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, c.zconj_eq_mul]
    exact e0
  rw [e, map_mul, c.lamHom_zconj hsig]
  generalize c.lamHom π ⟨x * z, hxz⟩ = a
  generalize c.lamHom π ⟨y, hyN⟩ = b
  exact (neg_mul a b).symm

theorem parFun_mul_case4
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) {x y : G} (hx : x ∈ Rs) (hy : y ∈ Rs)
    (hxN : x ∉ c.N1) (hyN : y ∉ c.N1) :
    c.parFun π (x * y) = c.parFun π x * c.parFun π y := by
  have hxz : x * z ∈ c.N1 := hR.not_mem_N1_mul_z hx hxN
  have hyz : y * z ∈ c.N1 := hR.not_mem_N1_mul_z hy hyN
  have e0 : x * y = (x * z) * (z * (y * z) * z) := by
    calc x * y = x * (z * z) * y * (z * z) := by rw [c.h.z_sq]; group
      _ = (x * z) * (z * (y * z) * z) := by group
  have hzyz : z * (y * z) * z ∈ c.N1 := by
    have h2 := c.z_conj_N1 hyz
    rwa [c.z_inv] at h2
  have hxyN : x * y ∈ c.N1 := by rw [e0]; exact c.N1.mul_mem hxz hzyz
  rw [c.parFun_of_not_mem hxN hxz, c.parFun_of_not_mem hyN hyz, c.parFun_of_mem hxyN]
  have e : (⟨x * y, hxyN⟩ : ↥c.N1) = ⟨x * z, hxz⟩ * c.zconjN1 ⟨y * z, hyz⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, c.zconj_eq_mul]
    exact e0
  rw [e, map_mul, c.lamHom_zconj hsig]
  generalize c.lamHom π ⟨x * z, hxz⟩ = a
  generalize c.lamHom π ⟨y * z, hyz⟩ = b
  exact (neg_mul_neg a b).symm

theorem parFun_mul
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) {x y : G} (hx : x ∈ Rs) (hy : y ∈ Rs) :
    c.parFun π (x * y) = c.parFun π x * c.parFun π y := by
  by_cases hxN : x ∈ c.N1
  · by_cases hyN : y ∈ c.N1
    · have hxyN : x * y ∈ c.N1 := c.N1.mul_mem hxN hyN
      rw [c.parFun_of_mem hxN, c.parFun_of_mem hyN, c.parFun_of_mem hxyN]
      have e : (⟨x * y, hxyN⟩ : ↥c.N1) = ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
      rw [e, map_mul]
    · exact c.parFun_mul_case2 hR hx hy hxN hyN
  · by_cases hyN : y ∈ c.N1
    · exact c.parFun_mul_case3 hsig hR hx hxN hyN
    · exact c.parFun_mul_case4 hsig hR hx hy hxN hyN

@[expose] noncomputable def parHom
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) : ↥Rs →* ℤˣ where
  toFun x := c.parFun π (x : G)
  map_one' := by
    rw [Subgroup.coe_one, c.parFun_of_mem c.N1.one_mem]
    exact map_one (c.lamHom π)
  map_mul' x y := by
    rw [Subgroup.coe_mul]
    exact c.parFun_mul hsig hR x.2 y.2

theorem parFun_z {Rs : Subgroup G} (hR : c.IsRs Rs) : c.parFun π z = -1 := by
  have hzN : z ∉ c.N1 := fun h => hR.relIndex_R.2 ⟨hR.z_mem, h⟩
  have hzz : z * z ∈ c.N1 := by rw [c.h.z_sq]; exact c.N1.one_mem
  rw [c.parFun_of_not_mem hzN hzz]
  have e : (⟨z * z, hzz⟩ : ↥c.N1) = 1 := Subtype.ext (c.h.z_sq)
  rw [e, map_one]

@[expose] noncomputable def U1
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) : Subgroup G :=
  (c.parHom hsig hR).ker.map Rs.subtype

theorem mem_U1
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) {x : G} :
    x ∈ c.U1 hsig hR ↔ x ∈ Rs ∧ c.parFun π x = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem U1_le
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) : c.U1 hsig hR ≤ Rs :=
  fun _ hx => ((c.mem_U1 hsig hR).1 hx).1

theorem z_not_mem_U1
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) : z ∉ c.U1 hsig hR := by
  intro h
  have h1 := ((c.mem_U1 hsig hR).1 h).2
  rw [c.parFun_z hR] at h1
  exact absurd h1 (by decide)

theorem U1_relIndex
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) : (c.U1 hsig hR).relIndex Rs = 2 := by
  have hinj : Function.Injective Rs.subtype := Subtype.val_injective
  have h1 : (c.U1 hsig hR).relIndex Rs = (c.parHom hsig hR).ker.index := by
    have h2 := Subgroup.relIndex_map_map_of_injective (c.parHom hsig hR).ker (⊤ : Subgroup ↥Rs) hinj
    have h3 : (⊤ : Subgroup ↥Rs).map Rs.subtype = Rs := by
      rw [← MonoidHom.range_eq_map]; exact Rs.range_subtype
    rw [h3, Subgroup.relIndex_top_right] at h2
    exact h2
  rw [h1, Subgroup.index_ker]
  have hsurj : (c.parHom hsig hR).range = ⊤ := by
    refine MonoidHom.range_eq_top.2 fun u => ?_
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨⟨z, hR.z_mem⟩, ?_⟩
      exact c.parFun_z hR
  rw [hsurj, Subgroup.card_top, Nat.card_eq_fintype_card]
  exact Fintype.card_units_int

theorem mem_U1_of_mem_N1
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) {x : G} (hx : x ∈ Rs) (hxN : x ∈ c.N1) :
    x ∈ c.U1 hsig hR ↔ c.lamHom π ⟨x, hxN⟩ = 1 := by
  rw [c.mem_U1 hsig hR, c.parFun_of_mem hxN]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

theorem mem_U1_of_not_mem_N1
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {Rs : Subgroup G} (hR : c.IsRs Rs) {x : G} (hx : x ∈ Rs) (hxN : x ∉ c.N1)
    (hxz : x * z ∈ c.N1) :
    x ∈ c.U1 hsig hR ↔ c.lamHom π ⟨x * z, hxz⟩ = -1 := by
  rw [c.mem_U1 hsig hR, c.parFun_of_not_mem hxN hxz]
  constructor
  · intro h
    exact neg_eq_iff_eq_neg.1 h.2
  · intro h
    exact ⟨hx, by rw [h]; exact neg_neg 1⟩

theorem lam_of_conj_z
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b))
    {n y : G} (hn : n ∈ c.N1) (hny : n * z * n⁻¹ = y) :
    ∃ h : y * z ∈ c.N1, c.lamHom π ⟨y * z, h⟩ = 1 := by
  have hzn : z * n * z⁻¹ ∈ c.N1 := c.z_conj_N1 hn
  have hyz : y * z = n * (z * n * z⁻¹)⁻¹ := by
    have h1 : n * (z * n * z⁻¹)⁻¹ = (n * z * n⁻¹) * z⁻¹ := by group
    rw [h1, hny, c.z_inv]
  have hmem : y * z ∈ c.N1 := by
    rw [hyz]; exact c.N1.mul_mem hn (c.N1.inv_mem hzn)
  refine ⟨hmem, ?_⟩
  have e : (⟨y * z, hmem⟩ : ↥c.N1) = ⟨n, hn⟩ * (c.zconjN1 ⟨n, hn⟩)⁻¹ :=
    Subtype.ext hyz
  rw [e, map_mul, map_inv, c.lamHom_zconj hsig]
  exact mul_inv_cancel _

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
