module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem card_mulAut_of_elemAb_sixteen {E : Type*} [Group E] [Finite E]
    (hc : ∀ a b : E, a * b = b * a) (hs : ∀ a : E, a * a = 1) (hcard : Nat.card E = 16) :
    Nat.card (MulAut E) = 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup E := { ‹Group E› with mul_comm := hc }
  have h2 : ∀ x : Additive E, (2 : ℕ) • x = 0 := fun x => by
    change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
    rw [sq, hs]
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule h2
  have hfin : Module.Finite (ZMod 2) (Additive E) := Module.Finite.of_finite
  have h4 : Module.finrank (ZMod 2) (Additive E) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    have h1 : Nat.card (Additive E) = 2 ^ 4 := by
      change Nat.card E = 2 ^ 4
      rw [hcard]
      norm_num
    rw [h1, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : MulAut E ≃ (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun α => { (MulEquiv.toAdditive α : Additive E ≃+ Additive E) with
        map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive α) c x }
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := fun α => by ext; rfl
      right_inv := fun f => by ext; rfl }
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) h4
  have hGL := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive E)).toEquiv
  rw [Nat.card_congr e, ← Nat.card_congr hGL,
    ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field, ZMod.card]
  decide

theorem relIndex_centralizer_eq_ncard {G : Type*} [Group G] (X : Subgroup G) (t : G) :
    (centralizer ({t} : Set G)).relIndex X = {y : G | ∃ x ∈ X, x⁻¹ * t * x = y}.ncard := by
  let _ : MulAction X G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp X.subtype)
  have hsmul : ∀ (x : X) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := fun _ _ => rfl
  have hstab : MulAction.stabilizer X t = (centralizer ({t} : Set G)).subgroupOf X := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul, eq_comm]
  have horb : MulAction.orbit X t = {y : G | ∃ x ∈ X, x⁻¹ * t * x = y} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G)⁻¹, inv_mem x.2, by rw [hsmul, inv_inv]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x⁻¹, inv_mem hx⟩, by rw [hsmul]; simp⟩
  rw [relIndex, ← hstab, MulAction.index_stabilizer, horb]

section Section

variable {G : Type*} [Group G] (P : Subgroup G)

@[expose] def innSub : Subgroup (MulAut P) := (MulAut.conj : P →* MulAut P).range

theorem mulAut_mul_conj_mul_inv (α : MulAut P) (p : P) :
    α * MulAut.conj p * α⁻¹ = MulAut.conj (α p) := by
  refine MulEquiv.ext fun q => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

instance innSub_normal : (innSub P).Normal :=
  ⟨fun _ ⟨p, hp⟩ α => ⟨α p, by rw [← hp, mulAut_mul_conj_mul_inv]⟩⟩

@[expose] def secHom : normalizer (P : Set G) →* MulAut (innSub P) :=
  (MulAut.conjNormal (H := innSub P)).comp P.normalizerMonoidHom

theorem conj_eq_conj_iff {p q : P} :
    MulAut.conj p = MulAut.conj q ↔ ∀ r : P, (p * q⁻¹) * r = r * (p * q⁻¹) := by
  constructor
  · intro h r
    have e := congrArg (fun α : MulAut P => α (q⁻¹ * r * q)) h
    simp only [MulAut.conj_apply] at e
    have e' : p * (q⁻¹ * r * q) * p⁻¹ = r := by rw [e]; group
    calc p * q⁻¹ * r = p * (q⁻¹ * r * q) * p⁻¹ * (p * q⁻¹) := by group
      _ = r * (p * q⁻¹) := by rw [e']
  · intro h
    refine MulEquiv.ext fun r => ?_
    simp only [MulAut.conj_apply]
    have e := h (q * r * q⁻¹)
    calc p * r * p⁻¹ = (p * q⁻¹) * (q * r * q⁻¹) * (p * q⁻¹)⁻¹ := by group
      _ = (q * r * q⁻¹) * (p * q⁻¹) * (p * q⁻¹)⁻¹ := by rw [e]
      _ = q * r * q⁻¹ := by group

theorem secHom_apply_conj (x : normalizer (P : Set G)) (p : P) :
    ((secHom P x ⟨MulAut.conj p, ⟨p, rfl⟩⟩ : innSub P) : MulAut P) =
      MulAut.conj (P.normalizerMonoidHom x p) := by
  rw [secHom, MonoidHom.comp_apply, MulAut.conjNormal_apply, mulAut_mul_conj_mul_inv]

theorem secHom_eq_one_iff (x : normalizer (P : Set G)) :
    secHom P x = 1 ↔ ∀ p ∈ P, ∀ q ∈ P,
      (x * p * (x : G)⁻¹ * p⁻¹) * q = q * (x * p * (x : G)⁻¹ * p⁻¹) := by
  constructor
  · intro h p hp q hq
    have e := secHom_apply_conj P x ⟨p, hp⟩
    rw [h, MulAut.one_apply] at e
    have := (conj_eq_conj_iff P).1 e.symm ⟨q, hq⟩
    exact congrArg Subtype.val this
  · intro h
    refine MulEquiv.ext fun c => Subtype.ext ?_
    obtain ⟨_, ⟨p, rfl⟩⟩ := c
    rw [MulAut.one_apply, secHom_apply_conj]
    refine (conj_eq_conj_iff P).2 fun r => Subtype.ext ?_
    exact h p p.2 r r.2

theorem conj_eq_one_iff_mem {Z : Subgroup G} (hZ : ∀ z, z ∈ Z ↔ z ∈ P ∧ ∀ q ∈ P, z * q = q * z)
    (z : P) : MulAut.conj z = 1 ↔ (z : G) ∈ Z := by
  rw [← map_one MulAut.conj, conj_eq_conj_iff, hZ]
  simp only [inv_one, mul_one]
  constructor
  · intro h
    exact ⟨z.2, fun q hq => congrArg Subtype.val (h ⟨q, hq⟩)⟩
  · rintro ⟨-, h⟩ r
    exact Subtype.ext (h r r.2)

theorem innSub_comm_sq {Z : Subgroup G} (hZ : ∀ z, z ∈ Z ↔ z ∈ P ∧ ∀ q ∈ P, z * q = q * z)
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Z) (hsq : ∀ p ∈ P, p * p ∈ Z) :
    (∀ a b : innSub P, a * b = b * a) ∧ ∀ a : innSub P, a * a = 1 := by
  constructor
  · rintro ⟨_, ⟨p, rfl⟩⟩ ⟨_, ⟨q, rfl⟩⟩
    refine Subtype.ext ?_
    change MulAut.conj p * MulAut.conj q = MulAut.conj q * MulAut.conj p
    rw [← map_mul, ← map_mul, conj_eq_conj_iff]
    intro r
    have hz := (hZ _).1 (hcomm p p.2 q q.2)
    exact Subtype.ext (by
      have := hz.2 r r.2
      simpa [mul_assoc] using this)
  · rintro ⟨_, ⟨p, rfl⟩⟩
    refine Subtype.ext ?_
    change MulAut.conj p * MulAut.conj p = 1
    rw [← map_mul]
    exact (conj_eq_one_iff_mem P hZ (p * p)).2 (hsq p p.2)

variable [Finite G]

theorem card_innSub {Z : Subgroup G} (hZ : ∀ z, z ∈ Z ↔ z ∈ P ∧ ∀ q ∈ P, z * q = q * z)
    (hcard : Nat.card P = 16 * Nat.card Z) : Nat.card (innSub P) = 16 := by
  have hk := Subgroup.card_ker_mul_card_range (MulAut.conj : P →* MulAut P)
  have hker : Nat.card (MulAut.conj : P →* MulAut P).ker = Nat.card Z := by
    refine Nat.card_congr
      { toFun := fun z => ⟨((z : P) : G), (conj_eq_one_iff_mem P hZ z).1 z.2⟩
        invFun := fun z => ⟨⟨z, ((hZ z).1 z.2).1⟩, (conj_eq_one_iff_mem P hZ _).2 z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hker, hcard] at hk
  have hZ0 : 0 < Nat.card Z := Nat.card_pos
  change Nat.card (MulAut.conj : P →* MulAut P).range = 16
  nlinarith

theorem index_ker_secHom_dvd {Z : Subgroup G}
    (hZ : ∀ z, z ∈ Z ↔ z ∈ P ∧ ∀ q ∈ P, z * q = q * z) (hcard : Nat.card P = 16 * Nat.card Z)
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Z) (hsq : ∀ p ∈ P, p * p ∈ Z) :
    (secHom P).ker.index ∣ 20160 := by
  obtain ⟨hinn_comm, hinn_sq⟩ := innSub_comm_sq P hZ hcomm hsq
  have hcardAut := card_mulAut_of_elemAb_sixteen hinn_comm hinn_sq (card_innSub P hZ hcard)
  rw [Subgroup.index_ker, ← hcardAut]
  exact Subgroup.card_subgroup_dvd_card (secHom P).range

end Section

theorem relIndex_centralizer_dvd_card {G : Type*} [Group G] [Finite G] {K V : Subgroup G} {t : G}
    (hKV : ∀ x ∈ K, ∀ v ∈ V, x * v = v * x) (hKt : ∀ x ∈ K, x⁻¹ * t * x * t⁻¹ ∈ V) :
    (centralizer ({t} : Set G)).relIndex K ∣ Nat.card V := by
  let ψ : K →* V :=
    { toFun := fun x => ⟨(x : G)⁻¹ * t * x * t⁻¹, hKt x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((x : G) * y)⁻¹ * t * (x * y) * t⁻¹ =
          ((x : G)⁻¹ * t * x * t⁻¹) * ((y : G)⁻¹ * t * y * t⁻¹)
        have e := hKV y y.2 _ (hKt x x.2)
        calc ((x : G) * y)⁻¹ * t * (x * y) * t⁻¹ =
            (y : G)⁻¹ * ((x : G)⁻¹ * t * x * t⁻¹) * y * ((y : G)⁻¹ * t * y * t⁻¹) := by group
          _ = (y : G)⁻¹ * (y * ((x : G)⁻¹ * t * x * t⁻¹)) * ((y : G)⁻¹ * t * y * t⁻¹) := by
              rw [mul_assoc (y : G)⁻¹ _ (y : G), e]
          _ = _ := by group) }
  have hker : ψ.ker = (centralizer ({t} : Set G)).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_singleton_iff]
    change (⟨(x : G)⁻¹ * t * x * t⁻¹, _⟩ : V) = 1 ↔ _
    rw [Subtype.ext_iff, coe_one, mul_inv_eq_one]
    constructor
    · intro h
      calc (x : G) * t = x * ((x : G)⁻¹ * t * x) := by rw [h]
        _ = t * x := by group
    · intro h
      calc (x : G)⁻¹ * t * x = (x : G)⁻¹ * (t * x) := by group
        _ = (x : G)⁻¹ * (x * t) := by rw [h]
        _ = t := by group
  rw [relIndex, ← hker, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card ψ.range

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
