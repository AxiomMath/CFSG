module

public import CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts

public section

namespace CFSG.LinearAlgebra

namespace CoprimeActions

namespace CoprimeElementaryAbelianInvariantHyperplaneComplement

open ElementaryAbelianHyperplaneCounts

theorem exists_complement {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    [IsMulCommutative E] (hE : ∀ x : E, x ^ p = 1) (H : Subgroup (MulAut E))
    (hcop : Nat.Coprime (Nat.card H) p) (D : Subgroup E) (hD : D.index = p)
    (hHD : ∀ h : H, D.map h.val.toMonoidHom = D) :
    ∃ R : Subgroup E, R ⊓ D = ⊥ ∧ R ⊔ D = ⊤ ∧ Nat.card R = p ∧
      ∀ h : H, R.map h.val.toMonoidHom = R := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup E := { ‹Group E› with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  letI := moduleOf hE
  haveI : NeZero (Nat.card H : ZMod p) := by
    refine ⟨?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) h
    exact hp.one_lt.ne' this
  let ρ : Representation (ZMod p) H (Additive E) :=
    { toFun := fun h =>
        { toFun := fun x => Additive.ofMul (h.1 (Additive.toMul x))
          map_add' := fun x y => by simp
          map_smul' := fun c x => by
            exact ZMod.map_smul (MonoidHom.toAdditive h.1.toMonoidHom) c x }
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl }
  have hmem : ∀ (S : Subgroup E) (x : Additive E), x ∈ subgroupEquiv hE S ↔ Additive.toMul x ∈ S :=
    fun S x => Iff.rfl
  have hρ : ∀ (h : H) (x : Additive E), ρ h x = Additive.ofMul (h.1 (Additive.toMul x)) :=
    fun h x => rfl
  let D' : Subrepresentation ρ :=
    { toSubmodule := subgroupEquiv hE D
      apply_mem_toSubmodule := fun h v hv => by
        rw [hmem] at hv ⊢
        rw [hρ]
        have : h.1 (Additive.toMul v) ∈ D.map h.val.toMonoidHom := ⟨_, hv, rfl⟩
        rwa [hHD h] at this }
  obtain ⟨R', hR'⟩ := exists_isCompl D'
  set e := subgroupEquiv hE with he
  have hRe : e (e.symm R'.toSubmodule) = R'.toSubmodule := e.apply_symm_apply _
  have hinf : D'.toSubmodule ⊓ R'.toSubmodule = ⊥ := by
    have := congrArg Subrepresentation.toSubmodule hR'.inf_eq_bot
    exact this
  have hsup : D'.toSubmodule ⊔ R'.toSubmodule = ⊤ := by
    have := congrArg Subrepresentation.toSubmodule hR'.sup_eq_top
    exact this
  have hDe : D'.toSubmodule = e D := rfl
  refine ⟨e.symm R'.toSubmodule, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    rw [e.map_inf, hRe, e.map_bot, ← hDe, inf_comm, hinf]
  · apply e.injective
    rw [e.map_sup, hRe, e.map_top, ← hDe, sup_comm, hsup]
  · haveI : Module.Finite (ZMod p) (Additive E) := Module.Finite.of_finite
    have hcard : ∀ S : Subgroup E, Nat.card S = p ^ Module.finrank (ZMod p) (e S) := by
      intro S
      have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := e S)
      rw [Nat.card_zmod] at this
      exact (Nat.card_congr (Equiv.refl _)).trans this
    have hV : Nat.card E = p ^ Module.finrank (ZMod p) (Additive E) := by
      have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
      rw [Nat.card_zmod] at this
      exact (Nat.card_congr (Equiv.refl _)).trans this
    have h1 : D.index * Nat.card D = Nat.card E := Subgroup.index_mul_card D
    rw [hcard D, hV, hD] at h1
    have h2 : Module.finrank (ZMod p) (e D) + 1 = Module.finrank (ZMod p) (Additive E) := by
      apply Nat.pow_right_injective hp.two_le
      simp only
      rw [pow_succ, ← h1, mul_comm]
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq D'.toSubmodule R'.toSubmodule
    rw [hsup, hinf, finrank_top, finrank_bot, hDe] at h3
    rw [hcard, hRe]
    have : Module.finrank (ZMod p) R'.toSubmodule = 1 := by omega
    rw [this, pow_one]
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := R'.apply_mem_toSubmodule h (v := Additive.ofMul y) (by rw [← hRe] at hy; exact hy)
      rw [hρ] at this
      rw [← hRe]; exact this
    · intro hx
      refine ⟨h.1⁻¹ x, ?_, by simp⟩
      have := R'.apply_mem_toSubmodule (h⁻¹) (v := Additive.ofMul x) (by rw [← hRe] at hx; exact hx)
      rw [hρ] at this
      rw [← hRe]; exact this
end CoprimeElementaryAbelianInvariantHyperplaneComplement
end CoprimeActions
end CFSG.LinearAlgebra
