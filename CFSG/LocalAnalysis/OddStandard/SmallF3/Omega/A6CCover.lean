module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTransAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def a6cConj (L : Subgroup G) {s : G} (hsN : s ∈ normalizer (L : Set G)) :
    MulAut ↥L where
  toFun y := ⟨s * y * s⁻¹, (hsN y).mp y.2⟩
  invFun y := ⟨s⁻¹ * y * s, by
    have h := (inv_mem hsN : s⁻¹ ∈ normalizer (L : Set G)) (y : G)
    rw [inv_inv] at h
    exact h.mp y.2⟩
  left_inv y := Subtype.ext (by
    change s⁻¹ * (s * (y : G) * s⁻¹) * s = y
    group)
  right_inv y := Subtype.ext (by
    change s * (s⁻¹ * (y : G) * s) * s⁻¹ = y
    group)
  map_mul' a b := Subtype.ext (by
    change s * ((a : G) * (b : G)) * s⁻¹ = (s * (a : G) * s⁻¹) * (s * (b : G) * s⁻¹)
    group)

theorem coe_a6cConj (L : Subgroup G) {s : G} (hsN : s ∈ normalizer (L : Set G)) (y : ↥L) :
    ((a6cConj L hsN y : ↥L) : G) = s * y * s⁻¹ := rfl

theorem a6cConj_mul_self (L : Subgroup G) {s : G} (hsN : s ∈ normalizer (L : Set G))
    (hss : s * s ∈ centralizer (L : Set G)) : a6cConj L hsN * a6cConj L hsN = 1 := by
  ext y
  have hc : (s * s) * (y : G) = (y : G) * (s * s) := (Subgroup.mem_centralizer_iff.mp hss (y : G)
    y.2).symm
  change s * (s * (y : G) * s⁻¹) * s⁻¹ = y
  calc s * (s * (y : G) * s⁻¹) * s⁻¹ = (s * s) * (y : G) * (s * s)⁻¹ := by group
    _ = y := by rw [hc]; group

theorem mem_fixSub_a6cConj_iff (L : Subgroup G) {s : G} (hsN : s ∈ normalizer (L : Set G))
    (p : ↥L) : p ∈ fixSub (a6cConj L hsN) ↔ s * (p : G) = (p : G) * s := by
  rw [mem_fixSub_iff]
  constructor
  · intro h
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h)

@[expose] def a6cFixEquiv (L : Subgroup G) {s : G} (hsN : s ∈ normalizer (L : Set G)) :
    ↥(fixSub (a6cConj L hsN)) ≃* ↥(L ⊓ centralizer ({s} : Set G)) where
  toFun p := ⟨((p : ↥L) : G), p.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
    ((mem_fixSub_a6cConj_iff L hsN p.1).mp p.2).symm⟩
  invFun q := ⟨⟨(q : G), q.2.1⟩, (mem_fixSub_a6cConj_iff L hsN ⟨(q : G), q.2.1⟩).mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (show (q : G) ∈ centralizer ({s} : Set G) from
      q.2.2)).symm⟩
  left_inv p := rfl
  right_inv q := rfl
  map_mul' a b := rfl

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem a6c_exists_centCover [Finite G] (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hss : s * s ∈ centralizer (L : Set G)) :
    ∃ ρ : ↥(L ⊓ centralizer ({s} : Set G)) →* ↥(ffFix hQ h2 x), OddCentralCover ρ ∧
      ∀ c : ↥(L ⊓ centralizer ({s} : Set G)),
        ((ρ c : ↥(ffFix hQ h2 x)) : ↥(omegaProj hQ)) =
          ff6mPhi e ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ := by
  let σ : MulAut ↥L := a6cConj L hs.1
  let α : MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ h2 x
  have hσ2 : σ * σ = 1 := a6cConj_mul_self L hs.1 hss
  have hαρ : ∀ y : ↥L, ff6mPhi e (σ y) = α (ff6mPhi e y) := fun y =>
    (ff6m_phi_conj hQ h2 e hs y (σ y) (by rw [coe_a6cConj])).symm
  have hρfix : OddCentralCover (fixHom (ff6mPhi e) σ α hαρ) :=
    (ff6m_phi_cover e hodd).oddCentralCover_fixHom hσ2 hαρ
  let f : ↥(L ⊓ centralizer ({s} : Set G)) ≃* ↥(fixSub σ) := (a6cFixEquiv L hs.1).symm
  refine ⟨(fixHom (ff6mPhi e) σ α hαρ).comp f.toMonoidHom, oddCentralCover_comp hρfix f, ?_⟩
  intro c
  show ((fixHom (ff6mPhi e) σ α hαρ) (f c) : ↥(omegaProj hQ)) = ff6mPhi e ⟨(c : G), _⟩
  rw [coe_fixHom]
  congr 1

end Model

end CFSG.OddStandard.SmallF3.Omega
