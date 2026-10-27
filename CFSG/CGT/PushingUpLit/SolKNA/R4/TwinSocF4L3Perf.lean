module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Elt2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Ent
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups commutatorElement

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal] {z : A} {K : Type} [Field K]
  [Finite K] {e : ↥T ≃* projectiveSL 3 K} (F : L3Frame T z K e)

@[expose] def L3Frame.J : Subgroup A := (slPart (⊤ : Subgroup (GL (Fin 2) K))).map F.π

theorem L3Frame.J_le : F.J ≤ T ⊓ Subgroup.centralizer ({z} : Set A) := by
  rw [← F.hrange]
  exact Subgroup.map_le_range _ _

theorem L3Frame.comm_le :
    ⁅T ⊓ Subgroup.centralizer ({z} : Set A), T ⊓ Subgroup.centralizer ({z} : Set A)⁆ ≤ F.J := by
  rw [← F.hrange]
  exact commutator_range_le F.π

theorem L3Frame.J_perfect (h4 : 4 ≤ Nat.card K) : Group.IsPerfect ↥F.J := by
  haveI : Group.IsPerfect ↥(slPart (⊤ : Subgroup (GL (Fin 2) K))) :=
    isPerfect_of_equiv_sl2 h4 slPartTopEquiv
  exact Group.IsPerfect.map F.π

@[expose] noncomputable def L3Frame.Φ : SL(2, K) →* MulAut ↥T :=
  (MulAut.conjNormal (H := T)).comp
    ((F.π.comp (slPart (⊤ : Subgroup (GL (Fin 2) K))).subtype).comp slPartTopEquiv.symm.toMonoidHom)

theorem L3Frame.Φ_injective (hC : Subgroup.centralizer (T : Set A) = ⊥) :
    Function.Injective F.Φ :=
  (conjNormal_injective hC).comp ((injective_slPart F.hk).comp slPartTopEquiv.symm.injective)

theorem L3Frame.Φ_range : F.Φ.range = F.J.map (MulAut.conjNormal (H := T)) := by
  ext x
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨F.π (slPartTopEquiv.symm B : ↥(slPart (⊤ : Subgroup (GL (Fin 2) K)))),
      ⟨_, (slPartTopEquiv.symm B).2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨slPartTopEquiv ⟨c, hc⟩, ?_⟩
    show MulAut.conjNormal (F.π ((slPartTopEquiv.symm (slPartTopEquiv ⟨c, hc⟩) :
      ↥(slPart (⊤ : Subgroup (GL (Fin 2) K)))) : ↥(⊤ : Subgroup (GL (Fin 2) K)))) = _
    rw [MulEquiv.symm_apply_apply]

variable {R : Subgroup A} {S : Sylow 2 R}

theorem L3Frame.J_centralizes (hd : TightDatum R S z) (hodd : Odd (Nat.card K))
    (h4 : 4 ≤ Nat.card K) : ∀ y ∈ F.J, ∀ s ∈ sylowSet S, y * s = s * y := by
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hd F.hrange F.hk hodd h4 slPartTopEquiv
  intro y hy s hs
  exact Subgroup.mem_centralizer_iff.mp (hRJ (mem_sylowSet_le S hs)) y hy

variable (hC : Subgroup.centralizer (T : Set A) = ⊥) (hd : TightDatum R S z)
  (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) {p f : ℕ} (hp : p.Prime)
  (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
  (hZ : Subgroup.center (projectiveSL 3 K) = ⊥)

include hC hd hodd h4 h2 hp hp2 hf hK hZ

theorem two_elts_mem_J {r : ℕ} (hr : 4 ≤ r) (hcls : TightClsR r A R S z) :
    ∀ ψ ∈ autCentOf T (sylowSet S), ∀ k : ℕ, ψ ^ 2 ^ k = 1 →
      ψ ∈ F.J.map (MulAut.conjNormal (H := T)) := by
  obtain ⟨l, ν, hlord, hmax, hl, b, hb, hbι⟩ := l3_entry hC hd hodd h4 h2 F hr hcls
  intro ψ hψ k hk
  obtain ⟨B, hBdet, hψB⟩ := two_elt_conj F hp hp2 hf hK h2 hZ (k := r - 1) (by omega) hlord
    (by rwa [show r - 1 + 1 = r by omega]) hl hb hbι hψ hk
  rw [hψB]
  refine ⟨F.π ⟨B, Subgroup.mem_top _⟩, ⟨⟨B, Subgroup.mem_top _⟩, mem_slPart.mpr ?_, rfl⟩, rfl⟩
  exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, hBdet]; rfl)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
