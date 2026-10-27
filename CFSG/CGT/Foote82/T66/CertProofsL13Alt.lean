module

public import CFSG.CGT.Foote82.T66.CitedL13
public import CFSG.CGT.Foote82.T66.CitedMC2
import CFSG.Quasithin.SteinbergCBI16A7
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.LocalAnalysis.ComponentClassification.Sol78AltCentralizer
import CFSG.LocalAnalysis.EvenBN.Tits.I21LModAHeart
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 Matrix

namespace L13Alt

theorem h1Zero_of_Z1A_le_B1A {X G M V : Type} [Group X] [Group G] [AddCommGroup M]
    [AddCommGroup V] {act : X → M → M} {μ : G →* AddMonoid.End V} (φ : X ≃* G) (e : M ≃+ V)
    (he : ∀ x m, e (act x m) = μ (φ x) (e m))
    (h : CFSG.Quasithin.JonesParshall.Z1A μ ≤ CFSG.Quasithin.JonesParshall.B1A μ) :
    L13Aux.H1Zero X M act := by
  intro F hF
  let f : G → V := fun g => e (F (φ.symm g))
  have hf : f ∈ CFSG.Quasithin.JonesParshall.Z1A μ := fun g g' => by
    simp only [f, map_mul, hF, map_add, he, MulEquiv.apply_symm_apply]
  obtain ⟨v, hv⟩ := h hf
  refine ⟨e.symm v, fun x => ?_⟩
  apply e.injective
  have h1 := congrFun hv (φ x)
  rw [CFSG.Quasithin.JonesParshall.coboundaryA_apply] at h1
  simp only [f, MulEquiv.symm_apply_apply] at h1
  rw [← h1, map_sub, he, AddEquiv.apply_symm_apply]

@[expose] noncomputable def conjAut {N P : Type} [AddCommGroup N] [Module (ZMod 2) N]
    [AddCommGroup P] [Module (ZMod 2) P] (e : N ≃ₗ[ZMod 2] P) :
    (N ≃ₗ[ZMod 2] N) ≃* (P ≃ₗ[ZMod 2] P) where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by
    ext v
    simp
  right_inv h := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

@[expose] noncomputable def glvEquiv {N : Type} [AddCommGroup N] [Module (ZMod 2) N] {n : ℕ}
    (e : N ≃ₗ[ZMod 2] (Fin n → ZMod 2)) : GLV N ≃* GL (Fin n) (ZMod 2) :=
  (conjAut e).trans (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) (ZMod 2)).symm

theorem glvEquiv_mulVec {N : Type} [AddCommGroup N] [Module (ZMod 2) N] {n : ℕ}
    (e : N ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (g : GLV N) (v : N) :
    ((glvEquiv e g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e v = e (g v) := by
  rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, glvEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  show e (g (e.symm (e v))) = e (g v)
  rw [LinearEquiv.symm_apply_apply]

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem injective_of_surjective_alt7 {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (e : N ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) (Y : Subgroup (GLV N))
    (α : ↥Y →* alternatingGroup (Fin 7)) (hα : Function.Surjective α) : Function.Injective α := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hK
  let Ψ : GLV N ≃* alternatingGroup (Fin 8) :=
    (glvEquiv e).trans CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm
  haveI : Finite (GLV N) := Finite.of_injective Ψ Ψ.injective
  let Y' : Subgroup (alternatingGroup (Fin 8)) := Y.map Ψ.toMonoidHom
  have hYY' : Nat.card ↥Y' = Nat.card ↥Y :=
    (Nat.card_congr (Y.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).toEquiv).symm
  have hY : Nat.card ↥Y = 2520 * Nat.card ↥α.ker := by
    rw [← card_alt7, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
  have hK2 : 2 ≤ Nat.card ↥α.ker := (Subgroup.one_lt_card_iff_ne_bot _).mpr hK
  have htop : Y' = ⊤ := by
    by_contra hne
    have hidx := CFSG.ComponentClassification.Sol78.le_index_of_mulEquiv_alternating
      (by norm_num : 5 ≤ 8) (MulEquiv.refl _) hne
    have hmul := Subgroup.index_mul_card Y'
    rw [card_alt8, hYY', hY] at hmul
    have : 8 * (2520 * 2) ≤ Y'.index * (2520 * Nat.card ↥α.ker) :=
      Nat.mul_le_mul hidx (Nat.mul_le_mul_left _ hK2)
    omega
  have hYcard : Nat.card ↥Y = 20160 := by
    rw [← hYY', htop, Subgroup.card_top, card_alt8]
  have hYsimple : IsSimpleGroup ↥Y := by
    have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((Y.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α.ker with h | h
  · exact hK h
  · rw [h, Subgroup.card_top] at hY
    omega

end L13Alt

open L13Alt

theorem h1AltSevenFour_holds : H1AltSevenFour := by
  intro N _ _ _ hdim Y ⟨α, hα⟩
  haveI : Module.Finite (ZMod 2) N := Module.Finite.of_finite
  let e : N ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) := (Module.finBasisOfFinrankEq (ZMod 2) N hdim).equivFun
  let α' : ↥Y ≃* alternatingGroup (Fin 7) :=
    MulEquiv.ofBijective α ⟨injective_of_surjective_alt7 e Y α hα, hα⟩
  let M : CFSG.Quasithin.SteinbergCB.I16.A7 →* GL (Fin 4) (ZMod 2) :=
    (glvEquiv e).toMonoidHom.comp (Y.subtype.comp α'.symm.toMonoidHom)
  have hM : Function.Injective M :=
    (glvEquiv e).injective.comp (Subtype.val_injective.comp α'.symm.injective)
  refine h1Zero_of_Z1A_le_B1A α' e.toAddEquiv (fun y v => ?_)
    (CFSG.Quasithin.SteinbergCB.I16.Z1A_le_B1A_A7 M hM)
  rw [CFSG.Quasithin.SteinbergCB.I16.matAct_apply]
  show e ((y : GLV N) v) = ((glvEquiv e (α'.symm (α' y) : GLV N) : GL (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ e v
  rw [MulEquiv.symm_apply_apply, glvEquiv_mulVec]

theorem a6NoSixDimIrr_holds : A6NoSixDimIrr := by
  intro W _ _ _ H ⟨φ⟩ hirr hdim
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  let ψ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W) := H.subtype.comp φ.symm.toMonoidHom
  have h := CFSG.LocalAnalysis.EvenBN.Tits.I21L.modA_finrank_irred ψ (fun U hU => by
    have hinv : Invariant H U := fun k hk u hu => by
      have := hU (φ ⟨k, hk⟩) u hu
      simpa [ψ] using this
    rcases hirr.2.2 U hinv bot_le le_top with h | h
    · exact Or.inl h
    · exact Or.inr h)
  omega

end CFSG.CGT.Foote82

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

namespace L13Alt

variable {N : Type} [AddCommGroup N] [Module (ZMod 2) N]

theorem h1Zero_of_central [Finite N] (Y : Subgroup (GLV N)) (z : ↥Y)
    (hz : ∀ y : ↥Y, z * y = y * z) (hfix : ∀ v : N, (z : GLV N) v = v → v = 0) :
    L13Aux.H1Zero ↥Y N fun y a => (y : GLV N) a := by
  intro F hF
  have hinj : Function.Injective fun v : N => (z : GLV N) v - v := by
    intro v w hvw
    have h : (z : GLV N) (v - w) = v - w := by
      rw [map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp hvw
    exact sub_eq_zero.mp (hfix _ h)
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.mp hinj) (F z)
  have hm' : (z : GLV N) m - m = F z := hm
  refine ⟨m, fun y => hinj ?_⟩
  have hzy : F (z * y) = F (y * z) := by rw [hz y]
  rw [hF, hF] at hzy
  have hzy' : F z + (z : GLV N) (F y) = F y + (y : GLV N) (F z) := hzy
  have hcomm : ∀ v, (z : GLV N) ((y : GLV N) v) = (y : GLV N) ((z : GLV N) v) := fun v =>
    congrArg (fun k : ↥Y => (k : GLV N) v) (hz y)
  show (z : GLV N) (F y) - F y = (z : GLV N) ((y : GLV N) m - m) - ((y : GLV N) m - m)
  have h1 : (z : GLV N) (F y) - F y = (y : GLV N) (F z) - F z := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm, hzy', add_comm]
  rw [h1, ← hm', map_sub, map_sub, hcomm]
  abel

theorem h1Zero_threeAltSix (h6 : A6NoSixDimIrr) [Finite N] (hdim : Module.finrank (ZMod 2) N = 6)
    (Y : Subgroup (GLV N)) (hirr : IsIrr Y ⊤) (α : ↥Y →* alternatingGroup (Fin 6))
    (hα : Function.Surjective α) (hker : α.ker ≤ Subgroup.center ↥Y) :
    L13Aux.H1Zero ↥Y N fun y a => (y : GLV N) a := by
  by_cases hK : α.ker = ⊥
  · exact absurd hdim (h6 N Y ⟨MulEquiv.ofBijective α ⟨(MonoidHom.ker_eq_bot_iff α).mp hK, hα⟩⟩
      hirr)
  obtain ⟨⟨z, hzK⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzc : ∀ y : ↥Y, z * y = y * z := fun y =>
    (Subgroup.mem_center_iff.mp (hker hzK) y).symm
  refine h1Zero_of_central Y z hzc fun v hv => ?_
  let J : Submodule (ZMod 2) N :=
    { carrier := {u | (z : GLV N) u = u}
      add_mem' := fun {a b} ha hb => by
        show (z : GLV N) (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := map_zero _
      smul_mem' := fun c u hu => by
        show (z : GLV N) (c • u) = c • u
        rw [map_smul, hu] }
  have hJ : Invariant Y J := fun k hk u hu => by
    have hu' : (z : GLV N) u = u := hu
    show (z : GLV N) (k u) = k u
    have h := congrArg (fun g : ↥Y => (g : GLV N) u) (hzc ⟨k, hk⟩)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h
    rw [h, hu']
  rcases hirr.2.2 J hJ bot_le le_top with h | h
  · have hvJ : v ∈ J := hv
    rw [h] at hvJ
    exact (Submodule.mem_bot _).mp hvJ
  · exfalso
    apply hz1'
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    have hu : u ∈ J := h ▸ Submodule.mem_top
    exact hu

end L13Alt

end CFSG.CGT.Foote82
