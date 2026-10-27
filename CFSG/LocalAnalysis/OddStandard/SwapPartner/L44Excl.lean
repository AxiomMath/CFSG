module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Core

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem card_centralizer_ge_and_not_seven_dvd_of_lieModel {Y : Type} [Group Y] [Finite Y]
    (S A : Subgroup Y) [S.Normal] (hS : LieModel S .PSL 4 2 2)
    (hC : ∀ y : Y, (∀ s ∈ S, y * s = s * y) → y = 1)
    (hAS : A ≤ S) (eA : A ≃* alternatingGroup (Fin 8))
    (t d : Y) (ht1 : t ≠ 1) (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a = a * t)
    (hd2 : d * d = 1) (hdt : d * t = t * d) (hdA : ∀ a ∈ A, d * a * d⁻¹ ∈ A)
    (hdout : ¬ ∃ a ∈ A, ∀ x ∈ A, d * x * d⁻¹ = a * x * a⁻¹) :
    15360 ≤ Nat.card (Subgroup.centralizer ({d} : Set Y)) ∧
      ¬ 7 ∣ Nat.card (Subgroup.centralizer ({d} : Set Y)) := by
  classical
  obtain ⟨K, hfieldK, -, hcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel (Q := ↥S) (n := 4) (p := 2) (f := 2) hS
  have hK4 : Nat.card K = 4 := by rw [hcard]; norm_num
  let Ψ : Y →* MulAut (projectiveSL 4 K) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := S))
  have hΨ_apply : ∀ (y : Y) (s : ↥S), Ψ y (e s) = e (MulAut.conjNormal y s) := by
    intro y s
    show e (MulAut.conjNormal y (e.symm (e s))) = e (MulAut.conjNormal y s)
    simp only [MulEquiv.symm_apply_apply]
  have hcongr_conj : ∀ z : ↥S, (MulAut.congr e) (MulAut.conj z) = MulAut.conj (e z) := by
    intro z
    ext p
    show e (MulAut.conj z (e.symm p)) = MulAut.conj (e z) p
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hconj : MulAut.conjNormal (H := S) y = 1 := by
      apply (MulAut.congr e).injective
      show (MulAut.congr e) (MulAut.conjNormal (H := S) y) = (MulAut.congr e) 1
      rw [map_one]
      exact hy
    apply hC y
    intro s hs
    have h := congrArg (fun f : MulAut ↥S => ((f ⟨s, hs⟩ : ↥S) : Y)) hconj
    simp only [MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mk] at h
    calc y * s = (y * s * y⁻¹) * y := by group
      _ = s * y := by rw [h]
  have hinn : ∀ x : projectiveSL 4 K, ∃ s : Y, Ψ s = MulAut.conj x := by
    intro x
    refine ⟨((e.symm x : ↥S) : Y), ?_⟩
    have hstep : Ψ ((e.symm x : ↥S) : Y) =
        (MulAut.congr e) (MulAut.conj (e.symm x)) := by
      show (MulAut.congr e) (MulAut.conjNormal ↑(e.symm x)) =
        (MulAut.congr e) (MulAut.conj (e.symm x))
      rw [MulAut.conjNormal_val]
    rw [hstep, hcongr_conj, MulEquiv.apply_symm_apply]
  let A' : Subgroup (projectiveSL 4 K) := (A.subgroupOf S).map e.toMonoidHom
  let eA' : A' ≃* alternatingGroup (Fin 8) :=
    ((A.subgroupOf S).equivMapOfInjective e.toMonoidHom e.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hAS).trans eA)
  have htA' : ∀ a' ∈ A', Ψ t a' = a' := by
    intro a' ha'
    change a' ∈ (A.subgroupOf S).map e.toMonoidHom at ha'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [Subgroup.mem_subgroupOf] at hs
    change Ψ t (e s) = e s
    have hconj : MulAut.conjNormal t s = s := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      rw [htA (s : Y) hs]
      group
    rw [hΨ_apply, hconj]
  have hdA' : ∀ a' ∈ A', Ψ d a' ∈ A' := by
    intro a' ha'
    change a' ∈ (A.subgroupOf S).map e.toMonoidHom at ha'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [Subgroup.mem_subgroupOf] at hs
    change Ψ d (e s) ∈ A'
    rw [hΨ_apply]
    change e (MulAut.conjNormal d s) ∈ (A.subgroupOf S).map e.toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨MulAut.conjNormal d s, by
      rw [Subgroup.mem_subgroupOf]
      simpa only [MulAut.conjNormal_apply] using hdA (s : Y) hs, rfl⟩
  have hdout' : ¬ ∃ a' ∈ A', ∀ x' ∈ A', Ψ d x' = a' * x' * a'⁻¹ := by
    rintro ⟨a', ha', hfix⟩
    change a' ∈ (A.subgroupOf S).map e.toMonoidHom at ha'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [Subgroup.mem_subgroupOf] at ha
    apply hdout
    refine ⟨(a : Y), ha, fun x hx => ?_⟩
    have hmem : e ⟨x, hAS hx⟩ ∈ A' := by
      change e ⟨x, hAS hx⟩ ∈ (A.subgroupOf S).map e.toMonoidHom
      rw [Subgroup.mem_map]
      exact ⟨⟨x, hAS hx⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩
    have hx' := hfix (e ⟨x, hAS hx⟩) hmem
    rw [hΨ_apply] at hx'
    have h2 : MulAut.conjNormal d ⟨x, hAS hx⟩ = a * ⟨x, hAS hx⟩ * a⁻¹ := by
      apply e.injective
      simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using hx'
    have h3 : d * x * d⁻¹ = (a : Y) * x * (a : Y)⁻¹ := by
      have := congrArg (fun z : ↥S => (z : Y)) h2
      simpa only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_mk] using this
    exact h3
  exact card_centralizer_ge_and_not_seven_dvd hK4 Ψ hΨ hinn A' eA' t d ht1 ht2 htA'
    hd2 hdt hdA' hdout'

end CFSG.OddStandard.AltStdSec.SwapPartner
