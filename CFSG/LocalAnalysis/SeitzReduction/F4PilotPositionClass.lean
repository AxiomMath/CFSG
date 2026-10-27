module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFacts
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

section Involutions

variable {K : Type} [Field K]

theorem exists_perfect_of_conj {C : Type*} [Group C] {w c : C} {P : Subgroup C}
    (hP : ⁅P, P⁆ = P) (hwP : c * w * c⁻¹ ∈ P)
    (hPc : P ≤ centralizer ({c * w * c⁻¹} : Set C)) :
    ∃ P' : Subgroup C, ⁅P', P'⁆ = P' ∧ w ∈ P' ∧ P' ≤ centralizer ({w} : Set C) := by
  refine ⟨P.map (MulAut.conj c⁻¹).toMonoidHom, by rw [← map_commutator, hP],
    ⟨c * w * c⁻¹, hwP, by simp [mul_assoc]⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have h := mem_centralizer_singleton_iff.1 (hPc hp)
  rw [mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc c⁻¹ * p * c * w = c⁻¹ * (p * (c * w * c⁻¹)) * c := by group
    _ = c⁻¹ * ((c * w * c⁻¹) * p) * c := by rw [h]
    _ = w * (c⁻¹ * p * c) := by group

theorem exists_perfect_le_centralizer_of_orderOf_eq_two (hF1 : FactF1 K)
    (hF3p : FactF3Perfect K) (hF4b : FactF4b K) {w : adjointGroup .F4 K} (hw : orderOf w = 2) :
    ∃ P : Subgroup (adjointGroup .F4 K), ⁅P, P⁆ = P ∧ w ∈ P ∧
      P ≤ centralizer ({w} : Set (adjointGroup .F4 K)) := by
  obtain ⟨c, hc⟩ := hF1 w hw
  have hκ : ∀ κ : TwoCentral, c * w * c⁻¹ = yRep K κ → ∃ P : Subgroup (adjointGroup .F4 K),
      ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ centralizer ({w} : Set (adjointGroup .F4 K)) := by
    intro κ h
    refine exists_perfect_of_conj (c := c) (P := centralizer ({yRep K κ} : Set _)) (hF3p κ) ?_ ?_
    · rw [h]
      exact mem_centralizer_singleton_iff.2 rfl
    · rw [h]
  rcases hc with h | h | h | h
  · exact hκ .t h
  · exact hκ .u h
  · exact hκ .tu h
  · obtain ⟨P, hP, hvP, hPc⟩ := hF4b
    exact exists_perfect_of_conj (c := c) hP (h ▸ hvP) (h ▸ hPc)

end Involutions

section Conj

theorem conj_not_mem_of_forall_perfect {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L)) (hZ : center L = ⊥)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) :
    g⁻¹ * t * g ∉ L := by
  intro hw
  have hwo : orderOf (g⁻¹ * t * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ht]
  obtain ⟨P, hP, hwP, hPL, hPw⟩ := hperf _ hw hwo
  have hPt : P ≤ centralizer ({t} : Set G) := hPL.trans (le_centralizer_of_mem_centralizer htC)
  have hPLL := std_perfect_le_inf_conjugate hset hOut htC ht g hP hPt hPw
  obtain ⟨l, hl, hlw⟩ := (hPLL hwP).2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hlw
  have htl : t = l := by
    have : g * (g⁻¹ * l * g) * g⁻¹ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hlw]
    simpa [mul_assoc] using this.symm
  have htZ : (⟨t, htl ▸ hl⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro a
    exact Subtype.ext (mem_centralizer_iff.1 htC a a.2)
  rw [hZ, mem_bot] at htZ
  have ht1 : t = 1 := congrArg Subtype.val htZ
  rw [ht1, orderOf_one] at ht
  exact absurd ht (by decide)

theorem exists_perfect_le_of_mulEquiv
    {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (e : L ≃* adjointGroup .F4 K)
    (hF1 : FactF1 K) (hF3p : FactF3Perfect K) (hF4b : FactF4b K) :
    ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G) := by
  intro w hwL hw
  set φ : adjointGroup .F4 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hwC : orderOf (e ⟨w, hwL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_mk, hw]
  obtain ⟨P, hP, hwP, hPc⟩ := exists_perfect_le_centralizer_of_orderOf_eq_two hF1 hF3p hF4b hwC
  have hφw : φ (e ⟨w, hwL⟩) = w := by simp [hφdef]
  refine ⟨P.map φ, by rw [← map_commutator, hP], ⟨_, hwP, hφw⟩, ?_, ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact (e.symm p).2
  · rintro _ ⟨p, hp, rfl⟩
    have h := mem_centralizer_singleton_iff.1 (hPc hp)
    rw [mem_centralizer_singleton_iff, ← hφw, ← map_mul, ← map_mul, h]

end Conj

section Aut

variable {L C : Type*} [Group L] [Group C]

theorem pow_trans_trans_apply (e : L ≃* C) (φ : MulAut C) (k : ℕ) (a : L) :
    (((e.trans φ).trans e.symm : MulAut L) ^ k) a = e.symm ((φ ^ k) (e a)) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih]
    simp

theorem exists_mulAut_normalForm_of_mulEquiv (e : L ≃* C)
    (h : ∃ φ : MulAut C, (∀ β : MulAut C, ∃ (c : C) (k : ℕ), β = MulAut.conj c * φ ^ k) ∧
      ∀ n : ℕ, φ ^ n ∈ (MulAut.conj : C →* MulAut C).range → φ ^ n = 1) :
    ∃ φ : MulAut L, (∀ β : MulAut L, ∃ (c : L) (k : ℕ), β = MulAut.conj c * φ ^ k) ∧
      ∀ n : ℕ, φ ^ n ∈ (MulAut.conj : L →* MulAut L).range → φ ^ n = 1 := by
  obtain ⟨φ, hgen, hinn⟩ := h
  refine ⟨(e.trans φ).trans e.symm, fun β => ?_, fun n hn => ?_⟩
  · obtain ⟨c, k, hck⟩ := hgen ((e.symm.trans β).trans e)
    refine ⟨e.symm c, k, MulEquiv.ext fun a => ?_⟩
    have h1 := congrArg (fun γ : MulAut C => γ (e a)) hck
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.mul_apply,
      MulAut.conj_apply] at h1
    rw [MulAut.mul_apply, MulAut.conj_apply, pow_trans_trans_apply]
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  · obtain ⟨l, hl⟩ := hn
    have hC : φ ^ n = MulAut.conj (e l) := by
      refine MulEquiv.ext fun x => ?_
      have h1 := congrArg (fun γ : MulAut L => γ (e.symm x)) hl
      simp only [MulAut.conj_apply, pow_trans_trans_apply, MulEquiv.apply_symm_apply] at h1
      rw [MulAut.conj_apply]
      apply e.symm.injective
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    have h1 := hinn n ⟨e l, hC.symm⟩
    refine MulEquiv.ext fun a => ?_
    rw [pow_trans_trans_apply, h1]
    simp

end Aut

@[expose] def OuterFusionTwoCentral {G : Type*} [Group G] (L : Subgroup G) (t : G) : Prop :=
  ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∉ L ⊔ zpowers t →
    ∃ h : G, ∃ z ∈ L, h⁻¹ * t * h = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u

end CFSG.SeitzReduction.F4Pilot
