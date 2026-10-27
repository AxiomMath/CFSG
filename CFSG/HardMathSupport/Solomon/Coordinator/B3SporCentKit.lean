module

public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section AutModel

variable {M : Type*} [Group M] [Finite M] {P R : Subgroup M}

theorem autModel_pow_apply {β : MulAut ↥P} {r : M}
    (hr : ∀ q : ↥P, ((β q : ↥P) : M) = r * q * r⁻¹) (k : ℕ) :
    ∀ q : ↥P, (((β ^ k) q : ↥P) : M) = r ^ k * q * (r ^ k)⁻¹ := by
  induction k with
  | zero => intro q; simp
  | succ k ih =>
    intro q
    rw [pow_succ', MulAut.mul_apply, hr, ih q, pow_succ']
    group

theorem b3SporPair_of_autModel {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hAM : CFSG.Sporadic.SmallOddCore.AutModel P R)
    (hP : Nonempty (↥P ≃* (TauCeti.CFSGIndex.sporadic name).Group))
    (h : ∀ r ∈ R, r ^ p = 1 → B3Phi p (Subgroup.centralizer ({r} : Set M) ⊓ P)) :
    B3SporPair name p := by
  intro S _ _ hs hnc he β hβ
  let e : S ≃* ↥P := he.some.trans hP.some.symm
  let β' : MulAut ↥P := MulAut.congr e β
  have hβ'e : ∀ x : S, β' (e x) = e (β x) := fun x => by
    simp [β', MulAut.congr_apply]
  obtain ⟨r, hrR, hr⟩ := hAM.surj β'
  have hrp : r ^ p = 1 := by
    refine hAM.inj (r ^ p) (R.pow_mem hrR p) fun q hq => ?_
    have h1 := autModel_pow_apply hr p ⟨q, hq⟩
    have hβp : β' ^ p = 1 := by rw [← map_pow, hβ, map_one]
    rw [hβp, MulAut.one_apply] at h1
    have h2 : q = r ^ p * q * (r ^ p)⁻¹ := h1
    calc r ^ p * q = (r ^ p * q * (r ^ p)⁻¹) * r ^ p := by group
      _ = q * r ^ p := by rw [← h2]
  let φ : S →* M := P.subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := P.subtype_injective.comp e.injective
  have hmap : (fixSubgroup β).map φ = Subgroup.centralizer ({r} : Set M) ⊓ P := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hfx : β x = x := hx
      refine ⟨?_, (e x).2⟩
      have h1 := hr (e x)
      rw [hβ'e, hfx] at h1
      change (e x : M) * r = r * (e x : M)
      calc (e x : M) * r = (r * (e x : M) * r⁻¹) * r := by rw [← h1]
        _ = r * (e x : M) := by group
    · rintro ⟨hyr, hyP⟩
      refine ⟨e.symm ⟨y, hyP⟩, ?_, by simp [φ]⟩
      change β (e.symm ⟨y, hyP⟩) = e.symm ⟨y, hyP⟩
      apply e.injective
      rw [← hβ'e, e.apply_symm_apply]
      apply Subtype.ext
      rw [hr]
      change r * y * r⁻¹ = y
      calc r * y * r⁻¹ = (y * r) * r⁻¹ := by rw [hyr]
        _ = y := by group
  have hB := h r hrR hrp
  rw [← hmap] at hB
  exact (b3Phi_map_iff hp φ hφ).1 hB

end AutModel

end CFSG.HardMathSupport.Solomon.Coordinator
