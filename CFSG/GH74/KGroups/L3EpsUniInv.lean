module

public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.KGroups.L3EpsUniAut

public section

namespace CFSG.GH74.KGroups.L3Eps.Uni

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {p f : ℕ} {F : Type} [Field F]

theorem IsCover.comp_equiv {h : UnitaryFieldData p f F} {K K' : Type*} [Group K] [Group K']
    {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ) (e : K ≃* K') :
    IsCover h (e.toMonoidHom.comp θ) := by
  refine ⟨e.surjective.comp hθ.surj, ?_⟩
  ext y
  rw [← hθ.ker]
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem exists_cover_of_equiv (h : UnitaryFieldData p f F) {K : Type*} [Group K]
    (e₀ : K ≃* StatedProj (StatedSU 3 (p ^ f) F)) :
    ∃ θ : ↥(unitarySU p f F 3) →* K, IsCover h θ := by
  let ψ : K ≃* unitaryPSU h 3 := e₀.trans (unitaryPSUEquiv h (by norm_num)).symm
  refine ⟨ψ.symm.toMonoidHom.comp (unitaryProj h 3), ψ.symm.surjective.comp (unitaryProj_surjective h 3), ?_⟩
  ext g
  change ψ.symm (unitaryProj h 3 g) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]

theorem theta_dU_ne_one (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) {K : Type*} [Group K]
    {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ) : θ (dU hq) ≠ 1 := by
  intro h1
  have : dU hq ∈ θ.ker := h1
  rw [hθ.ker, mem_unitaryScalars] at this
  obtain ⟨c, -, -, hc⟩ := this
  have h00 := congrFun (congrFun (congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc) 0) 0
  have h22 := congrFun (congrFun (congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc) 2) 2
  simp [coe_dU, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h22
  apply two_ne_zero_of_odd_pow h hq
  linear_combination h22 - h00

theorem theta_dU_sq (hq : Odd (p ^ f)) {K : Type*} [Group K] (θ : ↥(unitarySU p f F 3) →* K) :
    θ (dU hq) * θ (dU hq) = 1 := by
  rw [← map_mul, dU_mul_self, map_one]

theorem invData_of_cover (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ) :
    InvData (p ^ f) K (θ (dU hq)) (levS hq θ) := by
  refine ⟨card_levS h hθ hq, quasisimple_levS h hθ hq (by omega), θ_dU_mem_levS h hq, levS_le_centralizer hq,
    fun x hx s hs => levS_conj_mem h hθ hq hx hs, fun x hx y hy => levS_commutator_mem h hθ hq hx hy,
    fun s hs hs2 => levS_involution h hθ hq hs hs2, fun s hs => levS_center h hθ hq h5 s hs,
    fun σ hσ hfix => aut_fixing_levS h hp h5 hq hθ hσ hfix,
    fun σ hσ hout hσt P hPS hP => graph_solvable_levS h hp h5 hq hθ hσ hout hσt P hPS hP⟩

end CFSG.GH74.KGroups.L3Eps.Uni
