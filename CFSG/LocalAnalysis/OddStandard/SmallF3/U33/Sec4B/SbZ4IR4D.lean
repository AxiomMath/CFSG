module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ST2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4P

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


private theorem z4iPartD_bound (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ∀ R : Subgroup ↥(ctxNQ t tau x₁ x₂ rho), IsPGroup 2 R →
      R ≤ centralizer ({hz.z4iT} : Set ↥(ctxNQ t tau x₁ x₂ rho)) → Nat.card R ≤ 128 := by
  intro R hR hRc
  let R' : Subgroup G := R.map (ctxNQ t tau x₁ x₂ rho).subtype
  have hR'p : IsPGroup 2 R' := hR.map (ctxNQ t tau x₁ x₂ rho).subtype
  have hcard : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (ctxNQ t tau x₁ x₂ rho).subtype_injective
  have hR'c : R' ≤ centralizer ({t} : Set G) := by
    rintro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hRc hr))
  have hb := S4A.card_le_of_isPGroup_le_centralizer_conj (S := S) (t := t)
    hz.toCtx10.le_invCent hz.toCtx10.isPGroup hz.toCtx10.relIndex_odd
    (Ctx4.card_S_seven hz.toCtx10.toCtx4) 1 hR'p (by simpa using hR'c)
  calc Nat.card R = Nat.card R' := hcard.symm
    _ ≤ 2 ^ 7 := hb
    _ = 128 := by norm_num

theorem z4iPartD (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng V' : Subgroup G} :
    S4B.Z4IPartD (hz.z4iSub Ng) (hz.z4iSub (ctxQ t tau x₁ x₂ rho))
      (hz.z4iSub (ctxYq t tau x₁ x₂ rho)) (hz.z4iSub (fourGrp x₁ x₂)) (hz.z4iSub V')
      (hz.z4iSub (baseGrp x₁ x₂)) (hz.z4iSub (ctxKI t tau x₁ x₂ rho))
      hz.z4iRho hz.z4iT hz.z4iTau hz.z4iLam := by
  refine {
    t_ne_one := fun h => hz.t_ne_one (congrArg Subtype.val h)
    t_ne_tau := fun h => hz.t_ne_tau (congrArg Subtype.val h)
    t_sq := Subtype.ext hz.t_mul_self
    tau_sq := Subtype.ext hz.tau_mul_self
    l_sq := Subtype.ext hz.lam_mul_self
    t_tau := Subtype.ext hz.t_comm_tau
    t_l := Subtype.ext hz.t_lam_comm
    tau_l := Subtype.ext hz.tau_lam
    t_rho := Subtype.ext hz.rho_comm_t.symm
    tau_rho := Subtype.ext hz.rho_comm_tau.symm
    l_rho := Subtype.ext hz.lam_rho
    B_cent_t := fun b hb => by
      have hbB : (b : G) ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
        rw [hz.CQ_t]
        exact hb
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hbB.2).symm
    cent_t_Q := fun q hq hcomm => by
      have hqcent : (q : G) ∈ centralizer ({t} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm).symm
      have hqB : (q : G) ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨hq, hqcent⟩
      rw [hz.CQ_t] at hqB
      exact hqB
    V_cent_t := fun v hv => by
      have hvY : (v : G) ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
        rw [hz.CY_t]
        exact hv
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hvY.2).symm
    Y_cent_t := fun y hy hcomm => by
      have hycent : (y : G) ∈ centralizer ({t} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm).symm
      have hyV : (y : G) ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨hy, hycent⟩
      rw [hz.CY_t] at hyV
      exact hyV
    bound := z4iPartD_bound hz
    not_conj := fun g hg =>
      (Z4Pre.tau_ttau_not_conj (⟨hz.toCtx4Q, hz.q_iso⟩ : Z4Pre t L S x₁ x₂ lam rho tau)).2
        (g : G) (congrArg Subtype.val hg)
  }

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
