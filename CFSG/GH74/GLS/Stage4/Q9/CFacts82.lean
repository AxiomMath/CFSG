module

public import CFSG.GH74.GLS.Stage4.Q9.DFacts
public import CFSG.GH74.GLS.Stage4.Q9.Link1
public import CFSG.GH74.GLS.Stage4.Q9.Lemma82
public import CFSG.GH74.GLS.Stage4.Q9.SettingFacts
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem q8cycle_of_link
    {G : Type} [Group G] {K : Subgroup G} {z : G} (ψ : ↥K ≃* SL2)
    (hzK : z ∈ K) (hz : ψ ⟨z, hzK⟩ = minusOne) : Q8Cycle K z := by
  intro p hp q hq hpp hqq hqp
  have hz' : ψ.symm minusOne = ⟨z, hzK⟩ := by rw [← hz]; simp
  have hpp' : ψ ⟨p, hp⟩ * ψ ⟨p, hp⟩ = minusOne := by
    rw [← map_mul]
    have : (⟨p, hp⟩ * ⟨p, hp⟩ : ↥K) = ⟨z, hzK⟩ := Subtype.ext hpp
    rw [this, hz]
  have hqq' : ψ ⟨q, hq⟩ * ψ ⟨q, hq⟩ = minusOne := by
    rw [← map_mul]
    have : (⟨q, hq⟩ * ⟨q, hq⟩ : ↥K) = ⟨z, hzK⟩ := Subtype.ext hqq
    rw [this, hz]
  have hqp' : ψ ⟨q, hq⟩ * ψ ⟨p, hp⟩ * (ψ ⟨q, hq⟩)⁻¹ = ψ ⟨p, hp⟩ * minusOne := by
    rw [← map_inv, ← map_mul, ← hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hqp)
  obtain ⟨r', h1, h2⟩ := q8cycle_sl2 _ _ hpp' hqq' hqp'
  refine ⟨((ψ.symm r' : ↥K) : G), (ψ.symm r').2, ?_, ?_⟩
  · rcases h1 with h | h
    · left
      have := congrArg (fun x => ψ.symm x) h
      simpa using congrArg Subtype.val this
    · right
      have := congrArg (fun x => ψ.symm x) h
      simpa [hz'] using congrArg Subtype.val this
  · rcases h2 with h | h
    · left
      have := congrArg (fun x => ψ.symm x) h
      simpa using congrArg Subtype.val this
    · right
      have := congrArg (fun x => ψ.symm x) h
      simpa [hz'] using congrArg Subtype.val this

theorem Q9Setting.seven
    {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂) : 7 ∣ Nat.card G := by
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, -, -⟩ := q9_link S
  have hQ₁ : Q8Cycle K₁ z := q8cycle_of_link ψ₁ S.z_mem₁ (hz₁ ⟨z, S.z_mem₁⟩ rfl)
  have hQ₂ : Q8Cycle K₂ z := q8cycle_of_link ψ₂ S.z_mem₂ (hz₂ ⟨z, S.z_mem₂⟩ rfl)
  exact seven_dvd_card S.z_ord S.comm S.inter_eq (fun k hk h => S.K₁_sq_eq_one k hk h) hQ₁ hQ₂
    S.u S.w₁ S.w₂ S.a S.u_mem S.u_ord S.u_ne S.w₁_mem S.w₂_mem S.w₁_sq S.w₂_sq S.w₁_act S.w₂_act
    S.a_norm_z S.a_norm_u S.a_moves S.a_cent

end CFSG.GH74.GLS.Stage4.Q9
