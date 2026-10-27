module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_hF (hS : Setting G) (hX : A10Facts) (hc : PointConfig IsA10Type G 5 P M x J)
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hB : A10StageB P x J ψ)
    {U : Subgroup G} (hU : IIPlane 5 P x J U)
    (hL42i : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ U →
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x) :
    ∀ F : Subgroup G, IsPGroup 5 F → U ≤ F → F ≤ M → CFSG.Open.pRank 5 F ≤ 2 →
      IsMulCommutative F ∧ ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
  intro F hFp hUF hFM hrk
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := plane_S_decomp hX.sylow hX.noOuter hc
  obtain ⟨-, hTel, -⟩ := plane_T_structure hX.sylow hc
  have hSP : u3S P x = (P : Subgroup G) := le_antisymm inf_le_left (le_inf le_rfl hB.1)
  haveI : IsMulCommutative (u3T P x J) := hTel.1
  haveI : IsCyclic Z := hZcyc
  have hPab : IsMulCommutative (P : Subgroup G) := by
    rw [← hSP, ← hsup]
    exact plane_sup_comm (fun a ha b hb => (hZT b hb a ha).symm)
  have hPc : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : (P : Subgroup G)) ⟨b, hb⟩)
  obtain ⟨m, hm⟩ := plane_pgroup_le_conj hFp P
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    have h := hPc _ (hm a ha) _ (hm b hb)
    calc a * b = m * (m⁻¹ * a * m * (m⁻¹ * b * m)) * m⁻¹ := by group
      _ = m * (m⁻¹ * b * m * (m⁻¹ * a * m)) * m⁻¹ := by rw [h]
      _ = b * a := by group
  refine ⟨IsMulCommutative.of_setLike_mul_comm hFc, fun g hg => hL42i g ?_⟩
  let E : Subgroup G :=
    { carrier := {f | f ∈ F ∧ f ^ 5 = 1}
      mul_mem' := fun {a b} ha hb => ⟨F.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hFc a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨F.one_mem, one_pow 5⟩
      inv_mem' := fun {a} ha => ⟨F.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hEF : E ≤ F := fun f hf => hf.1
  have hUE : U ≤ E := fun u hu => ⟨hUF hu, hU.elem.2 u hu⟩
  have hEel : IsElemAbelian 5 E :=
    ⟨IsMulCommutative.of_setLike_mul_comm (fun a ha b hb => hFc a ha.1 b hb.1), fun f hf => hf.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hFp.to_le hEF)
  have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank (by norm_num) hEF hEel hk).trans hrk
  have hEU : E = U := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hUE ?_
    rw [hk, hU.card]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have hx5 : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hyE : (MulAut.conj g).toMonoidHom (x ^ n) ∈ E := by
    refine ⟨hg ⟨x ^ n, hz, rfl⟩, ?_⟩
    rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx5, one_zpow, map_one]
  rw [hEU] at hyE
  exact hyE

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
