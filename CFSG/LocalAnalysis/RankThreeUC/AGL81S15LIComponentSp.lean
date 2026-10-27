module

public import CFSG.ClassicalGroups.Symplectic.CentralCoverSp
public import CFSG.ClassicalGroups.Symplectic.OddCentralizerSylow
public import CFSG.GroupTheory.SylowComap

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic

theorem odd_centralizer_centralizes_of_component_sp_of_card_ge_five
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U) (hUmax : IsSylowTwoOf U ⊤)
    {x : L} (hxodd : Odd (orderOf x)) (hxc : x ∈ Subgroup.centralizer (U : Set L))
    (hQcard : 5 ≤ Q.card) : ∀ l : L, x * l = l * x := by
  classical
  obtain ⟨F, hFfield, hFfinite, hFchar, π, hFcard, hπsurj, hker⟩ :=
    exists_central_cover_sp_of_card_ge_five hL m hm Q hQ hv e hQcard
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenter : Subgroup.center (StatedSp m F) = ⊥ :=
    center_statedSp_eq_bot_of_charP_two (m := m) (by omega)
  have hkerbot : π.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hkerbot
  have hUindex : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hUmax.2.2
  let W : Sylow 2 L := hU2.toSylow hUindex
  have hWcoe : (W : Subgroup L) = U := IsPGroup.toSylow_coe hU2 hUindex
  have hker2 : IsPGroup 2 π.ker := by
    rw [hkerbot]
    exact IsPGroup.of_bot
  let Uhat : Sylow 2 (StatedSp m F) :=
    CFSG.sylowComapOfKerIsPGroup π hπsurj hker2 W
  have hUhatcoe : (Uhat : Subgroup (StatedSp m F)) = U.comap π := by
    rw [CFSG.coe_sylowComapOfKerIsPGroup, hWcoe]
  obtain ⟨xhat, hxhat⟩ := hπsurj x
  have hxhat_odd : Odd (orderOf xhat) := by
    rw [← orderOf_injective π hinj xhat, hxhat]
    exact hxodd
  have hxhat_central :
      xhat ∈ Subgroup.centralizer ((Uhat : Subgroup (StatedSp m F)) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyU : π y ∈ U := by
      rw [hUhatcoe] at hy
      exact hy
    have hcomm : π y * x = x * π y :=
      (Subgroup.mem_centralizer_iff.mp hxc) (π y) hyU
    apply hinj
    calc π (y * xhat) = π y * π xhat := map_mul π y xhat
      _ = π y * x := by rw [hxhat]
      _ = x * π y := hcomm
      _ = π xhat * π y := by rw [hxhat]
      _ = π (xhat * y) := by rw [map_mul]
  have hxhat_center : xhat ∈ Subgroup.center (StatedSp m F) :=
    odd_centralizer_sylow_le_center_sp hm Uhat hxhat_odd hxhat_central
  rw [hcenter] at hxhat_center
  have hxhat_one : xhat = 1 := Subgroup.mem_bot.mp hxhat_center
  have hx_one : x = 1 := by
    rw [← hxhat, hxhat_one, map_one]
  intro l
  rw [hx_one]
  simp

end CFSG.LocalAnalysis.RankThreeUC.S15

end
