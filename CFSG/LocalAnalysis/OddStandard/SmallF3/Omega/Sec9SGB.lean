module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Early
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4SlcProj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec9g_centerIn_sq_eq_one [Finite G] {L : Subgroup G} (hL : IsOm6M L) {c : G}
    (hc : c ∈ centerIn L) (hc2 : c * c = 1) : c = 1 := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcL : c ∈ L := ((sec4_mem_centerIn_iff c).mp hc).1
  have hcorder : orderOf c = 2 := orderOf_eq_prime (by rwa [pow_two]) hne
  have hccent : c ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact ((sec4_mem_centerIn_iff c).mp hc).2 k hk |>.symm
  exact sec711M_not_central hL hcL hcorder hccent

theorem sec9g_mem_sup_centerIn {B L : Subgroup G} (hBL : B ≤ L) {y : G}
    (hy : y ∈ B ⊔ centerIn L) : ∃ b ∈ B, ∃ c ∈ centerIn L, y = b * c := by
  refine sec4_mem_sup_of_commute ?_ hy
  intro b hb c hc
  exact (((sec4_mem_centerIn_iff c).mp hc).2 b (hBL hb)).symm

theorem asc82Sec8B_of (hM : Asc82Tab6M) : Asc82Sec8B := by
  intro G _ _ t L S z g B hctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hBL : B ≤ L := fun x hx => (hctx.B_le hx).1
  have hBS : B ≤ S := fun x hx => (hctx.B_le hx).2
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hzL : z ∈ L := hctx.pocket.mem
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb => hctx.B_e16.1.2 b hb
  refine ⟨?_, ?_⟩
  · have hBp : IsPGroup 2 B := IsPGroup.of_card (n := 4) hctx.B_e16.2
    obtain ⟨P, hP, hBP⟩ := sec68_exists_sylow_ge hBp hBL
    have hzcent : z ∈ centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hctx.central b (hBS hb)
    have hzinf : z ∈ L ⊓ centralizer (B : Set G) := ⟨hzL, hzcent⟩
    have hzsup : z ∈ B ⊔ centerIn L := by
      have h := (hM.aut_B G L hLM P hP B hBP hctx.B_e16).2.2
      rw [h] at hzinf
      exact hzinf
    obtain ⟨b, hb, c, hc, hzbc⟩ := sec9g_mem_sup_centerIn hBL hzsup
    have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
    have hbb : b * b = 1 := by rw [← pow_two]; exact hB2 b hb
    have hcb : c * b = b * c := ((sec4_mem_centerIn_iff c).mp hc).2 b (hBL hb)
    have hmul : z * z = (b * b) * (c * c) := by
      rw [hzbc]
      calc (b * c) * (b * c) = b * (c * b) * c := by group
        _ = b * (b * c) * c := by rw [hcb]
        _ = (b * b) * (c * c) := by group
    have hcc : c * c = 1 := by
      rw [hmul, hbb, one_mul] at hzz
      exact hzz
    have hc1 : c = 1 := sec9g_centerIn_sq_eq_one hLM hc hcc
    rw [hzbc, hc1, mul_one]
    exact hb
  · intro b hb hb1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hb2 : orderOf b = 2 := orderOf_eq_prime (hB2 b hb) hb1
    exact hM.inv_one_class G L hLM z b hzL (hBL hb) hz2 hb2

end CFSG.OddStandard.SmallF3.Omega
