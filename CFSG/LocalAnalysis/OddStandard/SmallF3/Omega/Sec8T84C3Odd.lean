module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Tr

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

theorem oddCore_eq_bot_of_wreath (hA5 : Sec8T84FactA5) {G : Type} [Group G] (E B : Subgroup G)
    (hE : IsElemAb2 E 8) (hB : IsElemAb2 B 4) (hBE : B ≤ E) (u : MulAut ↥E)
    (A H P M1 M2 : Subgroup (MulAut ↥E)) (hu2 : u * u = 1)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6))) (hAu : ∀ a ∈ A, a * u = u * a)
    (hAf : ∀ a ∈ A, (∀ e : ↥E, (e : G) ∈ B → a e = e) → a = 1)
    (huH : u ∈ H) (hAH : A ≤ H) (hPH : P ≤ H) (hPn : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P)
    (hPodd : Odd (Nat.card ↥P)) (hPu : ∀ p ∈ P, p * u = u * p → p = 1)
    (hW : WreathMod H P M1 M2 u) : P = ⊥ := by
  classical
  obtain ⟨⟨hEcomm, hEexp⟩, hEcard⟩ := hE
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_mem_isMulCommutative E a.2 b.2) }
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hctx : Ctx ↥E u H (B.subgroupOf E) :=
    { sq := fun v => Subtype.ext (by simpa [pow_two] using hEexp v v.2)
      card := hEcard
      u_sq := hu2
      u_mem := huH
      fix := fun e => (hfix e).trans Subgroup.mem_subgroupOf.symm
      card_B := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE).toEquiv, hB.2]
        norm_num
      trans := fun x hx hx1 y hy hy1 =>
        trans_of_factA5 hA5 E B hB hBE u hfix A H hA hAu hAf hAH x
          (Subgroup.mem_subgroupOf.mp hx) hx1 y (Subgroup.mem_subgroupOf.mp hy) hy1 }
  exact eq_bot_of_ctx hctx hPn hPodd hPu hW

end C10

end CFSG.OddStandard.SmallF3.Omega
