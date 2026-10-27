module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.QuaternionStructure CFSG.GorensteinWalter
open scoped MatrixGroups

theorem nonempty_mulEquiv_sl2_of_ker {E : Type*} [Group E] [Finite E] {k : Type*} [Field k]
    [Finite k] (hk : ringChar k ≠ 2) (π : E →* PSL2 k) (hπ : Function.Surjective π) {z : E}
    (hker : π.ker = Subgroup.zpowers z) (hz : orderOf z = 2)
    (huniq : ∀ t : E, orderOf t = 2 → t = z) : Nonempty (E ≃* SL(2, k)) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hzk : z ∈ π.ker := hker ▸ Subgroup.mem_zpowers z
  have hcen : π.ker ≤ Subgroup.center E := by
    rw [hker, Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    have h1 : orderOf (g * z * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
    have h3 := huniq _ h1
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h3]
  have h2p : IsPGroup 2 π.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hπ hcen h2p
    (QuotientGroup.mk' (Subgroup.center SL(2, k)))
  have hβx : ∀ x, π (β x) = (QuotientGroup.mk x : PSL2 k) := fun x => DFunLike.congr_fun hβ x
  have hβneg : β (-1) ≠ 1 := by
    intro hneg
    let w := CFSG.Semidihedral.OddLinearNormals.quarterTurn k
    have hw2 : w ^ 2 = -1 := CFSG.Semidihedral.OddFieldSL2.quarterTurn_square k
    have hβw2 : (β w) ^ 2 = 1 := by rw [← map_pow, hw2, hneg]
    have hwc : (QuotientGroup.mk w : PSL2 k) ≠ 1 := fun h1 =>
      CFSG.Semidihedral.OddLinearNormals.quarterTurn_not_mem_center k
        ((QuotientGroup.eq_one_iff w).mp h1)
    have hβw1 : β w ≠ 1 := by
      intro h1
      apply hwc
      rw [← hβx w, h1, map_one]
    have hzeq := huniq _ (orderOf_eq_prime hβw2 hβw1)
    have hp1 : π (β w) = 1 := by
      rw [hzeq]
      exact hzk
    exact hwc (by rw [← hβx w]; exact hp1)
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : β x = 1 := hx
    have hx2 : (QuotientGroup.mk x : PSL2 k) = 1 := by rw [← hβx x, hx1, map_one]
    have hxc : x ∈ Subgroup.center SL(2, k) := (QuotientGroup.eq_one_iff x).mp hx2
    rcases mem_center_specialLinearGroup_two_iff.mp hxc with rfl | rfl
    · exact one_mem _
    · exact absurd hx1 hβneg
  have hcardE : Nat.card E = Nat.card SL(2, k) := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top, hker, Nat.card_zpowers, hz] at h1
    rw [← h1, natCard_specialLinearGroup_two h2]
    ring
  have hbij : Function.Bijective β := hinj.bijective_of_nat_card_le (le_of_eq hcardE)
  exact ⟨(MulEquiv.ofBijective β hbij).symm⟩

theorem isSL2ModOdd_of_mulEquiv {G : Type} [Group G] {H : Subgroup G} {F : Type*} [Field F]
    [Finite F] (hF : ringChar F ≠ 2) (e : ↥H ⧸ classicalInvolutionOddCore ↥H ≃* SL(2, F)) :
    IsSL2ModOdd H (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  have hp : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
  have : Fintype (GaloisField (ringChar F) n) := Fintype.ofFinite _
  let eF : F ≃+* GaloisField (ringChar F) n :=
    FiniteField.ringEquivOfCardEq (by
      rw [hn, Fintype.card_eq_nat_card (α := GaloisField (ringChar F) n),
        GaloisField.card _ _ hn0])
  refine ⟨ringChar F, n, hp, hF, n.pos, ?_, ⟨e.trans (slRingEquiv eF)⟩⟩
  rw [Nat.card_eq_fintype_card, hn]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
