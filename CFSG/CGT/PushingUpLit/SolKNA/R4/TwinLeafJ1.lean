module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafAut
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

theorem exists_noncomm_of_simple_of_not_prime {G : Type*} [Group G] [IsSimpleGroup G]
    (hp : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := fun a b => h a b }
  exact hp (IsSimpleGroup.prime_card (α := G))


theorem noQ16_mulAut_j1 (F : Type) [Group F] (h : NativeSporadic.IsSporadic F .J1) :
    NoQ16 (MulAut F) := by
  obtain ⟨e₀⟩ := h
  let e : F ≃* NativeSporadic.J1 := e₀
  have : Finite NativeSporadic.J1 := CFSG.Sporadic.J1.fam_j1_simplicity.1
  have hs : IsSimpleGroup NativeSporadic.J1 := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hp : ¬ (Nat.card NativeSporadic.J1).Prime := by
    rw [CFSG.Sporadic.J1.card_J1]
    norm_num
  have hZ : Subgroup.center NativeSporadic.J1 = ⊥ :=
    center_eq_bot_of_simple (exists_noncomm_of_simple_of_not_prime hp)
  exact noQ16_mulAut_of_equiv e (noQ16_mulAut_of_bijective_conj hZ
    (CFSG.Sporadic.Schreier.at_j1_schreier).2.1 (by rw [CFSG.Sporadic.J1.card_J1]; norm_num))


theorem twinLeafR_j1 {r n : ℕ} (hr : 4 ≤ r) :
    TwinLeafR r n fun F _ => NativeSporadic.IsSporadic F .J1 :=
  twinLeafR_of_noQ16Aut hr fun F _ hF => noQ16_mulAut_j1 F hF

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
