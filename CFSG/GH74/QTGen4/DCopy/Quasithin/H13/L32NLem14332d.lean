module

public import CFSG.Quasithin.H13.L32NLem14332d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)}

theorem Ctx14332.card_le_of_elem_F4 (h1288 : Lemma12_8_8_two_F4) (hKG : KGSp4Quad)
    (C : Ctx14332 G T L V V₂ g a D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hsq : ∀ y ∈ centerOf (fsuU T V), y * y = 1) :
    Nat.card ↥(D.img (l32nH T V)) ≤ 120 := by
  obtain ⟨-, -, -, hq⟩ := h1288 G T L V 3 (fsuV1 T V) V₂ C.setting D
  obtain ⟨q, -, hpol, hinv⟩ := hq (frattiniOf_eq_bot_of_sq (zU_comm _) hsq)
  refine hKG D.V D.B (L128A.HatU.B_isAlt D) (L128A.HatU.B_nondegenerate D) hd _ ?_ q hpol hinv
  intro γ hγ v w
  obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w

theorem not_case_iii_F4 (h1288 : Lemma12_8_8_two_F4) (h14323 : Lemma14323Rest_F4) (hKGq : KGSp4Quad)
    (hKGl : KGSp4Line)
    (C : Ctx14332 G T L V V₂ g a D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hiii : Case14323iii T V g D) : False := by
  have := finite_linearEquiv D

  have hH360 : 360 ≤ Nat.card ↥(D.img (l32nH T V)) := by
    rcases hiii.iso with he | he <;> obtain ⟨e⟩ := he
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    · rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide

  have hne : ∃ y ∈ centerOf (fsuU T V), y * y ≠ 1 := by
    by_contra hall
    push Not at hall
    have := C.card_le_of_elem_F4 h1288 hKGq hd hall
    omega
  have hcard : Nat.card ↥(centerOf (fsuU T V)) = 4 ∨ Nat.card ↥(centerOf (fsuU T V)) = 8 := by
    have := C.card_zU
    rcases hiii.card_zU with h2 | h4
    · left; omega
    · right; omega
  have hodd := C.odd_centralizes_of_not_elem hcard hne
  have hstab := stab_le C hodd

  obtain ⟨⟨hVE, hV4⟩, -, -, -⟩ := h14323 G T L V C.hyp V₂ g C.plane C.gP C.gN D hd
  have hiso : ∀ x ∈ D.hat V, ∀ y ∈ D.hat V, D.B x y = 0 := D.isotropic_hat C.V_U C.V_comm
  have hfin : Module.finrank (ZMod 2) ↥(D.hat V) = 2 := by
    have : Module.Finite (ZMod 2) ↥(D.hat V) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hV4
    have h22 : (2 : ℕ) ^ Module.finrank (ZMod 2) ↥(D.hat V) = 2 ^ 2 := by rw [hV4]; norm_num
    exact Nat.pow_right_injective le_rfl h22
  have hπV : D.π a ∈ D.hat V := L128A.HatU.π_mem_hat D (C.plane.1.1 C.aV₂) C.aU
  have hB : ∀ γ ∈ D.img (l32nH T V), ∀ v w, D.B (γ v) (γ w) = D.B v w := by
    intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w
  obtain ⟨γ, hγH, hγa, w, hw, hγw⟩ := hKGl D.V D.B (L128A.HatU.B_isAlt D)
    (L128A.HatU.B_nondegenerate D) hd _ hB hH360 (D.π a) C.pi_ne (D.hat V) hπV hfin hiso
  have hγS : γ ∈ D.img (l32nH T V) ⊓ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) :=
    Subgroup.mem_inf.mpr ⟨hγH, MulAction.mem_stabilizer_iff.mpr hγa⟩
  obtain ⟨h, hh, hN, rfl⟩ := (L128A.HatU.mem_img D).mp (hstab hγS)
  have hw' : w ∈ D.hat (l32nE T V V₂ g) := hVE ▸ hw
  have := C.maps_hatE hh hN w hw'
  rw [← hVE] at this
  exact hγw this

end L14332

end CFSG.Quasithin.H13
