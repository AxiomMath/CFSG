module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMAct
public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMA7Comm
public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMLift
public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMNine
public import CFSG.LocalAnalysis.GLTheoremB.I2810.LayerMPerm

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section LayerM
variable {V : Type} [Group V] [Finite V]
variable {Kh Eh : Subgroup (MulAut V)} {n : ℕ} {π : ↥Kh →* ↥(alternatingGroup (Fin n))}
  {Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))}

theorem card_Vv_eq (d : ASData Kh Eh n π Vv V₄) : Nat.card ↥Vv = Nat.card ↥Eh :=
  LayerM.card_Vv_eq_aux d

theorem perm_gen_nine_base {V₄ Vv : Subgroup ↥(alternatingGroup (Fin 9))} (hV₄ : IsRootFour V₄)
    (hVv : Vv ≤ V₄) (hc : Nat.card ↥Vv = 2 ∨ Nat.card ↥Vv = 4) :
    ∃ (s : ℕ) (xs : Fin s → ↥(alternatingGroup (Fin 9))), Nat.card ↥Vv ^ s ≤ 2 ^ 6 ∧
      ⊤ ≤ ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom :=
  LayerM.perm_gen_nine_base_aux hV₄ hVv hc

theorem perm_gen_nine (hn : 9 ≤ n) (hV₄ : IsRootFour V₄) (hVv : Vv ≤ V₄)
    (hc : Nat.card ↥Vv = 2 ∨ Nat.card ↥Vv = 4) :
    ∃ (s : ℕ) (xs : Fin s → ↥(alternatingGroup (Fin n))), Nat.card ↥Vv ^ s ≤ 2 ^ 6 ∧
      ∃ F : Subgroup ↥(alternatingGroup (Fin n)),
        F ≤ ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom ∧
          Nonempty (↥F ≃* ↥(alternatingGroup (Fin 9))) :=
  LayerM.perm_gen_nine_of_base hn (fun hV hv hc => perm_gen_nine_base hV hv hc) hV₄ hVv hc

theorem perm_gen_seven {Vv V₄ : Subgroup ↥(alternatingGroup (Fin 7))}
    (hV₄ : IsRootFour V₄) (hVv : Vv ≤ V₄) (hc : Nat.card ↥Vv = 2 ∨ Nat.card ↥Vv = 4) :
    ∃ (s : ℕ) (xs : Fin s → ↥(alternatingGroup (Fin 7))), Nat.card ↥Vv ^ s ≤ 16 ∧
      (Nat.card ↥Vv = 2 → Nat.card ↥Vv ^ s ≤ 8) ∧
        ⊤ ≤ ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom :=
  LayerM.perm_gen_seven_aux hV₄ hVv hc

theorem lift_core (d : ASData Kh Eh n π Vv V₄) {s : ℕ} (xs : Fin s → ↥(alternatingGroup (Fin n))) :
    ∃ J : Subgroup (MulAut V), (fixV' J).index ≤ Nat.card ↥Eh ^ s ∧ ⁅J, J⁆ ≤ Kh ∧
      ∀ y : ↥Kh, π y ∈
          ⁅⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom, ⨆ i, Vv.map (MulAut.conj (xs i)).toMonoidHom⁆ →
        ∃ z ∈ Subgroup.center ↥Kh, (y : MulAut V) * (z : MulAut V) ∈ ⁅J, J⁆ :=
  LayerM.lift_core_aux d xs

theorem kh_le_J (d : ASData Kh Eh n π Vv V₄) {J : Subgroup (MulAut V)}
    {G : Subgroup ↥(alternatingGroup (Fin n))} (hG : ⊤ ≤ G) (hJK : ⁅J, J⁆ ≤ Kh)
    (hJ : ∀ y : ↥Kh, π y ∈ ⁅G, G⁆ →
      ∃ z ∈ Subgroup.center ↥Kh, (y : MulAut V) * (z : MulAut V) ∈ ⁅J, J⁆) : Kh ≤ J :=
  LayerM.kh_le_J_aux d hG hJK hJ

theorem cover_A9 (d : ASData Kh Eh n π Vv V₄) {J : Subgroup (MulAut V)}
    {G F : Subgroup ↥(alternatingGroup (Fin n))} (hFG : F ≤ G)
    (hF : Nonempty (↥F ≃* ↥(alternatingGroup (Fin 9)))) (hJK : ⁅J, J⁆ ≤ Kh)
    (hJ : ∀ y : ↥Kh, π y ∈ ⁅G, G⁆ →
      ∃ z ∈ Subgroup.center ↥Kh, (y : MulAut V) * (z : MulAut V) ∈ ⁅J, J⁆) :
    ∃ Y : Subgroup (MulAut V), Y ≤ J ∧ ∃ π' : ↥Y →* ↥(alternatingGroup (Fin 9)),
      Function.Surjective π' ∧ π'.ker ≤ Subgroup.center ↥Y :=
  LayerM.cover_A9_aux d hFG hF hJK hJ

theorem a9_exclusion (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {J Y : Subgroup (MulAut V)}
    (hJ : (fixV' J).index ≤ 2 ^ 6) (hYJ : Y ≤ J) (π' : ↥Y →* ↥(alternatingGroup (Fin 9)))
    (hπ : Function.Surjective π') (hker : π'.ker ≤ Subgroup.center ↥Y) : False :=
  LayerM.a9_exclusion_aux hc h2 hJ hYJ π' hπ hker

theorem a7_small_false (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))}
    (d : ASData Kh Eh 7 π7 Vv7 V₇) (hidx : (fixV' Kh).index ≤ 8) : False :=
  LayerM.a7_small_false_aux hc h2 d hidx

theorem a7_center_index (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))}
    (d : ASData Kh Eh 7 π7 Vv7 V₇) (hidx : (fixV' Kh).index ≤ 16) :
    Subgroup.center ↥Kh = ⊥ ∧ (fixV' Kh).index = 16 :=
  LayerM.a7_center_index_aux hc h2 d hidx

theorem a7_comm_irred
    (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))}
    (d : ASData Kh Eh 7 π7 Vv7 V₇) (hZ : Subgroup.center ↥Kh = ⊥) (hidx : (fixV' Kh).index = 16) :
    Nat.card ↥(commV' Kh) = 16 ∧ ∀ Y : Subgroup V, Y ≤ commV' Kh → (∀ g ∈ Kh, ∀ y ∈ Y, g y ∈ Y) →
      Y = ⊥ ∨ Y = commV' Kh :=
  LayerM.a7_comm_irred_aux hc h2 d hZ hidx

end LayerM

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
