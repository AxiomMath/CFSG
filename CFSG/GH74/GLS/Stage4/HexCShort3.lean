module

public import CFSG.GH74.GLS.Stage4.HexCShort2
public import CFSG.GH74.GLS.Stage4.HexCQuot

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem mem_normalizer_of_conj {N : Subgroup G} {g : G} (h1 : ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, g⁻¹ * n * g⁻¹⁻¹ ∈ N) : g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => h1 n hn, fun hn => ?_⟩
  have := h2 _ hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at this

theorem V15_norm (R : RGD2 6 H r₁ r₂ U root) {q : G} (hq : q ∈ Vsub root 1 5) {n : G}
    (hn : n ∈ Vsub root 2 4) : q * n * q⁻¹ ∈ Vsub root 2 4 := by
  have key : Vsub root 1 5 ≤ Subgroup.normalizer ((Vsub root 2 4 : Subgroup G) : Set G) := by
    refine iSup₂_le fun k hk => ?_
    have hk' := mem_intList_iff.1 hk
    intro x hx
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl
    · exact mem_normalizer_of_conj (fun n hn => root1_norm R hx hn)
        (fun n hn => root1_norm R ((root 1).inv_mem hx) hn)
    · exact Subgroup.le_normalizer (root_le_Vsub (by norm_num) (by norm_num) hx)
    · exact Subgroup.le_normalizer (root_le_Vsub (by norm_num) (by norm_num) hx)
    · exact Subgroup.le_normalizer (root_le_Vsub (by norm_num) (by norm_num) hx)
    · exact mem_normalizer_of_conj (fun n hn => root5_norm R hx hn)
        (fun n hn => root5_norm R ((root 5).inv_mem hx) hn)
  exact (Subgroup.mem_normalizer_iff.1 (key hq) n).1 hn

theorem phi6_D_mem (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (t : E.Fˣ) :
    phi6 r₁ r₂ E.φ (sl2D t) ∈ H := by
  rw [phi6_apply]; exact r12_conj_H R _ (E.hD t)

theorem natQuot_short (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (hC : Hex6Comm root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) :
    NatQuot (phi6 r₁ r₂ E.φ) (Vsub root 1 5) (Vsub root 2 4) (root 5) (root 1) where
  N_le := Vsub_mono (by norm_num) (by norm_num)
  A_le := root_le_Vsub (by norm_num) (by norm_num)
  B_le := root_le_Vsub (by norm_num) (by norm_num)
  N_norm := fun q hq n hn => V15_norm R hq hn
  commAA := fun x hx y hy => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hC.ab 5 (by norm_num) (by norm_num) x hx y hy)]
    exact Subgroup.one_mem _
  commBB := fun x hx y hy => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hC.ab 1 (by norm_num) (by norm_num) x hx y hy)]
    exact Subgroup.one_mem _
  commAB := fun x hx y hy => by
    have h := rgd2_octComm R 1 5 (by norm_num) (by norm_num) (by norm_num) y hy x hx
    have hV : ⁅y, x⁆ ∈ Vsub root 2 4 := by
      refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (1 : ℤ) 5, root k) ≤ Vsub root 2 4) h
      have := Set.mem_Ioo.1 hk
      exact root_le_Vsub (by omega) (by omega)
    rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ hV
  UN := fun c n hn => root6_norm hC (phi6_U_mem R E c) hn
  LN := fun c n hn => rootNeg6_norm R hC (phi6_L_mem R E c) hn
  uA := fun c a ha => by rw [short_uA R E hC c ha]; exact Subgroup.one_mem _
  lB := fun c b hb => by rw [short_lB R E hC c hb]; exact Subgroup.one_mem _
  uB := fun c b hb => short_uB R E c hb
  lA := fun c a ha => short_lA R E c ha
  ndU := fun b hb hk => short_ndU R E hC hO hb hk
  ndL := fun a ha hk => short_ndL R E hC hO ha hk

end CFSG.GH74.GLS.Stage4.Hex
