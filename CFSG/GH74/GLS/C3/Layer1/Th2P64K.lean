module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64J
public import CFSG.GH74.GLS.C3.Layer1.Th2P64G
public import CFSG.GH74.GLS.C3.Layer1.Th2P64I

public section

open Equiv Equiv.Perm Subgroup CFSG
open CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs CFSG.ABGLocalTools CFSG.GH74.GLS.IVK
open scoped commutatorElement

namespace CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem CxK_conj_mem {x : G} {K : Subgroup G}
    (hKn : ∀ m ∈ centralizer ({x} : Set G), ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    {v : G} (hv : v ∈ centralizer ({x} : Set G)) {c : G} (hc : c ∈ CxK x K) :
    v * c * v⁻¹ ∈ CxK x K := by
  have hvx : v * x * v⁻¹ = x := by
    have := mem_centralizer_singleton_iff.1 hv
    rw [this]; group
  have hK : Stage1.Thm3.Sec4.cmap v K = K := by
    ext k
    rw [Stage1.Thm3.Sec4.mem_cmap]
    constructor
    · intro h1
      have := hKn v hv _ h1
      simpa [mul_assoc] using this
    · intro hk
      have := hKn v⁻¹ (Subgroup.inv_mem _ hv) k hk
      simpa using this
  have h1 : v * c * v⁻¹ ∈ Stage1.Thm3.Sec4.cmap v (CxK x K) := by
    rw [Stage1.Thm3.Sec4.mem_cmap]
    have : v⁻¹ * (v * c * v⁻¹) * v = c := by group
    rw [this]; exact hc
  rw [← PumpTerm.CxK_cmap' v x K, hvx, hK] at h1
  exact h1

theorem b_prop64_lemma66_of
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) : B_prop64_lemma66 := by
  classical
  intro G _ _ hG x y K T S hs hL2 B hB b J hobs hA hN2 h65b V hV hBV
  by_contra hcon
  push Not at hcon
  obtain ⟨e₇⟩ := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : CenterlessBar K := centerlessBar_of_hasL2Model (fun q hq => hq) hL2
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel := hE.2.1
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hP : RankTwoShape (T ⊓ K) :=
    rankTwoShape_sylow_L2 hs.sylow_P (TwoThin.isQuasisimple_hat hs.comp) (fun q hq => hq) hL2
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) := by
    have := pRank_eq_two_of_rankTwoShape hP
    omega
  have hKn := hs.K_normal hG4 hcen hP2
  have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hB.1.1
  have hBT : B ≤ T := hBR.trans (sup_le inf_le_left inf_le_left)
  have hBx : B ≤ centralizer ({x} : Set G) := hBT.trans hs.T_le_C
  have hJK : J ≠ K := fun h' => Th2.not_nonempty_A7_of_hasL2Model hL2 (h' ▸ ⟨e₇⟩)
  have hxb : x ≠ b := (hobs.ne_x_of_shape hG hs hcen hP hB hJK).symm
  have hxo := hs.orderOf_x
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo, sq] at this
  have hx1 : x ≠ 1 := fun h1 => by rw [h1] at hxo; simp at hxo
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b hobs.mem) hobs.ne_one
  have hbC : b ∉ CxK x K := fun hbC => h65b b hbC hb2 1 (by simp)
  have hxcomm : x * b = b * x := (mem_centralizer_singleton_iff.1 (hBx hobs.mem)).symm
  have hPQ := hs.commDisj hcen
  obtain ⟨U, hU, E₁, hE₁S, hE₁2, hBdef⟩ := (isS_sup_iff hPQ hP B).1 hB
  have hEqQ : E₁ ≤ T ⊓ CxK x K := hE₁S.1
  obtain ⟨a, ha, q, hq, hbaq⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu q hq => hPQ.comm u (hU.1 hu) q (hEqQ hq)) (hBdef ▸ hobs.mem : b ∈ U ⊔ E₁)
  have haK : a ∈ K := (hU.1 ha).2
  have haB : a ∈ B := hBdef ▸ Subgroup.mem_sup_left ha
  have hqC : q ∈ CxK x K := (hEqQ hq).2
  have hqB : q ∈ B := hBdef ▸ Subgroup.mem_sup_right hq
  have hE₁B : E₁ ≤ B ⊓ CxK x K := le_inf (hBdef ▸ le_sup_right) (hEqQ.trans inf_le_right)
  have hE₁4 : 4 ≤ Nat.card ↥E₁ := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hE₁S.2.1]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥E₁ := Nat.pow_le_pow_right (by norm_num) hE₁2
  have hB16 : Nat.card ↥B = 16 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hBel]
    have h1 : 4 ≤ pRank 2 ↥B := hE.2.2
    have h2 : pRank 2 ↥B ≤ 4 := (pRank_le_top' B).trans hG4
    rw [le_antisymm h2 h1]
    norm_num
  have hVD : V ≤ centralizer ({x, b} : Set G) := hV.le
  have hVb : V ≤ centralizer ({b} : Set G) := hVD.trans (Subgroup.centralizer_le (by simp))
  have hVx : V ≤ centralizer ({x} : Set G) := hVD.trans (Subgroup.centralizer_le (by simp))
  have hVN : V ≤ normalizer (J : Set G) := hVb.trans (hobs.centralizer_le_normalizer hG4 hBel)
  obtain ⟨e, heE, hesw⟩ := hobs.exists_swap_of_bad hG4 hBel e₇ hN2 hB16 hx2 hx1 hxb hxcomm hBx hV hBV hVN
    (fun v hv c hc => CxK_conj_mem hKn (hVx hv) hc) hbC hE₁B hE₁4 hcon
  exact false_of_swap_in_E hL34 h102 hG hs hL2 hBel hobs e₇ haK haB hqC hqB hbaq.symm hbC
    (hE₁B heE).2 (hE₁B heE).1 (hVN (hBV (hE₁B heE).1)) hesw

end CFSG.GH74.GLS
