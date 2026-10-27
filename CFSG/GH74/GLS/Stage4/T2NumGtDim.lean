module

public import CFSG.GH74.GLS.Stage4.T6W.T6Rle
public import CFSG.GH74.GLS.Stage4.T2NumGtIvk11c
public import CFSG.GH74.GLS.Stage4.T2NumGtBridge
public import CFSG.GH74.GLS.Stage4.T2NumGtDefs
public import CFSG.GH74.GLS.Stage4.T2NumGtSecSurj
public import CFSG.GH74.GLS.IVK.Proofs2.NatModFinal
public import CFSG.GH74.GLS.Stage4.T6W.T6Sec

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6W CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ch6Gt_dim (h11c : IVK_11_1c_dim) : Ch6GtD := by
  intro G _ _ Gs _ q₁ q₂ hlt hmod z K₁ K₂ F₁ F₂ _ _ t hSet hRem p n m hp hp2 hq₂p hq₁p N u hz hK₁ hK₂ hq₁ hq₂
    hCoord hSec y R hTS
  have hctx : T6CtxW N u p := t6CtxW_of hSet hRem hz hK₁ hK₂ hq₁ hq₂ hp hp2 ⟨n, hq₂p⟩ hCoord hSec
  have hm : N.q₁ = p ^ m := by rw [hq₁]; exact hq₁p
  have hn : N.q₂ = p ^ n := by rw [hq₂]; exact hq₂p
  have hloc := hSec.loc
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have := hloc.q₁_ge; rw [hm, h0] at this; simp at this
    · exact h0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := hloc.q₂_ge; rw [hn, h0] at this; simp at this
    · exact h0
  have hlt' : N.q₂ < N.q₁ := by rw [hq₁, hq₂]; exact hlt
  have hnm : n < m := by
    by_contra hcon
    push Not at hcon
    have : p ^ m ≤ p ^ n := Nat.pow_le_pow_right hp.pos hcon
    rw [hm, hn] at hlt'
    omega
  have hMod : T6Mod N p m := t6Mod_of IVK.Proofs2.ivk_11_1b_nat hctx hm
  have hyK : y ∈ N.K₁ := hTS.yK
  have hy1 : y ≠ 1 := fun e => hTS.y_ne (e ▸ Subgroup.one_mem _)
  have hyp : ¬ p ∣ orderOf y := by
    intro hd
    have h1 : p ∣ N.q₁ - 1 := hd.trans hTS.y_dvd
    rw [hm] at h1
    exact ng_not_dvd_pow_sub_one hp hm1 h1
  have hRR : R ≤ R₂ N p := R_le_R₂ hctx hTS.R_p hTS.R_cent hTS.R_inv
  have hX₂R := X₂_le_R₂ hctx
  have hq₂lt : N.q₂ < N.q₂ ^ 3 := by
    calc N.q₂ = N.q₂ ^ 1 := (pow_one _).symm
      _ < N.q₂ ^ 3 := Nat.pow_lt_pow_right (by have := hloc.q₂_ge; omega) (by norm_num)
  have hne : N.X₂ ≠ R₂ N p := by
    intro heq
    have h1 : Nat.card ↥R ≤ Nat.card ↥(R₂ N p) := Subgroup.card_le_of_le hRR
    rw [← heq, hloc.card_X₂, hTS.R_card] at h1
    omega
  obtain ⟨F, iF, fF, φ, hcardF, hinj, hrange, hzφ, -, -, -, -⟩ := hctx.coord.coord₁
  obtain ⟨e, he⟩ := t6_coord_equiv hinj hrange hzφ hloc.z_mem_K₁
  have hF : Nat.card F = p ^ m := hcardF.trans hm
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨hKR, hKX⟩ := K₁_sec_X₂R₂ hctx
  have hcomm := (R₂_inv_comm hctx).2
  have hinv := (R₂_inv_comm hctx).1
  have hexp := R₂_exp hctx ⟨m, hm⟩
  obtain ⟨V, _, _, _, ρ, π, hcard, hπ0, hπadd, hρπ⟩ :=
    t6_sec_rep (p := p) (K := N.K₁) (A := R₂ N p) (B := N.X₂) hKR hKX hcomm hexp
  have hinj' : Function.Injective ρ :=
    t6_sec_faithful hp hp2 hodd e hloc.z_mem_K₁ he hX₂R hKR hinv hne ρ π hπ0 hπadd hρπ
  have hπsurj : Function.Surjective π := ng_sec_surj π hcard hπ0 hπadd
  have hirred := K₁_irred_of hctx hm hn hMod hyK hy1 hyp hRR hTS.R_card hTS.y_cent
  have hsimple : IsSimpleModule (MonoidAlgebra (ZMod p) ↥N.K₁) ρ.asModule :=
    T2.simple_of_section_irred ρ π hKR hπ0 hπadd hπsurj hρπ hirred hX₂R hne
  have hOrd := R₂_order hctx hm hn hMod hyK hy1 hyp hRR hTS.R_card hTS.y_cent
  have hrelcard : N.X₂.relIndex (R₂ N p) = N.q₁ ^ 2 * N.q₂ ^ 2 := by
    have hrel : N.X₂.relIndex (R₂ N p) * N.q₂ = Nat.card ↥(R₂ N p) := by
      have := Subgroup.relIndex_mul_card N.X₂ (R₂ N p)
      rwa [inf_eq_left.2 hX₂R, hloc.card_X₂] at this
    have hq₂pos : 0 < N.q₂ := by have := hloc.q₂_ge; omega
    apply Nat.eq_of_mul_eq_mul_right hq₂pos
    rw [hrel, hOrd]; ring
  have hfin : Module.finrank (ZMod p) V = 2 * m + 2 * n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hcard, hrelcard, hm, hn, ← pow_mul, ← pow_mul, ← pow_add] at h1
    have := Nat.pow_right_injective hp.two_le h1
    omega
  have hhas : HasSL2Model ↥N.K₁ (fun r => r = p ^ m) :=
    ⟨F, inferInstance, inferInstance, hF, ⟨e.trans (specialLinearGroupEquivStatedSL 2 F)⟩⟩
  have hkey := h11c p m hp hp2 ↥N.K₁ hhas V ρ hinj' hsimple (by omega) (by omega)
  rw [hfin] at hkey
  have hm3 : m = 3 * n := by omega
  rw [hq₁p, hq₂p, ← pow_mul, hm3, mul_comm]

end CFSG.GH74.GLS.Stage4.Rest
