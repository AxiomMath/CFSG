module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294AltComb
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Defs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

private theorem i294_conjNormal_injective_alt {Y : Type} [Group Y] {L : Subgroup Y}
    [L.Normal] (hc : centralizer (L : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut ↥L) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hcent : a ∈ centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : a * l * a⁻¹ = l := by
      have := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : Y)) ha
      simpa [MulAut.conjNormal_apply] using this
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hc, Subgroup.mem_bot] at hcent
  exact hcent

theorem i294_false_of_alternating {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] {z g : Y} {D : Subgroup Y} (h : I294Cfg p L z g D) (hDL : D ≤ L) {n : ℕ}
    (hn : 5 ≤ n) (e : ↥L ≃* alternatingGroup (Fin n)) : False := by
  have hp : p.Prime := h.prime
  have hodd : p ≠ 2 := h.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hrankL : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥L)) := by
    have h1 := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (MulAut.conjNormal : Y →* MulAut ↥L) (i294_conjNormal_injective_alt h.cent)
    rw [h.rank] at h1
    exact h1
  have h3p : 3 * p ≤ n := by
    by_cases hn6 : n = 6
    · subst hn6
      exfalso
      have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)
      have h6 := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_mulAut_alternating_six_le hp hodd
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hdiv : 6 / p ≤ 2 := Nat.div_le_of_le_mul (by omega)
      have h32 : 3 ≤ 2 := (hrankL.trans heq.le).trans (h6.trans hdiv)
      omega
    · have h1 := CFSG.AGLEmbedding.pRank_top_mulAut_le hn hn6 e hp
      exact (Nat.le_div_iff_mul_le hp.pos).1 (hrankL.trans h1)
  obtain ⟨x, hxD, hx1, hsyl⟩ := h.sylowLine
  have hxL : x ∈ L := hDL hxD
  have hxp : x ^ p = 1 := h.elem.2 x hxD
  obtain ⟨xL, hxLx⟩ : ∃ xL : ↥L, (xL : Y) = x := ⟨⟨x, hxL⟩, rfl⟩
  have hxL1 : xL ≠ 1 := by
    intro h1
    apply hx1
    rw [← hxLx, h1, OneMemClass.coe_one]
  have hxLp : xL ^ p = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hxLx, OneMemClass.coe_one]
    exact hxp
  have hap : (e xL : Equiv.Perm (Fin n)) ^ p = 1 := by
    have h2 : e (xL ^ p) = 1 := by rw [hxLp, map_one]
    rw [map_pow] at h2
    have h3 := congrArg Subtype.val h2
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3
    exact h3
  have ha1 : (e xL : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h1
    apply hxL1
    apply e.injective
    rw [map_one]
    exact Subtype.ext (by rw [h1, OneMemClass.coe_one])
  obtain ⟨E, hE_le, -, hE_card⟩ :=
    exists_elemAbelian_three_of_pow_eq_one hp hodd h3p hap ha1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : alternatingGroup (Fin n) →* Y, ∀ b, ψ b = ((e.symm b : ↥L) : Y) :=
    ⟨L.subtype.comp e.symm.toMonoidHom, fun _ => rfl⟩
  have hψinj : Function.Injective ψ := by
    intro b c hbc
    rw [hψ, hψ] at hbc
    exact e.symm.injective (Subtype.ext hbc)
  have hψa : ψ (e xL) = x := by
    rw [hψ, MulEquiv.symm_apply_apply, hxLx]
  have hEalt : E ≤ alternatingGroup (Fin n) := fun y hy => (Subgroup.mem_inf.1 (hE_le hy)).2
  obtain ⟨EY, hEY⟩ : ∃ EY : Subgroup Y, EY = (E.subgroupOf (alternatingGroup (Fin n))).map ψ :=
    ⟨_, rfl⟩
  have hEY_card : Nat.card EY = p ^ 3 := by
    rw [hEY, Subgroup.card_map_of_injective hψinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEalt).toEquiv, hE_card]
  have hEY_cent : EY ≤ centralizer ({x} : Set Y) := by
    rw [hEY]
    rintro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hbE : (b : Equiv.Perm (Fin n)) ∈ E := Subgroup.mem_subgroupOf.mp hb
    have hcb := (Subgroup.mem_inf.1 (hE_le hbE)).1
    have hc1 := Subgroup.mem_centralizer_iff.mp hcb _ (Set.mem_singleton _)
    have hc2 : e xL * b = b * e xL := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hc1)
    have hc3 := congrArg ψ hc2
    rw [map_mul, map_mul, hψa] at hc3
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff.mp ht]
    exact hc3
  have hdvd : p ^ 3 ∣ Nat.card (centralizer ({x} : Set Y)) := by
    rw [← hEY_card]
    exact Subgroup.card_dvd_of_le hEY_cent
  have hC0 : Nat.card (centralizer ({x} : Set Y)) ≠ 0 := Nat.card_pos.ne'
  have h3le := (hp.pow_dvd_iff_le_factorization hC0).1 hdvd
  have hsc := hsyl.card_eq
  rw [h.card] at hsc
  have h2 := Nat.pow_right_injective hp.two_le hsc
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
