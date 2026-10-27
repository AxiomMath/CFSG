module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56X0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Cov

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem pCoreOf_eq_self_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 ↥K) :
    pCoreOf 2 K = K := by
  show (pCore 2 ↥K).map K.subtype = K
  apply le_antisymm (Subgroup.map_subtype_le _)
  intro b hb
  have htop : (⊤ : Subgroup ↥K) ≤ pCore 2 ↥K :=
    le_sSup ⟨Subgroup.normal_top, hK.of_equiv Subgroup.topEquiv.symm⟩
  exact ⟨⟨b, hb⟩, htop (Subgroup.mem_top _), rfl⟩

private theorem commutator_mem_of_sq_mem {s : Setting3 G L} {e : Setting3.Ext s}
    (hH : F33Hyp s e) {K : Subgroup G} (hKle : K ≤ e4Y s)
    (hKnorm : ∀ k ∈ e4Y s, ∀ q ∈ K, k * q * k⁻¹ ∈ K)
    (hsq : ∀ k ∈ e4Y s, k ^ 2 ∈ K) :
    ∀ y ∈ e4Y s, ∀ y' ∈ e4Y s, ⁅y, y'⁆ ∈ K := by
  haveI hnorm' : (K.subgroupOf (e4Y s)).Normal :=
    (Subgroup.normal_subgroupOf_iff hKle).mpr fun h k hh hk => hKnorm k hk h hh
  have hexp : ∀ g : (↥(e4Y s) ⧸ K.subgroupOf (e4Y s)), g ^ 2 = 1 := by
    intro g
    refine QuotientGroup.induction_on g fun y => ?_
    change (QuotientGroup.mk' (K.subgroupOf (e4Y s)) y) ^ 2 = 1
    rw [← map_pow]
    show ((y ^ 2 : ↥(e4Y s)) : ↥(e4Y s) ⧸ K.subgroupOf (e4Y s)) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq (y : G) y.2
  have hcomm : IsMulCommutative (↥(e4Y s) ⧸ K.subgroupOf (e4Y s)) := by
    apply IsMulCommutative.of_comm
    intro g h
    have hgh : (g * h) ^ 2 = 1 := hexp (g * h)
    rw [pow_two] at hgh
    calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by
        have hg := hexp g
        have hh := hexp h
        rw [pow_two] at hg hh
        rw [inv_eq_of_mul_eq_one_right hg, inv_eq_of_mul_eq_one_right hh]
  have hcommle : _root_.commutator ↥(e4Y s) ≤ K.subgroupOf (e4Y s) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := ↥(e4Y s))
      (N := K.subgroupOf (e4Y s))).mp hcomm
  intro y hy y' hy'
  have hmem : ⁅(⟨y, hy⟩ : ↥(e4Y s)), (⟨y', hy'⟩ : ↥(e4Y s))⁆ ∈
      _root_.commutator ↥(e4Y s) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcoe : ((⁅(⟨y, hy⟩ : ↥(e4Y s)), (⟨y', hy'⟩ : ↥(e4Y s))⁆ : ↥(e4Y s)) : G) =
      ⁅y, y'⁆ :=
    map_commutatorElement (f := (e4Y s).subtype) _ _
  have hmem' := hcommle hmem
  rw [Subgroup.mem_subgroupOf] at hmem'
  simpa [hcoe] using hmem'

theorem y56_Y_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : ∀ y ∈ e4Y c.s, y ^ 2 ∈ e4Q c.s := by
  obtain ⟨y₀, hy₀⟩ := y56_exists_y0 c hH
  have hd2 : c.d * c.d = 1 := by
    have h := pow_orderOf_eq_one c.d
    rw [c.d_order] at h
    simpa [pow_two] using h
  have hux : ∀ u ∈ e4Y c.s, u ^ 2 ∈ e4Q c.s → ∀ x ∈ e4X0 c.s,
      (u * x) ^ 2 ∈ e4Q c.s := by
    intro u hu hu2 x hx
    have hc : ⁅u⁻¹, x⁆ ∈ e4Q c.s :=
      y56_Y_X0_comm hH u⁻¹ ((e4Y c.s).inv_mem hu) x hx
    have hx2 : x ^ 2 ∈ e4Q c.s := y56_X0_sq hH x hx
    have hmain : (u * x) ^ 2 = u ^ 2 * ⁅u⁻¹, x⁆ * x ^ 2 := by
      rw [pow_two, commutatorElement_def]
      group
    rw [hmain]
    exact (e4Q c.s).mul_mem ((e4Q c.s).mul_mem hu2 hc) hx2
  intro y hy
  rcases y56_Y_cover c hH hy₀ y hy with hyX0 | ⟨x, hx, rfl⟩ | ⟨n, hn, x, hx, rfl⟩
  · exact y56_X0_sq hH y hyX0
  · exact hux c.d (y56_d_mem_Y c hH)
      (by rw [pow_two, hd2]; exact (e4Q c.s).one_mem) x hx
  · have hnN : n ∈ e4N c.s := y56_NL_le_N hH hn
    have huY : n * y₀ * n⁻¹ ∈ e4Y c.s :=
      y56_N_norm_Y hH n hnN y₀ (y56_y0_mem_Y hH hy₀)
    have hy02 : y₀ ^ 2 ∈ c.s.fr.E :=
      y56_V_le_E hH (y56_C2_sq c hH y₀ hy₀.1)
    have hu2 : (n * y₀ * n⁻¹) ^ 2 ∈ e4Q c.s := by
      have h : (n * y₀ * n⁻¹) ^ 2 = n * (y₀ ^ 2) * n⁻¹ := by
        rw [pow_two, pow_two]
        group
      rw [h]
      exact y56_N_norm_Q hH n hnN (y₀ ^ 2) (Subgroup.mem_sup_left hy02)
    exact hux (n * y₀ * n⁻¹) huY hu2 x hx

theorem y56_Y_comm (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ y ∈ e4Y c.s, ∀ y' ∈ e4Y c.s, ⁅y, y'⁆ ∈ e4Q c.s :=
  commutator_mem_of_sq_mem hH ((y56_Q_le_X0 hH).trans (y56_X0_le_Y hH))
    (y56_Y_norm_Q hH) (y56_Y_sq c hH)

theorem y56_Y_isPGroup (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : IsPGroup 2 ↥(e4Y c.s) := by
  intro y
  have hy2 : (y : G) ^ 2 ∈ e4Q c.s := y56_Y_sq c hH (y : G) y.2
  have hy4 : (y : G) ^ 4 = 1 := by
    have h := y56_Q_sq hH ((y : G) ^ 2) hy2
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact h
  exact ⟨2, Subtype.ext (by simpa using hy4)⟩

theorem y56_C4_eq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    C4 c.s = ⁅e4Y c.s, e4N c.s⁆ ⊔ e4Q c.s := by
  rw [e4_C4_eq]
  have hKle : ⁅e4Y c.s, e4N c.s⁆ ≤ e4Y c.s := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hb' : b * a⁻¹ * b⁻¹ ∈ e4Y c.s := y56_N_norm_Y hH b hb a⁻¹ ((e4Y c.s).inv_mem ha)
    have hcomm : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [hcomm]
    exact (e4Y c.s).mul_mem ha hb'
  rw [pCoreOf_eq_self_of_isPGroup ((y56_Y_isPGroup c hH).to_le hKle)]

end CFSG.OddStandard.HigherRank.YamadaG23
