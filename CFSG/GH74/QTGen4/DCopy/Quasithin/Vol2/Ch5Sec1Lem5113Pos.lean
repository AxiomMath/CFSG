module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Pos

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem Main513.d3_stab_zero_five_six_F4 {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}
    (h510 : Stmt5_1_10_F4) (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hc5 : Case5_512 T H X Kh₁)
    {e : O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)}
    (hr0 : (modO2Image (conjClosure Kh₁ T) (oTwoUpper H)).map e.toMonoidHom = A7Std.r0)
    (hp0 : (modO2Image (conjClosure Kh₁ T) (T ⊓ conjClosure Kh₁ T)).map e.toMonoidHom =
      A7Std.p0)
    {D₃ : Subgroup G} (hD₃ : D₃ ≤ D ⊓ conjClosure Kh₁ T) (h3 : Nat.card D₃ = 3)
    (hD₃K : ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hDK : D ⊓ conjClosure Kh₁ T ≤ D₃) :
    (∀ d : ↥(conjClosure Kh₁ T), (d : G) ∈ D₃ → ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) →
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 0 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 5 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 6) ∧
    ∃ d : ↥(conjClosure Kh₁ T), (d : G) ∈ D₃ ∧
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 0 ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) := le_normalizer_conjClosure Kh₁ T
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hTY : IsSylowTwoOf T (conjClosure Kh₁ T ⊔ T) := h.isSylowTwoOf le_sup_right
  have hON : pCoreOf 2 (conjClosure Kh₁ T) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    refine le_trans ?_ ((F7.isSylowTwoOf_pCoreOf_le hTY).trans hTK)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        (hTKh.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have hD := m.nota.2.1
  have hDT : ∀ t ∈ T, ∀ d ∈ D, ∃ d' ∈ D, ∃ t' ∈ T, t * d = d' * t' := by
    intro t ht d hd
    have hBT := Subgroup.coe_mul_of_right_le_normalizer_left (borelL T L) T
      h.T_le_normalizer_borel
    have hDL : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hD.1.trans inf_le_right
    have hDS := Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) hDL
    have h1 : t * d ∈ ((borelL T L ⊔ T : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hD.1 hd))
    rw [hBT] at h1
    obtain ⟨y, hy, s, hs, hys⟩ := h1
    have hys' : y * s = t * d := hys
    have hy' : y ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
      rw [h.borelL_eq_sup hD]
      exact hy
    rw [hDS] at hy'
    obtain ⟨d', hd', r, hr, hdr⟩ := hy'
    have hdr' : d' * r = y := hdr
    exact ⟨d', hd', r * s, T.mul_mem (Subgroup.mem_inf.mp hr).1 hs,
      by rw [← hys', ← hdr', mul_assoc]⟩
  obtain ⟨-, -, hBorel, hHall, -⟩ := h510 G T M L H B D n m.hyp m.nota
  rw [m.hyp.borel_eq hBorel] at hHall
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hTKs : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hB3 : Nat.card B = 3 := by
    have := (isCyclic_card_of_isHall_borelOf le_rfl hc5.1 hTKs hHall).2
    norm_num at this
    exact this
  exact d3_stab_zero_five_six_of m.lt.le hKperf hON h.sylow.1 hTKh hr0 hp0 hD.2.1 hDT hD₃ h3
    hD₃K hDK hB3 (fun b hb => (hHall.1 hb).1) m.nota.2.2

end CFSG.Quasithin.H13
