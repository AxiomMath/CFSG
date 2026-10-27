module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapMove
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapZPerm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapSW2
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapSW2Eight
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Frac53

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

@[expose] def Solomon75SwapMoveZ : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → ∀ s, IsSec5Inv X Z s →
    (∃ A, Sec5Comp X n (normalizer (Z : Set X)) A ∧ A.map (MulAut.conj s).toMonoidHom ≠ A) →
      ∃ u ∈ Z, u ≠ 1 ∧ ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
        B.map (MulAut.conj u).toMonoidHom ≠ B

section Glue

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem sw2_contra (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s) (hzs : z * s = s * z)
    {M : Subgroup X} (hM : Sec5Comp X n (centralizer ({z} : Set X)) M)
    (hMs : M.map (MulAut.conj s).toMonoidHom ≠ M) {y : X} (hy2 : y * y = 1)
    (hyz : y * z = z * y) (hys : y * s = s * y) (hyM : y ∈ normalizer (M : Set X))
    (hfix : fixCount ((AhatModel.ofCover hM.2).perm y hyM) = n - 4) :
    ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
      ∃ b ∈ B, ⁅b, y⁆ ∉ oddCoreOf (centralizer ({s} : Set X)) := by
  have hn : 8 ≤ n := h.maxdeg.1
  rcases Nat.lt_or_ge n 9 with h9 | h9
  · exact sw2_contra_eight h hs hzs (by omega) hM hMs hy2 hyz hys hyM hfix
  · exact sw2_contra_ge9 h hs hzs h9 hM hMs hy2 hyz hys hyM hfix

theorem swapMoveZ_of_pieces (hF : Solomon75Frac53) : Solomon75SwapMoveZ := by
  intro X _ _ n z Z S h s hs ⟨A, hA, hAs⟩
  have hzs : z * s = s * z :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Z_le_centralizer_of_frac53 hF h hs h.z_mem))
  obtain ⟨M, Δ, hD⟩ := exists_swapDiag hF h hs hA hAs
  obtain ⟨y, hyΔ, hy2, hyM, hfix⟩ := exists_type22_involution hD
  have hyC := hD.le_cen hyΔ
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 hyC.1
  have hys : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.1 hyC.2
  obtain ⟨B, hB, b, hb, hnot⟩ := sw2_contra h hs hzs hD.comp hD.moved hy2 hyz hys hyM hfix
  have hz1 : z ≠ 1 := by
    intro e
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  obtain ⟨B', hB', hmoved⟩ := exists_moved_of_diag h hs hzs hD ⟨B, hB, y, hyΔ, b, hb, hnot⟩
  exact ⟨z, h.z_mem, hz1, B', hB', hmoved⟩

theorem noSwap_of_swapMoveZ (hF : Solomon75Frac53) (h2 : Solomon75TwoComp)
    (hM : Solomon75SwapMoveZ) : Solomon75NoSwap := by
  intro X _ _ n z Z S h s hs A hA
  by_contra hAs
  obtain ⟨u, huZ, hu1, B, hB, hBu⟩ := hM X n z Z S h s hs ⟨A, hA, hAs⟩
  have hZs : Z ≤ centralizer ({s} : Set X) := Z_le_centralizer_of_frac53 hF h hs
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hu2o : orderOf u = 2 := h.orderOf_eq_two_of_mem_Z huZ hu1
  have hZu : Z ≤ Subgroup.zpowers u := by
    intro r hrZ
    by_contra hr
    have hr1 : r ≠ 1 := fun e => hr (e ▸ one_mem _)
    have hur : r * u = u * r := h.Z_comm hrZ huZ
    obtain ⟨r', hr'Z, hr'1, hr'B⟩ : ∃ r' ∈ Z, r' ≠ 1 ∧ r' ∈ normalizer (B : Set X) := by
      rcases zPerm_of_moved h hs hZs huZ hu1 hB hBu hrZ with h1 | h1
      · exact ⟨r, hrZ, hr1, mem_normalizer_of_map_conj_eq h1⟩
      · refine ⟨r * u, Z.mul_mem hrZ huZ, ?_,
          mem_normalizer_of_map_conj_eq (map_conj_mul_eq_of_eq hu2 hur h1)⟩
        intro e
        apply hr
        have hru : r = u := by
          calc r = r * (u * u) := by rw [hu2, mul_one]
            _ = (r * u) * u := by rw [mul_assoc]
            _ = u := by rw [e, one_mul]
        rw [hru]
        exact Subgroup.mem_zpowers u
    have hr'2 : r' ^ 2 = 1 := by rw [sq]; exact h.Z_sq_eq_one hr'Z
    have hsc := mem_centralizerSection_of_swap h hs.sq hZs huZ hu1 hr'Z hB hBu hr'B
    exact K0_ne_bot_of_centralizerSection hr'2 hB hsc
      (K0_inf_centralizer_eq_bot_of_swap hF h hs hA hAs hr'Z hr'1)
  have hz1 : z ≠ 1 := by
    intro e
    have := h.orderOf_z
    rw [e, orderOf_one] at this
    omega
  have hzu : z = u := by
    rcases zpowers_eq_of_orderOf_two hu2o z (hZu h.z_mem) with e | e
    · exact absurd e hz1
    · exact e
  have hZz : Z = Subgroup.zpowers z := by
    refine le_antisymm ?_ ((Subgroup.zpowers_le).2 h.z_mem)
    rw [hzu]
    exact hZu
  subst hZz
  have hNc : normalizer ((Subgroup.zpowers z : Subgroup X) : Set X) = centralizer ({z} : Set X) :=
    normalizer_zpowers_eq_centralizer h.orderOf_z
  have hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A := by
    rw [← hNc]
    exact hA
  have hA₂ : Sec5Comp X n (centralizer ({z} : Set X)) (A.map (MulAut.conj s).toMonoidHom) := by
    rw [← hNc]
    exact hA.map_conj (Subgroup.le_normalizer hs.mem)
  exact h2 X n z S h ⟨A, A.map (MulAut.conj s).toMonoidHom, hA₁, hA₂, fun e => hAs e.symm⟩

theorem noSwap_of_pieces (hF : Solomon75Frac53) (h2 : Solomon75TwoComp) : Solomon75NoSwap :=
  noSwap_of_swapMoveZ hF h2 (swapMoveZ_of_pieces hF)

theorem solomon75NoSwap_of_twoComp (hTC : Solomon75TwoComp) : Solomon75NoSwap :=
  noSwap_of_pieces (solomon75Frac53_of_twoComp hTC) hTC

end Glue

end CFSG.OddStandard.Solomon75
