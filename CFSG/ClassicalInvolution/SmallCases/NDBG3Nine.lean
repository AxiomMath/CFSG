module

public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOmegaStep

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem omegaOfSet_subset_of_exact (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hex : ExactMembers Ω) {M J : Subgroup G} {zM zJ : G} (hM : M ∈ Ω)
    (hv : AViol Ω M J zM zJ) : omegaOfSet Ω (twinSet Ω M) ⊆ omegaOfSet Ω (twinSet Ω J) := by
  intro L hLset
  obtain ⟨v, Ms, hVU, hVJ, -, -, htw, hvv⟩ :=
    exists_hexagon_data hp hq hΩ hM hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hMT : M ∈ twinSet Ω M := ⟨hM, zM, hv.hzK, hv.hzK⟩
  have hMsT : Ms ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  have hMsΩ : Ms ∈ Ω := hMsT.1
  have hzMs : IsUniqueInvolution Ms zM := isUniqueInvolution_of_mem_twinSet hv.hzK hMsT
  have hzJM : zJ ∈ M ⊔ Ms := mem_sup_of_hexagon hp hΩ hv.hzJ hVU hVJ hvv
  have hLΩ : L ∈ Ω := hLset.1
  have hLnbr : L ∈ omegaNbr Ω M := hLset.2 M hMT
  obtain ⟨-, hLM, T, hTR, hTL, hTN⟩ := id hLnbr
  obtain ⟨c, hcL⟩ := hΩ.exists_uniqueInvolution hp hq hLΩ
  have hTsyl : IsSylow2In T L :=
    Disconnected.AschTight.Sec7.isSylow2In_of_mem_RSet_of_le hp hΩ hTR hLΩ hTL
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp hTR
  have hLMs : L ≠ Ms := (hLset.2 Ms hMsT).2.1
  have hTC : T ≤ Subgroup.centralizer ({zM} : Set G) := fun x hx =>
    mem_centralizer_singleton_of_conj_eq
      (hv.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hx)))
  have hcent : ∀ N ∈ twinSet Ω M, N ≠ L → N ≤ Subgroup.centralizer (T : Set G) := by
    intro N hN hNL n hn
    have hNΩ : N ∈ Ω := hN.1
    have hzN : IsUniqueInvolution N zM := isUniqueInvolution_of_mem_twinSet hv.hzK hN
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := Thompson.comm_le_oddCore_of_isSylow2In (l6_2 p f) hp hq hΩ hNΩ hLΩ hNL hzN hcL
      hTsyl hTC (Subgroup.commutator_mem_commutator hx hn)
    rw [oddCoreOf_eq_bot_of_exact hex hNΩ, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hsup : M ⊔ Ms ≤ Subgroup.centralizer (T : Set G) :=
    sup_le (hcent M hMT (Ne.symm hLM)) (hcent Ms hMsT (Ne.symm hLMs))
  have hTzJ : T ≤ Subgroup.centralizer ({zJ} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hsup hzJM) x hx)
  refine ⟨hLΩ, fun J' hJ' => ?_⟩
  have hJ'Ω : J' ∈ Ω := hJ'.1
  have hzJ' : IsUniqueInvolution J' zJ := isUniqueInvolution_of_mem_twinSet hv.hzJ hJ'
  have hLJ' : L ≠ J' := by
    rintro rfl
    have h1 : M ∈ omegaNbr Ω L := omegaNbr_symm (l6_2 p f) hp hq hΩ hM hLΩ hLnbr
    have hKP := (l6_3 p f hp hq G Ω hΩ J hv.mem L hJ').1
    have h2 : M ∈ KPerp Ω J := by
      rw [hKP]
      exact Or.inr h1
    rcases h2 with h | h
    · exact hv.star.2.1 h.symm
    · exact hv.not_nbr (omegaNbr_symm (l6_2 p f) hp hq hΩ hv.mem hM h)
  exact ⟨hLΩ, hLJ', T, hTR, hTL,
    hΩ.le_normalizer_of_le_centralizer hp hq hJ'Ω hLΩ (Ne.symm hLJ') hzJ' hTL hT2 (by omega) hTzJ⟩

end CFSG.ClassicalInvolution.NDB.NDBG3
