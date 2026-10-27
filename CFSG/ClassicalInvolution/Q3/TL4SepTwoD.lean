module

public import CFSG.ClassicalInvolution.Q3.TL4SepTwoC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)} {J L : Subgroup G}

theorem oddCoreOf_eq_bot_of_isPGroup {L : Subgroup G} (hL2 : IsPGroup 2 L) : oddCoreOf L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    hL2.to_le (Subgroup.zpowers_le.mpr (oddCoreOf_le_self L hx))
  rw [Subgroup.mem_bot]
  exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) hx hx2

theorem T4Min.false_of_mem_normalizer (hm : T4Min r G Δ J L) {u v : G}
    (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v) (hinu : TightInO2 u)
    (hinv : TightInO2 v) (hvJ : v ∈ Subgroup.normalizer (J : Set G)) : False := by
  have h := hm.hyp
  obtain ⟨Pu, hPun, hPu2, huP⟩ := hinu
  obtain ⟨Pv, hPvn, hPv2, hvP⟩ := hinv
  have : Pv.Normal := hPvn
  have : Pu.Normal := hPun
  have hQn : (Pu ⊔ Pv).Normal := Subgroup.sup_normal Pu Pv
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pv) := IsPGroup.to_sup_of_normal_right hPu2 hPv2
  have huQ : u ∈ Pu ⊔ Pv := Subgroup.mem_sup_left huP
  have hvQ : v ∈ Pu ⊔ Pv := Subgroup.mem_sup_right hvP
  have hJ2 := h.isPGroup_of_inO2 hm.memJ hu ⟨_, hQn, hQ2, huQ⟩
  have hL2 := h.isPGroup_of_inO2 hm.memL hv ⟨_, hQn, hQ2, hvQ⟩
  have hJR := mem_RSet_self hm.memJ hJ2
  have hLR := mem_RSet_self hm.memL hL2
  have hJL : J ≠ L := fun e => hm.notConj ⟨1, by rw [conjSub_one, e]⟩
  have huv : u ≠ v := fun e => hJL (h.noTwins J hm.memJ L hm.memL u hu (e ▸ hv))
  obtain ⟨X, hXC, hX2, hX4⟩ :=
    h.exists_le_centralizer hm.memJ hm.memL hu hv hQn hQ2 huQ hvQ hvJ
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXC
  have hV4 : 4 ≤ Nat.card V := hX4.trans (Subgroup.card_le_of_le hXV)
  have hVne : V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV4
    omega
  have huV : u ∈ V := mem_of_isPGroup_of_ne_bot hu (hV.1.trans inf_le_left) hV.2.1 hVne
  have hJtw : J ∉ twinSet Δ L := by
    rintro ⟨-, z, hzL, hzJ⟩
    exact huv ((hzJ.eq hu).symm.trans (hzL.eq hv))
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu.sq) hu.ne_one
  have hRJ : ∀ R ∈ RSet Δ, R ≤ J → R = J := fun R hR hRJ =>
    ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hm.memJ hR hRJ).eq_of_le hJ2 le_rfl hRJ).symm
  rcases Sec6Gen.l6_2Gen G Δ h.hyp L hm.memL v hv J hm.memJ hJtw u hu V hV huV with
    ⟨hVu, -⟩ | ⟨hVu, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVL⟩
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · have hJstar : J ∈ omegaStarNbr Δ L :=
      ⟨hm.memJ, hJL, V, hVU, hV.1.trans inf_le_left, hVN⟩
    by_cases hJn : J ∈ omegaNbr Δ L
    · obtain ⟨-, -, R, hR, hRJ', hRN⟩ := hJn
      rw [hRJ R hR hRJ'] at hRN
      exact hm.notComm (commutes_of_le_normalizer h.hyp hLR hJR hL2 hJ2 hJL.symm hRN).symm
    · obtain ⟨g, -, hg⟩ := h.aEmpty L hm.memL J hJstar hJn v u hv hu
      exact hm.notConj ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩
  · rw [hRJ V hVR (hV.1.trans inf_le_left), oddCoreOf_eq_bot_of_isPGroup hL2] at hVL
    refine hm.notComm fun x hx y hy => ?_
    have hc := hVL (Subgroup.commutator_mem_commutator hx hy)
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc

end CFSG.ClassicalInvolution.Q3.TL4
