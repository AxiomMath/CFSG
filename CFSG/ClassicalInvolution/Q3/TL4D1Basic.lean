module

public import CFSG.ClassicalInvolution.Q3.TL4SepMainB
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.commutes_of_mem_normalizer (h : T4Hyp r G Δ) {J L : Subgroup G} (hJ : J ∈ Δ)
    (hL : L ∈ Δ) (hnc : ¬ ∃ g : G, conjSub g J = L) {u v : G} (hu : IsUniqueInvolution J u)
    (hv : IsUniqueInvolution L v) (hinu : TightInO2 u) (hinv : TightInO2 v)
    (hvJ : v ∈ Subgroup.normalizer (J : Set G)) : Commutes J L := by
  by_contra hcomm
  obtain ⟨Pu, hPun, hPu2, huP⟩ := hinu
  obtain ⟨Pv, hPvn, hPv2, hvP⟩ := hinv
  have : Pv.Normal := hPvn
  have : Pu.Normal := hPun
  have hQn : (Pu ⊔ Pv).Normal := Subgroup.sup_normal Pu Pv
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pv) := IsPGroup.to_sup_of_normal_right hPu2 hPv2
  have huQ : u ∈ Pu ⊔ Pv := Subgroup.mem_sup_left huP
  have hvQ : v ∈ Pu ⊔ Pv := Subgroup.mem_sup_right hvP
  have hJ2 := h.isPGroup_of_inO2 hJ hu ⟨_, hQn, hQ2, huQ⟩
  have hL2 := h.isPGroup_of_inO2 hL hv ⟨_, hQn, hQ2, hvQ⟩
  have hJR := mem_RSet_self hJ hJ2
  have hLR := mem_RSet_self hL hL2
  have hJL : J ≠ L := fun e => hnc ⟨1, by rw [conjSub_one, e]⟩
  have huv : u ≠ v := fun e => hJL (h.noTwins J hJ L hL u hu (e ▸ hv))
  obtain ⟨X, hXC, hX2, hX4⟩ := h.exists_le_centralizer hJ hL hu hv hQn hQ2 huQ hvQ hvJ
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
    ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hJ hR hRJ).eq_of_le hJ2 le_rfl hRJ).symm
  rcases Sec6Gen.l6_2Gen G Δ h.hyp L hL v hv J hJ hJtw u hu V hV huV with
    ⟨hVu, -⟩ | ⟨hVu, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVL⟩
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · have hJstar : J ∈ omegaStarNbr Δ L := ⟨hJ, hJL, V, hVU, hV.1.trans inf_le_left, hVN⟩
    by_cases hJn : J ∈ omegaNbr Δ L
    · obtain ⟨-, -, R, hR, hRJ', hRN⟩ := hJn
      rw [hRJ R hR hRJ'] at hRN
      exact hcomm (commutes_of_le_normalizer h.hyp hLR hJR hL2 hJ2 hJL.symm hRN).symm
    · obtain ⟨g, -, hg⟩ := h.aEmpty L hL J hJstar hJn v u hv hu
      exact hnc ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩
  · rw [hRJ V hVR (hV.1.trans inf_le_left), oddCoreOf_eq_bot_of_isPGroup hL2] at hVL
    refine hcomm fun x hx y hy => ?_
    have hc := hVL (Subgroup.commutator_mem_commutator hx hy)
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc

omit [Finite G] in
theorem tightInO2_conj {u : G} (h : TightInO2 u) (g : G) : TightInO2 (g * u * g⁻¹) := by
  obtain ⟨P, hPn, hP2, hP⟩ := h
  exact ⟨P, hPn, hP2, hPn.conj_mem u hP g⟩

theorem thm4Res2C3_of_thmD1 {n : ℕ} (hD : ThmD1RBelow 3 n) : Thm4Res2C3 n := by
  intro G _ _ hG J L hm _ u v hu hv hinu hinv _
  refine hm.notComm (hD G hG _ hm.hyp ?_ J hm.memJ L hm.memL hm.notConj)
  rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩) z hz
  · rw [hz.eq (hu.conj g)]
    exact tightInO2_conj hinu g
  · rw [hz.eq (hv.conj g)]
    exact tightInO2_conj hinv g

end CFSG.ClassicalInvolution.Q3.TL4
