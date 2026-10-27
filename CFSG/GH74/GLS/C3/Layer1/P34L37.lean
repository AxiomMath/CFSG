module

public import CFSG.GH74.GLS.C3.Layer1.P34Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}

theorem lemma37 (c : Cfg34 X T P Q x z f h) (hD : DihedralShapeFacts) (hQ : QShapeFacts)
    (hOdd : OddMove) : Lemma37 T z := by
  intro g₀ hg₀
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h8, hPp, hPgen, hPz⟩ := hD X P c.P_dihedral
  obtain ⟨-, ⟨w, hwP, hww⟩, -, -⟩ := hPz z c.z_mem c.z_order c.z_central
  obtain ⟨hQ1, -, -, -⟩ :=
    hQ X T Q x c.T_pgroup c.Q_le c.Q_norm c.x_mem_Q c.x_order c.x_central c.Q_shape
  have hsubset : {p : X | p ∈ P ∧ p * p = 1} ⊆ {t : X | t ∈ T ∧ t * t = 1} :=
    fun p hp => ⟨c.P_le hp.1, hp.2⟩
  have hPT0 : P ≤ T0 T := fun a ha => closure_mono hsubset (hPgen a ha)
  have hzZ : z ∈ Z0 T := mem_Z0 c.z_mem_T c.z_sq c.z_cent_T
  let Tsyl : Sylow 2 X := c.T_pgroup.toSylow c.T_index
  have hcentz : ∀ a ∈ Z0 T, a ∈ centralizer ((T0 T : Subgroup X) : Set X) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 (fun s hs => ha.2.2 s hs)
  obtain ⟨n₁, hn₁, hn₁z⟩ := burnside_fusion_lemma_centralizer Tsyl (W := T0 T) T0_le
    isWeaklyClosedIn_T0 (hcentz z hzZ) (hcentz _ hg₀) (g := g₀) rfl
  set N₀ : Subgroup X := normalizer (T0 T : Set X) with hN₀
  let H : Subgroup N₀ := (centralizer ({z} : Set X)).comap N₀.subtype
  have hTH : T.subgroupOf N₀ ≤ H := fun t ht =>
    mem_centralizer_singleton_iff.2 (c.z_cent_T t (Subgroup.mem_subgroupOf.1 ht))
  have hHidx : ¬ 2 ∣ H.index := fun h2 => c.T_index
    (h2.trans ((Subgroup.index_dvd_of_le hTH).trans
      (Subgroup.relIndex_dvd_index_of_le T_le_normalizer_T0)))
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hmem : (⟨n₁, hn₁⟩ : N₀) ∈ H := by rw [htop]; exact Subgroup.mem_top _
    have h1 : n₁ * z = z * n₁ := mem_centralizer_singleton_iff.1 hmem
    apply hne
    rw [← hn₁z]
    calc n₁⁻¹ * z * n₁ = n₁⁻¹ * (z * n₁) := by group
      _ = n₁⁻¹ * (n₁ * z) := by rw [h1]
      _ = z := by group
  obtain ⟨m, hmodd, hmH⟩ := hOdd N₀ H hHidx hHtop
  set g : X := (m : X) with hg
  have hgN : g ∈ N₀ := m.2
  have hgodd : Odd (orderOf g) := by rw [hg, Subgroup.orderOf_coe m]; exact hmodd
  have hgz : g⁻¹ * z * g ≠ z := by
    intro h'
    apply hmH
    show (m : X) ∈ centralizer ({z} : Set X)
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * (g⁻¹ * z * g) := by rw [h']
      _ = z * g := by group
  have hggN : g * g ∈ N₀ := N₀.mul_mem hgN hgN
  have hz02 : (g * g)⁻¹ * z * (g * g) ≠ z := by
    intro h'
    apply hgz
    obtain ⟨j, hj⟩ := hgodd
    have hg1 : g ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one g
    have hgeq : g = (g * g) ^ (j + 1) := by
      rw [← sq, ← pow_mul]
      calc g = g ^ (2 * j + 1) * g := by rw [hg1, one_mul]
        _ = g ^ (2 * (j + 1)) := by rw [← pow_succ]; congr 1
    have hcomm : Commute (g * g) z := by
      show (g * g) * z = z * (g * g)
      calc (g * g) * z = (g * g) * ((g * g)⁻¹ * z * (g * g)) := by rw [h']
        _ = z * (g * g) := by group
    have hcg : Commute g z := by rw [hgeq]; exact hcomm.pow_left (j + 1)
    have : g * z = z * g := hcg.eq
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [← this]
      _ = z := by group
  have hz12 : (g * g)⁻¹ * z * (g * g) ≠ g⁻¹ * z * g := by
    intro h'
    apply hgz
    have : g⁻¹ * (g⁻¹ * z * g) * g = g⁻¹ * z * g := by
      calc g⁻¹ * (g⁻¹ * z * g) * g = (g * g)⁻¹ * z * (g * g) := by group
        _ = g⁻¹ * z * g := h'
    calc g⁻¹ * z * g = g * (g⁻¹ * (g⁻¹ * z * g) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [this]
      _ = z := by group
  have h1N : (1 : X) ∈ N₀ := N₀.one_mem
  obtain ⟨hT0_0, hnorm_0, hz_0, hzc_0, huniq_0⟩ := c.conj_facts h1N hPT0
  obtain ⟨hT0_1, hnorm_1, hz_1, hzc_1, huniq_1⟩ := c.conj_facts hgN hPT0
  obtain ⟨hT0_2, hnorm_2, hz_2, hzc_2, huniq_2⟩ := c.conj_facts hggN hPT0
  have hinf : ∀ e ∈ N₀, ∀ e' ∈ N₀, e⁻¹ * z * e ≠ e'⁻¹ * z * e' →
      conjSubgroup P e ⊓ conjSubgroup P e' = ⊥ := by
    intro e he e' he' hne'
    obtain ⟨h_e, hn_e, -, -, hu_e⟩ := c.conj_facts he hPT0
    obtain ⟨h_e', hn_e', -, -, hu_e'⟩ := c.conj_facts he' hPT0
    by_contra hbot
    obtain ⟨n, hn, hn1, hncent⟩ := exists_central_of_normal (W := T0 T)
      (T0_isPGroup c.T_pgroup) (N := conjSubgroup P e ⊓ conjSubgroup P e')
      (fun a ha => h_e a ha.1) (fun t ht a ha => ⟨hn_e t ht a ha.1, hn_e' t ht a ha.2⟩) hbot
    have h1 := hu_e n hn.1 (fun a ha => hncent a (h_e a ha))
    have h2 := hu_e' n hn.2 (fun a ha => hncent a (h_e' a ha))
    rcases h1 with h1 | h1
    · exact hn1 h1
    rcases h2 with h2 | h2
    · exact hn1 h2
    exact hne' (h1.symm.trans h2)
  have hinf12 := hinf g hgN (g * g) hggN hz12.symm
  have hcomm : ∀ e ∈ N₀, ∀ e' ∈ N₀, e⁻¹ * z * e ≠ e'⁻¹ * z * e' →
      ∀ a ∈ conjSubgroup P e, ∀ b ∈ conjSubgroup P e', a * b = b * a := by
    intro e he e' he' hne'
    obtain ⟨h_e, hn_e, -⟩ := c.conj_facts he hPT0
    obtain ⟨h_e', hn_e', -⟩ := c.conj_facts he' hPT0
    exact commute_of_inf_bot (W := T0 T) (fun a ha => h_e a ha) (fun b hb => h_e' b hb)
      (fun t ht a ha => hn_e t ht a ha) (fun t ht b hb => hn_e' t ht b hb) (hinf e he e' he' hne')
  have hY : ∀ e ∈ N₀, e⁻¹ * z * e ≠ z → ∀ b ∈ conjSubgroup P e,
      b ∈ (Q ⊔ zpowers f) ⊔ zpowers z := by
    intro e he hez b hb
    have hbT : b ∈ T := T0_le ((c.conj_facts he hPT0).1 b hb)
    refine (c.kf_3B b hbT).1 (fun a ha => ?_)
    have ha1 : a ∈ conjSubgroup P (1 : X) := by
      rw [mem_conjSubgroup_iff]; simpa using ha
    have := hcomm 1 h1N e he (by simpa using hez.symm) a ha1 b hb
    exact this.symm
  have hsq : ∀ e ∈ N₀, e⁻¹ * z * e ≠ z → e⁻¹ * z * e ∈ Q := by
    intro e he hez
    have hw' : e⁻¹ * w * e ∈ conjSubgroup P e := by
      rw [mem_conjSubgroup_iff]
      have e1 : e * (e⁻¹ * w * e) * e⁻¹ = w := by group
      rw [e1]; exact hwP
    have hwY := hY e he hez _ hw'
    have := c.sq_mem_Q hwY
    have e2 : (e⁻¹ * w * e) * (e⁻¹ * w * e) = e⁻¹ * z * e := by
      calc (e⁻¹ * w * e) * (e⁻¹ * w * e) = e⁻¹ * (w * w) * e := by group
        _ = e⁻¹ * z * e := by rw [hww]
    rwa [e2] at this
  have hz1Q : g⁻¹ * z * g ∈ Q := hsq g hgN hgz
  have hz2Q : (g * g)⁻¹ * z * (g * g) ∈ Q := hsq (g * g) hggN hz02
  have hz1Z : g⁻¹ * z * g ∈ Z0 T := Z0_conj hgN hzZ
  have hz2Z : (g * g)⁻¹ * z * (g * g) ∈ Z0 T := Z0_conj hggN hzZ
  have hQ4 : Nat.card ↥Q = 4 := by
    refine hQ1 _ hz1Q _ hz2Q ?_ ?_ hz12.symm hz1Z.2.1 hz2Z.2.1 ?_ ?_
    · intro h1
      apply c.z_ne_one
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      apply c.z_ne_one
      calc z = (g * g) * ((g * g)⁻¹ * z * (g * g)) * (g * g)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact (hz1Z.2.2 _ hz2Z.1).symm
    · intro q hq hq2
      have hqT0 : q ∈ T0 T := mem_T0 (c.Q_le hq) hq2
      exact ⟨(hz1Z.2.2 q hqT0), (hz2Z.2.2 q hqT0)⟩
  have hsub : ((conjSubgroup P g : Subgroup X) : Set X) * ((conjSubgroup P (g * g) : Subgroup X) : Set X) ⊆
      (((Q ⊔ zpowers f) ⊔ zpowers z : Subgroup X) : Set X) := by
    rw [Set.mul_subset_iff]
    intro a ha b hb
    exact ((Q ⊔ zpowers f) ⊔ zpowers z).mul_mem (hY g hgN hgz a ha)
      (hY (g * g) hggN hz02 b hb)
  have hcardmul := card_mul_of_inf_bot hinf12
  have hle1 : Nat.card ↥(((conjSubgroup P g : Subgroup X) : Set X) *
      ((conjSubgroup P (g * g) : Subgroup X) : Set X)) ≤
      Nat.card ↥(((Q ⊔ zpowers f) ⊔ zpowers z : Subgroup X) : Set X) :=
    Nat.card_mono (Set.toFinite _) hsub
  have hPcard : ∀ e : X, Nat.card ↥(conjSubgroup P e) = Nat.card ↥P := fun e => by
    unfold conjSubgroup
    exact Subgroup.card_map_of_injective (MulAut.conj e⁻¹).injective
  have h16 := c.card_Qfz_le
  rw [hcardmul, hPcard, hPcard] at hle1
  have hY' : Nat.card ↥(((Q ⊔ zpowers f) ⊔ zpowers z : Subgroup X) : Set X) =
      Nat.card ↥((Q ⊔ zpowers f) ⊔ zpowers z) := rfl
  rw [hY'] at hle1
  rw [hQ4] at h16
  have := Nat.mul_le_mul h8 h8
  omega

end CFSG.GH74.GLS.C3.Layer1.P34
