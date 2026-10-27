module

public import CFSG.CGT.Timmesfeld75.JLemmaRoot
public import CFSG.CGT.Timmesfeld75.O2Lift
public import CFSG.CGT.Timmesfeld75.Lemma25

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T : Subgroup G}

theorem hyp_ne_bot (h : Lemma26Hyp G T) : T ≠ ⊥ := by
  rintro rfl
  have := h.2.1
  rw [Subgroup.card_bot] at this
  omega

theorem hyp_four_le_card [Finite G] (h : Lemma26Hyp G T) : 4 ≤ Nat.card T :=
  four_le_card_of_isElemAbelian h.1.1 (hyp_ne_bot h) (by have := h.2.1; omega)

theorem hyp_normalClosure_eq_top (h : Lemma26Hyp G T) :
    Subgroup.normalClosure (T : Set G) = ⊤ := by
  rw [← closure_classD_eq_normalClosure]
  exact h.2.2.2.2

theorem hyp_isConj_of_mem_classD (h : Lemma26Hyp G T) {x y : G} (hx : x ∈ classD T)
    (hy : y ∈ classD T) : IsConj x y := by
  obtain ⟨d₀, hd₀⟩ := h.2.2.1
  rw [hd₀] at hx hy
  exact (isConj_comm.1 hx).trans hy

theorem hyp_classD_le_of_mem (h : Lemma26Hyp G T) {N : Subgroup G} [hN : N.Normal]
    {x : G} (hx : x ∈ classD T) (hxN : x ∈ N) : classD T ⊆ N := by
  intro y hy
  obtain ⟨c, hc⟩ := isConj_iff.1 (hyp_isConj_of_mem_classD h hx hy)
  rw [← hc]
  exact hN.conj_mem x hxN c

theorem hyp_inf_eq_bot_of_normal_pGroup [Finite G] (h : Lemma26Hyp G T) {N : Subgroup G}
    [hN : N.Normal] (hN2 : IsPGroup 2 N) : T ⊓ N = ⊥ := by
  by_contra hne
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht1' : t ≠ 1 := fun e => ht1 (Subtype.ext e)
  have hD : classD T ⊆ N := hyp_classD_le_of_mem h (mem_classD_of_mem ht.1 ht1') ht.2
  have hNtop : N = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← h.2.2.2.2]
    exact (Subgroup.closure_le N).2 hD
  have hS : IsPGroup 2 (⊤ : Subgroup G) := hNtop ▸ hN2
  have hTnorm : ∀ g : G, conjSubgroup g T = T := fun g =>
    eq_of_conj_le_pGroup h.1 hS le_top le_top
  have hDT : classD T ⊆ T := by
    rintro _ ⟨g, s, hs, hs1, rfl⟩
    have h1 : conjSubgroup g⁻¹ T = T := hTnorm g⁻¹
    have h2 : g⁻¹ * s * g ∈ conjSubgroup g⁻¹ T := by
      rw [mem_conjSubgroup, inv_inv]
      simpa [mul_assoc] using hs
    rwa [h1] at h2
  have hTtop : T = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← h.2.2.2.2]
    exact (Subgroup.closure_le T).2 hDT
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ :=
    exists_mul_ne_one_of_four_le_card h.1.1 (hyp_four_le_card h)
  have hxD := mem_classD_of_mem hx hx1
  have hyD := mem_classD_of_mem hy hy1
  have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
    have ha : a ∈ T := hTtop ▸ Subgroup.mem_top a
    have hb : b ∈ T := hTtop ▸ Subgroup.mem_top b
    exact elemAbelian_mul_comm h.1.1 ha hb
  have hconj : x = y := by
    obtain ⟨c, hc⟩ := isConj_iff.1 (hyp_isConj_of_mem_classD h hxD hyD)
    rw [← hc, hcomm c x, mul_inv_cancel_right]
  apply hxy
  rw [← hconj]
  simpa [pow_two] using h.1.1.2 x hx

theorem hyp_twoCore_le_center [Finite G] (h : Lemma26Hyp G T) {N : Subgroup G} [N.Normal]
    (hN2 : IsPGroup 2 N) : N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro k
  have h1 := commutator_mem_normalClosureInf h.1 hN2 (hyp_normalClosure_eq_top h) hn k
  rw [normalClosureInf_eq_bot_of_inf_eq_bot (hyp_inf_eq_bot_of_normal_pGroup h hN2),
    Subgroup.mem_bot] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

theorem hyp_oddCore_le_center [Finite G] (h : Lemma26Hyp G T) {N : Subgroup G} [hN : N.Normal]
    (hodd : Odd (Nat.card N)) : N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro k
  have hcl := hyp_normalClosure_eq_top h
  have hk : k ∈ Subgroup.normalClosure (T : Set G) := by rw [hcl]; trivial
  exact (oddCore_le_center h.1 (hyp_four_le_card h) N (by rw [hcl]; exact le_top)
    (fun k _ n hn => hN.conj_mem n hn k) hodd n hn k hk).symm

theorem hyp_pGroup_le_center [Finite G] (h : Lemma26Hyp G T) (p : ℕ) (hp : p.Prime)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p N) : N ≤ Subgroup.center G := by
  by_cases hp2 : p = 2
  · subst hp2
    exact hyp_twoCore_le_center h hN
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := hN.exists_card_eq
    exact hyp_oddCore_le_center h (by rw [hm]; exact (hp.odd_of_ne_two hp2).pow)

theorem hyp_solvable_bot [Finite G] (h : Lemma26Hyp G T) :
    ∀ R : Subgroup (G ⧸ Subgroup.center G), R.Normal → Group.IsSolvable R → R = ⊥ :=
  solvable_normal_bot_of_pSubgroups_central fun p hp _ hPn hPp => by
    have := hPn
    exact hyp_pGroup_le_center h p hp hPp

theorem hyp_inf_center_eq_bot [Finite G] (h : Lemma26Hyp G T) : T ⊓ Subgroup.center G = ⊥ := by
  have hn : (T ⊓ Subgroup.center G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hz : g * x * g⁻¹ = x := by
      rw [Subgroup.mem_center_iff.1 hx.2 g]
      group
    rw [hz]
    exact hx
  have h2 : IsPGroup 2 (T ⊓ Subgroup.center G : Subgroup G) :=
    (isPGroup_two_of_isElemAbelian h.1.1).to_le inf_le_left
  have := hyp_inf_eq_bot_of_normal_pGroup h (N := T ⊓ Subgroup.center G) h2
  rwa [← inf_assoc, inf_idem] at this

theorem hyp_classD_inf_center [Finite G] (h : Lemma26Hyp G T) {x : G} (hx : x ∈ classD T) :
    x ∉ Subgroup.center G := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hx
  intro hc
  have htc : t ∈ Subgroup.center G := by
    have hy : g * (g⁻¹ * t * g) * g⁻¹ = g⁻¹ * t * g := by
      rw [Subgroup.mem_center_iff.1 hc g]
      group
    have e : t = g⁻¹ * t * g := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = g⁻¹ * t * g := hy
    rw [e]
    exact hc
  have hmem : t ∈ T ⊓ Subgroup.center G := ⟨ht, htc⟩
  rw [hyp_inf_center_eq_bot h, Subgroup.mem_bot] at hmem
  exact ht1 hmem

end CFSG.CGT.T75E
