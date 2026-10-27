module

public import CFSG.Goldschmidt.Steps.G74Basic
import CFSG.Goldschmidt.Steps.Completion
import CFSG.Goldschmidt.Steps.Balance
import CFSG.Walter.Bender1970.S4.ComponentTools

public section

namespace CFSG.Goldschmidt

open G74 in
theorem G74_of (h31 : S_G31) (h36 : S_G36) (h71 : S_G71) (h73 : S_G73) : S_G74 := by
  intro G _ _ S A hG h8 hE
  classical
  have := hG.isSimpleGroup
  have hex : ∃ n : ℕ, ∃ a ∈ A, a ≠ 1 ∧ ∃ H ∈ CFSG.Walter.benderM a, ∃ K : Subgroup G,
      GorensteinWalter.IsComponentOf K (normalClosureIn H A) ∧
      Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) = n := by
    obtain ⟨a, ha, ha1, H, hH, hE'⟩ := hE
    obtain ⟨K, hK⟩ : ∃ K, GorensteinWalter.IsComponentOf K (normalClosureIn H A) := by
      by_contra hcon
      push Not at hcon
      exact hE' (sSup_eq_bot.mpr fun K hK => absurd hK (hcon K))
    exact ⟨_, a, ha, ha1, H, hH, K, hK, rfl⟩
  have hmin : ∀ a ∈ A, a ≠ 1 → ∀ H ∈ CFSG.Walter.benderM a, ∀ K : Subgroup G,
      GorensteinWalter.IsComponentOf K (normalClosureIn H A) →
      Nat.find hex ≤ Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
    fun a ha ha1 H hH K hK => Nat.find_min' hex ⟨a, ha, ha1, H, hH, K, hK, rfl⟩
  obtain ⟨a, ha, ha1, H, hH, K, hK, hKm, hch⟩ : ∃ a ∈ A, a ≠ 1 ∧
      ∃ H ∈ CFSG.Walter.benderM a, ∃ K : Subgroup G,
      GorensteinWalter.IsComponentOf K (normalClosureIn H A) ∧
      Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) = Nat.find hex ∧
      (IsGoldL2 K → ∀ a' ∈ A, a' ≠ 1 → ∀ H' ∈ CFSG.Walter.benderM a', ∀ K' : Subgroup G,
        GorensteinWalter.IsComponentOf K' (normalClosureIn H' A) → IsGoldL2 K') := by
    by_cases hnl : ∃ a ∈ A, a ≠ 1 ∧ ∃ H ∈ CFSG.Walter.benderM a, ∃ K : Subgroup G,
        GorensteinWalter.IsComponentOf K (normalClosureIn H A) ∧
        Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) = Nat.find hex ∧
        ¬ IsGoldL2 K
    · obtain ⟨a, ha, ha1, H, hH, K, hK, hKm, hKL⟩ := hnl
      exact ⟨a, ha, ha1, H, hH, K, hK, hKm, fun h => absurd h hKL⟩
    · obtain ⟨a, ha, ha1, H, hH, K, hK, hKm⟩ := Nat.find_spec hex
      refine ⟨a, ha, ha1, H, hH, K, hK, hKm, fun hK2 a' ha' ha'1 H' hH' K' hK' => ?_⟩
      by_contra hK'2
      have hne : Nat.card (A ⊓ Subgroup.centralizer (K' : Set G) : Subgroup G) ≠ Nat.find hex :=
        fun h => hnl ⟨a', ha', ha'1, H', hH', K', hK', h, hK'2⟩
      have hlt := lt_of_le_of_ne (hmin a' ha' ha'1 H' hH' K' hK') (Ne.symm hne)
      have h1 := card_le_four_mul_of_isGoldL2 h31 hG ha hH hK hK2
      have h2 := four_mul_card_inf_centralizer_le h31 h36 hG ha' hH' hK'
      omega
  set A₀ := A ⊓ Subgroup.centralizer (K : Set G) with hA₀
  have hS := G73.isSStarIn_of_mem_benderM hG ha hH
  have hHco := CFSG.Walter.isCoatom_of_mem_benderM hH
  have h1 : ∀ a₀ ∈ A₀, a₀ ≠ 1 → CFSG.Walter.benderM a₀ = {H} :=
    h73 G S A hG h8 a ha ha1 H hH K hK hch
  have hHmem : ∀ b ∈ A₀, b ≠ 1 → H ∈ CFSG.Walter.benderM b := fun b hb hb1 =>
    (h1 b hb hb1).symm ▸ Set.mem_singleton H
  have hA₀ne : A₀ ≠ ⊥ := inf_centralizer_ne_bot h36 hG ha ha1 hH hK
  have h2a : 2 ≤ Nat.card A₀ := by
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hA₀ne
    omega
  have h4 : ∀ g ∈ Subgroup.normalizer (A : Set G), g ∉ H → A₀ ⊓ conjSub g A₀ = ⊥ := by
    intro g _ hgH
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    have hc : g * b * g⁻¹ ∈ A₀ := mem_conjSub.mp hb.2
    have hc1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    have e2 := CFSG.Walter.benderM_conj_eq_singleton g⁻¹ (h1 _ hc hc1)
    have hb' : g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b := by group
    rw [hb', h1 b hb.1 hb1] at e2
    have e3 : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
      (Set.singleton_eq_singleton_iff.mp e2).symm
    have hmem := CFSG.Walter.map_conj_eq_iff_mem_normalizer.mp e3
    rw [G73.normalizer_eq hG hHco le_rfl (G73.ne_bot_of_mem_benderM ha1 hH)
      Subgroup.le_normalizer] at hmem
    exact hgH (by simpa using H.inv_mem hmem)
  have h3 : ¬ Subgroup.normalizer (A : Set G) ≤ H := by
    intro hNH
    have hQn : Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (normalClosureIn H A : Set G) :=
      hNH.trans (G73.le_normalizer_normalClosureIn H A)
    have hNK : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (K : Set G) := by
      intro hle
      have hinv : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (A₀ : Set G) :=
        fun n hn => Subgroup.inf_normalizer_le_normalizer_inf ⟨hn,
          GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup K (hle hn)⟩
      rcases hG.irreducible A₀ inf_le_left hinv with h0 | h0
      · exact hA₀ne h0
      · refine G73.not_inf_le_centralizer h31 hS hG.elem hK fun x hx => ?_
        have hx₀ : x ∈ A₀ := by rw [h0]; exact hx.1
        exact hx₀.2
    obtain ⟨x₁, hx₁, hx₁K⟩ : ∃ x₁ ∈ Subgroup.normalizer (A : Set G),
        K.map (MulAut.conj x₁).toMonoidHom ≠ K := by
      by_contra hcon
      push Not at hcon
      exact hNK fun x hx => CFSG.Walter.map_conj_eq_iff_mem_normalizer.mp (hcon x hx)
    obtain ⟨x₂, hx₂, hx₂K, hx₁₂⟩ : ∃ x₂ ∈ Subgroup.normalizer (A : Set G),
        K.map (MulAut.conj x₂).toMonoidHom ≠ K ∧
          K.map (MulAut.conj x₁).toMonoidHom ≠ K.map (MulAut.conj x₂).toMonoidHom := by
      by_contra hcon
      push Not at hcon
      exact hG.noIndexTwo _ inf_le_left (index_eq_two hx₁ hx₁K fun a ha b hb haK hbK =>
        (hcon a ha haK).symm.trans (hcon b hb hbK))
    set K₁ := K.map (MulAut.conj x₁).toMonoidHom with hK₁def
    set K₂ := K.map (MulAut.conj x₂).toMonoidHom with hK₂def
    have hK₁ := CFSG.Walter.isComponentOf_map_conj hK (hQn hx₁)
    have hK₂ := CFSG.Walter.isComponentOf_map_conj hK (hQn hx₂)
    have hK₁C : K₁ ≤ Subgroup.centralizer (K : Set G) :=
      CFSG.Walter.le_centralizer_of_isComponentOf_ne hK₁ hK hx₁K
    have hK₂C : K₂ ≤ Subgroup.centralizer (K : Set G) :=
      CFSG.Walter.le_centralizer_of_isComponentOf_ne hK₂ hK hx₂K
    have hK₂K₁ : K₂ ≤ Subgroup.centralizer (K₁ : Set G) :=
      CFSG.Walter.le_centralizer_of_isComponentOf_ne hK₂ hK₁ (Ne.symm hx₁₂)
    have hcard₁ : Nat.card (A ⊓ K₁ : Subgroup G) = Nat.card (A ⊓ K : Subgroup G) := by
      have hA1 : A.map (MulAut.conj x₁).toMonoidHom = A :=
        CFSG.Walter.map_conj_eq_iff_mem_normalizer.mpr hx₁
      have hmap : (A ⊓ K).map (MulAut.conj x₁).toMonoidHom = A ⊓ K₁ := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x₁).injective, hA1]
      rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj x₁).injective]
    have hlt : A ⊓ K₁ < A₀ := by
      refine lt_of_le_of_ne (le_inf inf_le_left (inf_le_right.trans hK₁C)) fun heq => ?_
      refine G73.not_inf_le_centralizer h31 hS hG.elem hK₂ fun x hx => ?_
      have hx₀ : x ∈ A₀ := ⟨hx.1, hK₂C hx.2⟩
      rw [← heq] at hx₀
      exact Subgroup.le_centralizer_iff.mp hK₂K₁ hx₀.2
    have hlt' : Nat.card (A ⊓ K : Subgroup G) < Nat.card A₀ :=
      hcard₁ ▸ Subgroup.card_lt_of_lt hlt
    have hAle : Nat.card A ≤ Nat.card (A ⊓ K : Subgroup G) * Nat.card A₀ := by
      calc Nat.card A = Nat.card (A ⊓ K ⊔ A₀ : Subgroup G) := by
            rw [← G73.eq_inf_sup_inf_centralizer h31 hS hG.elem hK]
        _ ≤ _ := card_sup_le hG.elem.1 inf_le_left inf_le_left
    have hA₀sq : Nat.card A < Nat.card A₀ * Nat.card A₀ :=
      lt_of_le_of_lt hAle (Nat.mul_lt_mul_of_pos_right hlt' Nat.card_pos)
    have hcomp : ∀ a₁ ∈ A, a₁ ≠ 1 → ∀ H₁ ∈ CFSG.Walter.benderM a₁, ∀ L : Subgroup G,
        GorensteinWalter.IsComponentOf L (normalClosureIn H₁ A) → L ≤ H := by
      intro a₁ ha₁ ha₁1 H₁ hH₁ L hL
      have hmL := hmin a₁ ha₁ ha₁1 H₁ hH₁ L hL
      have hne : A₀ ⊓ (A ⊓ Subgroup.centralizer (L : Set G)) ≠ ⊥ := by
        intro h0
        have hc : Nat.card (A₀ ⊔ (A ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) =
            Nat.card A₀ * Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
          card_sup_of_inf_eq_bot hG.elem.1 inf_le_left inf_le_left h0
        have hle : Nat.card (A₀ ⊔ (A ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) ≤
            Nat.card A := Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
        have hmL' : Nat.card A₀ ≤ Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
          rw [hKm]
          exact hmL
        have hmul := Nat.mul_le_mul_left (Nat.card A₀) hmL'
        omega
      obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
      intro k hk
      exact CFSG.Walter.centralizer_le_of_mem_benderM (hHmem b hb.1 hb1')
        (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hb.2.2 k hk))
    have hA₀4 : 4 ≤ Nat.card A₀ := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := (G73.isPGroup hG).exists_card_eq
      have hdvd : Nat.card A₀ ∣ 2 ^ n := hn ▸ Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rw [hk] at hA₀sq ⊢
      rcases k with _ | _ | k
      · simp at hA₀sq
        omega
      · simp at hA₀sq
        omega
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hA₀el : CFSG.Open.IsElemAbelian 2 A₀ :=
      ⟨⟨⟨fun x y => Subtype.ext (comm_of_le hG.elem.1 inf_le_left inf_le_left x x.2 y y.2)⟩⟩,
        fun x hx => hG.elem.2 x hx.1⟩
    have hH₁H : ∀ a₁ ∈ A, a₁ ≠ 1 → ∀ H₁ ∈ CFSG.Walter.benderM a₁, H₁ ≤ H := by
      intro a₁ ha₁ ha₁1 H₁ hH₁
      have hAH₁ := G73.le_of_mem_benderM hG ha₁ hH₁
      have hO : oddCoreOf H₁ ≤ H :=
        Completion.le_of_inf_centralizer_le hA₀el hA₀4 (Completion.odd_card_oddCoreOf H₁)
          ((inf_le_left.trans hAH₁).trans (Completion.le_normalizer_oddCoreOf H₁))
          fun b hb hb1 =>
            inf_le_right.trans (CFSG.Walter.centralizer_le_of_mem_benderM (hHmem b hb hb1))
      have hQ : normalClosureIn H₁ A ≤ H := by
        refine (normalClosureIn_le_sup h71 hG h8 ha₁ ha₁1 hH₁).trans
          (sup_le (sup_le (G73.le_of_mem_benderM hG ha hH) ?_) ?_)
        · exact sSup_le fun L hL => hcomp a₁ ha₁ ha₁1 H₁ hH₁ L hL
        · refine (Balance.oddCoreOf_le_of_normal (G73.normalClosureIn_le H₁ A) ?_).trans hO
          exact (Subgroup.normal_subgroupOf_iff_le_normalizer (G73.normalClosureIn_le H₁ A)).mpr
            (G73.le_normalizer_normalClosureIn H₁ A)
      have hAQ : A ≤ normalClosureIn H₁ A :=
        (le_inf le_rfl hAH₁).trans (G73.inf_le_normalClosureIn H₁ A)
      exact (le_sup_normalizer hG.le hG.closed (G73.normalClosureIn_le H₁ A)
        (G73.le_normalizer_normalClosureIn H₁ A) hAQ).trans (sup_le hQ hNH)
    refine not_forall_centralizer_le hG hHco.1 fun c hc hc1 => ?_
    obtain ⟨H₁, hH₁⟩ := G73.benderM_nonempty hG hc1
    exact (CFSG.Walter.centralizer_le_of_mem_benderM hH₁).trans (hH₁H c hc hc1 H₁ hH₁)
  have h2b : Nat.card A₀ ^ 2 ≤ Nat.card A := by
    obtain ⟨g, hgN, hgH⟩ := IsConcreteLE.not_le_iff_exists.mp h3
    have hA₀g : conjSub g A₀ ≤ A := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hgN x).mpr (mem_conjSub.mp hx).1
    have hc := card_sup_of_inf_eq_bot hG.elem.1 inf_le_left hA₀g (h4 g hgN hgH)
    rw [card_conjSub] at hc
    rw [sq, ← hc]
    exact Subgroup.card_le_of_le (sup_le inf_le_left hA₀g)
  exact ⟨a, ha, ha1, H, hH, K, hK, h1, h2a, h2b, h3, h4⟩

end CFSG.Goldschmidt
