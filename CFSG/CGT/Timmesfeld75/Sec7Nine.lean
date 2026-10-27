module

public import CFSG.CGT.Timmesfeld75.Sec7Three
public import CFSG.CGT.Timmesfeld75.Sec78Stmt
public import CFSG.CGT.Timmesfeld75.Lemma26

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.isRootInvolutionSet (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (h66 : Sec66)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m)
    (hno : ∀ d ∈ classD T, ∀ e ∈ classD T, ∀ k : ℕ, Odd k → 3 ≤ k → orderOf (d * e) ≠ 2 * k) :
    CFSG.Timmesfeld.IsRootInvolutionSet (classD T) := by
  have hTab := hc.hy.pair.wc.1
  refine ⟨fun d hd => ?_, fun d hd e he => ?_, fun d hd e he h4 => h66 G T T₁ n m hc d hd e he h4⟩
  · obtain ⟨g, t, ht, ht1, rfl⟩ := hd
    rw [orderOf_inv_mul_mul_eq]
    exact orderOf_eq_prime (hTab.2 t ht) ht1
  · obtain ⟨h4 | hodd | ⟨k, hk, hk2⟩, -⟩ := hc.sec73 h1 h62 h63 h66 hA8 hnat hd he
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr hodd)
    · rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · obtain ⟨c, hc'⟩ := hk
        left
        rw [hk2]
        omega
      · exact absurd hk2 (hno d hd e he k hk hk3)

theorem classD_isConj (h57 : Step57) (hy : StepHyp T T₁) :
    ∃ d₀ : G, classD T = {g | IsConj d₀ g} := by
  have hTbot : T ≠ ⊥ := by
    rintro rfl
    have := hy.card
    rw [Subgroup.card_bot] at this
    omega
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTbot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  refine ⟨t, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨g, s, hs, hs1, rfl⟩
    obtain ⟨h, -, hts⟩ := h57 G T T₁ hy t ht ht1' s hs hs1
    exact isConj_iff.2 ⟨g⁻¹ * h, by rw [← hts]; group⟩
  · intro hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    exact ⟨c⁻¹, t, ht, ht1', by rw [← hc]; group⟩

theorem listGroup_of_root (h26 : Lemma26Input) [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) (hT : IsWC T) (h4 : 2 < Nat.card T)
    (hcl : ∃ d₀ : G, classD T = {g | IsConj d₀ g})
    (hroot : CFSG.Timmesfeld.IsRootInvolutionSet (classD T)) : ListGroup G := by
  have hTbot : T ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h4
    omega
  have hgen : Subgroup.closure (classD T) = ⊤ := by
    rw [closure_classD_eq_normalClosure]
    exact normalClosure_eq_top_of_simple hTbot
  obtain ⟨hmod, -⟩ := h26 G T hT h4 hcl hroot hgen
  have hlist : ListGroup (G ⧸ Subgroup.center G) := by
    rcases hmod with ⟨n', m', hn', hm', hmodel⟩ | ⟨m', hm', hmodel⟩ | ⟨s, hs, hs3, hmodel⟩ | ⟨e⟩
    · exact Or.inl ⟨n', m', hn', hm', hmodel⟩
    · exact Or.inr (Or.inl ⟨m', hm', hmodel⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, hs, hs3, hmodel⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨6, le_refl _, by norm_num, e⟩)))
  have hc : Subgroup.center G = ⊥ := center_eq_bot_of_simple_nonabelian G hna
  exact ListGroup.of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)).symm hlist

theorem step79_of (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    (h57 : Step57) (h26 : Lemma26Input) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (h66 : Sec66) (h78 : Sec78) : Step79 := by
  intro G _ T T₁ hy n m hn4 hm hA8 hq hT hnat
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hP.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  have hc : Sec6Ctx T T₁ n m := ⟨hy, hS, hI, hq, hT, Or.inr (Or.inl hnat)⟩
  have hroot := hc.isRootInvolutionSet h1 h62 h63 h66 hA8 hnat
    (fun d hd e he k hk hk3 => h78 G T T₁ n m hc hnat hn4 hA8 d hd e he k hk hk3)
  exact listGroup_of_root h26 hy.nonab hP.wc (by have := hy.card; omega)
    (classD_isConj h57 hy) hroot

theorem step711_of (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    (h57 : Step57) (h26 : Lemma26Input) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (h66 : Sec66) (h710 : Sec710) : Step711 := by
  intro G _ T T₁ hy m hm hq hT hnat
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hP.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  have hc : Sec6Ctx T T₁ 3 m := ⟨hy, hS, hI, hq, hT, Or.inr (Or.inl hnat)⟩
  have hroot := hc.isRootInvolutionSet h1 h62 h63 h66 (by omega) hnat
    (fun d hd e he k hk hk3 => h710 G T T₁ m hc hnat hm d hd e he k hk hk3)
  exact listGroup_of_root h26 hy.nonab hP.wc (by have := hy.card; omega)
    (classD_isConj h57 hy) hroot

end CFSG.CGT.Timmesfeld75
